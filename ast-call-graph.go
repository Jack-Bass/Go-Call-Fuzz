package main

import (
	"bytes"
	crypto "crypto/rand"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"go/types"
	"log"
	"math"
	"math/big"
	"math/rand"
	"os"
	"strings"
	"unicode"

	"golang.org/x/text/cases"
	"golang.org/x/text/language"
	"golang.org/x/tools/go/cfg"
)

// Impose an upper bound on the length of enumerated paths
// Only necessary when program is very large
const maxPathLen int = 10
const maxDfsIter = 5000000

/*
 * Generate a random byte array.  This is useful for providing input data to
 * fuzz tests.  Generally, it is bad practice to start with an empty corpus,
 * and I can attest to an empty corpus not helping very much.
 *
 * Generating random data is useful in a sense that it is literally fed to the
 * static testing file as well as used to generate said randomness here.
 */

func getRandomBytes() []byte {
	// TODO: Consider adding a variable upper bound
	length := rand.Intn(100)
	bytes := make([]byte, length)
	crypto.Read(bytes)
	return bytes
}

// TODO: Rand refactor
const letters string = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

// TODO: Refactor documentation comments to match Go's style

/*
 * Similar to above method, but this gives us a random string from random bytes.
 */
func getRandomString() string {
	length := rand.Intn(100)
	bytes := make([]byte, length)
	for i := range bytes {
		bytes[i] = letters[rand.Intn(len(letters))]
	}
	return string(bytes)
}

/*
 * Need to be able to identify types mainly when we automate writing fuzz tests.
 * Names are not strictly necessary but make assigning variable names easier.
 */

type parameter struct {
	paramName    string
	paramType    ast.Expr
	paramPackage string `default:""` // used for struct parameters
}

type fuzzTarget struct {
	method     method
	parameters []parameter
}

/*
 * A string representation of a fuzz target is simply its
 * invocation.
 *
 * For example, consider a method foo.func() with parameters
 * int a, string b.
 *
 * This should return "foo.func(a, b)"
 */
func (target fuzzTarget) String() string {
	out := fmt.Sprintf("%s(", target.method)

	for i, param := range target.parameters {
		out += param.paramName

		if i < len(target.parameters)-1 {
			out += ", "
		}
	}

	return out + ")"
}

/*
 * Checking parameters is unnecessary, since sharing a method would
 * imply the parameters are the same.
 */
/*
func (target fuzzTarget) equals(otherTarget fuzzTarget) bool {
	return target.method.equals(otherTarget.method)
}
*/

type method struct {
	name         string
	body         []*cfg.Block
	pkgName      string
	fileName     string
	fset         *token.FileSet
	details      *ast.FuncType
	isReceiver   bool   `default:"false"`
	receiverName string `default:""`
	receiverType ast.Expr
}

func (thisMethod method) equals(otherMethod method) bool {
	return thisMethod.name == otherMethod.name &&
		thisMethod.pkgName == otherMethod.pkgName
}

/**
 * "Overriding" toString() functionality for methods.
 */
func (meth method) String() string {
	return fmt.Sprintf("%s.%s", meth.pkgName, meth.name)
}

type callGraphEdge struct {
	caller method
	callee method
}

func (thisEdge callGraphEdge) equals(otherEdge callGraphEdge) bool {
	// Equal if caller and callee methods equal
	return thisEdge.caller.equals(otherEdge.caller) && thisEdge.callee.equals(otherEdge.callee)
}

func (edge callGraphEdge) toGraphvizString() string {
	// if tables are enabled
	//return edge.caller.pkgName + ":" + edge.caller.name + " -> " + edge.callee.pkgName + ":" + edge.callee.name + ";"

	// Experiment with more complicated names later
	return "\"" + edge.caller.pkgName + "\\n" + edge.caller.name + "\" -> \"" + edge.callee.pkgName + "\\n" + edge.callee.name + "\";"
}

/**
 * DEBUG: Overriding toString() functionality for a GV edge
 */
func (edge callGraphEdge) String() string {
	return fmt.Sprintf("%s.%s -> %s.%s", edge.caller.pkgName, edge.caller.name, edge.callee.pkgName, edge.callee.name)
}

type callGraphAnalyzer struct {
	graphs     []*cfg.CFG
	blocks     map[int32]*cfg.Block
	methods    []method
	edges      []callGraphEdge
	packages   []string
	startNodes []method
	startNode  *method
	exitNode   *method
	interfaces []string
	structs    []string
}

/*
 * Return whether a given function call is tracked by this analyzer.
 */
func (analyzer callGraphAnalyzer) isFunctionCall(methodName string) bool {
	for _, method := range analyzer.methods {
		if methodName == method.name {
			return true
		}
	}

	return false
}

func nodeString(n ast.Node, fset *token.FileSet) string {
	var b bytes.Buffer
	format.Node(&b, fset, n)
	return b.String()
}

func formatNodeHtml(fset *token.FileSet, n ast.Node) string {
	str := nodeString(n, fset)
	sanitized := strings.ReplaceAll(str, "&", "&amp;")
	sanitized = strings.ReplaceAll(sanitized, "<=", "&le;")
	sanitized = strings.ReplaceAll(sanitized, ">=", "&ge;")
	sanitized = strings.ReplaceAll(sanitized, "<", "&lt;")
	sanitized = strings.ReplaceAll(sanitized, ">", "&gt;")
	sanitized = strings.ReplaceAll(sanitized, "\t", "")

	return sanitized
}

/*
 * If the given node is an assignment statement or call statement that
 * calls another method, we can get the callee if it is one of the method
 * names linked to this analyzer.
 */
func (analyzer callGraphAnalyzer) getCallees(node ast.Node, fset *token.FileSet) []method {
	_, isCall := node.(*ast.ExprStmt)
	_, isAssn := node.(*ast.AssignStmt)
	var calls []method = make([]method, 0)

	if isCall || isAssn {
		str := nodeString(node, fset)

		// Assignment statement takes the form
		// variable = Expression, where expression can include function call(s)
		if isAssn {
			// If no function is called, there is no callee
			if !strings.Contains(str, "(") {
				return calls
			}
		}

		funcs := strings.Split(str, ")")
		for _, f := range funcs {
			funcCalls := analyzer.parseFunctions(f, isAssn)
			calls = append(calls, funcCalls...)
		}
	}

	return calls
}

func (analyzer callGraphAnalyzer) parseFunctions(str string, isAssn bool) []method {
	var funcs []method = make([]method, 0)

	// Replicate do-while functionality
	// Stop when index of "(" is -1
	start := 0
	orig := str

	for strings.Contains(str, "(") {
		if start >= len(orig) {
			break
		}

		// var pkg string
		// pkg = ""
		str = str[:strings.Index(str, "(")]
		i := strings.LastIndex(str, ".")
		if i > -1 && i != len(str)-1 {
			// don't go backwards
			/*
				if strings.LastIndex(str, " ")+1 < i {
					pkg = str[strings.LastIndex(str, " ")+1 : i]
				}
			*/
			str = str[i+1:]
		}

		// remove newlines if any?
		str = strings.Replace(str, "\r", "", -1)
		str = strings.Replace(str, "\n", "", -1)
		str = strings.Replace(str, "\t", "", -1)

		// remove all spaces
		str = strings.Replace(str, " ", "", -1)

		if isAssn {
			if strings.Contains(str, "=") {
				str = str[strings.Index(str, "=")+1:]
			} else {
				// Starting index is 1 after comma or 0
				if strings.Contains(str, ",") {
					str = str[strings.Index(str, ",")+1:]
				}
			}

			// first characetr is an operator
			// TODO: Definitely a way to refactor this
			// For example, does not support ternary, inequality, etc.
			ops := []byte{'+', '-', '*', '/'}
			for _, op := range ops {
				if len(str) > 0 && str[0] == op {
					str = str[1:]
					break
				}
			}
		}

		// Add call to output
		if analyzer.isFunctionCall(str) {
			// map to all methods with matching name
			methods := analyzer.mapStringToMethod(str)

			// check for duplicates
			isDuplicate := false
			for _, f := range funcs {
				for _, method := range methods {
					if f.equals(method) {
						isDuplicate = true
						break
					}
				}

				if isDuplicate {
					break
				}
			}

			if !isDuplicate {
				funcs = append(funcs, methods...)
			} else {
				return funcs
			}
		} else {
			return funcs
		}

		// Reset str
		start = strings.Index(orig, str) + len(str) + 1
		if start < len(orig) {
			str = orig[start:]
		} else {
			str = ""
		}
	}

	return funcs
}

func (analyzer *callGraphAnalyzer) mapStringToMethod(methodName string) []method {
	var methods []method = make([]method, 0)
	for _, method := range analyzer.methods {
		if method.name == methodName {
			methods = append(methods, method)
		}
	}
	return methods
}

func (analyzer *callGraphAnalyzer) enumerateEdges() {
	/*
	 * For each method body,
	 * isolate method calls to list of methods we know
	 */
	for _, caller := range analyzer.methods {
		methodBody := caller.body
		for _, block := range methodBody {
			for _, node := range block.Nodes {
				callees := analyzer.getCallees(node, caller.fset)

				for _, callee := range callees {
					edge := callGraphEdge{
						caller: caller,
						callee: callee,
					}

					// TODO: More efficient way to check duplicates?
					var isDuplicateEdge bool = false
					for _, callGraphEdge := range analyzer.edges {
						if edge.equals(callGraphEdge) {
							isDuplicateEdge = true
							break
						}
					}

					if !isDuplicateEdge {
						analyzer.edges = append(analyzer.edges, edge)
					}
				}
			}
		}
	}
}

func (analyzer callGraphAnalyzer) writeDigraphToFile(mocksDir string) {
	outputPackage := mocksDir[strings.LastIndex(mocksDir, "/")+1:]
	outputDir := "./out/" + outputPackage
	var outputFile string = "cfg.out.txt"
	outputPath := fmt.Sprintf("%s/%s", outputDir, outputFile)

	// create output directory if it does not exist
	os.MkdirAll(outputDir, os.ModePerm)

	// remove pre-existing call graph if it does exist
	_, err := os.Stat(outputPath)
	if err == nil {
		os.Remove(outputPath)
	}

	file, err := os.Create(outputPath)
	if err != nil {
		log.Fatal(err)
	}

	var outputString string = ""
	outputString += "digraph G {\n"

	// edit graph style
	outputString += "\trankdir=\"LR\";\n"
	//outputString += "\tsplines=true;\n"

	outputString += "\tedge [style=\"dashed\"];\n\n"

	for _, edge := range analyzer.edges {
		outputString += "\t" + edge.toGraphvizString() + "\n"
	}

	outputString += "}\n"

	// Write file
	file.WriteString(outputString)

	if err := file.Close(); err != nil {
		log.Fatal(err)
	}

	fmt.Println("Successfully wrote Graphviz output to " + outputPath)
}

func CreateCallGraph(paths []string, moduleDir string, allImports []string, mocksDir string) {
	var analyzer callGraphAnalyzer = callGraphAnalyzer{
		graphs:     make([]*cfg.CFG, 0),
		blocks:     make(map[int32]*cfg.Block, 0),
		methods:    make([]method, 0),
		edges:      make([]callGraphEdge, 0),
		packages:   make([]string, 0),
		startNodes: make([]method, 0),
		startNode:  nil,
		exitNode:   nil,
		interfaces: make([]string, 0),
		structs:    make([]string, 0),
	}

	for i, path := range paths {
		// Print debug information
		fmt.Println("Parsing file ", path, ": ", (i + 1), " of ", len(paths))

		fset := token.NewFileSet()
		node, err := parser.ParseFile(fset, path, nil, 0)
		if err != nil {
			log.Fatal(err)
		}

		// Find local interfaces and structs
		// Modified from: https://scene-si.org/2018/06/19/listing-interfaces-with-go-ast-for-gomock-moq/
		// Of course, this needs to be refactored anyway.
		ast.Inspect(node, func(n ast.Node) bool {
			switch t := n.(type) {
			case *ast.TypeSpec:
				switch t.Type.(type) {
				case *ast.InterfaceType:
					analyzer.interfaces = append(analyzer.interfaces, t.Name.Name)
				case *ast.StructType:
					analyzer.structs = append(analyzer.structs, t.Name.Name)
				}
			}
			return true
		})

		for _, f := range node.Decls {
			fn, ok := f.(*ast.FuncDecl)
			if !ok {
				continue
			}

			bs := fn.Body

			mayReturn := func(ce *ast.CallExpr) bool {
				name := formatNodeHtml(fset, ce.Fun)

				bannedFunctions := []string{"panic", "log.Fatal", "os.Exit"}
				var willReturn bool = true

				for _, banned := range bannedFunctions {
					if name == banned {
						willReturn = false
						break
					}
				}

				return willReturn
			}

			graph := cfg.New(bs, mayReturn)

			// See if this is a normal function or receiver method
			receiverName := ""
			var receiverType ast.Expr
			isReceiver := false
			if fn.Recv != nil {
				isReceiver = true

				if len(fn.Recv.List) > 0 {
					name := ""
					if len(fn.Recv.List[0].Names) > 0 {
						name = fn.Recv.List[0].Names[0].String()
					}

					typ := fn.Recv.List[0].Type
					// typ = typ[strings.Index(typ, "*")+1:]
					receiverName = name
					receiverType = typ
				}
			}

			// Keep track of method names and bodies
			method := method{
				name:         fn.Name.Name,
				body:         graph.Blocks,
				pkgName:      node.Name.Name,
				fileName:     path,
				fset:         fset,
				details:      fn.Type,
				isReceiver:   isReceiver,
				receiverName: receiverName,
				receiverType: receiverType,
			}

			// Keep track of program's entry point
			if method.name == "main" {
				analyzer.startNodes = append(analyzer.startNodes, method)
			}

			analyzer.graphs = append(analyzer.graphs, graph)
			analyzer.methods = append(analyzer.methods, method)

			// Incorporate package information
			duplicatePackage := false
			pack := node.Name.Name
			for _, pkg := range analyzer.packages {
				if pkg == pack {
					duplicatePackage = true
					break
				}
			}

			if !duplicatePackage {
				analyzer.packages = append(analyzer.packages, pack)
			}
		}
	}

	fmt.Println("Finished parsing provided files.")

	// Find all caller->callee edges
	analyzer.enumerateEdges()

	fmt.Println("Finished enumerating edges.")

	// add dummy start node
	start := method{
		name:       "START",
		body:       make([]*cfg.Block, 0),
		pkgName:    "START",
		fileName:   "START",
		fset:       nil,
		isReceiver: false,
	}
	analyzer.startNode = &start
	analyzer.methods = append(analyzer.methods, start)

	// add dummy exit node
	exit := method{
		name:       "EXIT",
		body:       make([]*cfg.Block, 0),
		pkgName:    "EXIT",
		fileName:   "EXIT",
		fset:       nil,
		isReceiver: false,
	}
	analyzer.exitNode = &exit
	analyzer.methods = append(analyzer.methods, exit)

	programPaths := analyzer.enumeratePaths()

	fmt.Println("Finished enumerating paths.")

	// Connect exit back to start
	uniqueMethods := analyzer.getUsedMethods()
	fmt.Println("Finished getting used methods.")

	analyzer.createStronglyConnectedGraph(uniqueMethods)
	fmt.Println("Finished creating SCC.")

	scc := analyzer.tarjanScc(uniqueMethods)
	fmt.Println("Applied Tarjan's SCC algorithm.")

	// Compute cyclomatic complexity
	// M = E - N + P
	numEdges := len(analyzer.edges)
	numNodes := len(uniqueMethods)
	numCycles := len(scc)
	cycloComp := numEdges - numNodes + numCycles
	fmt.Printf("M = E - N + P = %d - %d + %d = %d\n", numEdges, numNodes, numCycles, cycloComp)

	// Construct graphviz output
	analyzer.writeDigraphToFile(mocksDir)

	fmt.Printf("M = %d, and there are %d paths.\n\n", cycloComp, len(programPaths))

	// Use generated paths to write fuzz test signatures
	fuzzTargets := generateFuzzTests(programPaths)

	writeFuzzTestsToFile(fuzzTargets, allImports, analyzer.structs, mocksDir)
}

/*
 * This method writes the methods we want to fuzz to a file.  Generally,
 * fuzz tests in Go can follow the same format, but modifications may be
 * necessary for more special methods (aka, non-primitive ones).
 *
 * Currently, this does not support import statements like
 * foo "/path/to/pkg"
 *
 * Instead, imports are treated like:
 * "/path/to/pkg/foo"
 */
func writeFuzzTestsToFile(targets []fuzzTarget, allImports, structs []string, mocksDir string) {
	// Extract directory name from mocksDir
	outputPackage := mocksDir[strings.LastIndex(mocksDir, "/")+1:]
	outputDir := fmt.Sprintf("./fuzzing_test/%s/", outputPackage)

	// create directory if not exists
	os.MkdirAll(outputDir, os.ModePerm)

	outputFile := fmt.Sprintf("%s/fuzz_test.go", outputDir)

	// Remove fuzz file if it already exists
	_, err := os.Stat(outputFile)
	if err == nil {
		os.Remove(outputFile)
	}

	// Create new file
	file, err := os.Create(outputFile)
	if err != nil {
		log.Fatal(err)
	}

	// Write "preamble"
	out := ""
	out += fmt.Sprintf("package fuzzing_test_%s\n\n", outputPackage)
	out += "import (\n"
	// out += "\t\"testing\"\n\n"

	// import necessary packages
	// This is a bit overkill, but remocing some unnecessary imports
	// does not seem like too big of an ask in the grand scheme of things.
	for _, imp := range allImports {
		out += "\t" + imp + "\n"
	}

	// Import fuzz-headers
	out += "\t" + `fuzz "github.com/AdaLogics/go-fuzz-headers"` + "\n"

	// Add local and dependency mocks
	out += "\t" + `gcf "github.com/Jack-Bass/Go-Call-Fuzz/gcf_mocks/` + outputPackage + `"` + "\n"
	out += "\t" + `gcfDep "github.com/Jack-Bass/Go-Call-Fuzz/gcf_mocks/dependencies"` + "\n"
	out += ")\n"

	// Create skeletons for each fuzz target
	for _, target := range targets {
		test, isValidTest := generateFuzzTestSkeleton(target, structs, mocksDir)

		if isValidTest {
			out += "\n"
			out += test
			out += "\n"
		}
	}

	file.WriteString(out)
	fmt.Println("Successfully wrote Graphviz output to " + outputFile)
}

/*
 * These are the types that Go's default fuzzer can handle.
 * This method helps determine if we need to use struct-aware fuzzing.
 */
func isDefaultFuzzable(typeStr string) bool {
	acceptedTypes := []string{
		"[]byte",
		"string",
		"bool",
		"byte",
		"rune",
		"float32",
		"float64",
		"int",
		"int8",
		"int16",
		"int32",
		"int64",
		"uint",
		"uint8",
		"uint16",
		"uint32",
		"uint64",
	}

	for _, acc := range acceptedTypes {
		if acc == typeStr {
			return true
		}
	}

	return false
}

/*
 * Originally, I thought an empty corpus would be good enough.  However, the
 * fuzzer really won't generate anything on its own with an empty corpus unless
 * it's a very simple toy example like divide-by-zero.
 *
 * Thus, we can initialize the corpus with some random values every time we run
 * this program.  Most values will be complex and thus fall under the []byte
 * "catch-all", so we'll see what other simple types need to be randomized.
 * Throwing an exception here is probably a bad idea, but it would also be a
 * waste of time to create random inputs for types I never actually use as
 * parameters.
 */
func generateCorpus(typesArr []string) string {
	// TODO: Change/parameterize the upper bound?
	ub := 100
	i := 0
	corpus := ""

	for i < ub {
		// Create new corpus entry
		corpus += "\tf.Add("

		for j, typeStr := range typesArr {
			// generate new input for this type
			entry := ""

			if typeStr == "int" {
				entry = fmt.Sprintf("%d", rand.Int())
			} else if typeStr == "uint8" {
				var num uint = uint(rand.Intn(math.MaxUint8))
				entry = fmt.Sprintf("%d", num)
			} else if typeStr == "uint32" {
				entry = fmt.Sprintf("%d", rand.Uint32())
			} else if typeStr == "int64" {
				// Create random int64 using big int
				max := new(big.Int)
				max.Exp(big.NewInt(2), big.NewInt(63), nil).Sub(max, big.NewInt(1))

				//Generate cryptographically strong pseudo-random between 0 - max
				n, err := crypto.Int(crypto.Reader, max)
				if err != nil {
					//error handling
					fmt.Println("Failed to create random big int")
					panic(err)
				}

				// represent big int in base-10
				entry = n.Text(10)

				// Since a big int is much bigger than an int64,
				// Want to make sure we do not pass a number too big to the corpus
				if len(entry) > 18 {
					entry = entry[:19]
				}
			} else if typeStr == "float64" {
				maxFloat := math.MaxFloat64

				// Generate random float64 between max and min
				randFloat := 2*rand.Float64()*maxFloat/2 - maxFloat/2

				entry = fmt.Sprintf("%f", randFloat)
			} else if typeStr == "string" {
				entry = fmt.Sprintf("\"%s\"", getRandomString())
			} else if typeStr == "[]byte" {
				bytes := getRandomBytes()
				entry = "[]byte{"

				for k, b := range bytes {
					entry += fmt.Sprintf("%d", b)

					if k < len(bytes) {
						entry += ", "
					}
				}

				entry += "}"
			} else if typeStr == "bool" {
				coin := rand.Float32()
				b := (coin < 0.5)
				entry = fmt.Sprintf("%t", b)
			} else {
				// Have to manually fix these when they occur
				// This will be removed in the future.
				fmt.Println("WARNING: ")
				fmt.Print("Do not know how to randomize type " + typeStr + "!\n\n\n")
			}

			corpus += entry

			if j < len(typesArr) {
				corpus += ", "
			}
		}

		corpus += ")\n"
		i++
	}

	corpus += "\n"
	return corpus
}

/*
 * Every fuzz target takes a similar shape when crafting a fuzz harness.
 * This method takes its parameters and types to create a harness
 * specifically-suited for calling it.
 */
func generateFuzzTestSkeleton(target fuzzTarget, structs []string, mocksDir string) (string, bool) {

	// determine if we can use default skeleton or struct-aware skeleton
	isDefaultSkeleton := isDefaultFuzzableTarget(target)

	if isDefaultSkeleton {
		// Anything that gets this far should be a valid call,
		// since invalid methods so far should be flagged as
		// struct-aware skeletons.
		return getDefaultSkeleton(target), true
	} else {
		return getStructAwareSkeleton(target, structs, mocksDir)
	}
}

func getDefaultSkeleton(target fuzzTarget) string {
	out := ""

	// Add package as title in case methods have duplicate names
	pkgUpper := cases.Title(language.English, cases.Compact).String(target.method.pkgName)
	out += fmt.Sprintf("func Fuzz%s%s(f *testing.F) {\n", pkgUpper, target.method.name)
	out += "\tf.Fuzz(func(gcfT *testing.T, "

	// insert parameters
	typesArr := make([]string, 0)
	for i, param := range target.parameters {
		typeString := types.ExprString(param.paramType)
		out += fmt.Sprintf("%s %s", param.paramName, typeString)

		if i < len(target.parameters)-1 {
			out += ", "
		}

		typesArr = append(typesArr, typeString)
	}

	out += ") {\n"

	// Add random parameters to corpus
	corpus := generateCorpus(typesArr)

	// insert corpus before call to Fuzz
	out = out[:strings.Index(out, "\t")] + corpus + out[strings.Index(out, "\t"):]

	// Add function call
	call := fmt.Sprintf("\t\t%s\n", target)
	if target.method.isReceiver {
		// Follow variable.Method() instead of package.Method()
		methodStr := target.method.String()
		newCall := fmt.Sprintf("%s.%s", target.method.receiverName, methodStr[strings.Index(methodStr, ".")+1:])

		call = fmt.Sprintf("\t\t%s\n", newCall)
	}
	out += fmt.Sprintf("\t\t%s\n", call)

	// end function
	out += "\t})\n"
	out += "}\n"
	return out
}

/*
 * This method generates a fuzz harness for a fuzz target with one or more
 * structs/interfaces as parameters.  Since these are not acceptable using the
 * default Go fuzzing, this leverages other packages.
 */
func getStructAwareSkeleton(target fuzzTarget, structs []string, mocksDir string) (string, bool) {
	out := ""

	// No use using this call if it is private
	if target.method.isReceiver {
		if len(target.method.receiverName) == 0 {
			return out, false
		}

		if unicode.IsLower(rune(target.method.receiverName[0])) {
			return out, false
		}
	}

	// Add package as title in case methods have duplicate names
	pkgUpper := cases.Title(language.English, cases.Compact).String(target.method.pkgName)
	out += fmt.Sprintf("func Fuzz%s%s(f *testing.F) {\n", pkgUpper, target.method.name)
	out += "\tf.Fuzz(func(gcfT *testing.T, "

	var structParams []parameter = make([]parameter, 0)

	// insert default-fuzzable parameters
	typesArr := make([]string, 0)
	for _, param := range target.parameters {
		typeString := types.ExprString(param.paramType)

		if !isDefaultFuzzable(typeString) {
			structParams = append(structParams, param)
			continue
		}

		typesArr = append(typesArr, typeString)
		out += fmt.Sprintf("%s %s", param.paramName, typeString)

		// params here will never be the last one unlike before
		out += ", "
	}

	// Will use this data to fuzz structs
	out += "data []byte) {\n"
	typesArr = append(typesArr, "[]byte")

	// Create consumer
	out += "\t\tconsumer := fuzz.NewConsumer(data)\n"
	out += "\t\tconsumer.AllowUnexportedFields()\n" // hidden data in struct, may need to disable

	// If our method is a receiver, we need to create another struct.
	if target.method.isReceiver {
		var p parameter = parameter{
			paramName:    target.method.receiverName,
			paramType:    target.method.receiverType,
			paramPackage: target.method.pkgName,
		}

		template, isValidTemplate := getStructParamTemplate(p, structs, mocksDir)
		if isValidTemplate {
			out += template
		} else {
			return out, false
		}
	}

	// For each struct parameter, generate data using consumer
	for _, structParam := range structParams {
		template, isValidTemplate := getStructParamTemplate(structParam, structs, mocksDir)

		if isValidTemplate {
			out += template
		} else {
			return out, false
		}
	}

	// Add random parameters to corpus
	corpus := generateCorpus(typesArr)

	// insert corpus before call to Fuzz
	out = out[:strings.Index(out, "\t")] + corpus + out[strings.Index(out, "\t"):]

	// Add function call
	call := fmt.Sprintf("\t\t%s\n", target)
	if target.method.isReceiver {
		// Follow variable.Method() instead of package.Method()
		methodStr := target.method.String()
		newCall := fmt.Sprintf("%s.%s", target.method.receiverName, methodStr[strings.Index(methodStr, ".")+1:])

		call = fmt.Sprintf("\t\t%s\n", newCall)
	}
	out += fmt.Sprintf("\t\t%s\n", call)

	// end function
	out += "\t})\n"
	out += "}\n"

	return out, true
}

/*
 * This method generates a few lines of code that will create and initialize
 * a struct using the go-fuzz-headers package.
 */
func getStructParamTemplate(structParam parameter, structs []string, mocksDir string) (string, bool) {
	out := ""
	typeString := types.ExprString(structParam.paramType)

	/*
	 * Outside interfaces may be used, which I was unable to account for.
	 * However, I have had better luck with assuming all structs used will
	 * be defined locally.  I can't say I expect that to stay true forever
	 * though.
	 */
	isStruct := func(typeString string) bool {
		name := typeString[strings.LastIndex(typeString, ".")+1:]
		for _, iName := range structs {
			if iName == name {
				return true
			}
		}

		return false
	}

	// search specified directory for wanted mock file
	searchDir := func(path, alias string) bool {
		files, err := os.ReadDir(path)
		if err != nil {
			log.Fatal(err)
		}

		for _, file := range files {
			var typeWithoutPkg string = typeString[strings.Index(typeString, ".")+1:]
			// All generated mocks should follow: mock_<name>.go
			expectedFilename := fmt.Sprintf("mock_%s.go", typeWithoutPkg)

			if !file.IsDir() && file.Name() == expectedFilename {
				out += fmt.Sprintf("\t\t%s := %s.NewMock%s(gcfT)\n", structParam.paramName, alias, typeWithoutPkg)
				return true
			}
		}

		return false
	}

	if !isStruct(typeString) {
		// Incorporate mocks instead

		// see if file exists locally or as a dependency
		isLocal := searchDir(mocksDir, "gcf")
		isDependency := searchDir("./gcf_mocks/dependencies/", "gcfDep") // TODO: Better way of doing this
		isFound := isLocal || isDependency

		// If we cannot represent this struct, then this fuzz test is useless
		if !isFound {
			// out += fmt.Sprintf("\t\tvar %s %s\n", structParam.paramName, typeString)
			return out, false
		}
	} else {
		// Should annotate references (pointers)
		initVarRef := ""
		generateCallRef := ""
		if strings.Index(typeString, "*") == 0 {
			// Can't declare a struct as *Foo{}
			// need to use reference &Foo{} instead
			typeString = typeString[1:]
			initVarRef = "&"
		} else {
			// Need to pass a reference to GenerateStruct
			generateCallRef = "&"
		}

		/*
		 * At this point, a struct must be valid.  There are two types:
		 * 1. Struct is local to this package
		 * 2. Struct is from another package in the program.
		 *     - In this case, do not refer to this package in invocation.
		 */
		fullName := fmt.Sprintf("%s.%s{}", structParam.paramPackage, typeString)

		// if two packages, then there are multiple periods
		firstPeriod := strings.Index(fullName, ".")
		lastPeriod := strings.LastIndex(fullName, ".")
		if firstPeriod != lastPeriod {
			// truncate FQN to only include second (external) package
			fullName = fullName[firstPeriod+1:]
		}

		// go-fuzz-headers must take a pointer as an argument
		out += fmt.Sprintf("\t\t%s := %s%s\n", structParam.paramName, initVarRef, fullName)

		// dereference parameter if necessary
		out += fmt.Sprintf("\t\tconsumer.GenerateStruct(%s%s)\n", generateCallRef, structParam.paramName)
	}

	return out, true
}

/*
 * A target is default fuzzable iff all of its parameters are default fuzzable.
 */
func isDefaultFuzzableTarget(target fuzzTarget) bool {
	for _, param := range target.parameters {
		typeString := types.ExprString(param.paramType)
		if !isDefaultFuzzable(typeString) {
			return false
		}
	}

	// Only default fuzzable if this is a function call, not a receiver method
	return !target.method.isReceiver
}

/*
 * Given a list of paths to traverse, this method creates a list of
 * fuzz targets that can then be used to craft a fuzz harness in a
 * testing file.  In particular, this extracts the method names and
 * parameters we need to analyze in order to automate the fuzz
 * harness generation.
 */
func generateFuzzTests(paths [][]method) []fuzzTarget {
	var targets []fuzzTarget = make([]fuzzTarget, 0)

	isPrivate := func(name string) bool {
		// targetName := name[strings.Index(name, ".")+1:]
		return unicode.IsLower(rune(name[0]))
	}

	isDuplicate := func(meth method, methods []fuzzTarget) bool {
		for _, tar := range methods {
			if tar.method.equals(meth) {
				return true
			}
		}
		return false
	}

	for _, path := range paths {
		if len(path) < 2 {
			continue
		}

		targetMethod := path[1]
		params := targetMethod.details.Params

		// Essentially, ignore functions without any parameters, since
		// we can't use them for testing random inputs
		i := 1
		noTarget := false // in case no methods on the path are unique
		for ok := true; ok && i < len(path); {
			targetMethod = path[i]
			params = targetMethod.details.Params

			// Check for dupliate target
			isDup := isDuplicate(targetMethod, targets)

			// Cannot access a private method in testing file
			isPrivateMethod := isPrivate(targetMethod.name)

			// If duplicate, try next method in line.
			// If we reach the end, then there is no method
			// we can add.
			if !isDup && !isPrivateMethod {
				ok = false
			} else if i >= len(path) {
				noTarget = true
				ok = false
			}

			i++
		}

		// Ensure chosen method is still valid to add as a target
		if noTarget || isPrivate(targetMethod.name) || len(params.List) == 0 || isDuplicate(targetMethod, targets) {
			continue
		}

		// Create fuzz target
		var target fuzzTarget = fuzzTarget{
			method:     targetMethod,
			parameters: make([]parameter, 0),
		}

		fmt.Printf("Principal method to investigate: %s\n", target.String())

		// Extract function parameters and types for generating inputs later
		// There is a nonzero chance I shot myself in the foot by removing the null
		// checks that were here before, but if we only get here by finding
		// parameters that are guaranteed to be non-empty, I don't see why the
		// checks would be strictly necessary.
		extractParameters := func(fl *ast.FieldList) {
			list := fl.List

			for _, n := range list {
				for _, name := range n.Names {
					param := parameter{
						paramName:    name.Name,
						paramType:    n.Type,
						paramPackage: target.method.pkgName,
					}

					fmt.Println(name)
					target.parameters = append(target.parameters, param)
				}
			}
		}

		extractParameters(params)
		targets = append(targets, target)
	}

	return targets
}

func (analyzer callGraphAnalyzer) enumeratePaths() [][]method {
	var paths [][]method = make([][]method, 0)

	// Initialize path variables
	var timesVisited map[string]int = make(map[string]int)
	var inDegree map[string]int = make(map[string]int)
	for _, start := range analyzer.startNodes {
		inDegree[start.String()]++
	}

	for _, e := range analyzer.edges {
		inDegree[e.callee.String()]++
	}

	// initial path
	path := []method{analyzer.startNodes[0]}

	// const maxIterations int = 1000
	numIterations := 0

	var dfsUtil func(path []method)
	dfsUtil = func(path []method) {
		numIterations++

		if numIterations >= maxDfsIter {
			paths = append(paths, path)
			return
		}

		if numIterations%10000 == 0 {
			fmt.Println("Visited DFS util ", numIterations, " time(s).")
		}

		u := path[len(path)-1]

		if timesVisited[u.String()] >= inDegree[u.String()] {
			return
		}

		// mark u as visited
		timesVisited[u.String()]++

		// get successors of u
		var succs []method = make([]method, 0)
		for _, e := range analyzer.edges {
			if e.caller.equals(u) {
				succs = append(succs, e.callee)
			}
		}

		// if u has no successors, we have reached end of a path
		if len(succs) == 0 || len(path) >= maxPathLen {
			paths = append(paths, path)
		} else {
			// enumerate all paths with successors of u
			for _, s := range succs {
				newPath := append(path, s)
				dfsUtil(newPath)
			}
		}

		// mark u as unvisited for new path
		timesVisited[u.String()]--
	}

	// Build paths using DFS algorithm
	dfsUtil(path)

	return paths
}

/*
 * Finding the number of strongly-connected components is important for the
 * cyclomatic complexity formula.  This is used to help find the set of paths
 * to cover all methods.  Since the algorithm to find SCCs is not the focus here,
 * I use Tarjan's classic algorithm.
 *
 * Algorithm based on the Wikipedia pseudocode:
 * https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
 */
func (analyzer callGraphAnalyzer) tarjanScc(uniqueMethods []method) [][]method {
	var scc [][]method = make([][]method, 0)

	index := 0
	var stack []method = make([]method, 0)

	// map nodes to a time-based index
	// use String(), since must be able to match on ==
	var nodeIndex map[string]int = make(map[string]int)
	var lowLink map[string]int = make(map[string]int)
	var onStack map[string]bool = make(map[string]bool)

	// initialize index and lowlink
	for _, method := range uniqueMethods {
		nodeIndex[method.String()] = -1
		lowLink[method.String()] = math.MaxInt
	}

	// main loop
	var strong func(v method)
	strong = func(v method) {
		// Set the depth index for v to the smallest unused index
		nodeIndex[v.String()] = index
		lowLink[v.String()] = index
		index++
		stack = append(stack, v)
		onStack[v.String()] = true

		min := func(a, b int) int {
			if a < b {
				return a
			}
			return b
		}

		// Consider successors of v
		for _, edge := range analyzer.edges {
			// adjacency lists/matrices are for suckers
			if !edge.caller.equals(v) {
				continue
			}

			w := edge.callee
			if nodeIndex[w.String()] == -1 {
				// Successor w has not yet been visited; recurse on it
				strong(w)
				lowLink[v.String()] = min(lowLink[v.String()], lowLink[w.String()])
			} else if onStack[w.String()] {
				// Successor w is in stack S and hence in the current SCC
				// If w is not on stack, then (v, w) is an edge pointing to
				// an SCC already found and must be ignored.
				// The next line may look odd - but is correct.
				// It says w.index not w.lowlink; that is deliberate and from the original paper
				lowLink[v.String()] = min(lowLink[v.String()], nodeIndex[w.String()])
			}
		}

		stackPop := func() method {
			i := len(stack) - 1
			m := stack[i]
			stack = append(stack[:i], stack[i+1:]...)
			return m
		}

		// If v is a root node, pop the stack and generate an SCC
		if lowLink[v.String()] == nodeIndex[v.String()] {
			var comp []method = make([]method, 0)
			var w method = method{}

			for ok := true; ok; ok = (!w.equals(v)) {
				w = stackPop()
				onStack[w.String()] = false
				comp = append(comp, w)
			}

			scc = append(scc, comp)
		}
	}

	// Start recursive fun
	for _, method := range analyzer.methods {
		if nodeIndex[method.String()] == -1 {
			strong(method)
		}
	}

	return scc
}

/*
 * This method takes any sink node and connects it back to the start of the graph,
 * which is useful for detecting the number of strongly connected components.
 */
func (analyzer *callGraphAnalyzer) createStronglyConnectedGraph(uniqueMethods []method) {
	// method struct does not support ==, so this is a hacky workaround
	var outDegree map[string]int = make(map[string]int)

	// initialize map
	for _, method := range uniqueMethods {
		outDegree[method.String()] = 0
	}

	for _, gvEdge := range analyzer.edges {
		caller := gvEdge.caller
		outDegree[caller.String()]++
	}

	// Add start node edges
	for _, start := range analyzer.startNodes {
		gve := callGraphEdge{
			caller: *analyzer.startNode,
			callee: start,
		}
		analyzer.edges = append(analyzer.edges, gve)
	}

	// Find sinks
	exit := analyzer.exitNode
	for meth, deg := range outDegree {
		if deg == 0 {
			// map this back to a method...
			name := meth[strings.Index(meth, ".")+1:]
			pkg := meth[:strings.Index(meth, ".")]

			var meth2 method
			for _, m := range analyzer.methods {
				if m.name == name && m.pkgName == pkg {
					meth2 = m
					break
				}
			}

			// EXIT should be a sink at this point
			if !meth2.equals(*analyzer.exitNode) {
				edge := callGraphEdge{
					caller: meth2,
					callee: *exit,
				}
				analyzer.edges = append(analyzer.edges, edge)
			}
		}
	}

	// Complete strongly-connected graph by adding exit -> start
	gve := callGraphEdge{
		caller: *exit,
		callee: *analyzer.startNode,
	}
	analyzer.edges = append(analyzer.edges, gve)
}

/*
 * This function searches an array of methods for a given method instance.
 * This is primarily used in the below getNumberOfNodes function.
 */
func containsMethod(methods []method, meth method) bool {
	for _, m := range methods {
		if m.equals(meth) {
			return true
		}
	}

	return false
}

/*
 * Although analyzer.methods reflects all the methods found in a program,
 * it may not accurately reflect all the methods used in the resulting
 * callgraph.
 */
func (analyzer callGraphAnalyzer) getUsedMethods() []method {
	var uniqueMethods []method = make([]method, 0)

	for _, gvEdge := range analyzer.edges {
		caller := gvEdge.caller
		callee := gvEdge.callee

		if !containsMethod(uniqueMethods, caller) {
			uniqueMethods = append(uniqueMethods, caller)
		}
		if !containsMethod(uniqueMethods, callee) {
			uniqueMethods = append(uniqueMethods, callee)
		}
	}

	uniqueMethods = append(uniqueMethods, *analyzer.exitNode)

	return uniqueMethods
}

func main() {
	/* AWS Example */

	// Need this for generating import statements later
	modDir := "./serverless-go-demo/"

	paths := []string{
		"./serverless-go-demo/bus/event_bridge.go",
		"./serverless-go-demo/domain/products.go",
		"./serverless-go-demo/domain/products_stream.go",
		"./serverless-go-demo/domain/products_test.go",
		"./serverless-go-demo/functions/delete-product/main.go",
		"./serverless-go-demo/functions/get-product/main.go",
		"./serverless-go-demo/functions/get-products/main.go",
		"./serverless-go-demo/functions/products-stream/main.go",
		"./serverless-go-demo/functions/put-product/main.go",
		"./serverless-go-demo/handlers/apigateway.go",
		"./serverless-go-demo/handlers/dynamodb.go",
		"./serverless-go-demo/integration-testing/integration_test.go",
		"./serverless-go-demo/store/dynamodb.go",
		"./serverless-go-demo/store/memory.go",
		"./serverless-go-demo/tools/tools.go",
		"./serverless-go-demo/types/bus.go",
		"./serverless-go-demo/types/product.go",
		"./serverless-go-demo/types/store.go",
		"./serverless-go-demo/types/mocks/mock_store.go",
	}

	allImports := []string{
		`"os"`,
		`"github.com/aws-samples/serverless-go-demo/domain"`,
		`"github.com/aws-samples/serverless-go-demo/handlers"`,
		`"github.com/aws/aws-lambda-go/lambda"`,
		`"github.com/aws-samples/serverless-go-demo/bus"`,
		`"net/http"`,
		`"github.com/aws/aws-lambda-go/events"`,
		`"github.com/aws/aws-sdk-go-v2/feature/dynamodb/attributevalue"`,
		`"github.com/aws/aws-sdk-go-v2/service/dynamodb"`,
		`"ddbtypes github.com/aws/aws-sdk-go-v2/service/dynamodb/types"`,
		`"context context"`,
		`"reflect reflect"`,
		`"types github.com/aws-samples/serverless-go-demo/types"`,
		`"gomock github.com/golang/mock/gomock"`,
	}

	// Where to store output test file
	mocksDir := "./gcf_mocks/aws"

	CreateCallGraph(paths, modDir, allImports, mocksDir)
}
