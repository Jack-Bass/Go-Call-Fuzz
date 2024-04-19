# Go-Call-Fuzz

Go-Call-Fuzz is a program designed to trace the call graph of a given Go 
project, enumerate the possible program paths, and create simple fuzz harnesses 
for the user to run.  Methods to fuzz are chosen based on the parameters they 
take and how early they appear in their respective paths.

Currently, not all parameter types are supported (such as arrays, maps, slices, 
and the empty interface/`any` type).  Struct parameters are fuzzed using the 
(go-fuzz-headers package)[https://github.com/AdaLogics/go-fuzz-headers], and 
interfaces are supported as long as their mocks are provided in the appropriate 
`gcf-mocks/<project-alias>` directory.  Currently, I use the 
(mockery package)[https://github.com/vektra/mockery] to manually create mocks.

## Installing and Running

To install this repository and its included example project submodule, run 

`git clone --recursive https://github.com/Jack-Bass/Go-Call-Fuzz`.

In the future, I plan on publishing this as a package/creating a command-line 
tool.  For now, you can run 

`go run ast-call-graph.go`

to invoke the program.  Running the program on a project is fairly manual so far, 
which will be addressed in the future.  Currently, you need to manually update the 
`main` method as follows: 

```
modDir := "<directory containing project's go.mod file>"

// Enumerate all project files to consider for call graph creation
// (This can be automated in the future)
paths := []string{
	"./path/to/<project>/.../file1.go", 
	...
	"./path/to/<project>/.../fileN.go",  
}

// All imports used by the provided project
// Can also be automated in the future
allImports := []string{
	`"import1"`, 
	...
	`"importN"`, 
}

// Where to store output test file
mocksDir := "./gcf-mocks/<project-alias>"

// Start the program
CreateCallGraph(paths, modDir, allImports, mocksDir)
```

The `<project-alias>` is a name given to the provided project.  For 
example, the `serverless-go-demo` `<project>` provided here has an alias 
of `aws`.  This determines where the mocks for this project should be 
placed and where the output files should go.

```
// Storing mock_<interface-name>.go files
gcf-mocks/<project-alias>/mock_1.go
...
gcf-mocks/<project-alias>/mock_N.go

// Output fuzzing file
fuzzing_test/<project-alias>/fuzz_test.go

// Output call graph
out/<project-alias>/cfg.out.txt
```

Two parameters to consider are `maxPathLen` and `maxDfsIter`.  `maxPathLen` 
is a limit on how long the enumerated paths from the call graph can be.  For a 
large program, evaluating all possible paths may take exponential time, so 
imposing a limit helps cut down on total runtime.

`mathDfsIter` refers to how long `enumeratePaths` will execute its DFS-esque 
algorithm.  Similarly to the previous parameter, this can cut down on execution 
time when there are many paths to consider.

## Future Work

There are many technical and Quality of Life improvements planned for this 
project.  Some of them include: 
- Refactoring the codebase into smaller files.
	- Such as a file for parsing, call graph generation, parameter randomization, etc.
- Better support for remaining Go types.
- Support for variadic parameters.
- Easier access to the program parameters in `ast-call-graph.go`.
- More automation for running Go-Call-Fuzz on projects.
- A command-line utility?
- Better program parsing/graph traversal.
