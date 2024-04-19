# Regarding Dependencies

When parsing the program input and enumerating the paths, it would be useful 
to track dependencies to outside packages, since this is currently not 
supported very well.  For structs, this can probably be done in the 
program.  However, mocks need to be manually generated, so mocks on external 
packages should be placed here.

For example, this directory contains a `context.Context` mock to use.
