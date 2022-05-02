The configuration to run the benchmarks in this directory is in the
[./build.sbt](./build.sbt) in this directory.

The array encoding benchmarks support configurable length via the
`ARRAY_MAX_LENGTH` environment variable.  The max length currently supported is
14, but this can be increased by adding more constants to
[./array-encoding/Constants.tla](./array-encoding/Constants.tla).
