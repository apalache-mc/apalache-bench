# Apalache Benchtests

## Prerequisites

- [sbt](https://www.scala-sbt.org/1.x/docs/Setup.html)
- [benchexec](https://github.com/sosy-lab/benchexec/blob/main/doc/INSTALL.md)

## Running the benchmarks

**NOTE:** The Apalache benchmarking framework is only compatible with Apalache
\>= `v0.22.0`.

### For all projects

``` sh
sbt benchmarksReport
```

### For a specific build of apalache

#### For a released version

Prefix the tag corresponding to the version with `@`:

``` sh
sbt 'set apalacheVersion := "@v0.21.0"; benchmarksReport'
```

#### For a branch or commit

Prefix the branch name or commit ref with `#`:

``` sh
sbt 'set apalacheVersion := "#unstable"; benchmarksReport'
sbt 'set apalacheVersion := "#c1ed9ef1596bb6e8df6b4f77a8335448eebfa80f"; benchmarksReport'
```

### For a specific project

The general recipe for running benchmarks and generating reports for a specific project is:

``` sh
sbt {project}/benchmarksReport
```

E.g., To run the benchmarks and produce reports for the [performance](./performance)
project, run:

``` sh
sbt performance/benchmarksReport
```

## Updating the site index

To generate the HTML file that indicates all of the reports, run

``` sh
sbt site/benchmarksIndexUpdate
```
