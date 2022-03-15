# Apalache Benchtests

## Prerequisites

- [sbt](https://www.scala-sbt.org/1.x/docs/Setup.html)
- [benchexec](https://github.com/sosy-lab/benchexec/blob/main/doc/INSTALL.md)
- [direnv](https://direnv.net/) or run `source ./.envrc`

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

## Generating reports and the website

### Updating the reports and site content

To generate the site that gather and presents the report data, run

``` sh
sbt site/benchmarksIndexUpdate site/benchmarksLongitudinalUpdate
```

This will update the files in [./src/site](./src/site). Open
[./src/site/index.html](./src/site/index.html) in your browser to preview the
site locally.

### Publishing the site to gh-pages

``` sh
sbt makeSite ghpagesPushSite
```

The site will be served at <https://informalsystems.github.io/apalache-bench/>.

## Debugging

That apalache generated files for each run including the `detailed.log`, are
saved into `site/reports/${verion}/${experiment}/${name}.files`, where

- `version` is the version of Apalache that was benchmarked
- `experiment` is the name of the experiment run
- `name` is the name and timestamp of the particular set of tasks executed
