description := "The Apalache Benchmarking System"
name := "apalache-bench"
organizationHomepage := Some(url("https://apalache.informal.systems/"))

ThisBuild / version := "0.0.1"
ThisBuild / sbtVersion := "1.6.1"
ThisBuild / scalaVersion := "2.13.6"
ThisBuild / organization := "systems.informal"

ThisBuild / apalacheVersion := "#unstable"
ThisBuild / benchmarksToolVersion := apalacheEnableVersion.value

lazy val performance = (project in file("performance"))

lazy val root = (project in file("."))
  .enablePlugins(Apalache)
  .aggregate(
    // Should aggregate every project that can run reports
    performance
  )

// Configure GH pages site
enablePlugins(GhpagesPlugin)
git.remoteRepo := "git@github.com:informalsystems/apalache-bench.git"
ghpagesNoJekyll := true

lazy val site = (project in file("src/site"))
  .enablePlugins(BenchExec)
  .settings(
    // Versions to include in the reports of performance accross versions
    benchmarksLongitudinalVersions := Set(
      "0.22.0",
      "0.23.0",
      "0.24.0",
      "0.25.0",
    ),
    benchmarksIndexFile := Some(baseDirectory.value / "index.html"),
  )
