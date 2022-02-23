# Notes

To test that benchexec is installed correctly and run tools:

```sh
python3 -m benchexec.test_tool_info dummy --read-only-dir / --overlay-dir /home
```

To test the apalache tool info (from within the same directory as the
`apalache.py` module):

```sh
python3 -m benchexec.test_tool_info .apalache --read-only-dir / --overlay-dir /home
```

To run the scratch configuration (from within the `./scratch` dir)

```sh
benchexec scratch/config.xml --read-only-dir / --overlay-dir /home
```

- Use task definition files: https://gitlab.com/sosy-lab/benchmarking/task-definition-format

## Output

Ends up in the `results` dir in the working directory

## Plan

- [x] Get tool info working
- Make PR with tool info
- [x] Generate task defs from sbt, with little EDSL as SBT plugin
- [x] Review Igor's PR on benchmark organization
- [x] Use SBT for running the benchmarks
- [x] Make sbt config into a plugin
- [x] Fetch apalache executable
- [x] Add way to specify which apalache version
- [ ] Publish the BenchExec reports on GH pages
    - [x] Set up sbt-site
    - [ ] Construct index for all benchmarks
- [ ] Transfer over the existing benchmarks
- [ ] Fix any missing results in output data
  - [ ] Compare across different version wc
- [ ] Enable running individual suites
- [ ] Enable running individual benchmarks in a suite?
- [ ] Open source the benchexec sbt rules
- [ ] Set up incremental builds for benchmarks? (With option to override?)
- [ ] Document how to run and add benchmarks
- [ ] Support adding benchmarks for files in remote repos: 
  - Create git-submodule for each remote project?
  - Use filter & sparse checkout to only pull the relevant dirs?
  - See https://stackoverflow.com/a/52269934/1187277


## Committing results: 


> If the target directory for the output files (specified with --outputpath) is
> a git repository without uncommitted changes and the option --commit is
> specified, benchexec will add and commit all created files to the git
> repository. One can use this to create a reliable archive of experimental
> results.

## TODO ADR:

- [ ] Why picked benchexec
  - considered:
    - bench press (only smt, not as mature)
    - python thing
    - bespoke
  - robust
  - actively maintained
  - widely known
  - publication quality
  - containment
- [ ] Why picked sbt
  - considered:
    - Dhall -- another novelty in our stack. Not known by most
    - XML -- can't generate experiments programmatically, verbose, not
      statically checked
  - we need a build system
  - we already use it and must know scala
