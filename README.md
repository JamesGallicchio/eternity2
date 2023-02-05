# eternity2
Research project trying to solve the Eternity II edge matching puzzle.

This repo contains an implementation of an efficient encoding for edge matching puzzles described in
[Heule 2008](https://www.cs.cmu.edu/~mheule/publications/eternity.pdf), along with various
redundant clauses and search partitioning schemes we are experimenting with.

It also contains various tools for testing our encodings against randomly generated boards.

## Building
The main tool we've been using for experiments is built in [Lean 4](https://github.com/leanprover/lean4),
which needs to be installed in order to build the binary (follow the installation
intructions in the linked repo).

Once Lean is installed, from this repo's lean/ subfolder execute
```
lake build
cp build/bin/eternity2 ../eternity2  # (or wherever you want it)
```
to download the code dependencies and build the CLI tool.

## Usage

Run `eternity2 --help` to see the available subcommands, and
`eternity2 [subcommand] --help` for help text for each of the subcommands.
