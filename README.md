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

## Terminology

- *Puzzle*: a set of tiles, along with dimensions of the board on which tiles are placed.
- *Tile*: a piece of the puzzle with 4 colors along its edges. Can be rotated but not flipped.
- *Square*: a location within the puzzle's borders.
- *Solution*: a perfect matching between the tiles of a puzzle and the squares of a puzzle,
along with a rotation for each tile. A solution is *correct* if all adjacent tile edges match.
- *Half-diamond*: Each square is broken into four "half-diamonds," with adjacent half-diamonds.
- *Diamond*: a pair of adjacent half-diamonds. In a correct solution, each of the board's
diamonds has a *single* color (the color of the two edges covering the diamond). 

We also have special terms for framed puzzles:
- *Framed* puzzles have a distinguished frame color that must be placed
along the frame (exterior border) of the puzzle board.
- *Unframed* puzzles have no distinguished color; edges on the frame are unconstrained.
- *Corner* squares touch the frame on two sides.
- *Side* squares touch the frame color on one side.
- *Center* squares are on the interior/do not touch the frame.
- *Frame*: the half-diamonds on the outer edge of the board (where the frame color will be placed).
- *Border*: the full-diamonds fully contained by corner/side squares
- *Center*: the full-diamonds that are not in the border.

And let's not forget signed puzzles:
- *Signed* puzzles have both a color and a *sign* on each tile edge.
  In a correct solution, each adjacent pair of edges must still have the same color, but *opposite* signs.
- *Tile-signed* puzzles are signed puzzles where each tile's edges share the same sign.
  Every unsigned edge-matching puzzle has a equisatisfiable tile-signed puzzle:
  if there is a solution, take the tile signs to be a checkerboard pattern on that solution.

## Custom File Formats

### `.puz`
These describe tile sets/puzzles. Framed and unframed, tile-signed and unsigned are supported.
```
<cols> [rows]
<north> <east> <south> <west> [+|-]
```
- Blank lines and lines starting with `c` are ignored.
- `cols` and `rows` must both be >= 2. If left unspecified, `rows = cols`.
- Each line after the size line represents a single tile.
- Colors must be positive natural numbers in base-10.
- 0 must be used for the frame color. Unframed puzzles should skip 0.
- The sign `[+|-]` is optional for each tile; some tiles can be given a sign and others not.
  The signs are relative to each other: flipping all signs in the file should represent the same puzzle.
  (This symmetry is generally broken during the encoding process, if it safely can be broken).

### `.sol`
These describe puzzle solutions. They do NOT encode the original tile set, so a solution is really
described by the original `.puz` file along with a `.sol` file.
```
<tile> <col> <row> <rot>
...
```
- Blank lines and lines starting with `c` are ignored.
- `tile` is the (0-)index of a tile in the `.puz` file ordering.
- `col`/`row` are the (0-indexed) col/row of the tile's location in the solution, where 0,0 is the top-left corner.
- `rot` is the number of anti-clockwise rotations to make, relative to the tile's listing in the `.puz` file.
  So, `rot=0` indicates it has the same orientation as in the `.puz` file, while `rot=1` indicates it must be
  rotated 90* anti-clockwise in the solution.

Note the `.sol` format can also be a partial solution; this is useful for describing known clue pieces.

## References

TODO
