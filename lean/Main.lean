import Cli
import Eternity2

open Eternity2
open System

def genTileSet (size coreColors edgeColors : Nat) : IO (TileSet size coreColors) := do
  let b ← DiamondBoard.generate size coreColors edgeColors
  let t := DiamondBoard.tileBoard b false
  return t.tileSet coreColors

def fetchEternity2Tiles : IO (TileSet 16 22) := do
  let ts ← TileSet.fromFile "../puzzles/e2pieces.txt"
  match ts with
  | ⟨16, 22, tiles⟩ => return tiles
  | ⟨size,colors,_⟩ => panic! s!"e2pieces.txt has size {size} and {colors} colors??"

def plotSolCounts (name : String) (size : Nat)
  (encoding : (colors : Nat) → TileSet size colors → EncCNF (List EncCNF.Var)) : IO Unit := do
  let plotsDir : FilePath := "./plots/"
  let outputFile : FilePath := plotsDir / s!"output_{name}_{size}.csv"
  let boardsDir : FilePath := plotsDir / "board"

  IO.FS.createDirAll boardsDir

  IO.FS.withFile outputFile .write (fun handle =>
    handle.putStrLn ("title,size,colors,solutions")
  )
  for i in [0:10] do
    let colors := size + i
    parallel for j in [0:10] do
      let tiles ← genTileSet size colors (size.sqrt + 1)
      let boardTitle := s!"{size}_{colors}_{j}"

      IO.println s!"Board: {boardTitle}"

      --TileSet.toFile
      --  (boardsDir / s!"board_{boardTitle}.txt").toString
      --  tiles
      let (blocking_vars, state) := EncCNF.new (encoding colors tiles)
      let sols ← SATSolve.allSols state (reportProgress := true) blocking_vars

      IO.FS.withFile outputFile .append (fun handle =>
        handle.putStrLn (s!"{boardTitle},{size},{colors},{sols.length}")
      )

def plotSignSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "sign" size fun colors ts => do
    let tile_vars ← Constraints.colorCardConstraints ts.tiles colors 
    return tile_vars.map (·.2)

def plotEdgeSignSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "edgesign" size fun colors ts => do
    let tile_vars ← Constraints.colorCardConstraints ts.tiles colors 
    return tile_vars.filterMap (fun (t, v) =>
      if !t.isCenter then some v else none)

def plotPuzzleSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "puzzle" size fun _ ts => do
    match ← Constraints.puzzleConstraints ts with
    | .error s => panic! s!"it got sad :(\n{s}"
    | .ok tsv => 
      return tsv.diamondVarList

def plotEdgePuzzleSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "edgepuzzle" size fun _ ts => do
    match ← Constraints.puzzleConstraints ts (onlyEdge := true) with
    | .error s => panic! s!"it got sad :(\n{s}"
    | .ok tsv => 
      return tsv.borderDiamondVarList

open Cli

def runGenTileSetCmd (p : Parsed) : IO UInt32 := do
  IO.println "c generated randomly"
  let size : Nat := p.flag! "size" |>.as! Nat
  let colors : Nat := p.flag! "colors" |>.as! Nat
  let bordercolors : Nat := p.flag! "bordercolors" |>.as! Nat

  let colors := if colors = 0 then size + 1 else colors
  let bordercolors := if bordercolors = 0 then size.sqrt + 1 else bordercolors

  let ts ← genTileSet size colors bordercolors
  IO.println ts.toFileFormat

  return 0


def genTileSetCmd := `[Cli|
  gen_tile_set VIA runGenTileSetCmd; ["0.0.1"]
  "Generate a random tile set."

  FLAGS:
    size : Nat; "The height/width of the board"
    colors : Nat; "The number of colors to fill the board with (0 means size+1)"
    bordercolors : Nat; "The number of colors to fill the border with (0 means sqrt(size) + 1)"

  EXTENSIONS:
    defaultValues! #[("colors", "0"), ("bordercolors", "0")]
]

def mainCmd := `[Cli|
  eternity2 NOOP; ["0.0.1"]
  "Tools working towards a solution to Eternity II"

  SUBCOMMANDS:
    genTileSetCmd
]

def main (args : List String) : IO UInt32 := do
  let e2 ← fetchEternity2Tiles
  match EncCNF.new do
    let _ ← Constraints.colorCardConstraints e2.tiles 17
    return ← Constraints.puzzleConstraints e2 (onlyEdge := true)
  with
  | (.error s, _) => panic! s!"it got sad :(\n{s}"
  | (.ok tsv, state) =>
  let sols ← SATSolve.allSols state (reportProgress := true) tsv.borderDiamondVarList
  IO.println s!"{sols.length}"
  return 0
