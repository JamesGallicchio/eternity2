import Cli
import Eternity2

open Eternity2
open System

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

def main (args : List String) : IO Unit := do
  plotPuzzleSolCounts (args[0]!.toNat!)
  -- let tb := (← GenBoard.generate 6 10 3).tileBoard
  -- IO.println tb
  -- IO.println ""
  -- let ts := tb.tileSet
  -- let (tsv,enc) := EncCNF.new do
    -- match ← Constraints.puzzleConstraints ts with
    -- | .error s => return panic! s!"it got sad :(\n{s}"
    -- | .ok tsv =>
      -- let () ← Constraints.fixCorner tsv
      -- let vList ← Constraints.colorCardConstraints tsv.tiles
      -- let () ← Constraints.associatePolarities tsv vList sorry
      -- return pure tsv
  -- IO.FS.withFile "test-cnf.txt" .write (fun h => do
    -- enc.prettyPrintAux h.putStrLn
    -- h.putStrLn ""
  -- )
  -- let tsv ← tsv
  -- IO.FS.withFile "test.txt" .write (fun h =>
    -- h.putStrLn ""
  -- )
  -- IO.FS.withFile "test-p.txt" .write (fun h =>
    -- h.putStrLn ""
  -- )
  -- match
    -- ← SolvePuzzle.solveAll enc tsv
  -- with
  -- | [] => IO.println "failed"
  -- | sols =>
    -- IO.println s!"{sols.length}"
    -- IO.FS.withFile "test.txt" .write (fun h =>
    -- for s in sols do
    --   h.putStrLn ""
    --   h.putStrLn
    --     <| toString
    --     <| s.tileBoard.mapColors (fun | none => " " | some a => toString a)
    -- )
  -- IO.println <|
    -- a.tileBoard.mapColors (fun | none => " " | some a => toString a)
