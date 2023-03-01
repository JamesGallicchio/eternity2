import Cli
import Eternity2

open Eternity2
open System

open Cli

def cadicalCmd (timeout : Option Nat) : LeanSAT.Solver IO :=
  match timeout with
  | none => LeanSAT.Solver.Impl.DimacsCommand "cadical"
  | some timeout => LeanSAT.Solver.Impl.DimacsCommand "timeout" [toString timeout, "cadical"]

/- Ensure directory exists -/
def ensureDirectoryExists (file : FilePath) : IO Unit := do
  if (←file.pathExists) then
    if !(←file.isDir) then
      throw (IO.Error.mkAlreadyExists 1
        <| s!"Path {file} is a file; please delete it if you want"
          ++ " to use this path as a directory.")
  else
    IO.FS.createDirAll file

def ensureFileDNEOrAskToOverwrite (file : FilePath) : IO Unit := do
  if ! (← file.pathExists) then
    return
  
  if ← file.isDir then
    IO.println <| s!"Path {file} is a directory; please delete it if"
                ++ " you want to use it as a file."
  else
    IO.print <| s!"Path {file} already exists. Overwrite it? (y/n) "
    let mut resp := none
    while resp.isNone do
      match (← (← IO.getStdin).getLine).trim with
      | "y" => resp := some true
      | "n" => resp := some false
      | _ => IO.print "Please respond \"y\" or \"n\": "
    match resp with
    | none => panic! "unreachable 98651320"
    | some false =>
      IO.println "Aborting process"
      throw (IO.Error.mkAlreadyExistsFile file.toString 1 "User decided to not overwrite")
    | some true =>
      IO.FS.removeFile file

def runGenTileSetCmd (p : Parsed) : IO UInt32 := do
  let size : Nat := p.flag! "size" |>.as! Nat
  let colors : Nat := p.flag! "colors" |>.as! Nat
  let bordercolors : Nat := p.flag! "bordercolors" |>.as! Nat

  let colors := if colors = 0 then size + 1 else colors
  let bordercolors := if bordercolors = 0 then size.sqrt + 1 else bordercolors

  let ts ← IO.ofExcept <|
    ← show RandomM _ from GenRandom.tileSet size ⟨List.range colors, List.range bordercolors⟩
  IO.println "c generated randomly"
  IO.println <| FileFormat.TileSet.toFileFormat ts

  return 0


def genTileSetCmd := `[Cli|
  "gen-tile-set" VIA runGenTileSetCmd; ["0.0.1"]
  "Generate a random tile set."

  FLAGS:
    size : Nat; "The height/width of the board"
    colors : Nat; "The number of colors to fill the board with (0 means size+1)"
    bordercolors : Nat; "The number of colors to fill the border with (0 means sqrt(size) + 1)"

  EXTENSIONS:
    defaultValues! #[("colors", "0"), ("bordercolors", "0")]
]

def runSolveTileSetCmd (p : Parsed) : IO UInt32 := do
  let tilesetArg ← IO.ofExcept <|
    p.flag? "tileset" |>.expectSome (fun () => "--tileset flag required")
  let tileset : FilePath := tilesetArg.as! String

  let logfile : FilePath :=
    p.flag? "logfile" |>.map (·.as! String)
      |>.getD (tileset.withFileName s!"{tileset.fileStem.get!}.log")
  let timeout : Option Nat :=
    p.flag? "timeout" |>.map (·.as! Nat)

  let useRedundant := p.flag! "use-redundant" |>.as! Bool
  let usePolarity := p.flag! "use-polarity" |>.as! Bool

  ensureFileDNEOrAskToOverwrite logfile

  let bd ← BoardDir.ofPuzFile tileset

  have := cadicalCmd timeout

  IO.FS.writeFile logfile ""
  IO.FS.withFile logfile .append (fun handle =>
    TaskIO.wait <|
      Log.run handle <|
        solveAndOutput
          bd
          { useRedundant, usePolarity}
          (parallelize := true)
  )

  return 0

def solveTileSetCmd := `[Cli|
  "solve-tile-set" VIA runSolveTileSetCmd; ["0.0.1"]
  "Solve the given tile set."

  FLAGS:
    tileset : String; "File containing the tileset to solve"
    logfile : String; "File for detailed logs"
    timeout : Nat; "Optional timeout for the solver (in seconds)"
    "use-redundant" : Bool; "Use redundant clauses (forbidden color & explicit piece locations)"
    "use-polarity" : Bool; "Use sign polarity constraints"
  
  EXTENSIONS:
    defaultValues! #[("use-redundant", "true"), ("use-polarity", "false")]
]

def runGenBoardSuiteCmd (p : Parsed) : IO UInt32 := do
  let output : FilePath :=
    (← (p.flag? "output"
    |>.expectSome (fun () => "option --output required")
    |> IO.ofExcept))
    |>.as! String
  let seed : Option Nat := p.flag? "seed" |>.map (·.as! Nat)

  let seed ← match seed with
    | none => IO.rand 0 (UInt32.size-1)
    | some s => pure s

  IO.println s!"Using seed {seed}"
  IO.setRandSeed seed

  if ←output.pathExists then
    IO.println s!"ERROR: Directory {output} already exists. Please delete the directory or choose a different name for the output directory."
    return 1

  IO.FS.createDirAll output

  let _ ← GenRandom.boardSuite seed output

  return 0


def genBoardSuiteCmd := `[Cli|
  "gen-board-suite" VIA runGenBoardSuiteCmd; ["0.0.1"]
  "Generate many random tile sets in the provided output directory."
  
  FLAGS:
    output : String; "Directory to place generated files (directory will be created if DNE)"
    seed : Nat; "Random seed to start with; intended for reproducibility"
]

def runSolveBoardSuiteCmd (p : Parsed) : IO UInt32 := do
  let suite : FilePath := p.flag! "suite" |>.as! String
  let timeout : Option Nat := p.flag? "timeout" |>.map (·.as! Nat)

  let logfile : FilePath :=
    p.flag? "logfile" |>.map (·.as! String)
      |>.getD (suite / s!"{← IO.monoMsNow}.log")

  ensureDirectoryExists suite

  let bs ← BoardSuite.ofDirectory suite

  -- sort by board size (increasing), then by number of center colors (decreasing)
  let bs := bs.boards.insertionSort (fun x y =>
    x.size < y.size ||
      x.size = y.size && x.colors.center.length > y.colors.center.length)

  have := cadicalCmd timeout

  IO.FS.withFile logfile .write (fun handle =>
    -- solve each board in parallel
    TaskIO.wait <| TaskIO.parUnit bs fun bdir => do
      Log.run handle <| Log.info s!"Board {bdir.puzFile}: starting"
      try (do
        Log.run handle <| solveAndOutput bdir {}
     ) catch
      | e => (
        let msg := e.toString.dropWhile (·.isWhitespace) |>.takeWhile (· ≠ '\n')
        Log.run handle <| Log.error s!"Board {bdir.puzFile}:\n\t{msg}"
      )
  )

  return 0

def solveBoardSuiteCmd := `[Cli|
  "solve-board-suite" VIA runSolveBoardSuiteCmd; ["0.0.1"]
  "Solve the tile sets in the provided board suite. Already-known solutions are automatically excluded, and fully solved puzzles are skipped. Outputs any new solutions to the puzzle directory."
  
  FLAGS:
    suite : String; "Directory with the board suite"
    timeout : Nat; "Timeout (in sec) to give up on solving a board"
    logfile : String; "File to log detailed results in"
]

def runTestSolveTimesCmd (p : Parsed) : IO UInt32 := do
  let suite : FilePath := p.flag! "suite" |>.as! String
  let timeout : Option Nat := p.flag? "timeout" |>.map (·.as! Nat)
  let useRedundant := p.flag! "use-redundant" |>.as! Bool
  let usePolarity := p.flag! "use-polarity" |>.as! Bool

  have := cadicalCmd timeout

  testSolveTimes suite {
    useRedundant,
    usePolarity,
    fixCorner := true
  }
  return 0

def testSolveTimesCmd := `[Cli|
  "test-solve-times" VIA runTestSolveTimesCmd; ["0.0.1"]
  "Sample solve times using a board suite. Outputs a CSV of the data"

  FLAGS:
    suite : String; "Directory with the board suite"
    timeout : Nat; "Timeout (in sec) to use when determining what color to stop sampling at"
    "use-redundant" : Bool; "Use redundant clauses (forbidden color & explicit piece locations)"
    "use-polarity" : Bool; "Use sign polarity constraints"
  
  EXTENSIONS:
    defaultValues! #[("use-redundant", "true"), ("use-polarity", "false")]
]

def runFindSignCorrsCmd (p : Parsed) : IO UInt32 := do
  let tileset : String ← IO.ofExcept <|
    p.flag? "tileset" |>.map (·.as! String) |>.expectSome fun () => "--tileset <file> argument missing"
  let sols : String ← IO.ofExcept <|
    p.flag? "sols" |>.map (·.as! String) |>.expectSome fun () => "--sols <dir> argument missing" 

  let ⟨_, _, ts⟩ ← FileFormat.TileSet.ofFile tileset
  let sols ←
    (← System.FilePath.walkDir sols (fun f => pure <| f.extension.isEqSome "sol"))
    |>.mapM (fun f => FileFormat.BoardSol.ofFile ts f)

  have := LeanSAT.Solver.Impl.ApproxMCCommand

  findCorrs ts sols.toList
  return 0

def findSignCorrsCmd := `[Cli|
  "find-sign-corrs" VIA runFindSignCorrsCmd; ["0.0.1"]
  "Find correlations between sign solutions on a board."

  FLAGS:
    tileset : String; "File containing the tileset"
    sols : String; "Directory with solution output"
    logfile : String; "File for detailed logs"
]

def mainCmd := `[Cli|
  eternity2 NOOP; ["0.0.1"]
  "Tools working towards a solution to Eternity II"

  SUBCOMMANDS:
    genTileSetCmd;
    genBoardSuiteCmd;
    solveBoardSuiteCmd;
    solveTileSetCmd;
    testSolveTimesCmd;
    findSignCorrsCmd
]

def main (args : List String) : IO UInt32 := do
  mainCmd.validate args
