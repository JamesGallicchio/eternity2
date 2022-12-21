import Cli
import Eternity2

open Eternity2
open System

open Cli

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

  let ts ← genTileSet size colors bordercolors
  IO.println "c generated randomly"
  IO.println ts.toFileFormat

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
  let tileset : FilePath := p.flag! "tileset" |>.as! String
  let output : FilePath := p.flag! "output" |>.as! String
  let logfile : FilePath :=
    p.flag? "logfile" |>.map (·.as! String)
      |>.getD s!"{output}.log"
  let useRedundant := p.flag! "use-redundant" |>.as! Bool
  let usePolarity := p.flag! "use-polarity" |>.as! Bool
  let signSol := p.flag? "sign-sol" |>.map (·.as! String)
  let parCorners := p.flag! "parallel-corners" |>.as! Bool

  ensureDirectoryExists output
  
  ensureFileDNEOrAskToOverwrite logfile

  match ← TileSet.fromFile tileset with
  | ⟨_, _, _, tiles⟩ =>

  IO.FS.writeFile logfile ""
  IO.FS.withFile logfile .append (fun handle => do
    TaskIO.wait <|
      Log.run handle <|
        outputAllSols
          tileset.fileStem.get! tiles output
          { useRedundant, usePolarity}
          (parallelize := parCorners)
          (signSol := ← signSol.mapM (SignSol.readSolution · tiles))
  )

  return 0

def solveTileSetCmd := `[Cli|
  "solve-tile-set" VIA runSolveTileSetCmd; ["0.0.1"]
  "Solve the given tile set."

  FLAGS:
    tileset : String; "File containing the tileset to solve"
    output : String; "Directory to output solutions"
    logfile : String; "File for detailed logs"
    "use-redundant" : Bool; "Use redundant clauses (forbidden color & explicit piece locations)"
    "use-polarity" : Bool; "Use sign polarity constraints"
    "sign-sol" : String; "If specified, the file with the sign solution to use"
    "parallel-corners" : Bool; "Run all corner configurations in parallel"

  EXTENSIONS:
    defaultValues! #[
      ("use-redundant", "true")
    , ("use-polarity", "false")
    , ("parallel-corners", "false") ]
]

def runConvertSolToSignsCmd (p : Parsed) : IO UInt32 := do
  let tileset : FilePath := p.flag! "tileset" |>.as! String
  let input : FilePath := p.flag! "input" |>.as! String
  let output : FilePath := p.flag! "output" |>.as! String

  match ← TileSet.fromFile tileset with
  | ⟨_, _, _, ts⟩ =>

  let sol ← BoardSol.readSolution input ts
  let ssol := SignSol.ofSol ts sol
  ssol.writeSolution output

  return 0

def convertSolToSignsCmd := `[Cli|
  "convert-sol-to-signs" VIA runConvertSolToSignsCmd; ["0.0.1"]
  "Given a board solution, get the sign solution derived from it."

  FLAGS:
    tileset : String; "File containing the original tileset"
    input : String; "File containing the board solution"
    output : String; "File to output the sign solution"
]

def runGenBoardSuiteCmd (p : Parsed) : IO UInt32 := do
  let output : FilePath := p.flag! "output" |>.as! String
  let seed : Option Nat := p.flag? "seed" |>.map (·.as! Nat)

  for seed in seed do
    IO.println s!"Using seed {seed}"
    IO.setRandSeed seed

  if ←output.pathExists then
    IO.println s!"ERROR: Directory {output} already exists. Please delete the directory or choose a different name for the output directory."
    return 1
  
  IO.FS.createDirAll output
  
  genBoardSuite output

  return 0


def genBoardSuiteCmd := `[Cli|
  "gen-board-suite" VIA runGenBoardSuiteCmd; ["0.0.1"]
  "Generate many random tile sets in the provided output directory."
  
  FLAGS:
    output : String; "Directory to place generated files (directory will be created if DNE)"
    seed : Nat; "Random seed to start with; intended for reproducibility"
]

def runTestSolveTimesCmd (p : Parsed) : IO UInt32 := do
  let suite : FilePath := p.flag! "boardsuite" |>.as! String
  let timeout : Nat := p.flag! "timeout" |>.as! Nat
  let useRedundant := p.flag! "use-redundant" |>.as! Bool
  let usePolarity := p.flag! "use-polarity" |>.as! Bool
  let useSolSigns := p.flag! "use-sol-signs" |>.as! Bool

  testSolveTimes suite timeout {
    useRedundant,
    usePolarity,
    fixCorner := true
  } (useSolSigns := useSolSigns)

  return 0

def testSolveTimesCmd := `[Cli|
  "test-solve-times" VIA runTestSolveTimesCmd; ["0.0.1"]
  "Sample solve times using a board suite. Outputs a CSV of the data"

  FLAGS:
    boardsuite : String; "Directory with the board suite"
    timeout : Nat; "Timeout (in sec) to use when determining what color to stop sampling at"
    "use-redundant" : Bool; "Use redundant clauses (forbidden color & explicit piece locations)"
    "use-polarity" : Bool; "Use sign polarity constraints"
    "use-sol-signs" : Bool; "Constrain tile signs to the (known) default board solution's signs"
  
  EXTENSIONS:
    defaultValues! #[("use-redundant", "true"), ("use-polarity", "false")]
]

def runFindSignCorrsCmd (p : Parsed) : IO UInt32 := do
  let size : Nat := p.flag! "size" |>.as! Nat
  let iters : Nat := p.flag! "iters" |>.as! Nat
  let timeout : Nat := p.flag! "timeout" |>.as! Nat

  let coreColors := size+1
  let edgeColors := Nat.sqrt size + 1
  let dboard ← GenBoard.generate size coreColors edgeColors
  let board := dboard.tileBoard

  findCorrs board.toBoardSol.fst (iters := iters) (timeout := timeout)
  return 0

def findSignCorrsCmd := `[Cli|
  "find-sign-corrs" VIA runFindSignCorrsCmd; ["0.0.1"]
  "Generate random board and find correlations between sign solutions on that board."

  FLAGS:
    size : Nat; "How big of a board to generate"
    iters : Nat; "Number of CNF scrambles to find solutions for"
    timeout : Nat; "Timeout (in ms) for each CNF scramble"
]

def mainCmd := `[Cli|
  eternity2 NOOP; ["0.0.1"]
  "Tools working towards a solution to Eternity II"

  SUBCOMMANDS:
    genTileSetCmd;
    genBoardSuiteCmd;
    solveTileSetCmd;
    convertSolToSignsCmd;
    testSolveTimesCmd;
    findSignCorrsCmd
]

def main (args : List String) : IO UInt32 := do
  mainCmd.validate args
