import Cli
import Eternity2

open Eternity2
open System

open Cli

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

def runGenAndSolveBoardsCmd (p : Parsed) : IO UInt32 := do
  let output : FilePath := p.flag! "output" |>.as! String
  let logfile : FilePath := p.flag! "logfile" |>.as! String

  if ←output.pathExists then
    IO.println s!"ERROR: Directory {output} already exists. Please delete the directory or choose a different name for the output directory."
    return 1
  
  IO.FS.createDirAll output
  
  if ←logfile.pathExists then
    IO.println s!"ERROR: File {logfile} already exists. Please delete the file or choose a different name for the log file."
    return 1

  IO.FS.writeFile logfile ""
  IO.FS.withFile logfile .append (fun handle =>
    TaskIO.wait <|
      Log.run handle <|
        genAndSolveBoards output
  )

  return 0


def genAndSolveBoardsCmd := `[Cli|
  "gen-and-solve-boards" VIA runGenAndSolveBoardsCmd; ["0.0.1"]
  "Generate many random tile sets with 7-9 colors, writing the tilesets + all solutions to files."
  
  FLAGS:
    output : String; "The directory to place generated files (directory will be created if DNE)"
    logfile : String; "The file to write log info to"
]

def mainCmd := `[Cli|
  eternity2 NOOP; ["0.0.1"]
  "Tools working towards a solution to Eternity II"

  SUBCOMMANDS:
    genTileSetCmd;
    genAndSolveBoardsCmd
]

def main (args : List String) : IO UInt32 :=
  mainCmd.validate args
