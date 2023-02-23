import Eternity2.Puzzle.BoardSol
import Eternity2.FileFormat.Puz
import Eternity2.FileFormat.Sol

open System

namespace Eternity2

structure SolvedBoard where
  path : FilePath
  size : Nat
  colors : Color.WithBorder.Settings
  tiles : TileSet size (Tile <| Color.WithBorder colors)
  sols : Array (BoardSol tiles)
  allSols : Bool

structure BoardSuite where
  boards : Array SolvedBoard

def BoardSuite.ofDirectory (path : FilePath) : IO BoardSuite := do

  -- find all .puz files in the directory
  let puzFiles ← path.walkDir (fun p => do return p.extension = some "puz")

  let boards ← puzFiles.mapM (fun file => do
    -- read the .puz file
    let ⟨size, colors, ts⟩ ← FileFormat.TileSet.ofFile file
    
    -- get all the .sol files in the same directory
    let solFiles ← (file.withFileName ".").walkDir (fun p => do return p.extension = some "sol")

    -- read each .sol file as a solution to `ts`
    let sols ← solFiles.mapM (FileFormat.BoardSol.ofFile ts)

    -- check whether `done` file is present in directory (which indicates all solutions were found)
    let done ← (file.withFileName "done").pathExists

    return ⟨file,size,colors,ts,sols,done⟩)
  return ⟨boards⟩
