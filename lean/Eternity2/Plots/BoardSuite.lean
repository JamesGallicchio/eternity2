import Eternity2.Puzzle.BoardSol
import Eternity2.FileFormat.Puz
import Eternity2.FileFormat.Sol

open System

namespace Eternity2

structure BoardDir where
  puzFile : FilePath
  size    : Nat
  colors  : Color.WithBorder.Settings
  ts      : TileSet size (Tile (Color.WithBorder colors))
  sols    : Array (FilePath × BoardSol ts)
  allSols : Bool

def BoardDir.updateFilesystem (bd : BoardDir) : IO Unit := do
  if ! (←bd.puzFile.pathExists) then
    FileFormat.TileSet.toFile bd.puzFile bd.ts

  if bd.allSols && !(← (bd.puzFile.withFileName "done" |>.pathExists)) then
    IO.FS.writeFile (bd.puzFile.withFileName "done") ""

  for (path, sol) in bd.sols do
    if !(← path.pathExists) then
      FileFormat.BoardSol.toFile path sol

def BoardDir.addSol (bd : BoardDir) (path : FilePath) (sol : BoardSol bd.ts) : IO BoardDir := do
  if ←path.pathExists then
    throw <| IO.Error.mkAlreadyExistsFile path.toString 1 "BoardDir.addSol"
  
  FileFormat.BoardSol.toFile path sol

  return { bd with sols := bd.sols.push (path, sol) }

def BoardDir.addSolNextName (bd : BoardDir) (sol : BoardSol bd.ts) : IO BoardDir := do
  let mut idx := 0
  let mut path := bd.puzFile.withFileName s!"sol_{idx}.sol"
  while ←path.pathExists do
    idx := idx+1
    path := bd.puzFile.withFileName s!"sol_{idx}.sol"

  addSol bd path sol

structure BoardSuite where
  boards : Array BoardDir

namespace BoardSuite

def ofDirectory (path : FilePath) : IO BoardSuite := do
  -- find all .puz files in the directory
  let puzFiles ← path.walkDir (fun p => do return p.extension = some "puz")

  let boards ← puzFiles.mapM (fun puzFile => do
    let ⟨size, colors, ts⟩ ← FileFormat.TileSet.ofFile puzFile

    -- get all the .sol files in the same directory
    let solFiles ←
      puzFile.withFileName "."
      |>.walkDir (fun p => do return p.extension = some "sol")

    -- read each sol file as a solution to ts
    let sols ← solFiles.mapM (fun f => do
      return (f, ← FileFormat.BoardSol.ofFile ts f))

    -- check whether `done` file is present in directory (which indicates all solutions were found)
    let allSols ← (puzFile.withFileName "done").pathExists
    return { puzFile, size, colors, ts, sols, allSols } )
  return ⟨boards⟩