import Eternity2.SATSolve
import Eternity2.TileSet

namespace Eternity2.PyEncodingShim

open System

/-- Encode ts via the simpler Python encoding -/
def pyEncode (ts : TileSet size colors) : IO (EncCNF.State × List EncCNF.Var) := do
  -- make some temp files
  let temp : FilePath := "temp"
  IO.FS.createDirAll temp
  let randInt ← IO.rand 0 100000

  let puzFile := temp / s!"puzzle_{randInt}.txt"
  let cnfFile := temp / s!"puzzle_{randInt}.cnf"

  -- write puzzle to file
  ts.toFile puzFile.toString

  -- run python script
  let output ← IO.Process.output {
    cmd := "python3"
    args := #["../py/main.py", "-i", puzFile.toString, "-o", cnfFile.toString]
  }

  -- read cnf from file
  let cnf ← EncCNF.State.fromFileDIMACS cnfFile.toString

  -- parse output


  -- clean up
  IO.FS.removeFile puzFile
  IO.FS.removeFile cnfFile

  return (cnf, sorry)
