import Eternity2.Plots.BoardSuite
import Eternity2.Puzzle.SolvePuzzle

namespace Eternity2

open LeanSAT LeanSAT.Encode Eternity2.Encoding

/- Find solutions not already found in `bdir`, outputting them to `bdir` -/
def solveAndOutput [Solver IO] (bdir : BoardDir)
      (es : SolvePuzzle.EncodingSettings)
      (parallelize : Bool := false)
      : Log IO Unit
  := do
  if bdir.allSols then
    Log.info s!"Board {bdir.puzFile}: already solved"
    return
  
  let (tsv, enc) := EncCNF.new! do
    -- encode the basic puzzle constraints
    let tsv ← SolvePuzzle.encodePuzzle bdir.ts es
    have : tsv.ts = bdir.ts := sorry
    -- block each existing solution
    for (_, sol) in bdir.sols do
      let a ← SolvePuzzle.encodeSol tsv (this ▸ sol)
      EncCNF.blockAssn a
    
    return tsv

  have : tsv.ts = bdir.ts := sorry

  let name := bdir.puzFile.toString
  let bdRef ← IO.mkRef ⟨bdir, sorry⟩
  if parallelize then
    let handle ← Log.getHandle
    let (_ : List Unit) ← (List.fins 6).parMap fun i => do
      Log.run handle do
      let ((), enc) := EncCNF.run! enc do
        Encoding.fixCorners tsv i
      Log.info s!"Board {name}, corner {i}: Starting solver"
      aux tsv enc s!"{name}, corner {i}" bdRef
      Log.info s!"Board {name}, corner {i}: Solver finished"
  else
    let ((), enc) := EncCNF.run! enc do
      Encoding.fixCorner tsv
    aux tsv enc name bdRef
  Log.info s!"Board {name}: All solutions found"
  let _ ← (← bdRef.get).1.markAllSols
where
  aux {size s} (tsv : TileSetVariables size s) enc name
    (bdRef : IO.Ref { bd : BoardDir // (BoardSol bd.ts) = (BoardSol tsv.ts) })
    : Log IO Unit := do
  for assn in Solver.solutions enc.toFormula tsv.diamondVarList do
    match SolvePuzzle.decodeSol tsv assn with
    | .error s =>
      Log.error s!"Failed to decode board {name} solution: {s}"
    | .ok sol =>
      let ⟨bdir,h⟩ ← bdRef.get
      let (path, bdir') ← bdir.addSolNextName (h ▸ sol)
      bdRef.set ⟨bdir', sorry⟩
      Log.info s!"Board {name}: Wrote solution to {path.fileName.get!}"
