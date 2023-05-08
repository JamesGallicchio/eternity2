import Eternity2.Plots.BoardSuite
import Eternity2.Puzzle.SolvePuzzle

namespace Eternity2

open LeanSAT LeanSAT.Encode Eternity2.Encoding

/- Find solutions not already found in `bdir`, outputting them to `bdir` -/
def solveAndOutput [Solver IO] (bdir : BoardDir)
      (es : SolvePuzzle.EncodingSettings)
      (parallelize : Bool)
      : Log IO Unit
  := do
  if bdir.allSols then
    Log.info s!"Board {bdir.puzFile}: already solved"
    return
  
  Log.info s!"Board {bdir.puzFile}: clue file {
      if bdir.clues.isSome then "present" else "not present"
    }; {bdir.sols.size} solutions present"
  
  let (tsv, enc) := EncCNF.new! do
    -- encode the basic puzzle constraints
    let tsv ← SolvePuzzle.encodePuzzle bdir.ts es
    -- if clues exist, encode them
    for clues in bdir.clues do
      SolvePuzzle.encodeClues tsv (clues)
    -- block each existing solution
    for (_, sol) in bdir.sols do
      let a ← SolvePuzzle.encodeSol tsv (sol)
      EncCNF.blockAssn a
    
    return tsv
  
  let name := bdir.puzFile.toString
  let bdRef : IO.Ref { bd : BoardDir //
    ∃ (hsize : bd.size = bdir.size)
    (hcolors : bd.colors = bdir.colors),
    bd.ts = hsize ▸ hcolors ▸ bdir.ts }
    ← IO.mkRef ⟨bdir, rfl, rfl, rfl⟩
  if parallelize then
    let handle ← Log.getLogger
    let (_ : List Unit) ← (List.fins 24).parMap fun i => do
      Log.run handle do
      let ((), enc) := EncCNF.run! enc do
        Encoding.fixCorners tsv i
      Log.info s!"Board {name}, corner {i}: Starting solver"
      aux tsv enc s!"{name}, corner {i}" bdRef
      Log.info s!"Board {name}, corner {i}: Solver finished"
  else
    aux tsv enc name bdRef
  Log.info s!"Board {name}: All solutions found"
  let _ ← (← bdRef.get).1.markAllSols
where
  aux (tsv : TileSetVariables bdir.ts) enc name
    (bdRef : IO.Ref _)
    : Log IO Unit := do
  for assn in Solver.solutions enc.toFormula tsv.diamondVarList do
    match SolvePuzzle.decodeSol tsv assn with
    | .error s =>
      Log.error s!"Failed to decode board {name} solution: {s}"
    | .ok sol =>
      let ⟨bd,h⟩ ← bdRef.get
      let sol : BoardSol bd.ts := cast (by
          rw [h.2.2]
          cases bd
          cases h.2.1
          cases h.1
          rfl
        ) sol
      let (path, bdir') ← bd.addSolNextName sol
      bdRef.set ⟨bdir', sorry⟩
      Log.info s!"Board {name}: Wrote solution to {path.fileName.get!}"
