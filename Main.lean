import Eternity2

open Eternity2

def genTileSet (size colors : Nat) : IO TileSet := do
  let b ← DiamondBoard.generate size colors
  let t := DiamondBoard.tileBoard b false
  return t.tileSet

def fetchEternity2Tiles : IO TileSet :=
  TileSet.fromFile "puzzles/e2pieces.txt"

def signSols (ts : TileSet) (reportProgress : Bool := false) : IO (List TileSet) := do
  IO.FS.createDirAll "cnf"
  let tempFileName := s!"cnf/temp{←IO.rand 1 10000}.cnf"
  let (tsVars, enc) := EncCNF.new (do
    let tsVars ← Constraints.colorCardConstraints ts.tiles 9
    EncCNF.addClause [⟨tsVars.head!.2, false⟩]
    return tsVars)

  enc.printFileDIMACS tempFileName

  let mut done := false
  let mut count := 0
  let mut sols := []

  while !done do
    if reportProgress && count % 1000 = 0 then
      IO.println s!"count = {count}"

    match ← SATSolve.runCadical tempFileName with
    | none => done := true
    | some as =>
      count := count + 1
      let sol :=
        ⟨ tsVars.map (fun (t,v) =>
            {t with sign := as.find? v |>.map (fun | true => .plus | false => .minus)})
        , ts.size⟩
      sols := sol :: sols
      let newClause : EncCNF.Clause :=
        tsVars.map (fun (_,v) => ⟨v, as.find? v |>.get!⟩)
      enc.appendFileDIMACSClause tempFileName newClause

  IO.FS.removeFile tempFileName
  return sols

section variable (size : Nat) (iters := 100) (reportProgress := true)

def sampleSolutionCounts := do
  let mut counts := []
  let width := 80
  IO.print ("[".pushn ' ' width ++ "]")
  for i in [0:iters] do
    if reportProgress then
      let stars := (width * i + width / 2 + 1) / iters
      IO.print ("\r[".pushn '*' stars |>.pushn ' ' (width-stars) |>.push ']')
      (←IO.getStdout).flush
    let ts ← genTileSet size size
    let sols ← signSols ts
    counts := sols.length :: counts

  IO.println ""
  return counts

def printSolutionCountStats := do
  let counts ← sampleSolutionCounts size
  IO.println s!"counts: {counts}"
  let avg := (counts.foldl (· + ·) (counts.length / 2)) / counts.length
  let var := (counts.foldl (fun acc x => acc + (x - avg) * (x - avg)) (counts.length / 2)) / counts.length
  IO.println s!"avg: {avg}"
  IO.println s!"var: {var}"
  IO.println s!"std: {Nat.sqrt var}"

end

def main : IO Unit := do
  printSolutionCountStats 6