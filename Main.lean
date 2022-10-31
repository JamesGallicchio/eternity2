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
    let tsVars ← Constraints.colorCardConstraints ts 9
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
      let sol := tsVars.map (fun (t,v) =>
        {t with sign := as.find? v |>.map (fun | true => .plus | false => .minus)})
      sols := sol :: sols
      let newClause : EncCNF.Clause :=
        tsVars.map (fun (_,v) => ⟨v, as.find? v |>.get!⟩)
      enc.appendFileDIMACSClause tempFileName newClause

  IO.FS.removeFile tempFileName
  return sols


def main : IO Unit := do
  let ts ← TileSet.fromFile "puzzles/rand7_7_7.txt"
  let sols ← signSols ts
  IO.println s!"{sols.length}"
