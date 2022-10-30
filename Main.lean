import Eternity2

open Eternity2

def genTileSet (size colors : Nat) : IO TileSet := do
  let b ← DiamondBoard.gen_dboard size colors
  let t := DiamondBoard.dboard_to_tboard b false
  return t.tileSet

def fetchEternity2Tiles : IO TileSet :=
  TileSet.fromFile "puzzles/e2pieces.txt"

def signSols (ts : TileSet) : IO (List TileSet) := do
  let (tsVars, enc) := EncCNF.new (do
    let tsVars ← ColorCardinality.colorCardConstraints ts 9
    EncCNF.addClause [⟨tsVars.head!.2, false⟩]
    return tsVars)

  let mut done := false
  let mut count := 0
  let mut sols := []

  while !done do
    if count % 1000 = 0 then
      IO.println s!"count = {count}"

    match ← SATSolve.runCadical "cnf/temp.cnf" with
    | none => done := true
    | some as =>
      count := count + 1
      let sol := tsVars.map (fun (t,v) =>
        {t with sign := as.find? v |>.map (fun | true => .plus | false => .minus)})
      sols := sol :: sols
      let newClause : EncCNF.Clause :=
        tsVars.map (fun (_,v) => ⟨v, as.find? v |>.get!⟩)
      enc.appendFileDIMACSClause "cnf/temp.cnf" newClause

  return sols


def main : IO Unit := do
  let ts ← genTileSet 7 7
  TileSet.toFile "puzzles/rand7_7_7.txt" ts
