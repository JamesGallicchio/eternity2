import Eternity2

open Eternity2

def main : IO Unit := do
  let b ← DiamondBoard.gen_dboard 2 9
  let t := DiamondBoard.dboard_to_tboard b false
  IO.println t

  let ts := t.tileSet
  let (tsVars, enc) := EncCNF.run (do
    let tsVars ← ColorCardinality.colorCardConstraints ts 9
    EncCNF.addClause [⟨tsVars.head!.2, false⟩]
    return tsVars)
  --enc.printDIMACS

  match ← enc.checkSAT "rand_colorconstraints.cnf" with
  | none => IO.println "Unsatisfiable"
  | some as =>
    IO.println "Satisfiable:"
    for (t,v) in tsVars do
      IO.println s!"{{t with sign := match as.find? v with | none => none | some true => some .plus | some false => some .minus}}"
