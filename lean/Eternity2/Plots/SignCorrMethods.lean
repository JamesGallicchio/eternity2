import Eternity2.Puzzle.SignSol
import Eternity2.Puzzle.Encoding
import Eternity2.Puzzle.SolvePuzzle
import Eternity2.Puzzle.SignCorrs
import Eternity2.FileFormat.Puz
import Eternity2.FileFormat.Clue
import LeanSAT.Solver.Impl.D4Command

namespace Eternity2

open LeanSAT Encode

open Notation in
def countSignSols (ts : TileSet size (Tile (Color.WithBorder s))) (clue : BoardClues ts) : IO Nat := do
  test (do
    let tsv ← Encoding.mkVars ts
    clue.clues.head?.forM (fun (p,q,r) =>
      if q.isPos then
        EncCNF.addClause (tsv.sign_vars p)
      else
        EncCNF.addClause (¬ tsv.sign_vars p))
    Encoding.colorCardConstraints tsv
    return tsv.signVarList)
where test (enc : EncCNF (List Var)) := do
  let (signVars,enc) := EncCNF.new! enc

  let (enc, varMap) := enc.cleanup
  let signVars := signVars.map varMap
  
  -- count with approxmc
  let (amcTime, amcCount) ← IO.timeMs (do
    have : Solver.ModelCount IO := LeanSAT.Solver.Impl.ApproxMCCommand "approxmc"
    return ← Solver.ModelCount.modelCount enc.toFormula signVars
  )

  -- count with d4
   let (d4time, d4Count) ← IO.timeMs (do
    have : Solver.ModelCount IO := LeanSAT.Solver.Impl.D4Command.ModelCount
    return (← Solver.ModelCount.modelCount enc.toFormula none /- signVars -/)
  )

  IO.println s!"{enc.nextVar} vars; {enc.clauses.length} clauses"
  IO.println s!"approxmc ({amcTime}ms): {amcCount}"
  IO.println s!"d4 ({d4time}ms): {d4Count}"
  
  return d4Count


/- Finds & outputs data about where solutions occur in the
discrimination search over sign solutions. Uses correlations produced
by the given `SignCorrSolver` -/
partial def findSolInSignDiscrSearch [Solver IO] [Solver.ModelSample IO] [SignCorrSolver IO] (ts : TileSet size (Tile <| Color.WithBorder s)) (sols : List (BoardSol ts)) : IO Unit := do
  let (tsv, enc) := EncCNF.new! do
    let tsv ← Encoding.mkVars ts
    do
      Encoding.colorCardConstraints tsv
      Encoding.signCardConstraints tsv
    return tsv

  IO.println "finding sign correlations"
  let samples ← Solver.ModelSample.modelSample enc.toFormula (some tsv.signVarList) 10
  for assn in samples do
    for p in List.fins _ do
      IO.print (s!"{p}={if assn.find! <| tsv.sign_vars p then '+' else '-'} ")
    IO.println ""
  let corrs ← SignCorrSolver.getCorrs tsv enc

  let corrList := corrs.inBiasOrder

  -- print correlation list nicely
  IO.println "correlation chain:"
  for (i,j,corr) in corrList do
    IO.println s!"{i}\t{j}\t{corr}"

  let count ← IO.mkRef 0
  let sols ← IO.mkRef sols.enum

  let res ← DiscrSearch.discrSearch (size * size - 1) (corrList, [], enc, none) (fun (corrList, path, enc, knownSol) => do
    -- if we already know a solution to this path, then do not do the solver check
    let knownSol ←
      match knownSol with
      | some sol =>
        --IO.println s!"skipping check"
        pure sol
      | none =>
      match ← Solver.solve enc.toFormula with
      | .unsat | .error =>
        --IO.println s!"failed at partial path {path.reverse}"
        return .fail -- early fail
      | .sat s => pure s
    match corrList with
    | (i,j,cs) :: corrList =>
      --IO.println s!"branching on {i},{j}"
      return .branch (fun d =>
        let setThemSame := if cs.same > cs.diff then d = .left else d = .right
        let ((), enc) :=
          open Notation in EncCNF.run! enc do
          if setThemSame then
            EncCNF.addClause (¬ tsv.sign_vars i ∨   tsv.sign_vars j)
            EncCNF.addClause (  tsv.sign_vars i ∨ ¬ tsv.sign_vars j)
          else
            EncCNF.addClause (  tsv.sign_vars i ∨   tsv.sign_vars j)
            EncCNF.addClause (¬ tsv.sign_vars i ∨ ¬ tsv.sign_vars j)
        let knownSol :=
          let iSign := knownSol.find? (tsv.sign_vars i)
          let jSign := knownSol.find? (tsv.sign_vars j)
          if iSign.isNone || jSign.isNone then
            dbgTrace s!"{i}: {iSign}, {j}: {jSign}" fun () => none
          else
          if ( iSign = jSign ) = setThemSame then
            some knownSol
          else
            none
        (corrList, d :: path, enc, knownSol))
    | [] =>
      --IO.println s!"trying path {path.reverse}"
      let mut sols' := []
      for (i,s) in ← sols.get do
        let ((), enc) := EncCNF.run! enc do
          Encoding.associatePolarities tsv
          let assn ← SolvePuzzle.encodeSol tsv s
          EncCNF.addAssn assn
        match ← Solver.solve enc.toFormula with
        | .unsat | .error =>
          sols' := (i,s) :: sols'
        | .sat _ =>
          IO.println s!"Sol #{i} found on sign sol #{← count.get}; path ({path.countp (· = .right)} rights): {path.reverse}"
      
      count.modify (· + 1)
      sols.set sols'
      if sols'.isEmpty then
        return .found ()
      else
        return .fail
  )
  match res with
  | some () => pure ()
  | none =>
    IO.println s!"Failed to find solutions: {(← sols.get).map (·.1)}"
