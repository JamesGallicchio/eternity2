import Eternity2.Puzzle.SignSol
import Eternity2.Puzzle.Encoding
import Eternity2.Puzzle.SolvePuzzle
import Eternity2.Puzzle.SignCorrs
import Eternity2.Plots.BoardSuite
import Eternity2.FileFormat.Puz
import Eternity2.FileFormat.Clue
import LeanSAT.Solver.Impl.D4Command
import Lean

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

structure SignSolLoc where
  -- in discr search order, number of valid sign solutions before this one
  index : Nat
  path : List DiscrSearch.Dir
deriving Lean.ToJson, Lean.FromJson

/- Finds & returns data about where solutions occur in the
discrimination search over sign solutions. Uses correlations produced
by the given `SignCorrSolver`.

Returns `.error ()` if the search fails to find all solutions. -/
partial def findSolInSignDiscrSearch [Solver IO] [Solver.ModelSample IO] [SignCorrSolver IO]
    (name : String)
    (ts : TileSet size (Tile <| Color.WithBorder s))
    (sols : List (System.FilePath × BoardSol ts))
    : Log IO (Except Unit <| List (System.FilePath × SignSolLoc)) := do
  let (tsv, enc) := EncCNF.new! do
    let tsv ← Encoding.mkVars ts
    do
      Encoding.colorCardConstraints tsv
      Encoding.signCardConstraints tsv
    return tsv

  Log.info s!"finding correlations for {name}"
  let corrs ← liftM (m := IO) <| SignCorrSolver.getCorrs tsv enc

  let corrList := corrs.inBiasOrder

  -- print correlation list nicely
  Log.info s!"correlation chain for {name}:\n{
    corrList.map (fun (i,j,corr) => s!"\t{i}\t{j}\t{corr}")
    |> String.intercalate "\n"
  }"

  let count ← IO.mkRef 0
  let sols ← IO.mkRef sols
  let foundsols ← IO.mkRef []

  let res : Option (List _) ←
    /- we need to make size*size-1 branches -/
    DiscrSearch.discrSearch (size * size - 1)
      /- (sorted) corr list, (reversed) partial path, encoding of partial path,
        and a solution for this branch if one is already known -/
      (init := (corrList, [], enc, none))
      (f := fun (corrList, path, enc, knownSol) => do
    -- find a solution for this path, using `knownSol` if present
    match
      ← knownSol.orElseM (do
      match ← liftM (m := IO) <| Solver.solve enc.toFormula with
      | .unsat | .error => return none
      | .sat s => return some s)
    with
    | none =>
      /- couldn't find a solution -/
      return .fail
    | some knownSol =>
    match corrList with
    | (i,j,cs) :: corrList =>
      -- branch on `i`,`j`
      let iSign := knownSol.find? (tsv.sign_vars i)
      let jSign := knownSol.find? (tsv.sign_vars j)
      if iSign.isNone || jSign.isNone then
        -- should not happen?
        Log.error s!"discr search on {name}: both i/j unassigned (corr list not in bias order). {i}: {iSign}, {j}: {jSign}"
        return .fail
      else return .branch (fun d =>
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
          if ( iSign = jSign ) = setThemSame then
            some knownSol
          else
            none
        (corrList, d :: path, enc, knownSol))
    | [] =>
      -- try to find solutions at this leaf
      let mut sols' := []
      for (fp,s) in ← sols.get do
        let ((), enc) := EncCNF.run! enc do
          Encoding.associatePolarities tsv
          let assn ← SolvePuzzle.encodeSol tsv s
          EncCNF.addAssn assn
        match ← liftM (m := IO) <| Solver.solve enc.toFormula with
        | .unsat | .error =>
          sols' := (fp,s) :: sols'
        | .sat _ =>
          Log.info s!"found sol {fp} at index {← count.get}"
          foundsols.modify (
            (fp, {index := ← count.get, path := path.reverse})
            :: ·)
      
      count.modify (· + 1)
      sols.set sols'
      if sols'.isEmpty then
        return .found (← foundsols.get)
      else
        return .fail
  )
  match res with
  | some L => return .ok L
  | none =>
    Log.error s!"discr search on {name}: Failed to find solutions: {(← sols.get).map (·.1)}"
    return .error ()


/- Runs discrimination search over sign solutions for all
solved boards in the board suite. Outputs the data to JSON in
the respective board folder. -/
partial def calcDiscrSearchStats [Solver IO] [Solver.ModelSample IO] [SignCorrSolver IO]
    (bs : BoardSuite)
    : Log IO Unit := do
  let logfile ← Log.getLogger
  let boards ← bs.boards
    |>.filterM (fun bd => do
      -- board should have all solutions, and should not already have stat file
      return bd.allSols && ! (← (bd.puzFile.withFileName "discr_search_stats.json").pathExists) )
  let tasks : Array (Task (Except IO.Error Unit)) ←
    boards.insertionSort (fun bd1 bd2 =>
      bd1.size < bd2.size ||
      bd1.size = bd2.size && bd1.colors.center < bd2.colors.center)
    |>.mapM (fun b => IO.asTask (Log.run logfile <| do
      let stats ← findSolInSignDiscrSearch
        b.puzFile.toString
        b.ts
        b.sols.toList
      match stats with
      | .error () => return
      | .ok stats =>
      let statfile := b.puzFile.withFileName "discr_search_stats.json"
      Log.info s!"writing stats to {statfile}"
      let json := Lean.ToJson.toJson stats
      IO.FS.writeFile statfile json.pretty
      ))

  IO.ofExcept <|
    ← IO.wait (← IO.mapTasks (fun _units => return ()) tasks.toList)
