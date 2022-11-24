import Eternity2.SATSolve.Cadical

namespace SATSolve

open System Std EncCNF

private def solveAux (s : CadicalSolver) (varsToGet : List Var)
  : Option (CadicalSolver × HashMap Var Bool) :=
  match s.solve with
  | (_, none) => panic! "Something went wrong running cadical"
  | (_, some false) => none
  | (s, some true) => some <|
    let res := varsToGet.foldl (fun map v =>
        match s.value v with
        | none => map
        | some true  => map.insert v true
        | some false => map.insert v false
      ) HashMap.empty
    (s, res)


set_option compiler.extract_closed false in
def solve (e : State) (varsToGet : List Var) :=
  let s := e.clauses.foldl (fun s clause =>
      s.addClause <| clause.map (fun l => (l.neg, l.var))
    ) (CadicalSolver.new ())
  solveAux s varsToGet

def addAndResolve (s : CadicalSolver) (c : Clause) (varsToGet : List Var)
  : Option (CadicalSolver × HashMap Var Bool) :=
  let s := s.addClause <| c.map (fun l => (l.neg, l.var))
  solveAux s varsToGet

/-- Find all solutions to a given CNF -/
def allSols (enc : State) (varsToGet : List Var)
            (varsToBlock : List Var := varsToGet)
            (reportProgress : Bool := false)
            (perItem : HashMap Var Bool → IO Unit): IO Unit
            := do

  let varsToGet := varsToGet.union varsToBlock

  let mut count := 0
  let mut satResult := SATSolve.solve enc varsToGet

  let start ← liftM (n := IO) IO.monoMsNow
  let mut lastUpdateTime := 0

  while satResult.isSome do
    let now ← liftM (n := IO) IO.monoMsNow
    if reportProgress && now - lastUpdateTime > 2000 then
      lastUpdateTime := now
      IO.print s!"\rfound {count} ({count*1000/(now-start)} / sec)"
      IO.FS.Stream.flush (← liftM (n := IO) IO.getStdout)

    match satResult with
    | none => panic! "Unreachable :( 12509814"
    | some (s, assn) =>
      count := count + 1
      perItem assn
      let newClause : EncCNF.Clause :=
        varsToBlock.filterMap (fun v => assn.find? v |>.map (⟨v, ·⟩))

      satResult := SATSolve.addAndResolve s newClause varsToGet

  if reportProgress then
    let duration := (← liftM (n := IO) IO.monoMsNow) - start
    IO.println s!"\rfound {count} solutions in {duration}ms ({(1000*count)/duration} / sec)"
    let std ← liftM (n := IO) IO.getStdout
    IO.FS.Stream.flush std

  return
