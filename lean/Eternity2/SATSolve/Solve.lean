import Eternity2.SATSolve.Cadical

namespace SATSolve

open System Std EncCNF

inductive SolveRes
| sat (assn : HashMap Var Bool)
| unsat
| error

def SolveRes.isSat : SolveRes → Bool
| .sat _  => true
| _       => false

def SolveRes.getAssn? : SolveRes → Option (HashMap Var Bool)
| .sat assn => some assn
| _         => none

private def solveAux (s : CadicalSolver) (varsToGet : List Var)
  : CadicalSolver × SolveRes :=
  match s.solve with
  | (s, none) => (s, .error)
  | (s, some false) => (s, .unsat)
  | (s, some true) => (s, .sat <|
    varsToGet.foldl (fun map v =>
      match s.value v with
      | none => map
      | some true  => map.insert v true
      | some false => map.insert v false
    ) HashMap.empty)


set_option compiler.extract_closed false in
/-- Solve the CNF `e`, returning the map of `varsToGet` to their
truth value in the solution, or `none` if unsat.
 -/
def solve (e : State) (varsToGet : List Var) :=
  let s := e.clauses.foldl (fun s clause =>
      s.addClause <| clause.map (fun l => (l.neg, l.var))
    ) (CadicalSolver.new ())
  solveAux s varsToGet

set_option compiler.extract_closed false in
/-- Solve the CNF `e`, returning the map of `varsToGet` to their
truth value in the solution, or `none` if unsat.

If `timeout = some m`, the call will timeout after `m` milliseconds.
 -/
def solveWithTermCond (e : State) (varsToGet : List Var) (terminate : IO Bool) :=
  let s := e.clauses.foldl (fun s clause =>
      s.addClause <| clause.map (fun l => (l.neg, l.var))
    ) (CadicalSolver.new ())
  let s := s.setTerminateCallback terminate
  solveAux s varsToGet

def solveWithTimeout (e : State) (varsToGet : List Var) (timeout : Nat)
  : IO (CadicalSolver × SolveRes) := do
  let startTime ← IO.monoMsNow
  return solveWithTermCond e varsToGet (do
    let now ← IO.monoMsNow
    return now > startTime + timeout)

def addAndResolve (s : CadicalSolver) (c : Clause) (varsToGet : List Var)
  : CadicalSolver × SolveRes :=
  let s := s.addClause <| c.map (fun l => (l.neg, l.var))
  solveAux s varsToGet

/-- Find all solutions to a given CNF -/
def allSols (enc : State) (varsToGet : List Var)
            (varsToBlock : List Var := varsToGet)
            (reportProgress : Bool := false)
            (termCond : Option (IO Bool) := none)
            (perItem : HashMap Var Bool → IO Unit): IO Unit
            := do

  let varsToGet := varsToGet.union varsToBlock

  let mut count := 0
  let mut (solver,satResult) :=
    match termCond with
    | some termCond =>
      SATSolve.solveWithTermCond enc varsToGet termCond
    | none =>
      SATSolve.solve enc varsToGet

  let start ← liftM (n := IO) IO.monoMsNow
  let mut lastUpdateTime := 0

  while satResult.isSat do
    let now ← liftM (n := IO) IO.monoMsNow
    if reportProgress && now - lastUpdateTime > 2000 then
      lastUpdateTime := now
      IO.print s!"\rfound {count} ({count*1000/(now-start)} / sec)"
      IO.FS.Stream.flush (← liftM (n := IO) IO.getStdout)

    match satResult with
    | .unsat | .error => panic! "Unreachable :( 12509814"
    | .sat assn =>
      count := count + 1
      perItem assn
      let newClause : EncCNF.Clause :=
        varsToBlock.filterMap (fun v => assn.find? v |>.map (⟨v, ·⟩))

      (solver, satResult) := SATSolve.addAndResolve solver newClause varsToGet

  if reportProgress then
    let duration := (← liftM (n := IO) IO.monoMsNow) - start
    IO.println s!"\rfound {count} solutions in {duration}ms ({(1000*count)/duration} / sec)"
    let std ← liftM (n := IO) IO.getStdout
    IO.FS.Stream.flush std

  return
