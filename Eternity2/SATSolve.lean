import Eternity2.EncCNF

namespace SATSolve

open Std EncCNF

@[extern "leancadical_initialize"]
private opaque cadicalInit : IO Unit

builtin_initialize cadicalInit

opaque CadicalSolver.Pointed : NonemptyType.{0}

def CadicalSolver := (CadicalSolver.Pointed).type

namespace CadicalSolver

instance : Nonempty CadicalSolver := CadicalSolver.Pointed.property

@[extern "leancadical_new"]
opaque new (u : @& Unit) : CadicalSolver

instance : Inhabited CadicalSolver := ⟨new ()⟩

@[extern "leancadical_add_clause"]
opaque addClause (C : CadicalSolver) (L : @& List (Bool × Nat)) : CadicalSolver

@[extern "leancadical_solve"]
opaque solve (C : CadicalSolver) : CadicalSolver × Option Bool

@[extern "leancadical_value"]
opaque value (C : @& CadicalSolver) (i : @& Nat) : Option Bool

end CadicalSolver

def runCadicalCLI (cnfFile : String) : IO (Option (HashMap Var Bool)) := do
  -- Run cadical on cnfFile
  let out := (← IO.Process.output {
    stdin := .piped
    stdout := .piped
    stderr := .piped
    cmd := "cadical"
    args := #[cnfFile, "--sat", "-f", "-q"]
  }).stdout
  let lines := out.splitOn "\n" |>.filter (not <| String.startsWith "c" ·)
  match lines with
  | "s SATISFIABLE" :: satis =>
    return some (
      satis
      |>.filter (not <| ·.isEmpty)
      |>.map (·.drop 2 |>.splitOn " ")
      |>.join
      |>.map (·.toInt!)
      |>.filter (· ≠ 0)
      |>.foldl (fun acc i =>
          acc.insert (Int.natAbs i - 1) (i > 0)
        ) (HashMap.empty)
    )
  | "s UNSATISFIABLE" :: _ => return none
  | out =>
    panic! s!"failed to parse output ({out.length} lines):\n{out.take 3}\n..."

set_option compiler.extract_closed false in
def solve (e : State) (varsToGet : List Var) : Option (CadicalSolver × HashMap Var Bool) :=
  let s := e.clauses.foldl (fun s clause =>
      s.addClause <| clause.map (fun l => (l.neg, l.var+1))
    ) (CadicalSolver.new ())
  match s.solve with
  | (_, none) => panic! "Something went wrong running cadical"
  | (_, some false) => none
  | (s, some true) => some <|
    let res := varsToGet.foldl (fun map v =>
        match s.value (v.succ) with
        | none => map
        | some true  => map.insert v true
        | some false => map.insert v false
      ) HashMap.empty
    (s, res)

def addAndResolve (s : CadicalSolver) (c : Clause) (varsToGet : List Var)
  : Option (CadicalSolver × HashMap Var Bool) :=
  let s := dbgTraceIfShared "s shared 1" s
  let s := s.addClause <| c.map (fun l => (l.neg, l.var+1))
  let s := dbgTraceIfShared "s shared 2" s
  match s.solve with
  | (_, none) => panic! "something went wrong running cadical"
  | (_, some false) => none
  | (s, some true) => some <|
    let s := dbgTraceIfShared "s shared 3" s
    let res := varsToGet.foldl (fun map v =>
        match s.value (v.succ) with
        | none => map
        | some true  => map.insert v true
        | some false => map.insert v false
      ) HashMap.empty
    let s := dbgTraceIfShared "s shared 4" s
    (s, res)