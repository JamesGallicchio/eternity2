import Eternity2.EncCNF

namespace SATSolve

open Std EncCNF System

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

/-- Find all solutions to a given CNF -/
def allSols (enc : State) (varsToGet : List Var)
            (reportProgress : Bool := false) : IO (List (AssocList Var Bool))
            := do
  IO.FS.createDirAll "cnf"
  let cnfDir : FilePath := "./cnf"
  let tempFileName ← (do
    let mut num : Nat := 1
    while ← (cnfDir / s!"temp{num}.cnf").pathExists do
      num := num + 1
    return cnfDir / s!"temp{num}.cnf")
  
  enc.printFileDIMACS tempFileName.toString

  let mut count := 0
  let mut sols := []
  let mut satResult := SATSolve.solve enc varsToGet

  let start ← IO.monoMsNow
  let mut lastUpdateTime := 0

  while satResult.isSome do
    let now ← IO.monoMsNow
    if reportProgress && now - lastUpdateTime > 2000 then
      lastUpdateTime := now
      IO.print s!"\rfound {count} ({count*1000/(now-start)} / sec)"
      (←IO.getStdout).flush

    match satResult with
    | none => panic! "Unreachable :( 12509814"
    | some (s, assn) =>
      count := count + 1
      let sol := varsToGet.foldl (fun acc v =>
        match assn.find? v with
        | none => acc
        | some b => acc.cons v b) AssocList.nil
      sols := sol :: sols
      let newClause : EncCNF.Clause :=
        varsToGet.filterMap (fun v => assn.find? v |>.map (⟨v, ·⟩))
      enc.appendFileDIMACSClause tempFileName.toString newClause

      satResult := SATSolve.addAndResolve s newClause varsToGet

  if reportProgress then
    let duration := (←IO.monoMsNow) - start
    IO.println s!"\rfound {count} solutions in {duration}ms ({(1000*count)/duration} / sec)"
    (←IO.getStdout).flush

  IO.FS.removeFile tempFileName
  return sols
