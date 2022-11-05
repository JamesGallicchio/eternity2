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
opaque addClause (C : CadicalSolver) (L : @& List Nat) : CadicalSolver

@[extern "leancadical_solve"]
opaque solve (C : CadicalSolver) : CadicalSolver × Option Bool

end CadicalSolver

def runCadical (cnfFile : String) : IO (Option (HashMap Var Bool)) := do
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
