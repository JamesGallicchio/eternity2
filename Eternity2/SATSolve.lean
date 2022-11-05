import Eternity2.EncCNF

namespace SATSolve

open Std EncCNF

@[extern "leankissat_initialize"]
private opaque kissatInit : IO Unit

builtin_initialize kissatInit

opaque KissatSolver.Pointed : NonemptyType.{0}

def KissatSolver := (KissatSolver.Pointed).type

namespace KissatSolver

instance : Nonempty KissatSolver := KissatSolver.Pointed.property

@[extern "leankissat_new"]
opaque new (_ : @& Unit) : KissatSolver

instance : Inhabited KissatSolver := ⟨new ()⟩

/-- Add clause of the form `[(neg₁,num₁), ⋯, (negₖ,numₖ)]`, where
literal `i` is the variable `numᵢ` and negated iff `negᵢ`. -/
@[extern "leankissat_add_clause"]
opaque addClause (C : KissatSolver) (L : @& List (Bool × Nat)) : KissatSolver

@[extern "leankissat_solve"]
opaque solve (C : KissatSolver) : KissatSolver × Option Bool

@[extern "leankissat_value"]
opaque value (C : @& KissatSolver) (i : @& Nat) : Option Bool

end KissatSolver

set_option compiler.extract_closed false in
def solve (e : State) (varsToGet : List Var) : Option (HashMap Var Bool) :=
  let s := e.clauses.foldl (fun s clause =>
      s.addClause <| clause.map (fun l => (l.neg, l.var+1))
    ) (KissatSolver.new ())
  match s.solve with
  | (_, none) => panic! "Something went wrong running kissat"
  | (_, some false) => none
  | (s, some true) => some <|
    let res := varsToGet.foldl (fun map v =>
        match s.value (v.succ) with
        | none => map
        | some true  => map.insert v true
        | some false => map.insert v false
      ) HashMap.empty
    res
