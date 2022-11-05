--import Eternity2.AuxDefs
--import Eternity2.Board
--import Eternity2.CardinalityHelpers
--import Eternity2.ColorCardConstraints
--import Eternity2.EncCNF
--import Eternity2.SATSolve
--import Eternity2.TileSet

@[extern "leancadical_initialize"]
private opaque cadicalInit : IO Unit

builtin_initialize cadicalInit

opaque CadicalSolver.Pointed : NonemptyType.{0}

def CadicalSolver := (CadicalSolver.Pointed).type

namespace CadicalSolver

instance : Nonempty CadicalSolver := CadicalSolver.Pointed.property

@[extern "leancadical_new"]
opaque new (_ : @& Unit) : CadicalSolver

instance : Inhabited CadicalSolver := ⟨new ()⟩

@[extern "leancadical_add_clause"]
opaque addClause (C : CadicalSolver) (L : @& List Nat) : CadicalSolver

@[extern "leancadical_solve"]
opaque solve (C : CadicalSolver) : CadicalSolver × Option Bool
