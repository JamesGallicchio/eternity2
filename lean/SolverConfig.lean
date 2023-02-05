import LeanSAT.Solver

instance : LeanSAT.Solver IO :=
  LeanSAT.Solver.Impl.DimacsCommand "cadical"

instance : LeanSAT.Solver.ApproxModelCount IO :=
  LeanSAT.Solver.Impl.ApproxMCCommand
