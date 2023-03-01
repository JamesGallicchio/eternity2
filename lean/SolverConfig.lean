import LeanSAT.Solver

instance : LeanSAT.Solver IO :=
  LeanSAT.Solver.Impl.DimacsCommand "timeout" (flags := ["5", "cadical"])

instance : LeanSAT.Solver.ApproxModelCount IO :=
  LeanSAT.Solver.Impl.ApproxMCCommand
