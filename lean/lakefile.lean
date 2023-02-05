import Lake
open Lake DSL

package eternity2 {
  precompileModules := true
}

lean_lib SolverConfig

lean_lib Eternity2

@[default_target]
lean_exe eternity2 {
  root := `Main
}

require «lean-sat» from git
  "https://github.com/JamesGallicchio/LeanSAT" @ "main"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "nightly"

