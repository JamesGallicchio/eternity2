import Lake
open Lake DSL

def cadicalDir : FilePath := "/home/james/Projects/cadical"

package eternity2 {
  moreLeancArgs := #[
    "-fPIC"
  ]
  moreLinkArgs := #[
    "-L", (cadicalDir / "build").toString,
    "-l", "cadical",
    "-l", "stdc++"
  ]
}

lean_lib Eternity2 {
}

target leancadical.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leancadical.o"
  let srcJob ← inputFile <| pkg.dir / "ffi" / "cadical_ffi.c"
  buildFileAfterDep oFile srcJob fun srcFile => do
    let flags := #[
      "-I", (← getLeanIncludeDir).toString,
      "-I", (cadicalDir / "src").toString,
      "-O3", "-fPIC"]
    compileO "cadical_ffi.c" oFile srcFile flags "g++"

extern_lib libleancadical (pkg : Package) := do
  let name := nameToStaticLib "leancadical"
  let ffiO ← fetch <| pkg.target ``leancadical.o
  buildStaticLib (pkg.buildDir / "lib" / name) #[ffiO]

@[default_target]
lean_exe eternity2 {
  root := `Main
}

require std from git
  "https://github.com/JamesGallicchio/std4" @ "iterators"
