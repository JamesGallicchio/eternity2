import Lake
open Lake DSL

/-- The directory where kissat source will be cloned/maintained -/
def kissatDir : FilePath := "./kissat"

package eternity2 {
  moreLinkArgs := #[
    "-L" ++ (kissatDir / "build").toString,
    "-I" ++ (kissatDir / "src").toString,
    "-lkissat"
  ]
}

lean_lib Eternity2

target leankissat.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leankissat.o"
  let srcFile ← inputFile <| pkg.dir / "ffi" / "leankissat.c"
  buildFileAfterDep oFile srcFile fun srcFile => do
    let flags := #[
      "-I" ++ (← getLeanIncludeDir).toString,
      "-I" ++ (kissatDir / "src").toString,
      "-O3", "-fPIC"]
    compileO "leankissat.c" oFile srcFile flags

extern_lib libleankissat (pkg : Package) := do
  let name := nameToStaticLib "leankissat"
  let ffiO ← fetch <| pkg.target ``leankissat.o
  buildStaticLib (pkg.buildDir / "lib" / name) #[ffiO]


@[default_target]
lean_exe eternity2 {
  root := `Main
}

require std from git
  "https://github.com/JamesGallicchio/std4" @ "iterators"

script setup _args := do  
  if !( (← kissatDir.pathExists)) then
    IO.println s!"Setting up kissat in new directory: {kissatDir}"
    let child ← IO.Process.spawn {
      cmd := "git"
      args := #["clone", "https://github.com/arminbiere/kissat"]
    }
    if (← child.wait) ≠ 0 then
      IO.println "Error while cloning kissat, canceling setup"
      return 1

  else if !( (← (kissatDir/".git").pathExists) ) then
    IO.println "Directory for kissat exists, but doesn't have a git repo?"
    IO.println s!"(try `rmdir {kissatDir})"
    return 1

  else
    IO.println "Updating kissat..."
    let child ← IO.Process.spawn {
      cmd := "git"
      args := #["pull"]
      cwd := some kissatDir
    }
    if (← child.wait) ≠ 0 then
      IO.println "Error while pulling kissat"
      return 1

  if (← (kissatDir / "makefile").pathExists) then
    IO.println "Cleaning kissat build..."
    let child ← IO.Process.spawn {
      cmd := "make"
      args := #[ "clean" ]
      cwd := kissatDir
    }
    if (← child.wait) ≠ 0 then
      IO.println "make clean failed?"
      return 1

  IO.println "Configuring kissat makefile..."
  let child ← IO.Process.spawn {
    cmd := s!"./configure"
    args := #["-fPIC"]
    cwd := kissatDir
  }
  if (← child.wait) ≠ 0 then
    IO.println "Error configuring kissat makefiles"
    return 1

  IO.println "Building kissat..."
  let child ← IO.Process.spawn {
    cmd := "make"
    cwd := kissatDir
  }
  if (← child.wait) ≠ 0 then
    IO.println "Error building kissat"
    return 1

  return 0

