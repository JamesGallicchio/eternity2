import Lake
open Lake DSL

/-- The directory where cadical source will be cloned/maintained -/
def cadicalDir : FilePath := "./cadical"
/-- The path to `libstdc++.so.6` -/
def libstdcpp : FilePath := "/usr/lib/x86_64-linux-gnu/libstdc++.so.6"

package eternity2 {
  moreLeancArgs := #[ "--verbose" ]
  moreLinkArgs := #[
    "-L" ++ (cadicalDir / "build").toString,
    "-I" ++ (cadicalDir / "src").toString,
    "-lcadical"
    -- libstdcpp.toString
  ]
}

lean_lib Eternity2

target leancadical.o (pkg : Package) : FilePath := do
  let oFile := pkg.buildDir / "c" / "leancadical.o"
  let srcFile ← inputFile <| pkg.dir / "ffi" / "leancadical.c"
  buildFileAfterDep oFile srcFile fun srcFile => do
    let flags := #[
      "-I" ++ (← getLeanIncludeDir).toString,
      "-I" ++ (cadicalDir / "src").toString,
      "-O3", "-fPIC"]
    compileO "leancadical.c" oFile srcFile flags "clang"

extern_lib libleancadical (pkg : Package) := do
  -- copy libcadical.so into build/lib
  IO.FS.createDirAll (pkg.buildDir / "lib")
  proc {
    cmd := "cp"
    args := #[
      (cadicalDir / "build" / "libcadical.a").toString,
      (pkg.buildDir / "lib" / "libcadical.a").toString ]
  }

  let name := nameToStaticLib "leancadical"
  let ffiO ← fetch <| pkg.target ``leancadical.o
  buildStaticLib (pkg.buildDir / "lib" / name) #[ffiO]


@[default_target]
lean_exe eternity2 {
  root := `Main
}

require std from git
  "https://github.com/JamesGallicchio/std4" @ "iterators"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "nightly"

script setup _args := do  
  if !( (← cadicalDir.pathExists)) then
    IO.println s!"Setting up cadical in new directory: {cadicalDir}"
    let child ← IO.Process.spawn {
      cmd := "git"
      args := #["clone", "https://github.com/arminbiere/cadical"]
    }
    if (← child.wait) ≠ 0 then
      IO.println "Error while cloning cadical, canceling setup"
      return 1

  else if !( (← (cadicalDir/".git").pathExists) ) then
    IO.println "Directory for cadical exists, but doesn't have a git repo?"
    IO.println cadicalDir
    return 1

  else
    IO.println "Updating cadical..."
    let child ← IO.Process.spawn {
      cmd := "git"
      args := #["pull"]
      cwd := some cadicalDir
    }
    if (← child.wait) ≠ 0 then
      IO.println "Error while pulling cadical?"
      return 1

  if (← (cadicalDir / "makefile").pathExists) then
    IO.println "Removing old cadical build..."
    let child ← IO.Process.spawn {
      cmd := "make"
      args := #[ "clean" ]
      cwd := cadicalDir
    }
    if (← child.wait) ≠ 0 then
      IO.println "make clean failed?"
      return 1

  IO.println "Configuring cadical makefile..."
  let cxxflags :=  "-I" ++ (←getLeanIncludeDir).toString ++
                          " -L" ++ ((←getLeanLibDir) / "..").toString ++
                          " -lc++"
  IO.println cxxflags
  let child ← IO.Process.spawn {
    cmd := s!"./configure"
    args := #["-fPIC"]
    env := #[ ("CXX", "clang++") ]
    cwd := cadicalDir
  }
  if (← child.wait) ≠ 0 then
    IO.println "Error configuring cadical makefiles"
    return 1

  IO.println "Building cadical..."
  let child ← IO.Process.spawn {
    cmd := "make"
    cwd := cadicalDir
  }
  if (← child.wait) ≠ 0 then
    IO.println "Error building cadical"
    return 1

  return 0

