import Lake
open Lake DSL

package eternity2 {
  -- add package configuration options here
}

lean_lib Eternity2 {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe eternity2 {
  root := `Main
}

require std from git
  "https://github.com/JamesGallicchio/std4" @ "iterators"
