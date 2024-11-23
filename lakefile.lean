import Lake
open Lake DSL

package "fad" where
  -- add package configuration options here

lean_lib «Fad» where
  -- add library configuration options here

lean_lib «AoC» where
  -- add library configuration options here


@[default_target]
lean_exe "fad" where
  root := `Main
