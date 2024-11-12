import Lake
open Lake DSL

package "graphs" where
  -- add package configuration options here

lean_lib «Graphs» where
  -- add library configuration options here

@[default_target]
lean_exe "graphs" where
  root := `Main
