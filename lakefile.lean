import Lake
open Lake DSL

package «levy-steinitz» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LevySteinitz» where
  -- add any library configuration options here
