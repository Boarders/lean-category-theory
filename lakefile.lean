import Lake
open Lake DSL

package «category-theory» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «CategoryTheory» where
  -- add library configuration options here
