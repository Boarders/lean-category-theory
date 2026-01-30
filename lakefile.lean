import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «how-to-prove-it» where
  -- add package configuration options here

lean_lib «HowToProveIt» where
  -- add library configuration options here

lean_lib «PropLogic» where
  roots := #[`PropLogic]

lean_lib «Category» where
  roots := #[`Category]

@[default_target]
lean_exe «how-to-prove-it» where
  root := `Main
