import Lake
open Lake DSL

package «certified-reduction»

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "8a178386ffc0f5fef0b77738bb5449d50efeea95"

lean_lib Populus where
  roots := #[`Populus]
