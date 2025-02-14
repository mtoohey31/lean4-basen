import Lake
open Lake DSL

package basen

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

@[default_target]
lean_lib «BaseN»
