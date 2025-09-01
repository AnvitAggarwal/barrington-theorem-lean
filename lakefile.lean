import Lake
open Lake DSL

-- Project info
package barrington_theorem_lean

-- Your library
lean_lib BarringtonTheoremLean

-- Require mathlib
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"
