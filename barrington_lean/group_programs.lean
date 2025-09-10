import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete

#print Group
#check Group Nat
#check Fin 5
#check Equiv.Perm
#print Equiv.Perm

variable [Group G]

structure GPTriple (G : Type) where
  i : ℕ
  g₀ : G
  g₁ : G

#print Bool

abbrev GroupProgram (G : Type) := List (GPTriple G)
abbrev Input := List Bool
variable {G : Type} [Group G]

def evalTriple (x : Input) (t : GPTriple G) : G :=
  if x[t.i]! then t.g₁ else t.g₀

def evalProgram (x : Input) (P : GroupProgram G) : G :=
  (P.map (evalTriple x)).prod

--building some examples

def x : Input := [true, false, true, false,
true, true, true, false]


def triple₁ : GPTriple (Equiv.Perm (Fin 5)) where
  i := 0
  g₀ := Equiv.swap 0 1
  g₁ := Equiv.swap 2 3

def triple₂ : GPTriple (Equiv.Perm (Fin 5)) where
  i := 1
  g₀ := Equiv.swap 1 2
  g₁ := Equiv.swap 3 4

def triple₃ : GPTriple (Equiv.Perm (Fin 5)) where
  i := 2
  g₀ := Equiv.swap 0 4
  g₁ := Equiv.swap 1 3

def example_GP : GroupProgram (Equiv.Perm (Fin 5))
  := [triple₁, triple₂, triple₃]

#eval evalProgram x example_GP
