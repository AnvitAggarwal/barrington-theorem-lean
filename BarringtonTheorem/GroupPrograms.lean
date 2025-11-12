import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace BarringtonTheorem

variable [Group G]

@[grind]
structure GPTriple (G : Type) (n : ℕ) where
  i : Fin n
  g₀ : G
  g₁ : G

abbrev GroupProgram (G : Type) (n : ℕ) := List (GPTriple G n)
abbrev Input (n : ℕ):= Fin n → Bool
variable {G : Type} [Group G]

@[grind]
def evalTriple (x : Input n) (t : GPTriple G n) : G :=
  if x t.i then t.g₁ else t.g₀

@[grind]
def evalProgram (x : Input n) (P : GroupProgram G n) : G :=
  (P.map (evalTriple x)).prod

end BarringtonTheorem

open BarringtonTheorem

--building some examples

def ls : List Bool := [true, false, true, false,
true, true, true, false]

def x : Input 5:=
  fun i => if i < ls.length then ls[i]! else false

def triple₁ : GPTriple (Equiv.Perm (Fin 5)) 5 where
  i := 0
  g₀ := Equiv.swap 0 1
  g₁ := Equiv.swap 2 3

def triple₂ : GPTriple (Equiv.Perm (Fin 5)) 5 where
  i := 1
  g₀ := Equiv.swap 1 2
  g₁ := Equiv.swap 3 4

def triple₃ : GPTriple (Equiv.Perm (Fin 5)) 5 where
  i := 2
  g₀ := Equiv.swap 0 4
  g₁ := Equiv.swap 1 3

def example_GP : GroupProgram (Equiv.Perm (Fin 5)) 5
  := [triple₁, triple₂, triple₃]

#eval evalProgram x example_GP
#eval example_GP.length
