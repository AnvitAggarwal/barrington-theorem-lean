import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic

#print Group
#check Group Nat
#check Fin 5
#check Equiv.Perm
#print Equiv.Perm

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

def x : Input := {true, false, true, false, true, true, true, false}

def five_cycle₁ : Fin 5 → Fin 5 :=
  fun n =>
    match n with
    |0 => 4
    |1 => 3
    |2 => 1
    |3 => 0
    |4 => 2

def five_cycle₂ : Fin 5 → Fin 5 :=
  fun n =>
    match n with
    |0 => 2
    |1 => 0
    |2 => 3
    |3 => 4
    |4 => 1

def five_cycle₃ : Fin 5 → Fin 5 :=
  fun n =>
    match n with
    |0 => 3
    |1 => 4
    |2 => 0
    |3 => 1
    |4 => 2

def five_cycle₄ : Fin 5 → Fin 5 :=
  fun n =>
    match n with
    |0 => 1
    |1 => 2
    |2 => 3
    |3 => 4
    |4 => 0

def triple₁ : GPTriple (Equiv.Perm (Fin 5)) where
  i := 0
  g₀ := Perm.cycle [0,1,2]
