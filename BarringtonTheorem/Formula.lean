import BarringtonTheorem.GroupPrograms
import Mathlib.Algebra.BigOperators.Fin

open BarringtonTheorem

class BoolBasis (b : Type) where
(arity : b → ℕ)
(eval (g : b) : (Fin (arity g) → Bool) → Bool)

inductive demorgan_basis where
| not : demorgan_basis
| and : demorgan_basis

instance : BoolBasis demorgan_basis where
  arity
    | demorgan_basis.not => 1
    | demorgan_basis.and => 2

  eval
    | demorgan_basis.not => fun xs => !(xs 0)
    | demorgan_basis.and => fun xs => xs 0 && xs 1

inductive Formula (n : ℕ) (b : Type) [BoolBasis b]: Type where
  | var : Fin n → Formula n b
  | cons (g : b) : (Fin (BoolBasis.arity g) → Formula n b) → Formula n b

def Formula.eval [BoolBasis b] : Formula n b → Input n → Bool
| Formula.var i, env => env i
| Formula.cons (g : b) f, env =>
  let xs : Fin (BoolBasis.arity g) → Bool :=
    fun i => Formula.eval (f i) env
  BoolBasis.eval g xs

open Finset

def Formula.size [BoolBasis b] : Formula n b → ℕ
| Formula.var _ => 1
| Formula.cons (g : b) f =>
  let fs : Fin (BoolBasis.arity g) → ℕ := fun i => Formula.size (f i)
  (univ : Finset (Fin (BoolBasis.arity g))).sum fs + 1

def Formula.depth [BoolBasis b] : Formula n b → ℕ
| Formula.var _ => 0
| Formula.cons (g : b) f =>
  let fd : Fin (BoolBasis.arity g) → ℕ := fun i => Formula.depth (f i)
  (univ: Finset (Fin (BoolBasis.arity g))).sup fd + 1

def computed_by_formula (b : Type) [BoolBasis b] (f : Input n → Bool) (d : ℕ) : Prop :=
  ∃ φ : Formula n b, Formula.depth φ ≤ d ∧ ∀ x : Input n, Formula.eval φ x = f x

-- building an example

def l : List Bool := [true, false, true, false,
true, true, true, false]
#eval l[2]!

def env1 : Fin 8 → Bool :=
  fun i => if i < l.length then l[i]! else false

def example_formula : Formula 8 demorgan_basis :=
  let fnot : Fin 1 → Formula 8 demorgan_basis :=
    fun
    | ⟨0, _⟩ => Formula.var 2

  let fand : Fin 2 → Formula 8 demorgan_basis :=
    fun
    | ⟨0, _⟩ => Formula.var 3
    | ⟨1, _⟩ => Formula.cons demorgan_basis.not fnot

  Formula.cons demorgan_basis.and fand

#eval Formula.eval example_formula env1
#eval Formula.size example_formula
#eval Formula.depth example_formula
