import Mathlib.Data.Nat.Basic

#check String

def s : String := "Barrington"
#check s
#eval s

inductive Formula : Type where
|var : String → Formula
|not : Formula → Formula
|and : Formula → Formula → Formula

def eval_formula : Formula → (String → Bool) → Bool
| Formula.var name, env => env name
| Formula.not f, env => not (eval_formula f env)
| Formula.and f1 f2, env => (eval_formula f1 env) && (eval_formula f2 env)

def sizeFormula : Formula → Nat
| Formula.var _ => 1
| Formula.not f => 1 + sizeFormula f
| Formula.and f1 f2 => 1 + sizeFormula f1 + sizeFormula f2

def depthFormula : Formula → Nat
| Formula.var _ => 0
| Formula.not f => 1 + depthFormula f
| Formula.and f1 f2 => 1 + Nat.max (depthFormula f1) (depthFormula f2)

-- building an example

def env1 : String → Bool :=
  fun name =>
  match name with
  | "x" => true
  | "y" => false
  | "z" => true
  | _   => false

def example_formula : Formula :=
  Formula.and (Formula.var "x") (Formula.not (Formula.var "y"))
#eval eval_formula example_formula env1
#eval sizeFormula example_formula
#eval depthFormula example_formula
