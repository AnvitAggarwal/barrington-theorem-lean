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

-- building an example

def env : String → Bool :=
  fun name =>
  match name with
  | "x" => true
  | "y" => false
  | "z" => true
  | _   => false

def example_formula : Formula :=
  Formula.and (Formula.var "x") (Formula.not (Formula.var "y"))
#eval eval_formula example_formula env
