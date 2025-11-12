import BarringtonTheorem.GroupPrograms
import BarringtonTheorem.Formula
import Mathlib.Tactic

open BarringtonTheorem

section EvalProgram

variable {n m : ℕ}

attribute [grind =] List.prod_append

lemma evalProgram_join (P : GroupProgram (Equiv.Perm (Fin n)) m) (Q : GroupProgram (Equiv.Perm (Fin n)) m) :
  ∀ (x : Input m), evalProgram x (P ++ Q) = (evalProgram x P) * (evalProgram x Q) := by grind

lemma evalProgram_product (P : GroupProgram (Equiv.Perm (Fin n)) m) (α : Equiv.Perm (Fin n)) (fm : Fin m) :
  ∀ (x : Input m), evalProgram x (P ++ [{i := fm, g₀ := α, g₁ := α}])  = evalProgram x P * α := by
  grind [List.prod_cons, List.prod_nil, mul_one]

lemma evalProgram_conjugate
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (γ : Equiv.Perm (Fin n)) (x : Input m) :
    evalProgram x
      (P.map (λ t =>
        { i := t.i,
          g₀ := γ * t.g₀ * γ⁻¹,
          g₁ := γ * t.g₁ * γ⁻¹ })) =
      γ * evalProgram x P * γ⁻¹ := by
  induction P <;> simp_all [evalProgram, evalTriple]

end EvalProgram

section HelperInequalities

lemma two_mul_add_le_pow_succ_of_le_pow_pred
 (n m k d f1 f2 : ℕ) (hn : n ≤ 4 ^ (d - 1))
 (hm : m ≤ 4 ^ (d - 1)) (hk : k = 2 * (n + m))
 (h_one_add_max_le_d : 1 + max f1 f2 ≤ d) : k ≤ 4 ^ d := by
  have h2 : 2 * (n + m) ≤ 2 * (2 * 4 ^ (d - 1)) := by grind
  have a : (d - 1) + 1 = d := by grind
  rw [← Nat.mul_assoc 2 2 (4 ^ (d - 1)), mul_comm 4 (4 ^ (d - 1))] at h2
  simp_all only [← Nat.pow_succ, Nat.succ_eq_add_one] 

lemma succ_four_pow_le_four_pow_succ (d : ℕ) : 1 + 4 ^ d ≤ 4 ^ (d + 1) := by
  induction d <;> grind

lemma succ_le_four_pow_of_le_four_pow_pred (n m k : ℕ) (h_k_gt_one : 1 <= k) (h_n_eq_m_add_one : n = m + 1) (h_m_le_four_power_k_sub_one: m ≤ 4 ^ (k - 1)) :
n ≤ 4^k := by
  have h1 := succ_four_pow_le_four_pow_succ (k - 1)
  rw [Nat.sub_add_cancel] at h1 <;> grind

end HelperInequalities

section Computability

variable {m : ℕ}

@[grind]
def computes_with {G : Type} [Group G] (α : G)
    (P : GroupProgram G m) (f : Input m → Bool) : Prop :=
  ∀ (x : Input m), evalProgram x P = if f x then α else 1

end Computability

section PermLemmas

variable {n m : ℕ}

lemma computable_for_conj_cycles
    (α β : Equiv.Perm (Fin n))
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (f : Input m → Bool)
    (hα : Equiv.Perm.IsCycle α)
    (hβ : Equiv.Perm.IsCycle β)
    (hαβ : α.support.card = β.support.card)
    (hcomputes_with : computes_with α P f) :
    ∃ (Q : GroupProgram (Equiv.Perm (Fin n)) m),
      Q.length = P.length ∧ computes_with β Q f := by
  obtain ⟨γ, hγ⟩ := Equiv.Perm.IsCycle.isConj hα hβ hαβ
  let Q : GroupProgram (Equiv.Perm (Fin n)) m :=
    P.map (λ t =>
      { i := t.i,
        g₀ := γ * t.g₀ * γ⁻¹,
        g₁ := γ * t.g₁ * γ⁻¹ })
  use Q
  constructor
  · simp [Q, List.length_map]
  · intro x
    simp [Q]
    rw [evalProgram_conjugate P γ x]
    by_cases f x
    case pos hpos => grind [mul_inv_cancel_right, SemiconjBy]
    case neg hneg => grind [mul_one, mul_inv_cancel]

lemma product_cycles_conjugate_cycle :
    ∃ (α β : Equiv.Perm (Fin 5)),
      Equiv.Perm.IsCycle α ∧
      α.support.card = 5 ∧
      Equiv.Perm.IsCycle β ∧
      β.support.card = 5 ∧
      Equiv.Perm.IsCycle (α * β * α⁻¹ * β⁻¹) ∧
      (α * β * α⁻¹ * β⁻¹).support.card = 5 := by
  -- Define two explicit 5-cycles α = (0 1 2 3 4) and β = (0 2 4 3 1)
  let α : Equiv.Perm (Fin 5) :=
    (Equiv.swap 0 4) * (Equiv.swap 0 3) * (Equiv.swap 0 2) * (Equiv.swap 0 1)
  let β : Equiv.Perm (Fin 5) :=
    (Equiv.swap 0 1) * (Equiv.swap 0 3) * (Equiv.swap 0 4) *(Equiv.swap 0 2)
  -- The commutator of the two 5-cycles is equal to (0 3 2 4 1)
  have hαβ : α * β * α⁻¹ * β⁻¹ = (Equiv.swap 0 1) * (Equiv.swap 0 4) * (Equiv.swap 0 2) * (Equiv.swap 0 3) := by decide
  refine ⟨α, β, ?_, ?_, ?_, ?_, ?_, ?_⟩

  -- IsCycle α
  . use 0
    constructor
    . trivial -- α 0 ≠ 0
    -- ∀ y ∈ (Fin 5), SameCycle 0 y in α
    . intro y hy
      fin_cases y <;>
      [use 0; use 1; use 2; use 3; use 4] <;>
      trivial
  -- α.support.card = 5
  . decide

  -- IsCycle β
  . use 0
    constructor
    . trivial
  -- ∀ y ∈ (Fin 5), SameCycle 0 y in β
    . intro y hy
      fin_cases y
      . use 0; trivial -- (β ^ 0) 0 = 0
      . use 4; trivial -- (β ^ 4) 0 = 1
      . use 1; trivial -- (β ^ 1) 0 = 2
      . use 3; trivial -- (β ^ 3) 0 = 3
      . use 2; trivial -- (β ^ 2) 0 = 4
  -- β.support.card = 5
  . decide

  -- IsCycle (α * β * α⁻¹ * β⁻¹)
  . rw [hαβ]
    . use 0
      constructor
      . trivial
      -- ∀ y ∈ (Fin 5), SameCycle 0 y in (α * β * α⁻¹ * β⁻¹)
      . intro y hy;
        fin_cases y
        . use 0; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 0) 0 = 0
        . use 4; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 4) 0 = 1
        . use 2; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 2) 0 = 2
        . use 1; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 1) 0 = 3
        . use 3; trivial -- ((α * β * α⁻¹ β⁻¹) ^ 3) 0 = 4
  -- (α * β * α⁻¹ * β⁻¹).support.card = 5
  . decide

lemma and_computable
    (α β : Equiv.Perm (Fin n))
    (hαcycle : Equiv.Perm.IsCycle α)
    (hβcycle : Equiv.Perm.IsCycle β)
    (f : Input m → Bool)
    (g : Input m → Bool)
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (Q : GroupProgram (Equiv.Perm (Fin n)) m)
    (hαcomputes : computes_with α P f)
    (hβcomputes : computes_with β Q g) :
    ∃ (R : GroupProgram (Equiv.Perm (Fin n)) m),
      R.length = 2 * (P.length + Q.length) ∧
      computes_with (α * β * α⁻¹ * β⁻¹) R (λ x => f x ∧ g x) := by
  rcases computable_for_conj_cycles α α⁻¹ P f hαcycle (Equiv.Perm.IsCycle.inv hαcycle) (by simp) hαcomputes with ⟨R, hRLen, hRcomputes⟩
  rcases computable_for_conj_cycles β β⁻¹ Q g hβcycle (Equiv.Perm.IsCycle.inv hβcycle) (by simp) hβcomputes with ⟨S, hSLen, hScomputes⟩
  let T : (GroupProgram (Equiv.Perm (Fin n)) m) := P ++ Q ++ R ++ S
  use T
  constructor
  . simp[T]
    rw [hRLen, hSLen]
    rw [← add_assoc, ← Nat.two_mul]
  . rw [computes_with]
    intro x
    have hP := hαcomputes x
    have hQ := hβcomputes x
    have hR := hRcomputes x
    have hS := hScomputes x
    simp[T]
    rw [evalProgram_join, evalProgram_join, evalProgram_join]
    rw [computes_with] at hαcomputes
    rw [computes_with] at hβcomputes
    rw [computes_with] at hRcomputes
    rw [computes_with] at hScomputes
    by_cases f x
    case pos fpos =>
      by_cases g x
      case pos gpos =>
        simp [fpos, gpos]
        simp [fpos] at hP
        simp [fpos] at hR
        simp [gpos] at hQ
        simp [gpos] at hS
        rw [hP, hQ, hR, hS]
        rw [←mul_assoc, ←mul_assoc]
      case neg gneg =>
        simp_all [mul_inv_cancel, mul_one]
    case neg fneg =>
      by_cases g x
      case pos gpos =>
        simp [fneg, gpos]
        simp [fneg] at hP
        simp [fneg] at hR
        simp [gpos] at hQ
        simp [gpos] at hS
        rw [hP, hQ, hR, hS]
        rw [←mul_assoc, ←mul_assoc, one_mul, mul_one, mul_inv_cancel]
      case neg gneg =>
        simp [fneg, gneg]
        simp [fneg] at hP
        simp [fneg] at hR
        simp [gneg] at hQ
        simp [gneg] at hS
        rw [hP, hQ, hR, hS]
        rw [mul_one, mul_one, mul_one]

variable [hm : NeZero m]

lemma not_computable
    (α : Equiv.Perm (Fin n))
    (P : GroupProgram (Equiv.Perm (Fin n)) m)
    (f : Input m → Bool)
    (hα_cycle : Equiv.Perm.IsCycle α)
    (hαcomputes : computes_with α P f) :
    ∃ (Q : GroupProgram (Equiv.Perm (Fin n)) m),
      Q.length = P.length + 1 ∧ computes_with α Q (λ x => ¬ f x) := by
  rcases computable_for_conj_cycles α α⁻¹ P f hα_cycle (Equiv.Perm.IsCycle.inv hα_cycle) (by simp) hαcomputes with ⟨Q, hQLen, hQcomputes⟩
  let R : GroupProgram (Equiv.Perm (Fin n)) m := Q ++ [{i := Fin.ofNat m 0, g₀ := α, g₁ := α}]
  use R
  constructor
  . simp [R]
    exact hQLen
  . simp only [R, computes_with]
    intro x
    rw [(evalProgram_product Q α)]
    unfold computes_with at hQcomputes
    have h1 := hQcomputes x
    by_cases f x
    case pos hpos=>
      simp [hpos] at h1
      simp [hpos]
      rw [h1]
      exact inv_mul_cancel α
    case neg hneg =>
      simp [hneg] at h1
      simp [hneg]
      exact h1

end PermLemmas

section BarringtonTheorem

variable {n m : ℕ} [hm : NeZero m]

theorem barrington_theorem
    (f : Input m → Bool)
    (hfcomputed : computed_by_formula f d) :
    ∀ (α : Equiv.Perm (Fin 5)), Equiv.Perm.IsCycle α → α.support.card = 5 → ∃ (P : GroupProgram (Equiv.Perm (Fin 5)) m),
      P.length ≤ 4 ^ d ∧
      computes_with α P f := by
  obtain ⟨φ, hφd, hφf⟩ := hfcomputed
  induction φ generalizing f d

  case var a =>
    intro α hαcycle hαsupport
    simp [Formula.eval] at hφf
    let P : GroupProgram (Equiv.Perm (Fin 5)) m :=
      [{i := a, g₀ := 1, g₁ := α}]
    refine ⟨P, ?_, ?_⟩
    · exact Nat.one_le_pow d 4 (by linarith)
    · intro x; simp [P, evalProgram, evalTriple, hφf]

  case not F F_ih =>
    unfold Formula.depth at hφd
    simp [Formula.eval] at hφf
    have hF_eval_eq : ∀ (x : Input m), F.eval x = decide ¬f x = true := by
      simp [hφf]
    have ih := @F_ih (d - 1) (λ x => ¬ f x) (by grind) hF_eval_eq
    intro α hαcycle hαsupport
    rcases ih α hαcycle hαsupport with ⟨P, hPlen, hcomputes_withP⟩
    rcases not_computable α P (λ x => ¬ f x) hαcycle hcomputes_withP with
      ⟨Q, hQLen, hcomputes_withQ⟩
    use Q
    constructor
    · exact succ_le_four_pow_of_le_four_pow_pred Q.length P.length d (Nat.le_of_add_right_le hφd) hQLen hPlen
    · simp at hcomputes_withQ
      exact hcomputes_withQ

  case and F1 F2 hF1 hF2 =>
    let f1 : Input m → Bool := λ x => F1.eval x
    let f2 : Input m → Bool := λ x => F2.eval x
    unfold Formula.depth at hφd
    have hf1depth_le_d : F1.depth ≤ d - 1 := by grind
    have hf2depth_le_d : F2.depth ≤ d - 1 := by grind
    rcases product_cycles_conjugate_cycle with ⟨α, β, hαcycle, hαsupport, hβcycle, hβsupport, hαβConjProd, hαβConjProdSupport⟩
    rcases (hF1 f1 hf1depth_le_d (by simp [f1]) α) hαcycle hαsupport with ⟨P, hPLength, hcomputesf1⟩
    rcases (hF2 f2 hf2depth_le_d (by simp [f2]) β) hβcycle hβsupport with ⟨Q, hQLength, hcomputesf2⟩
    rcases and_computable α β hαcycle hβcycle f1 f2 P Q hcomputesf1 hcomputesf2 with ⟨R, hRLength, hComputes⟩
    have existsαP :
      ∃ (α : Equiv.Perm (Fin 5)),
      α.IsCycle ∧ α.support.card = 5 ∧ ∃ P,
      List.length P ≤ 4 ^ d ∧ computes_with α P f := by
      refine ⟨(α * β * α⁻¹ * β⁻¹), hαβConjProd, hαβConjProdSupport, ?_⟩
      . use R
        constructor
        · exact two_mul_add_le_pow_succ_of_le_pow_pred P.length Q.length R.length d F1.depth F2.depth hPLength hQLength hRLength hφd
        · rw [computes_with] at hComputes
          have f1_and_f2_eq_f : ∀ (x : Input m), (f1 x ∧ f2 x) = f x := by
            intro x
            rw [← hφf x]
            simp [f1, f2, Formula.eval]
          intro x
          simp [hComputes x, Bool.decide_congr (iff_of_eq (f1_and_f2_eq_f x))]
    intro γ hγcycle hγsupport
    rcases existsαP with ⟨δ, hδCycle, hδSupport, S, hSlen, hSComputes⟩
    rcases @computable_for_conj_cycles 5 m δ γ S f hδCycle hγcycle (by rw [hδSupport, hγsupport]) hSComputes with ⟨T, hTlen, hTcomputes⟩
    use T
    rw [hTlen]
    exact And.intro hSlen hTcomputes

end BarringtonTheorem
