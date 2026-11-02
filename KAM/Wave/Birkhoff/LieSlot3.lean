/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieSlot2

/-!
# The slot recurrence for the Lie coefficients: the induction (blueprint-W `bpW:w3:lie-coeff`)

Package W3-FLOW, blueprint label `bpW:w3:lie-coeff` (audit finding F1).

`lieMb_slot`: `(k+1) Φ_{k+1}(v) = Σ_{i < 2k+1} Φ_k(contract_i v)` on all sequences `v`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E)

/-- Re-indexing of the sum over `antidiagonalTuple 3` shifting one coordinate. -/
theorem sum_antidiagonalTuple_succ (j : ℕ) (i : Fin 3) (G : (Fin 3 → ℕ) → E) :
    ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1), ((y i : ℕ) : ℂ) • G y =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j, (((x i : ℕ) : ℂ) + 1) •
        G (fun k => x k + if k = i then 1 else 0) := by
  have hf : ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1), ((y i : ℕ) : ℂ) • G y =
      ∑ y ∈ (Finset.Nat.antidiagonalTuple 3 (j + 1)).filter (fun y => y i ≠ 0),
        ((y i : ℕ) : ℂ) • G y := by
    refine (Finset.sum_filter_of_ne fun y _ h => ?_).symm
    intro h0
    apply h
    simp [h0]
  rw [hf]
  refine Finset.sum_nbij' (fun y k => y k - if k = i then 1 else 0)
    (fun x k => x k + if k = i then 1 else 0) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hy ⊢
    fin_cases i <;> simp at hy ⊢ <;> omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hx ⊢
    fin_cases i <;> simp <;> omega
  · intro y hy
    simp only [Finset.mem_filter] at hy
    funext k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [hk]
  · intro x hx
    funext k
    by_cases hk : k = i <;> simp [hk]
  · intro y hy
    simp only [Finset.mem_filter] at hy
    have : (fun k => (y k - if k = i then 1 else 0) + if k = i then 1 else 0) = y := by
      funext k
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [hk]
    rw [this]
    congr 2
    have h1 : y i - 1 + 1 = y i := by omega
    have h2 : ((y i : ℕ) : ℂ) = ((y i - 1 : ℕ) : ℂ) + 1 := by exact_mod_cast h1.symm
    simp [h2, add_comm]

/-- The induction hypothesis of the slot recurrence below index `j + 1`. -/
def LieSlotIH (j : ℕ) : Prop :=
  ∀ k' < j + 1, ∀ v : ℕ → E, ((k' : ℂ) + 1) • lieMb T (k' + 1) v =
    ∑ i ∈ Finset.range (2 * k' + 1), lieMb T k' (lieContract T i v)

/-- The contribution of a triple `(a, b, c)` to the contracted sum. -/
theorem lieSlot_term {j : ℕ} (ih : LieSlotIH T j) (v : ℕ → E) {a b c : ℕ} (h : a + b + c = j) :
    ∑ i ∈ Finset.range (2 * j + 3),
      T ![lieMb T a (lieContract T i v), lieMb T b (lieShift (2 * a + 1) (lieContract T i v)),
        lieMb T c (lieShift (2 * a + 2 * b + 2) (lieContract T i v))] =
      ((a : ℂ) + 1) • lieG T (a + 1) b c v + ((b : ℂ) + 1) • lieG T a (b + 1) c v +
        ((c : ℂ) + 1) • lieG T a b (c + 1) v := by
  have hr : 2 * j + 3 = (2 * a + 1) + ((2 * b + 1) + (2 * c + 1)) := by omega
  rw [hr, Finset.sum_range_add _ (2 * a + 1) ((2 * b + 1) + (2 * c + 1)),
    Finset.sum_range_add _ (2 * b + 1) (2 * c + 1)]
  have P1 : ∑ i ∈ Finset.range (2 * a + 1),
      T ![lieMb T a (lieContract T i v), lieMb T b (lieShift (2 * a + 1) (lieContract T i v)),
        lieMb T c (lieShift (2 * a + 2 * b + 2) (lieContract T i v))] =
      ((a : ℂ) + 1) • lieG T (a + 1) b c v := by
    rw [Finset.sum_congr rfl (g := fun i => T ![lieMb T a (lieContract T i v),
      lieMb T b (lieShift (2 * a + 1 + 2) v), lieMb T c (lieShift (2 * a + 2 * b + 2 + 2) v)])
      (fun i hi => by
        rw [Finset.mem_range] at hi
        rw [lieShift_contract_lt T v (show i < 2 * a + 1 by omega),
          lieShift_contract_lt T v (show i < 2 * a + 2 * b + 2 by omega)])]
    rw [T_sum0, ← ih a (by omega) v, T_smul0]
    unfold lieG
    have e1 : 2 * (a + 1) + 1 = 2 * a + 1 + 2 := by omega
    have e2 : 2 * (a + 1) + 2 * b + 2 = 2 * a + 2 * b + 2 + 2 := by omega
    rw [e1, e2]
  have P2 : ∑ i ∈ Finset.range (2 * b + 1),
      T ![lieMb T a (lieContract T (2 * a + 1 + i) v),
        lieMb T b (lieShift (2 * a + 1) (lieContract T (2 * a + 1 + i) v)),
        lieMb T c (lieShift (2 * a + 2 * b + 2) (lieContract T (2 * a + 1 + i) v))] =
      ((b : ℂ) + 1) • lieG T a (b + 1) c v := by
    rw [Finset.sum_congr rfl (g := fun i => T ![lieMb T a v,
      lieMb T b (lieContract T i (lieShift (2 * a + 1) v)),
      lieMb T c (lieShift (2 * a + 2 * b + 2 + 2) v)])
      (fun i hi => by
        rw [Finset.mem_range] at hi
        rw [lieShift_contract_ge T (2 * a + 1) i v,
          lieShift_contract_lt T v (show 2 * a + 1 + i < 2 * a + 2 * b + 2 by omega),
          lieMb_congr T a (lieContract T (2 * a + 1 + i) v) v (fun t ht =>
            lieContract_apply_lt T v (by omega))])]
    rw [T_sum1, ← ih b (by omega) (lieShift (2 * a + 1) v), T_smul1]
    unfold lieG
    have e2 : 2 * a + 2 * (b + 1) + 2 = 2 * a + 2 * b + 2 + 2 := by omega
    rw [e2]
  have P3 : ∑ i ∈ Finset.range (2 * c + 1),
      T ![lieMb T a (lieContract T (2 * a + 1 + (2 * b + 1 + i)) v),
        lieMb T b (lieShift (2 * a + 1) (lieContract T (2 * a + 1 + (2 * b + 1 + i)) v)),
        lieMb T c (lieShift (2 * a + 2 * b + 2)
          (lieContract T (2 * a + 1 + (2 * b + 1 + i)) v))] =
      ((c : ℂ) + 1) • lieG T a b (c + 1) v := by
    rw [Finset.sum_congr rfl (g := fun i => T ![lieMb T a v,
      lieMb T b (lieShift (2 * a + 1) v),
      lieMb T c (lieContract T i (lieShift (2 * a + 2 * b + 2) v))])
      (fun i hi => by
        rw [Finset.mem_range] at hi
        have e : 2 * a + 1 + (2 * b + 1 + i) = (2 * a + 2 * b + 2) + i := by omega
        rw [e, lieShift_contract_ge T (2 * a + 2 * b + 2) i v,
          lieMb_congr T a (lieContract T (2 * a + 2 * b + 2 + i) v) v (fun t ht =>
            lieContract_apply_lt T v (by omega)),
          lieMb_congr T b (lieShift (2 * a + 1) (lieContract T (2 * a + 2 * b + 2 + i) v))
            (lieShift (2 * a + 1) v) (fun t ht => by
              simp only [lieShift]
              exact lieContract_apply_lt T v (by omega))])]
    rw [T_sum2, ← ih c (by omega) (lieShift (2 * a + 2 * b + 2) v), T_smul2]
    unfold lieG
    rfl
  rw [P1, P2, P3, add_assoc]

/-- (`bpW:w3:lie-coeff`, slot recurrence) For every sequence `v`:
`(k+1) Φ_{k+1}(v) = Σ_{i < 2k+1} Φ_k(v¹, …, T(v^i, v^{i+1}, v^{i+2}), …)`. -/
theorem lieMb_slot (k : ℕ) (v : ℕ → E) :
    ((k : ℂ) + 1) • lieMb T (k + 1) v =
      ∑ i ∈ Finset.range (2 * k + 1), lieMb T k (lieContract T i v) := by
  induction k using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    cases k with
    | zero =>
      simp [lieMb_succ, lieContract, lieMb_zero, Finset.Nat.antidiagonalTuple_zero_right, lieShift]
    | succ j =>
      have ih' : LieSlotIH T j := fun k' hk' => ih k' (by omega)
      set Gy : (Fin 3 → ℕ) → E := fun y => lieG T (y 0) (y 1) (y 2) v with hGy
      have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have step1 : ((j : ℂ) + 1) • ∑ i ∈ Finset.range (2 * (j + 1) + 1),
          lieMb T (j + 1) (lieContract T i v) =
          ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 0 : ℕ) : ℂ) + 1) • lieG T (x 0 + 1) (x 1) (x 2) v +
          ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 1 : ℕ) : ℂ) + 1) • lieG T (x 0) (x 1 + 1) (x 2) v +
          ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 2 : ℕ) : ℂ) + 1) • lieG T (x 0) (x 1) (x 2 + 1) v := by
        have e1 : ∀ i, lieMb T (j + 1) (lieContract T i v) = ((1 : ℂ) / ((j : ℂ) + 1)) •
            ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
              T ![lieMb T (x 0) (lieContract T i v),
                lieMb T (x 1) (lieShift (2 * x 0 + 1) (lieContract T i v)),
                lieMb T (x 2) (lieShift (2 * x 0 + 2 * x 1 + 2) (lieContract T i v))] :=
          fun i => lieMb_succ T j _
        simp only [e1]
        rw [← Finset.smul_sum, smul_smul, mul_one_div_cancel hj1, one_smul, Finset.sum_comm,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
        simp only [Fin.sum_univ_three] at hx'
        have := lieSlot_term T ih' v hx'
        rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
        rw [this, add_assoc]
      have step2 : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 0 : ℕ) : ℂ) + 1) • lieG T (x 0 + 1) (x 1) (x 2) v +
          ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 1 : ℕ) : ℂ) + 1) • lieG T (x 0) (x 1 + 1) (x 2) v +
          ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 2 : ℕ) : ℂ) + 1) • lieG T (x 0) (x 1) (x 2 + 1) v =
          ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1), (((y 0 : ℕ) : ℂ) + (y 1 : ℕ) + (y 2 : ℕ)) •
            Gy y := by
        have s0 := sum_antidiagonalTuple_succ j 0 Gy
        have s1 := sum_antidiagonalTuple_succ j 1 Gy
        have s2 := sum_antidiagonalTuple_succ j 2 Gy
        have e0 : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 0 : ℕ) : ℂ) + 1) • lieG T (x 0 + 1) (x 1) (x 2) v =
            ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1), ((y 0 : ℕ) : ℂ) • Gy y := by
          rw [s0]; refine Finset.sum_congr rfl fun x _ => ?_; simp [hGy]
        have e1 : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 1 : ℕ) : ℂ) + 1) • lieG T (x 0) (x 1 + 1) (x 2) v =
            ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1), ((y 1 : ℕ) : ℂ) • Gy y := by
          rw [s1]; refine Finset.sum_congr rfl fun x _ => ?_; simp [hGy]
        have e2 : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 j,
            (((x 2 : ℕ) : ℂ) + 1) • lieG T (x 0) (x 1) (x 2 + 1) v =
            ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1), ((y 2 : ℕ) : ℂ) • Gy y := by
          rw [s2]; refine Finset.sum_congr rfl fun x _ => ?_; simp [hGy]
        rw [e0, e1, e2]
        simp only [add_smul, Finset.sum_add_distrib]
      have step3 : ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1),
          (((y 0 : ℕ) : ℂ) + (y 1 : ℕ) + (y 2 : ℕ)) • Gy y =
          ((j : ℂ) + 1) • ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1), Gy y := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        have hy' := Finset.Nat.mem_antidiagonalTuple.1 hy
        simp only [Fin.sum_univ_three] at hy'
        congr 1
        exact_mod_cast hy'
      have step4 : ((((j + 1 : ℕ) : ℂ)) + 1) • lieMb T (j + 1 + 1) v =
          ∑ y ∈ Finset.Nat.antidiagonalTuple 3 (j + 1), Gy y := by
        rw [lieMb_succ_G, smul_smul]
        have : ((((j + 1 : ℕ) : ℂ)) + 1) ≠ 0 := by
          rw [← Nat.cast_succ]; exact Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
        rw [mul_one_div_cancel this, one_smul]
      have hfin : ((j : ℂ) + 1) • ((((j + 1 : ℕ) : ℂ) + 1) • lieMb T (j + 1 + 1) v) =
          ((j : ℂ) + 1) • ∑ i ∈ Finset.range (2 * (j + 1) + 1),
            lieMb T (j + 1) (lieContract T i v) := by
        rw [step4, ← step3, ← step2, ← step1]
      have := smul_right_injective E hj1 hfin
      push_cast at this ⊢
      exact this

end KAM.Wave

end
