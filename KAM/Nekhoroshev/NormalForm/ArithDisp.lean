/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.ArithInduct
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: numerics, displacement and the radii

`nf-disp` (the constants `1.17`, `8 + 32/(36 ln 2) ≤ 10`) and the closed forms of the schedule.
Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8.
-/

@[expose] public noncomputable section

namespace KAM.NormalForm

section Numerics

variable {α p K r s ε : ℝ}


/-- (c), action direction, Case A: `∑ᵢ q Bᵢ/(e ᾱ σᵢ) ≤ qKε/α`. -/
theorem disp_I {N : ℕ} (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hs : 0 < s) (hε0 : 0 ≤ ε)
    {ε₁ : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε / 4) (hii : 6 ≤ 2 * Real.pi * K * s)
    (h8 : 8 * (N : ℝ) ≤ 2 * Real.pi * K * s) :
    ∑ i ∈ Finset.range (N + 1),
        conjExp p * nfB ε₁ ε i / (Real.exp 1 * (2 * Real.pi * α) * nfSig s N i) ≤
      conjExp p * K * ε / α := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have he := Real.exp_pos 1
  have he2 := exp_one_gt
  set W := conjExp p * ε / (Real.exp 1 * α) with hW
  have hW0 : 0 ≤ W := by positivity
  have hT0 : conjExp p * nfB ε₁ ε 0 / (Real.exp 1 * (2 * Real.pi * α) * nfSig s N 0) ≤ K * W := by
    have e : conjExp p * nfB ε₁ ε 0 / (Real.exp 1 * (2 * Real.pi * α) * nfSig s N 0) =
        6 / (2 * Real.pi * s) * W := by
      simp only [nfB, nfSig, ite_true, hW]
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hW0
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hKW : 0 ≤ K * W := by positivity
  have hfin : 2 * (K * W) ≤ conjExp p * K * ε / α := by
    have : conjExp p * K * ε / α = K * W * Real.exp 1 := by
      rw [hW]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left he2.le hKW |>.trans_eq' (by ring)
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [zero_add, Finset.sum_range_one]
    linarith
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Finset.sum_range_succ']
    set C := conjExp p * ε₁ / (Real.exp 1 * (2 * Real.pi * α) * (s / (4 * N))) with hC
    have hC0 : 0 ≤ C := by positivity
    have hterm : ∀ i ∈ Finset.range N,
        conjExp p * nfB ε₁ ε (i + 1) / (Real.exp 1 * (2 * Real.pi * α) * nfSig s N (i + 1)) =
          C * (1 / 4 ^ i) := by
      intro i _
      simp only [nfB, nfSig, hC, Nat.succ_ne_zero, ite_false]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsum := mul_le_mul_of_nonneg_left (sum_inv4_le N) hC0
    have hC1 : C * (4 / 3) ≤ K * W / 6 := by
      have e : C = 4 * N * conjExp p * ε₁ / (Real.exp 1 * (2 * Real.pi * α) * s) := by
        rw [hC]; field_simp
      have h1 : C ≤ N * conjExp p * ε / (Real.exp 1 * (2 * Real.pi * α) * s) := by
        rw [e]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ (N : ℝ) * conjExp p)
        linarith
      have h2 : N * conjExp p * ε / (Real.exp 1 * (2 * Real.pi * α) * s) ≤ K * W / 8 := by
        rw [div_le_iff₀ (by positivity)]
        have e2 : K * W / 8 * (Real.exp 1 * (2 * Real.pi * α) * s) =
            conjExp p * ε * (2 * Real.pi * K * s) / 8 := by
          rw [hW]; field_simp
        rw [e2]
        have := mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ conjExp p * ε)
        linarith
      have := mul_le_mul_of_nonneg_right (h1.trans h2) (by norm_num : (0 : ℝ) ≤ 4 / 3)
      linarith
    linarith

/-- (c), angle direction, Case A: `∑ᵢ q Bᵢ/(ᾱ ρᵢ) ≤ 10 q ε/(ᾱ r)`. -/
theorem disp_theta {N : ℕ} (hp : 1 < p) (hα : 0 < α) (_hK : 0 < K) (hr : 0 < r) (_hs : 0 < s)
    (hε0 : 0 ≤ ε) {ε₁ : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε / (2 * Real.pi * K * s))
    (hii : 6 ≤ 2 * Real.pi * K * s) (h8 : 8 * (N : ℝ) ≤ 2 * Real.pi * K * s) :
    ∑ i ∈ Finset.range (N + 1),
        conjExp p * nfB ε₁ ε i / (2 * Real.pi * α * nfRho r N i) ≤
      10 * conjExp p * ε / (2 * Real.pi * α * r) := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have hκ : 0 < 2 * Real.pi * K * s := by linarith
  set V := conjExp p * ε / (2 * Real.pi * α * r) with hV
  have hV0 : 0 ≤ V := by positivity
  have hfin : 10 * conjExp p * ε / (2 * Real.pi * α * r) = 10 * V := by rw [hV]; ring
  have hT0 : conjExp p * nfB ε₁ ε 0 / (2 * Real.pi * α * nfRho r N 0) = 8 * V := by
    simp only [nfB, nfRho, ite_true, hV]
    field_simp
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [zero_add, Finset.sum_range_one]
    rw [hT0, hfin]
    linarith
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Finset.sum_range_succ']
    set C := conjExp p * ε₁ / (2 * Real.pi * α * (r / (8 * N))) with hC
    have hC0 : 0 ≤ C := by positivity
    have hterm : ∀ i ∈ Finset.range N,
        conjExp p * nfB ε₁ ε (i + 1) / (2 * Real.pi * α * nfRho r N (i + 1)) =
          C * (1 / 4 ^ i) := by
      intro i _
      simp only [nfB, nfRho, hC, Nat.succ_ne_zero, ite_false]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsum := mul_le_mul_of_nonneg_left (sum_inv4_le N) hC0
    have hC1 : C ≤ V := by
      have e : C = 8 * N * conjExp p * ε₁ / (2 * Real.pi * α * r) := by
        rw [hC]; field_simp
      rw [e]
      have h1 : 8 * N * conjExp p * ε₁ ≤ 8 * N * conjExp p * (ε / (2 * Real.pi * K * s)) :=
        mul_le_mul_of_nonneg_left hε₁ (by positivity)
      have h2 : 8 * N * conjExp p * (ε / (2 * Real.pi * K * s)) ≤ conjExp p * ε := by
        have e3 : 8 * N * conjExp p * (ε / (2 * Real.pi * K * s)) =
            conjExp p * ε * (8 * N / (2 * Real.pi * K * s)) := by ring
        rw [e3]
        have : 8 * (N : ℝ) / (2 * Real.pi * K * s) ≤ 1 := by
          rw [div_le_one hκ]; exact h8
        calc conjExp p * ε * (8 * N / (2 * Real.pi * K * s)) ≤ conjExp p * ε * 1 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = conjExp p * ε := mul_one _
      rw [hV]
      exact div_le_div_of_nonneg_right (h1.trans h2) (by positivity)
    rw [hT0, hfin]
    have := mul_le_mul_of_nonneg_right hC1 (by norm_num : (0 : ℝ) ≤ 4 / 3)
    linarith

/-- Case B displacement: `qε/(e ᾱ (s/3)) ≤ qKε/α` and `qε/(ᾱ r/4) ≤ 10 qε/(ᾱ r)`. -/
theorem disp_B (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r) (hs : 0 < s) (hε0 : 0 ≤ ε)
    (hii : 6 ≤ 2 * Real.pi * K * s) :
    conjExp p * ε / (Real.exp 1 * (2 * Real.pi * α) * (s / 3)) ≤ conjExp p * K * ε / α ∧
      conjExp p * ε / (2 * Real.pi * α * (r / 4)) ≤ 10 * conjExp p * ε / (2 * Real.pi * α * r) := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have he := Real.exp_pos 1
  have he2 := exp_one_gt
  constructor
  · have e : conjExp p * ε / (Real.exp 1 * (2 * Real.pi * α) * (s / 3)) =
        3 / (2 * Real.pi * s) * (conjExp p * ε / (Real.exp 1 * α)) := by
      field_simp
    rw [e]
    have h1 : 3 / (2 * Real.pi * s) ≤ K := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h2 : conjExp p * ε / (Real.exp 1 * α) ≤ conjExp p * ε / α := by
      refine div_le_div_of_nonneg_left (by positivity) hα ?_
      have := mul_le_mul_of_nonneg_right he2.le hα.le
      linarith
    calc 3 / (2 * Real.pi * s) * (conjExp p * ε / (Real.exp 1 * α))
        ≤ K * (conjExp p * ε / α) :=
          mul_le_mul h1 h2 (by positivity) hK.le
      _ = conjExp p * K * ε / α := by ring
  · have e : conjExp p * ε / (2 * Real.pi * α * (r / 4)) =
        4 * (conjExp p * ε / (2 * Real.pi * α * r)) := by
      field_simp
    rw [e]
    have : 0 ≤ conjExp p * ε / (2 * Real.pi * α * r) := by positivity
    have e2 : 10 * conjExp p * ε / (2 * Real.pi * α * r) =
        10 * (conjExp p * ε / (2 * Real.pi * α * r)) := by ring
    rw [e2]
    linarith

/-! ### The radii -/

theorem nfR_succ_closed (r : ℝ) (N j : ℕ) :
    nfR r N (j + 1) = 3 * r / 4 - 2 * j * (r / (8 * N)) := by
  induction j with
  | zero => simp [nfR, nfRho]; ring
  | succ j ih =>
    rw [nfR, ih]
    simp only [nfRho, Nat.succ_ne_zero, ite_false]
    push_cast
    ring

theorem nfS_succ_closed (s : ℝ) (N j : ℕ) :
    nfS s N (j + 1) = 2 * s / 3 - 2 * j * (s / (4 * N)) := by
  induction j with
  | zero => simp [nfS, nfSig]; ring
  | succ j ih =>
    rw [nfS, ih]
    simp only [nfSig, Nat.succ_ne_zero, ite_false]
    push_cast
    ring

/-- `r_{N+1} = r/2`. -/
theorem nfR_final {N : ℕ} (hN : 1 ≤ N) (r : ℝ) : nfR r N (N + 1) = r / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [nfR_succ_closed]
  field_simp
  ring

/-- `s_{N+1} = s/6`. -/
theorem nfS_final {N : ℕ} (hN : 1 ≤ N) (s : ℝ) : nfS s N (N + 1) = s / 6 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [nfS_succ_closed]
  field_simp
  ring


/-! ### Positivity and monotonicity of the schedule -/

theorem nfRho_nonneg (hr : 0 ≤ r) (N i : ℕ) : 0 ≤ nfRho r N i := by
  unfold nfRho
  split_ifs <;> positivity

theorem nfSig_nonneg (hs : 0 ≤ s) (N i : ℕ) : 0 ≤ nfSig s N i := by
  unfold nfSig
  split_ifs <;> positivity

theorem nfRho_ne_zero {r : ℝ} {N i : ℕ} (hi : i ≠ 0) : nfRho r N i = r / (8 * N) := by
  simp [nfRho, hi]

theorem nfSig_ne_zero {s : ℝ} {N i : ℕ} (hi : i ≠ 0) : nfSig s N i = s / (4 * N) := by
  simp [nfSig, hi]

theorem nfRho_pos {N i : ℕ} (hr : 0 < r) (hi : i ≤ N) : 0 < nfRho r N i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [nfRho]; positivity
  · have hN : (0 : ℝ) < N := by exact_mod_cast (h.trans_le hi)
    rw [nfRho_ne_zero h.ne']
    positivity

theorem nfSig_pos {N i : ℕ} (hs : 0 < s) (hi : i ≤ N) : 0 < nfSig s N i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [nfSig]; positivity
  · have hN : (0 : ℝ) < N := by exact_mod_cast (h.trans_le hi)
    rw [nfSig_ne_zero h.ne']
    positivity

theorem nfR_anti (hr : 0 ≤ r) (N : ℕ) : Antitone (nfR r N) := by
  refine antitone_nat_of_succ_le fun i => ?_
  show nfR r N i - 2 * nfRho r N i ≤ nfR r N i
  have := nfRho_nonneg hr N i
  linarith

theorem nfS_anti (hs : 0 ≤ s) (N : ℕ) : Antitone (nfS s N) := by
  refine antitone_nat_of_succ_le fun i => ?_
  show nfS s N i - 2 * nfSig s N i ≤ nfS s N i
  have := nfSig_nonneg hs N i
  linarith

theorem nfR_le_three (hr : 0 ≤ r) {N i : ℕ} (hi : 1 ≤ i) : nfR r N i ≤ 3 * r / 4 := by
  have h1 : nfR r N i ≤ nfR r N 1 := nfR_anti hr N hi
  have : nfR r N 1 = 3 * r / 4 := by simp [nfR, nfRho]; ring
  linarith

theorem nfS_le_two (hs : 0 ≤ s) {N i : ℕ} (hi : 1 ≤ i) : nfS s N i ≤ 2 * s / 3 := by
  have h1 : nfS s N i ≤ nfS s N 1 := nfS_anti hs N hi
  have : nfS s N 1 = 2 * s / 3 := by simp [nfS, nfSig]; ring
  linarith

theorem nfR_gt_two_rho (hr : 0 < r) {N i : ℕ} (hi : i ≤ N) : 2 * nfRho r N i < nfR r N i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [nfR, nfRho]; linarith
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hN : (0 : ℝ) < N := by exact_mod_cast (h.trans_le hi)
    have hj : (j : ℝ) + 1 ≤ N := by exact_mod_cast hi
    rw [nfR_succ_closed, nfRho_ne_zero (Nat.succ_ne_zero j)]
    set ρ := r / (8 * (N : ℝ)) with hρ
    have hρ0 : 0 < ρ := by positivity
    have key : 3 * r / 4 = 6 * N * ρ := by rw [hρ]; field_simp; ring
    rw [key]
    have h1 := mul_le_mul_of_nonneg_right hj hρ0.le
    have h2 : 0 < (N : ℝ) * ρ := by positivity
    linarith

theorem nfS_gt_two_sig (hs : 0 < s) {N i : ℕ} (hi : i ≤ N) : 2 * nfSig s N i < nfS s N i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [nfS, nfSig]; linarith
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hN : (0 : ℝ) < N := by exact_mod_cast (h.trans_le hi)
    have hj : (j : ℝ) + 1 ≤ N := by exact_mod_cast hi
    rw [nfS_succ_closed, nfSig_ne_zero (Nat.succ_ne_zero j)]
    set σ := s / (4 * (N : ℝ)) with hσ
    have hσ0 : 0 < σ := by positivity
    have key : 2 * s / 3 = 8 / 3 * N * σ := by rw [hσ]; field_simp; ring
    rw [key]
    have h1 := mul_le_mul_of_nonneg_right hj hσ0.le
    have h2 : 0 < (N : ℝ) * σ := by positivity
    linarith

theorem nfR_half_le (hr : 0 < r) (N : ℕ) : r / 2 ≤ nfR r N (N + 1) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [nfR, nfRho]; linarith
  · exact (nfR_final h r).ge

theorem nfS_sixth_le (hs : 0 < s) (N : ℕ) : s / 6 ≤ nfS s N (N + 1) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [nfS, nfSig]; linarith
  · exact (nfS_final h s).ge

/-- `e^{-2πKσ} ≤ 1/8` for `σ = s/(4N)` and `N · 12 ln 2 ≤ κ`. -/
theorem exp_sigma_le {N : ℕ} (hN : 1 ≤ N)
    (hNle : (N : ℝ) * (12 * Real.log 2) ≤ 2 * Real.pi * K * s) :
    Real.exp (-(2 * Real.pi * K * (s / (4 * N)))) ≤ 1 / 8 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : Real.exp (-(3 * Real.log 2)) = 1 / 8 := by
    rw [Real.exp_neg, show 3 * Real.log 2 = Real.log 2 + Real.log 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_add, Real.exp_log two_pos]
    norm_num
  rw [← e]
  refine Real.exp_le_exp.mpr ?_
  have : 3 * Real.log 2 ≤ 2 * Real.pi * K * (s / (4 * N)) := by
    rw [show 2 * Real.pi * K * (s / (4 * N)) = 2 * Real.pi * K * s / (4 * N) by ring,
      le_div_iff₀ (by positivity)]
    linarith
  linarith

end Numerics

end KAM.NormalForm

end
