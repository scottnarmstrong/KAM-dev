/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Fast
public import KAM.Planetary.Preparation.SlowData
public import KAM.Planetary.Preparation.LogBounds

/-!
# Slow averaging: polynomial-in-`log` bounds of the radii (P11A-P7c, `stepP:p11:as-nr`, `as-b2`)

`s₁ ≥ c / (log 1/ε)^{τ+1}` and `s₂ ≥ c' / (log 1/ε)^{τ+1}`, and the eventual inequalities
`ε ℓ^m ≤ δ` obtained from `e4`.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

section Small

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

theorem min_div_le_min {A B P : ℝ} (hA : 0 < A) (hP : 1 ≤ P) :
    min A B / P ≤ min A (B / P) := by
  have hP0 : 0 < P := by linarith
  refine le_min ?_ ?_
  · calc min A B / P ≤ A / P := div_le_div_of_nonneg_right (min_le_left _ _) hP0.le
      _ ≤ A := div_le_self hA.le hP
  · exact div_le_div_of_nonneg_right (min_le_right _ _) hP0.le

/-- Eventually `ε ℓ^m ≤ δ`. -/
theorem eventually_eps_log_le {m δ : ℝ} (hm : 0 ≤ m) (hδ : 0 < δ) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), eps * Real.log (1 / eps) ^ m ≤ δ := by
  have he := e4 (a := (1 : ℝ)) (b := m) one_pos hm
  have := he.eventually (gt_mem_nhds hδ)
  filter_upwards [this] with eps h
  rw [Real.rpow_one] at h
  exact h.le

/-- Lower bound of `s₁`: `s₁ ≥ c / ℓ^{τ+1}`. -/
theorem p11s1_log_lower (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    min C.rC (C.gamma / (4 * C.L)) / ((6 / (Real.pi * C.sigma)) ^ (C.tau + 1) *
      Real.log (1 / eps) ^ (C.tau + 1)) ≤ p11s1 C eps := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  have hεM0 : 0 < eps * C.MF := mul_pos heps hM0
  have hK1 := p11K1_ge_one hC heps hεM
  have hℓΛ : Real.log (1 / (eps * C.MF)) ≤ Real.log (1 / eps) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul heps.ne' hM0.ne']
    have := Real.log_nonneg hMF
    linarith
  have hc30 : 0 < 6 / (Real.pi * C.sigma) := by positivity
  have hKΛ : p11K1 C eps ≤ 6 / (Real.pi * C.sigma) * Real.log (1 / eps) :=
    mul_le_mul_of_nonneg_left hℓΛ hc30.le
  have hP1 : 1 ≤ p11K1 C eps ^ (C.tau + 1) := Real.one_le_rpow hK1 (by linarith)
  have hL0 : 0 < C.L := by linarith
  have hA : 0 < min C.rC (C.gamma / (4 * C.L)) := lt_min hrC0 (by positivity)
  have h1 : min C.rC (C.gamma / (4 * C.L)) / p11K1 C eps ^ (C.tau + 1) ≤ p11s1 C eps := by
    have := min_div_le_min (B := C.gamma / (4 * C.L)) hrC0 hP1
    unfold p11s1
    rw [div_div] at this
    exact (div_le_div_of_nonneg_right (min_le_min_left _ (le_refl _)) (by linarith)).trans this
  refine le_trans ?_ h1
  have hl0 : 0 < Real.log (1 / eps) := by
    have := log_inv_ge_one heps (le_trans (by nlinarith) hεM)
    linarith
  rw [← Real.mul_rpow hc30.le hl0.le]
  exact div_le_div_of_nonneg_left hA.le (by positivity)
    (Real.rpow_le_rpow (by linarith) hKΛ (by linarith))

/-- Lower bound of `s₂`: `s₂ ≥ c / ℓ^{τ+1}`. -/
theorem p11s2_log_lower (hC : P11SecularSpec D C) {nu eps : ℝ} (hnu : 0 < nu) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)))
      (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1))) /
      Real.log (1 / eps) ^ (C.tau + 1) ≤ p11s2 C nu eps := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  have hl0 : 0 < Real.log (1 / eps) := by
    have := log_inv_ge_one heps (le_trans (by nlinarith) hεM)
    linarith
  have hL0 : 0 < C.L := by linarith
  have hc30 : 0 < 6 / (Real.pi * C.sigma) := by positivity
  have ha : 0 < 3 * nu / (Real.pi * (C.sigma / 12)) := by positivity
  have hq : 0 < Real.log (1 / eps) ^ (C.tau + 1) := Real.rpow_pos_of_pos hl0 _
  have hs1 := p11s1_log_lower hC heps hεM
  unfold p11s2
  have hK : p11K2 C nu eps = 3 * nu / (Real.pi * (C.sigma / 12)) * Real.log (1 / eps) := rfl
  have hX : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) := Real.rpow_pos_of_pos hc30 _
  have hY : 0 < (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1) := Real.rpow_pos_of_pos ha _
  refine le_min ?_ ?_
  · refine le_trans ?_ (div_le_div_of_nonneg_right hs1 (by norm_num : (0 : ℝ) ≤ 4))
    calc _ ≤ min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)) /
          Real.log (1 / eps) ^ (C.tau + 1) :=
          div_le_div_of_nonneg_right (min_le_left _ _) hq.le
      _ = _ := by field_simp
  · rw [hK, Real.mul_rpow ha.le hl0.le]
    calc _ ≤ C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1)) /
          Real.log (1 / eps) ^ (C.tau + 1) :=
          div_le_div_of_nonneg_right (min_le_right _ _) hq.le
      _ = _ := by field_simp

end Small

end KAM.Planetary

end
