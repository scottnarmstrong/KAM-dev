/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedBasic

/-!
# Smallness bridge for the prepared assembly (P11A-P8e)

The signed data `p11FastData D eps`, `p11SlowData D nu eps` satisfy their specifications for
small `eps`, together with the numeric smallness conditions of the prepared steps
(`eps MF ≤ e⁻¹`, `3 π eps ≤ π rz²/16`, `5 eps ≤ s₂`, `eps < 1`), packaged as one existence
statement `p11_prep_small`, and the eventual bound `M eps ℓ^q ≤ 1`.
-/

@[expose] public noncomputable section
open Set Filter
namespace KAM.Planetary

section Small

variable {n : ℕ}

/-- `5 ε ≤ s₂` for small `ε`. -/
theorem p11_prep_five_eventually {D : P11Physical n} {C : P11SecularData n}
    (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), 0 < eps → eps * C.MF ≤ Real.exp (-1) →
      5 * eps ≤ p11s2 C nu eps := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hπ := Real.pi_pos
  have hL0 : 0 < C.L := by linarith
  have hs1c0 : 0 < min C.rC (C.gamma / (4 * C.L)) := lt_min hrC0 (by positivity)
  have hc3p : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hap : 0 < (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by have : 0 < nu := by linarith
                             positivity) _
  have hcs20 : 0 < min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^
      (C.tau + 1))) (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^
      (C.tau + 1))) := lt_min (by positivity) (by positivity)
  filter_upwards [eventually_eps_log_le (m := C.tau + 1) (by linarith)
    (div_pos hcs20 (by norm_num : (0 : ℝ) < 5))] with eps h1 heps hεM
  have hs2 := p11s2_log_lower hC (nu := nu) (by linarith) heps hεM
  have hq : 0 < Real.log (1 / eps) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by have := slow_log_ge_one hC heps hεM; linarith) _
  refine le_trans ?_ hs2
  rw [le_div_iff₀ hq]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 5)] at h1
  linarith

/-- The signed data satisfy their specifications, and the numeric smallness conditions of the
prepared steps hold, for all small `eps`. -/
theorem p11_prep_small (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ e0 →
      eps * (p11SecularData D).MF ≤ Real.exp (-1) ∧
      3 * Real.pi * eps ≤ Real.pi * (p11SecularData D).rz ^ 2 / 16 ∧
      5 * eps ≤ p11s2 (p11SecularData D) nu eps ∧
      P11FastSpec (p11SecularData D) eps (p11FastData D eps) ∧
      P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps) ∧
      1 ≤ p11SlowConstant D nu := by
  have hC : P11SecularSpec D (p11SecularData D) := (holo_chart D).choose_spec.1
  obtain ⟨-, -, -, -, -, -, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨eps1, h1pos, -, hfast⟩ := avg_fast D
  obtain ⟨h2pos, -, hc21, hslow⟩ := (avg_slow D hnu).choose_spec.choose_spec
  have hc2 : p11SlowConstant D nu = (avg_slow D hnu).choose_spec.choose := by
    unfold p11SlowConstant; rw [dif_pos hnu]
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (p11_prep_five_eventually hC hnu)
  have hM0 : 0 < (p11SecularData D).MF := by linarith
  have hrz2 : 0 < (p11SecularData D).rz ^ 2 := by positivity
  refine ⟨min (u / 2) (min eps1 (min (avg_slow D hnu).choose
    (min (Real.exp (-1) / (p11SecularData D).MF) (min ((p11SecularData D).rz ^ 2 / 48)
      (1 / 2))))),
    lt_min (by simpa using hu) (lt_min h1pos (lt_min h2pos (lt_min (by positivity)
      (lt_min (by positivity) (by norm_num))))),
    lt_of_le_of_lt (min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
      (min_le_of_right_le (min_le_right _ _))))) (by norm_num), fun eps heps hle => ?_⟩
  have hle1 := hle.trans (min_le_left _ _)
  have hle2 := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle3 := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hle4 := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hle5 := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hεM : eps * (p11SecularData D).MF ≤ Real.exp (-1) := (le_div_iff₀ hM0).1 hle4
  have hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps) := by
    have h := (hfast eps heps hle2).2
    unfold p11FastData
    rw [dif_pos h]
    exact h.choose_spec
  have hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps) := by
    have h : ∃ A, P11SlowSpec D nu eps (p11SlowConstant D nu) A := by
      rw [hc2]; exact hslow eps heps hle3
    unfold p11SlowData
    rw [dif_pos h]
    exact h.choose_spec
  refine ⟨hεM, ?_, hsub ⟨heps, by linarith⟩ heps hεM, hF, hS, by rw [hc2]; exact hc21⟩
  have : 3 * eps ≤ (p11SecularData D).rz ^ 2 / 16 := by linarith
  nlinarith [Real.pi_pos]

/-- Eventually `M eps ℓ^q ≤ 1`. -/
theorem p11_prep_eventually_le {M q : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q) :
    ∃ e : ℝ, 0 < e ∧ ∀ eps : ℝ, 0 < eps → eps ≤ e → M * (eps * Real.log (1 / eps) ^ q) ≤ 1 := by
  have h := eventually_eps_log_le (m := q) hq (show 0 < 1 / (M + 1) by positivity)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 h
  refine ⟨min (u / 2) (1 / 2), lt_min (by simpa using hu) (by norm_num), fun eps heps hle => ?_⟩
  have hu2 := hle.trans (min_le_left _ _)
  have h12 := hle.trans (min_le_right _ _)
  have h1 : eps * Real.log (1 / eps) ^ q ≤ 1 / (M + 1) := hsub ⟨heps, by linarith⟩
  have hl : 0 ≤ Real.log (1 / eps) := Real.log_nonneg (by rw [le_div_iff₀ heps]; linarith)
  have hX : 0 ≤ eps * Real.log (1 / eps) ^ q := mul_nonneg heps.le (Real.rpow_nonneg hl q)
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

end Small

end KAM.Planetary

end
