/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMap
public import KAM.Planetary.TwoScale.StepConst
public import KAM.Planetary.TwoScale.MeasureTorus

/-!
# Two-scale KAM: applicability of the measure helpers (design finding N2, package P23-21)

`actionsMeas_of_limit` and `torusMeas_of_limit` build the bundles `ActionsMeas`/`TorusMeas` from
the exact clause shapes of `two_scale_kam` for the limit action map `i` and the limit map `Φ`
(block displacements, defect Lipschitz constants, rescaled displacement of `Φ`), using only
`KamHyp`. `ko_eq` identifies `K_Ω = ⋃ ω ∈ Ω, range (K ω)` with `Φ(ℝⁿ × D_*)` from the clause
`I₀ : Ω → D₀`. `meas_torus_final` is the resulting clause of `two_scale_kam`, with exact constant
`complementConstant`. `meas_of_iterative` is the joint check: on the witnesses of one application
of `iterative`, `limit_actions_of_steps` and `limit_phi_real_of_steps` feed these constructors.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology MeasureTheory

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

theorem KamHyp.kam_small_n (H : KamHyp D sbar p h f) :
    8192 * ((a + b : ℕ) : ℝ) * eHat p < 1 := by
  have h0 := H.eHat_nonneg
  have hk : 2 ^ 13 * ((a + b : ℕ) : ℝ) ≤ kamConstant (a + b) p.τ := le_max_left _ _
  have := H.small
  nlinarith [mul_le_mul_of_nonneg_right hk h0]

theorem KamHyp.mbar_div_le (H : KamHyp D sbar p h f) :
    p.Mbar₁ / p.Mbar ≤ 1 ∧ p.Mbar₂ / p.Mbar ≤ 1 ∧ p.Mhat / p.M ≤ 1 := by
  have hp := H.positive
  have hn := H.normalized
  exact ⟨(div_le_one hp.2.2.2.2.2.2.1).2 hn.2.1, (div_le_one hp.2.2.2.2.2.2.1).2 hn.2.2,
    (div_le_one hp.2.2.2.2.1).2 hn.1⟩

/-- `ActionsMeas` for the limit action map, from the clauses of `two_scale_kam`. -/
theorem actionsMeas_of_limit (H : KamHyp D sbar p h f) {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)}
    (hblk : ∀ I ∈ dioBase D h p,
      ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p)
    (hlip : ∀ I ∈ dioBase D h p, ∀ J ∈ dioBase D h p,
      ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖) :
    ActionsMeas D (dioBase D h p) i (eHat p) (rhoHat p) := by
  have he := H.eHat_nonneg
  have hR := H.R_pos
  obtain ⟨m1, m2, -⟩ := H.mbar_div_le
  have hk := H.kam_small_n
  have hERnn : 0 ≤ eHat p * rhoHat p := by positivity
  refine ⟨inter_subset_left, he, mul_pos (eHat_pos H) hR, fun I hI => ?_, fun I hI J hJ => ?_, ?_⟩
  · obtain ⟨b1, b2⟩ := hblk I hI
    refine norm_le_of_blocks (by positivity) (b1.trans ?_) (b2.trans ?_)
    · calc _ = (p.Mbar₁ / p.Mbar) * (20 * (eHat p * rhoHat p)) := by ring
        _ ≤ 1 * (20 * (eHat p * rhoHat p)) := by gcongr
        _ = _ := by ring
    · calc _ = (p.Mbar₂ / p.Mbar) * (20 * (eHat p * rhoHat p)) := by ring
        _ ≤ 1 * (20 * (eHat p * rhoHat p)) := by gcongr
        _ = _ := by ring
  · have := hlip I hI J hJ
    rw [Nat.cast_add]; exact this
  · rw [Nat.cast_add] at hk ⊢
    nlinarith

end KAM.Planetary

end
