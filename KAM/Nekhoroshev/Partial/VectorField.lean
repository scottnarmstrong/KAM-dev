/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Bracket
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The scaled norm and the size of the weighted field (`bpN:p11:scaled`, `bpN:p11:vf`)

`scaled ρ σ z = max (‖z.1‖/σ) (‖z.2‖/ρ)`, the norm `ν_{ρ,σ}` of the source on the extended
coordinates, and `vf`: on `𝒟_{R-ρ,s-σ}` the field `X^c_φ = wfield c φ` has `ν_{ρ,σ}` size at most
`|φ|_{R,s}/(ρσ)` and its slow part has size at most `c|φ|_{R,s}/ρ` (Part 11, package N11-C).
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

def scaled (ρ σ : ℝ) (z : EC n k) : ℝ := max (‖z.1‖/σ) (‖z.2‖/ρ)

theorem vf (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ U : ℝ} {φ : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hSL : slowLoss b.c ρ σ k) (hU : 0 ≤ U)
    (hφ : InClass b.base R s φ) (hb : WBound b.base R s φ U) :
    ∀ z ∈ Dom n b.base (R-ρ) (s-σ), scaled ρ σ (wfield b.c φ z) ≤ U/(ρ*σ) ∧
      ‖slowPair (wfield b.c φ z)‖ ≤ b.c*U/ρ := by
  intro z hz
  have hc : 0 ≤ b.c := div_nonneg (by positivity) (sq_nonneg _)
  have hcσ : b.c * σ ≤ ρ := by
    unfold slowLoss at hSL
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonneg hc hσ.le]
  have hcl := cauchy_loss hφ hb hρ hρR hσ hσs
  have hφθ : ∀ j, InClass b.base R (s - σ) (dtheta j φ) := fun j =>
    inClass_fderiv_apply ⟨hφ.differentiableOn.mono (Dom_mono le_rfl (by linarith)),
      fun l w hw => hφ.periodic l w (Dom_mono le_rfl (by linarith) hw)⟩ (Pi.single j 1, 0)
  have hφI : ∀ i, InClass b.base (R - ρ) s (dI i φ) := fun i =>
    inClass_fderiv_apply ⟨hφ.differentiableOn.mono (Dom_mono (by linarith) le_rfl),
      fun l w hw => hφ.periodic l w (Dom_mono (by linarith) le_rfl hw)⟩ (0, Pi.single i 1)
  have hθ : ∀ j, ‖dtheta j φ z‖ ≤ U / σ := fun j => by
    refine (sup_le_wbound (hφθ j) (hcl.2.1 j) z (Dom_mono (by linarith) le_rfl hz)).trans ?_
    have he : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    exact div_le_div_of_nonneg_left hU hσ (by nlinarith)
  have hI : ∀ i, ‖dI i φ z‖ ≤ U / ρ := fun i =>
    sup_le_wbound (hφI i) (hcl.2.2 i) z (Dom_mono le_rfl (by linarith) hz)
  have hslow : ∀ i : Fin (n + (k + k)), ‖(b.c : ℂ) * dI i φ z‖ ≤ b.c * U / ρ := fun i => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hI i) hc
  have h1 : ‖(wfield b.c φ z).1‖ ≤ U / ρ :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hU hρ.le)).mpr fun i => hI _
  have hcU : b.c * U / ρ ≤ U / σ := by
    rw [div_le_div_iff₀ hρ hσ]
    nlinarith [mul_le_mul_of_nonneg_right hcσ hU]
  have h2 : ‖(wfield b.c φ z).2‖ ≤ U / σ := by
    refine (pi_norm_le_iff_of_nonneg (div_nonneg hU hσ.le)).mpr fun j => ?_
    simp only [wfield]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left, norm_neg]
      exact hθ i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_right, Fin.append_left]
        exact (hslow _).trans hcU
      · simp only [Fin.append_right, neg_mul, norm_neg]
        exact (hslow _).trans hcU
  have h3 : ‖slowPair (wfield b.c φ z)‖ ≤ b.c * U / ρ := by
    have hnn : 0 ≤ b.c * U / ρ := by positivity
    rw [slowPair, Prod.norm_def]
    refine max_le ((pi_norm_le_iff_of_nonneg hnn).mpr fun i => ?_)
      ((pi_norm_le_iff_of_nonneg hnn).mpr fun i => ?_)
    · simp only [wfield, Fin.append_right, Fin.append_left]
      exact hslow _
    · simp only [wfield, Fin.append_right, neg_mul, norm_neg]
      exact hslow _
  refine ⟨max_le ?_ ?_, h3⟩
  · calc ‖(wfield b.c φ z).1‖ / σ ≤ U / ρ / σ := div_le_div_of_nonneg_right h1 hσ.le
      _ = U / (ρ * σ) := by rw [div_div]
  · calc ‖(wfield b.c φ z).2‖ / ρ ≤ U / σ / ρ := div_le_div_of_nonneg_right h2 hρ.le
      _ = U / (ρ * σ) := by rw [div_div, mul_comm]

end KAM.Nekhoroshev

end
