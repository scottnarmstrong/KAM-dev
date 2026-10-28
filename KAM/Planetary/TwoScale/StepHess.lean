/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepConst
public import KAM.Planetary.TwoScale.Inverse
public import KAM.Strip.HigherCauchy

/-!
# Two-scale KAM step: derivatives of `g` and the new Hessian (`stepP:p3:st-dg`, `st-U`)

Cauchy estimates for the averaged action function `g` (`‖∂g‖ ≤ 5E/R`, `‖∂²g‖ ≤ 80E/R²` on the
quarter-radius neighbourhood), the Hessian of `h + g`, and its inverse with the block bounds, via
the Neumann series (`ext_neumann`). Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- Cauchy bounds for a bounded holomorphic function on the half-radius neighbourhood. -/
theorem g_bounds {n : ℕ} {D : Set (Fin n → ℝ)} {r A : ℝ} (hr : 0 < r)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (KAM.actionNbhd D r))
    (hA : ∀ I ∈ KAM.actionNbhd D r, ‖g I‖ ≤ A) {I : Fin n → ℂ}
    (hI : I ∈ KAM.actionNbhd D (r / 2)) :
    ‖fderiv ℂ g I‖ ≤ 2 * A / r ∧ ‖fderiv ℂ (fderiv ℂ g) I‖ ≤ 16 * A / r ^ 2 := by
  have hopen := isOpen_actionNbhd' D r
  obtain ⟨J, hJ, hlt⟩ := hI
  have hsub : closedBall I (r / 2) ⊆ KAM.actionNbhd D r := by
    intro w hw
    refine ⟨J, hJ, ?_⟩
    have : ‖w - I‖ ≤ r / 2 := by simpa [dist_eq_norm] using hw
    calc ‖w - fun i => (J i : ℂ)‖ = ‖(w - I) + (I - fun i => (J i : ℂ))‖ := by congr 1; abel
      _ ≤ ‖w - I‖ + ‖I - fun i => (J i : ℂ)‖ := norm_add_le _ _
      _ < r := by linarith
  have hδ : 0 < r / 2 := by positivity
  have h1 := KAM.norm_fderiv_le_of_closedBall_bound hopen hg hδ hsub (fun w hw => hA w (hsub hw))
  have h2 := KAM.norm_fderiv_le_of_closedBall_bound hopen
    (differentiableOn_fderiv_of_isOpen hopen hg) (by positivity : 0 < r / 4)
    ((closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)).trans hsub)
    (fun w hw => KAM.norm_fderiv_le_on_half_closedBall hopen hg hδ hsub
      (fun u hu => hA u (hsub hu)) (closedBall_subset_closedBall (by linarith) hw))
  constructor
  · exact h1.trans_eq (by field_simp)
  · exact h2.trans_eq (by field_simp; ring)

theorem freq_add {n : ℕ} {h g : (Fin n → ℂ) → ℂ} {I : Fin n → ℂ} (hh : DifferentiableAt ℂ h I)
    (hg : DifferentiableAt ℂ g I) :
    freq (fun J => h J + g J) I = freq h I + freq g I := by
  funext i
  simp only [freq, Pi.add_apply]
  rw [fderiv_fun_add hh hg]; rfl

/-- Hessian of `h + g` is the sum of the Hessians on the open set where both are holomorphic. -/
theorem fderiv_freq_add {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) {h g : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h U) (hg : DifferentiableOn ℂ g U) {I : Fin n → ℂ} (hI : I ∈ U) :
    fderiv ℂ (freq (fun J => h J + g J)) I = fderiv ℂ (freq h) I + fderiv ℂ (freq g) I := by
  have h1 : freq (fun J => h J + g J) =ᶠ[nhds I] fun J => freq h J + freq g J := by
    filter_upwards [hU.mem_nhds hI] with J hJ
    exact freq_add (hh.differentiableAt (hU.mem_nhds hJ)) (hg.differentiableAt (hU.mem_nhds hJ))
  rw [h1.fderiv_eq]
  exact fderiv_add (differentiableAt_freq hU hh hI) (differentiableAt_freq hU hg hI)

theorem freq_g_fderiv {n : ℕ} {g : (Fin n → ℂ) → ℂ} {I : Fin n → ℂ} {c : ℝ}
    (hg : DifferentiableAt ℂ (fderiv ℂ g) I) (hc : ‖fderiv ℂ (fderiv ℂ g) I‖ ≤ c) (v : Fin n → ℂ) :
    ‖fderiv ℂ (freq g) I v‖ ≤ c * ‖v‖ := by
  have hc0 : 0 ≤ c := le_trans (ContinuousLinearMap.opNorm_nonneg _) hc
  have hd : DifferentiableAt ℂ (freq g) I :=
    differentiableAt_pi.2 fun i => hg.clm_apply (differentiableAt_const _)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have e : fderiv ℂ (freq g) I v j = fderiv ℂ (fderiv ℂ g) I v (Pi.single j 1) := by
    rw [fderiv_pi (fun i => (differentiableAt_pi.1 hd) i)]
    show fderiv ℂ (fun J => fderiv ℂ g J (Pi.single j 1)) I v = _
    rw [fderiv_clm_apply hg (differentiableAt_const _)]
    simp
  rw [e]
  refine ((fderiv ℂ (fderiv ℂ g) I v).le_opNorm _).trans ?_
  simp only [Pi.norm_single, norm_one, mul_one]
  exact ((fderiv ℂ (fderiv ℂ g) I).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

end KAM.Planetary

end
