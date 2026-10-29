/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.Setting
public import KAM.Weighted.Cauchy
public import KAM.Weighted.SupWeighted
import Mathlib.Tactic.Positivity

/-!
# Hamiltonian fields and their size (`bpN:p5:vf-bound`)

Blueprint-N Part 5, node `bpN:p5:vf-bound`.

* `KAM.Canonical.differentiableOn_hamField`: the frozen field `KAM.hamiltonianVectorFieldℂ φ` of a
  holomorphic `φ` is holomorphic;
* `KAM.Canonical.vf_bound`: for `φ ∈ O(r,s)` with `|φ|_{r,s} ≤ Φ`, on `𝒟_{r-ρ,s-σ}` one has
  `|∂_{I_i} φ| ≤ Φ/ρ`, `|∂_{θ_i} φ| ≤ Φ/(eσ)` and `ν_{ρ,σ}(X_φ) ≤ Φ/(ρσ)`.
-/

@[expose] public noncomputable section

open KAM.Weighted

namespace KAM.Canonical

variable {n : ℕ}

/-- The Hamiltonian field of a holomorphic function is holomorphic (K's
`KAM.holomorphic_regularity`). -/
theorem differentiableOn_hamField {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ U) :
    DifferentiableOn ℂ (KAM.hamiltonianVectorFieldℂ φ) U := by
  have h := (KAM.holomorphic_regularity_of_finiteDimensional hU hφ).1
  have hc : ∀ a : (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ (fun z => fderiv ℂ φ z a) U := fun a =>
    h.clm_apply (differentiableOn_const a)
  refine DifferentiableOn.prodMk ?_ ?_
  · exact differentiableOn_pi.2 fun i => hc _
  · exact differentiableOn_pi.2 fun i => (hc _).neg

/-- Restriction of the class to smaller radii. -/
private theorem inClass_mono {D : Set (Fin n → ℂ)} {r r' s s' : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r s u) (hr : r' ≤ r) (hs : s' ≤ s) :
    InClass D r' s' u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

/-- `bpN:p5:vf-bound`. -/
theorem vf_bound {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hφ : InClass D r s φ) (hb : WBound D r s φ Φ) (hρ : 0 < ρ) (hρr : ρ < r) (hσ : 0 < σ)
    (hσs : σ < s) :
    ∀ z ∈ Dom n D (r - ρ) (s - σ), (∀ i, ‖dI i φ z‖ ≤ Φ / ρ) ∧
      (∀ i, ‖dtheta i φ z‖ ≤ Φ / (Real.exp 1 * σ)) ∧
      scaledNorm ρ σ (KAM.hamiltonianVectorFieldℂ φ z) ≤ Φ / (ρ * σ) := by
  intro z hz
  have hsσ : 0 < s - σ := sub_pos.mpr hσs
  have hs : 0 < s := hσ.trans hσs
  have hcl := cauchy_loss hφ hb hρ hρr hσ hσs
  have hφ' : InClass D (r - ρ) (s - σ) φ := inClass_mono hφ (by linarith) (by linarith)
  have hΦ : 0 ≤ Φ := by
    have hz2 : z.2 ∈ polyNbhd D r := Dom_mono (r := r) (s := s) (by linarith) (by linarith) hz |>.2
    exact (tsum_nonneg fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans (hb _ hz2).2
  have hI : ∀ i, ‖dI i φ z‖ ≤ Φ / ρ := fun i => by
    have hcls := (coefficients_deriv hsσ hφ').2 i |>.1
    exact sup_le_wbound hcls ((hcl.2.2 i).mono le_rfl (by linarith) le_rfl) z hz
  have hθ : ∀ i, ‖dtheta i φ z‖ ≤ Φ / (Real.exp 1 * σ) := fun i => by
    have hcls := (coefficients_deriv hsσ hφ').1 i |>.1
    exact sup_le_wbound hcls ((hcl.2.1 i).mono (by linarith) le_rfl le_rfl) z hz
  refine ⟨hI, hθ, ?_⟩
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have h1 : ‖(KAM.hamiltonianVectorFieldℂ φ z).1‖ / σ ≤ Φ / (ρ * σ) := by
    rw [div_le_div_iff₀ hσ (by positivity)]
    have : ‖(KAM.hamiltonianVectorFieldℂ φ z).1‖ ≤ Φ / ρ :=
      (pi_norm_le_iff_of_nonneg (div_nonneg hΦ hρ.le)).2 hI
    calc _ ≤ Φ / ρ * (ρ * σ) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = Φ * σ := by field_simp
  have h2 : ‖(KAM.hamiltonianVectorFieldℂ φ z).2‖ / ρ ≤ Φ / (ρ * σ) := by
    have hnn : 0 ≤ Φ / (Real.exp 1 * σ) := div_nonneg hΦ (by positivity)
    have : ‖(KAM.hamiltonianVectorFieldℂ φ z).2‖ ≤ Φ / (Real.exp 1 * σ) :=
      (pi_norm_le_iff_of_nonneg hnn).2 fun i => by
        simpa [KAM.hamiltonianVectorFieldℂ, dtheta] using hθ i
    calc _ ≤ Φ / (Real.exp 1 * σ) / ρ := div_le_div_of_nonneg_right this hρ.le
      _ = Φ / (Real.exp 1 * (ρ * σ)) := by field_simp
      _ ≤ Φ / (1 * (ρ * σ)) :=
        div_le_div_of_nonneg_left hΦ (by positivity) (mul_le_mul_of_nonneg_right he (by positivity))
      _ = Φ / (ρ * σ) := by rw [one_mul]
  exact max_le h1 h2

end KAM.Canonical

end
