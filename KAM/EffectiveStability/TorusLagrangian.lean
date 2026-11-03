/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Exactness
public import KAM.Apost.Identities
public import KAM.Apost.Periodicity
public import KAM.Sharp.CohData

/-!
# The Lagrangian property of an exact invariant torus (track B, package B5-LAG, item 1)

For an embedding `K` holomorphic and primary on `T_r` with zero invariance error, the
Lagrangian matrix `Ω_K = DKᵀ Ω₀ DK` vanishes on `T_{r-δ}`.

Direct argument: `∂_ω Ω_K = -(DE)ᵀ Ω₀ DK - DKᵀ Ω₀ DE = 0` (`KAM.Apost.Identities.fi_dLagrange`
with `E = 0`), `Ω_K` is periodic with zero average (`KAM.Apost.Exactness.avg_lagrangeMat`), and
the Diophantine cohomological estimate with right-hand side `0` forces `Ω_K = 0`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.EffectiveStability

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r δ : ℝ}

/-- With zero invariance error, `∂_ω Ω_K = 0` on `T_r`. -/
theorem fderiv_lagrangeMat_omega_eq_zero (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError h K ω θ = 0) :
    ∀ θ ∈ complexStrip n r, fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) = 0 := by
  intro θ hθ
  have hD : fderiv ℂ (invarianceError h K ω) θ = 0 := by
    have : invarianceError h K ω =ᶠ[nhds θ] fun _ => 0 := by
      filter_upwards [(isOpen_complexStrip n r).mem_nhds hθ] with y hy using hE y hy
    rw [this.fderiv_eq]
    simp
  rw [Identities.fi_dLagrange hS hK hK𝔅 hθ]
  simp [errDerivMat, hD, colMat]

/-- **Lagrangian property (item 1).** An exact invariant primary torus is Lagrangian on every
strictly smaller strip. -/
theorem lagrangeMat_eq_zero_of_exact (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError h K ω θ = 0) (hδ : 0 < δ) (hδr : δ < r) :
    ∀ θ ∈ complexStrip n (r - δ), lagrangeMat K θ = 0 := by
  intro θ hθ
  have hn : 1 ≤ n := by have := hS.two_le; omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hτ0 : 0 ≤ τ := by linarith [hS.tau_ge]
  have hC := Sharp.cohData_crude hn hτ0
  set δ' := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'le : δ' ≤ 1 := min_le_right _ _
  have hδ'r : δ' < r := lt_of_le_of_lt (min_le_left _ _) hδr
  have hdiff : DifferentiableOn ℂ (lagrangeMat K) (complexStrip n r) :=
    Exactness.differentiableOn_lagrangeMat hK
  have hper : IsPeriodicOn (lagrangeMat K) r := periodic_lagrangeMat hKp
  have havg : avg (lagrangeMat K) = 0 := Exactness.avg_lagrangeMat hr hK hKp
  have hω := fderiv_lagrangeMat_omega_eq_zero hS hK hK𝔅 hE
  have key := hC.apriori hS.gamma_pos hS.dio hδ'0 hδ'le hδ'r (lagrangeMat K) 0 hdiff hper havg
    (fun θ hθ => by rw [hω θ hθ, norm_zero])
  have hθ' : θ ∈ complexStrip n (r - δ') := fun i =>
    (hθ i).trans_le (by linarith [min_le_left δ 1])
  have := key θ hθ'
  rw [mul_zero, norm_le_zero_iff] at this
  exact this
end KAM.EffectiveStability

end
