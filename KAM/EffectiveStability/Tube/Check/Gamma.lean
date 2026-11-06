/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.Domain
public import KAM.Frozen.Planetary.Defs.OscillatorAction

/-!
# The planet actions `Γ_j` in tube coordinates (T2-CONF, N5b)

The T2-CONF eccentricities are functions of the planet actions
`Γ_j(x) = KAM.Planetary.oscillatorAction ξ η j = (ξ_j² + η_j²)/2` (`x = (η, ξ)`). Through the chart
`x = rotMap V (polar (I, θ))`, with `φ = phiOf θ`,

  `Γ_j(x) = |Σ_k V_jk √I_k e^{i q_k}|²`, `q = (φ₀, φ₁, 0)`

(`chartGamma`, the same expression as N6's `eccGamma`, written for a real matrix). The common
phase `θ₂` drops out of `|·|²`.

* `oscillatorAction_eq_chartGamma`: the identity, for every `x`, with `I = u + B(φ)`, `(u, φ) =
  tubeChart V B x`.
* `oscillatorAction_prop_of_tube`: a property of `Γ_j(I, φ)` for all `φ` and all
  `|I_k - B_k(φ)| ≤ ρ` (e.g. N6's eccentricity enclosure) holds of `Γ_j(x)` for every `x` of the
  tube `tubeK V B ρ`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Matrix Real

/-- `Γ_j(I, φ) = |Σ_k V_jk √I_k e^{i q_k}|²` with `q = (φ₀, φ₁, 0)`, in real form. -/
def chartGamma (V : Matrix (Fin 3) (Fin 3) ℝ) (I : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (j : Fin 3) : ℝ :=
  (∑ k, V j k * √(I k) * cos (![φ 0, φ 1, 0] k)) ^ 2 +
    (∑ k, V j k * √(I k) * sin (![φ 0, φ 1, 0] k)) ^ 2

/-- `|Σ_k a_k e^{i(θ_k - t)}|² = |Σ_k a_k e^{iθ_k}|²`, in real form. -/
theorem sum_cos_sin_sub_sq (a θ : Fin 3 → ℝ) (t : ℝ) :
    (∑ k, a k * cos (θ k - t)) ^ 2 + (∑ k, a k * sin (θ k - t)) ^ 2 =
      (∑ k, a k * cos (θ k)) ^ 2 + (∑ k, a k * sin (θ k)) ^ 2 := by
  simp only [Fin.sum_univ_three, cos_sub, sin_sub]
  linear_combination
    ((a 0 * cos (θ 0) + a 1 * cos (θ 1) + a 2 * cos (θ 2)) ^ 2 +
      (a 0 * sin (θ 0) + a 1 * sin (θ 1) + a 2 * sin (θ 2)) ^ 2) * sin_sq_add_cos_sq t

theorem phiOf_vec_eq (θ : Fin 3 → ℝ) (k : Fin 3) :
    ![phiOf θ 0, phiOf θ 1, 0] k = θ k - θ 2 := by
  fin_cases k <;> simp [phiOf]

/-- **`Γ_j` in tube coordinates.** For orthogonal `V` and every `x`, with
`(u, φ) = tubeChart V B x`, `Γ_j(x) = chartGamma V (u + B φ) φ j`. -/
theorem oscillatorAction_eq_chartGamma {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    (B : (Fin 2 → ℝ) → (Fin 3 → ℝ)) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (j : Fin 3) :
    KAM.Planetary.oscillatorAction x.2 x.1 j =
      chartGamma V (tubeU V B x + B (tubeChart V B x).2) (tubeChart V B x).2 j := by
  set y := polarInv (rotMap Vᵀ x) with hy
  have hI : tubeU V B x + B (tubeChart V B x).2 = y.1 := sub_add_cancel _ _
  have hφ : (tubeChart V B x).2 = phiOf y.2 := rfl
  have hx : x = rotMap V (polar y) := by
    rw [hy, polar_polarInv, rotMap_rotMap_transpose hV]
  rw [hI, hφ, chartGamma, hx]
  show ((∑ k, V j k * (√(2 * y.1 k) * cos (y.2 k))) ^ 2 +
      (∑ k, V j k * (-√(2 * y.1 k) * sin (y.2 k))) ^ 2) / 2 = _
  have hs : ∀ k, √(2 * y.1 k) = √2 * √(y.1 k) := fun k => Real.sqrt_mul (by norm_num) _
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    phiOf_vec_eq, phiOf_vec_eq, phiOf_vec_eq, hs, hs, hs, cos_sub, cos_sub, cos_sub, sin_sub,
    sin_sub, sin_sub]
  linear_combination (1 / 2 : ℝ) *
    ((V j 0 * √(y.1 0) * cos (y.2 0) + V j 1 * √(y.1 1) * cos (y.2 1) +
        V j 2 * √(y.1 2) * cos (y.2 2)) ^ 2 +
      (V j 0 * √(y.1 0) * sin (y.2 0) + V j 1 * √(y.1 1) * sin (y.2 1) +
        V j 2 * √(y.1 2) * sin (y.2 2)) ^ 2) * h2 -
    ((V j 0 * √(y.1 0) * cos (y.2 0) + V j 1 * √(y.1 1) * cos (y.2 1) +
        V j 2 * √(y.1 2) * cos (y.2 2)) ^ 2 +
      (V j 0 * √(y.1 0) * sin (y.2 0) + V j 1 * √(y.1 1) * sin (y.2 1) +
        V j 2 * √(y.1 2) * sin (y.2 2)) ^ 2) * sin_sq_add_cos_sq (y.2 2)

/-- **Planet actions on the tube.** If a property `P j` holds of `Γ_j(I, φ)` for every `φ` and every
`I` with `|I_k - B_k(φ)| ≤ ρ`, it holds of `Γ_j(x)` on the tube `K = tubeK V B ρ` (e.g. two-sided
bounds of `Γ_j`, or of the eccentricity `√(1 - (1 - Γ_j/Λ_j)²)`). -/
theorem oscillatorAction_prop_of_tube {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {ρ : ℝ} {P : Fin 3 → ℝ → Prop}
    (hG : ∀ (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ), (∀ k, |I k - B φ k| ≤ ρ) → ∀ j,
      P j (chartGamma V I φ j))
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ tubeK V B ρ) (j : Fin 3) :
    P j (KAM.Planetary.oscillatorAction x.2 x.1 j) := by
  rw [oscillatorAction_eq_chartGamma hV B x j]
  exact hG _ _ (fun k => by simpa using hx.2 k) j

end KAM.EffectiveStability.Tube

end
