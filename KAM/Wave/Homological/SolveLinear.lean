/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Solve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The multiplier solve commutes with linear images (blueprint-W `bpW:w4:solve` (iv),
`bpW:w4:fourier-ops` (i))

* `homCoeff_clm`: `(Λ f)^_k = Λ f̂_k` for a continuous linear `Λ : E → E'`;
* `homSolve_intertwine`: if `Λ₁ T_k = T'_k Λ₀` then `Λ₁ (𝒮 u) = 𝒮' (Λ₀ u)` on `T_ρ` whenever
  the weighted coefficient series of `𝒮 u` is summable; `homSolve_clm` is the case `Λ₀ = id`.
-/

@[expose] public section

namespace KAM.Wave

open KAM

variable {E E' E₀ E₁ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]

/-- Continuous linear maps commute with the torus average of continuous maps. -/
theorem homTorusAverage_clm {v : (Fin 2 → ℝ) → E} (hv : Continuous v) (Λ : E →L[ℂ] E') :
    Λ (torusAverage v) = torusAverage fun x => Λ (v x) := by
  have hint : MeasureTheory.Integrable v (MeasureTheory.volume.restrict
      (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
    integrableOn_unitCube_of_continuous hv
  have := (Λ.restrictScalars ℝ).integral_comp_comm hint
  unfold torusAverage
  simpa using this.symm

omit [CompleteSpace E] in
theorem homContinuous_restrict {s : ℝ} (hs : 0 < s) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s)) :
    Continuous fun x : Fin 2 → ℝ => u fun j => (x j : ℂ) :=
  hu.continuousOn.comp_continuous
    (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
    fun x => ofReal_mem_complexStrip hs x

/-- **Coefficients of linear images** (blueprint `bpW:w4:fourier-ops` (i)). -/
theorem homCoeff_clm {s : ℝ} (hs : 0 < s) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s)) (Λ : E →L[ℂ] E') (k : Fin 2 → ℤ) :
    homCoeff (fun z => Λ (u z)) k = Λ (homCoeff u k) := by
  have hc := homContinuous_restrict hs hu
  have hchar : Continuous fun x : Fin 2 → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character (-k)).continuous.comp
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
  unfold homCoeff torusCoeffW
  have := homTorusAverage_clm (v := fun x : Fin 2 → ℝ =>
    character (-k) (fun j => (x j : ℂ)) • u fun j => (x j : ℂ)) (hchar.smul hc) Λ
  simp only [map_smul] at this
  exact this.symm

omit [CompleteSpace E'] in
/-- Continuous linear maps commute with absolutely convergent Fourier series. -/
theorem clm_fourierSumVec_of_summable {ρ : ℝ} {a : (Fin 2 → ℤ) → E}
    (ha : Summable fun k => ‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 ρ) (Λ : E →L[ℂ] E') :
    Λ (fourierSumVec a θ) = fourierSumVec (fun k => Λ (a k)) θ := by
  unfold fourierSumVec
  rw [Λ.map_tsum (summable_character_smul ha hθ)]
  exact tsum_congr fun k => by simp only [map_smul]

omit [CompleteSpace E₁] in
/-- **Multiplier solve, (iv)**: if `Λ₁ T_k = T'_k Λ₀` for all `k`, then `Λ₁ 𝒮 u = 𝒮' (Λ₀ u)` on
`T_ρ`, whenever `∑ ‖T_k û_k‖ e^{2π|k|₁ρ} < ∞`. -/
theorem homSolve_intertwine {s ρ : ℝ} (hs : 0 < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E'}
    {T' : (Fin 2 → ℤ) → E₀ →L[ℂ] E₁} (Λ₀ : E →L[ℂ] E₀) (Λ₁ : E' →L[ℂ] E₁)
    (hΛ : ∀ k, Λ₁.comp (T k) = (T' k).comp Λ₀) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hsum : Summable fun k =>
      ‖T k (homCoeff u k)‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 ρ) :
    Λ₁ (homSolve T u θ) = homSolve T' (fun z => Λ₀ (u z)) θ := by
  unfold homSolve
  rw [clm_fourierSumVec_of_summable hsum hθ Λ₁]
  unfold fourierSumVec
  refine tsum_congr fun k => ?_
  dsimp only
  rw [homCoeff_clm hs hu Λ₀ k]
  have := congrArg (fun L => L (homCoeff u k)) (hΛ k)
  simp only [ContinuousLinearMap.comp_apply] at this
  rw [this]

omit [CompleteSpace E₁] in
/-- **Multiplier solve, (iv)**, first part: `Λ 𝒮 u` is the solve of `u` with the multipliers
`Λ T_k`. -/
theorem homSolve_clm {s ρ : ℝ} (hs : 0 < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E'} (Λ : E' →L[ℂ] E₁)
    {u : (Fin 2 → ℂ) → E} (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hsum : Summable fun k =>
      ‖T k (homCoeff u k)‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 ρ) :
    Λ (homSolve T u θ) = homSolve (fun k => Λ.comp (T k)) u θ := by
  have := homSolve_intertwine (T' := fun k => Λ.comp (T k)) hs (ContinuousLinearMap.id ℂ E) Λ
    (fun k => by ext; simp) hu hsum hθ
  simpa using this

end KAM.Wave
