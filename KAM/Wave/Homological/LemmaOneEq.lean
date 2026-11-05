/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.CohEq
public import KAM.Wave.Homological.SolveImage
public import KAM.Wave.Homological.LemmaOneBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The component equations (`bpW:w4:lemma1`, step *The equation*, analytic part)

`homFamily_eq`: for a continuous linear functional `Λ` intertwining the multipliers of a component
with the scalar multipliers `mu_k`, the functional of the solve satisfies the scalar cohomological
equation of `CohEq.lean`. The specializations are the entrywise equations of the seven components.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem homFamily_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {s σ m mΛ mΛ' κ κ' α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ) (hκ' : 1 ≤ κ')
    (hσ : 0 < σ) (hσs : σ < s) (ω : Fin 2 → ℝ) (lam : ℝ) (Λ : E →L[ℂ] ℂ)
    {T : (Fin 2 → ℤ) → E →L[ℂ] E} (mu : (Fin 2 → ℤ) → ℂ)
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α)
    (hΛ : ∀ k, Λ.comp (T k) = (mu k • ContinuousLinearMap.id ℂ ℂ).comp Λ)
    (hmu : ∀ k, ‖mu k‖ ≤ κ' * waveA τ k / α)
    (hres : ∀ k, k ≠ 0 → Complex.I * ((homPairZ k ω : ℂ) - lam) * mu k = 1)
    {u : (Fin 2 → ℂ) → E} (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (hmΛ : ∀ z ∈ complexStrip 2 s, ‖Λ (u z)‖ ≤ mΛ)
    (hmΛ' : ∀ i : Fin 2, ∀ z ∈ complexStrip 2 s, ‖homPartial i (fun z => Λ (u z)) z‖ ≤ mΛ')
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ i, (ω i : ℂ) * Λ (homPartial i (homSolve T u) θ))
      - Complex.I * lam * Λ (homSolve T u θ) =
      Λ (u θ) - (1 + Complex.I * lam * mu 0) * homCoeff (fun z => Λ (u z)) 0 := by
  have hΛu : DifferentiableOn ℂ (fun z => Λ (u z)) (complexStrip 2 s) :=
    Λ.differentiable.comp_differentiableOn hu
  have hΛp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → Λ (u (z + Pi.single i 1)) = Λ (u z) :=
    fun i z hz => by rw [hp i z hz]
  have h1 : ∀ i : Fin 2, Λ (homPartial i (homSolve T u) θ) = homPartial i
      (homSolve (fun k => mu k • ContinuousLinearMap.id ℂ ℂ) (fun z => Λ (u z))) θ := fun i =>
    homSolve_partial_image_eq hτ hα hκ hσ hσs hT Λ hΛ hu hp hm i hθ
  have h2 := homSolve_image_eq hτ hα hκ hσ hσs hT Λ hΛ hu hp hm hθ
  simp only [h1, h2]
  exact homCohEq_scalar hτ hα hκ' hσ hσs ω lam mu hmu hres hΛu hΛp hmΛ hmΛ' hθ

/-- The non-resonant case: if `i(⟨k,ω⟩ - λ) m_k = 1` also for `k = 0`, the constant term drops. -/
theorem homFamily_eq_nonres {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {s σ m mΛ mΛ' κ κ' α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ) (hκ' : 1 ≤ κ')
    (hσ : 0 < σ) (hσs : σ < s) (ω : Fin 2 → ℝ) (lam : ℝ) (Λ : E →L[ℂ] ℂ)
    {T : (Fin 2 → ℤ) → E →L[ℂ] E} (mu : (Fin 2 → ℤ) → ℂ)
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α)
    (hΛ : ∀ k, Λ.comp (T k) = (mu k • ContinuousLinearMap.id ℂ ℂ).comp Λ)
    (hmu : ∀ k, ‖mu k‖ ≤ κ' * waveA τ k / α)
    (hres : ∀ k, Complex.I * ((homPairZ k ω : ℂ) - lam) * mu k = 1)
    {u : (Fin 2 → ℂ) → E} (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (hmΛ : ∀ z ∈ complexStrip 2 s, ‖Λ (u z)‖ ≤ mΛ)
    (hmΛ' : ∀ i : Fin 2, ∀ z ∈ complexStrip 2 s, ‖homPartial i (fun z => Λ (u z)) z‖ ≤ mΛ')
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ i, (ω i : ℂ) * Λ (homPartial i (homSolve T u) θ))
      - Complex.I * lam * Λ (homSolve T u θ) = Λ (u θ) := by
  have := homFamily_eq hτ hα hκ hκ' hσ hσs ω lam Λ mu hT hΛ hmu (fun k hk => hres k) hu hp hm
    hmΛ hmΛ' hθ
  have h0 := hres 0
  have e : (1 + Complex.I * lam * mu 0) = 0 := by
    have hz : (homPairZ 0 ω : ℂ) = 0 := by simp [homPairZ]
    rw [hz] at h0
    linear_combination -h0
  rw [e, zero_mul, sub_zero] at this
  exact this

end KAM.Wave
