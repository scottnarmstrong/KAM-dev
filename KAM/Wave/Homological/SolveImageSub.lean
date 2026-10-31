/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.SolveImage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lipschitz bounds for images of the solve (`bpW:w4:lemma1`, step *Lipschitz*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

The two-parameter versions of `SolveImage.lean`: for continuous linear `Λ` intertwining both pairs
of multipliers, `‖Λ𝒮₁u₁ - Λ𝒮₂u₂‖ ≤ κ' B^W_σ(m^L + 2M m_Λ/α)d/α`
(`homSolve_image_sub_bound`), and the same for the `θ`-derivatives
(`homSolve_image_partial_sub_bound`).
-/

@[expose] public section

namespace KAM.Wave

open KAM

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem homSolve_image_sub_bound {s σ m₁ m₂ mΛ mL κ κ' α τ M d : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α)
    (hκ : 1 ≤ κ) (hκ' : 1 ≤ κ') (hM : 0 ≤ M) (hd : 0 ≤ d) (hmL0 : 0 ≤ mL) (hσ : 0 < σ)
    (hσs : σ < s) {T₁ T₂ : (Fin 2 → ℤ) → E →L[ℂ] E} {T₁' T₂' : (Fin 2 → ℤ) → G →L[ℂ] G}
    (hT₁ : ∀ k, ‖T₁ k‖ ≤ κ * waveA τ k / α) (hT₂ : ∀ k, ‖T₂ k‖ ≤ κ * waveA τ k / α)
    (hT₁' : ∀ k, ‖T₁' k‖ ≤ κ' * waveA τ k / α) (hT₂' : ∀ k, ‖T₂' k‖ ≤ κ' * waveA τ k / α)
    (hTd : ∀ k, ‖T₁' k - T₂' k‖ ≤
      2 * κ' * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d)
    (Λ : E →L[ℂ] G) (hΛ₁ : ∀ k, Λ.comp (T₁ k) = (T₁' k).comp Λ)
    (hΛ₂ : ∀ k, Λ.comp (T₂ k) = (T₂' k).comp Λ) {u₁ u₂ : (Fin 2 → ℂ) → E}
    (hu₁ : DifferentiableOn ℂ u₁ (complexStrip 2 s))
    (hu₂ : DifferentiableOn ℂ u₂ (complexStrip 2 s))
    (hp₁ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u₁ (z + Pi.single i 1) = u₁ z)
    (hp₂ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u₂ (z + Pi.single i 1) = u₂ z)
    (hm₁ : ∀ z ∈ complexStrip 2 s, ‖u₁ z‖ ≤ m₁) (hm₂ : ∀ z ∈ complexStrip 2 s, ‖u₂ z‖ ≤ m₂)
    (hΛm₁ : ∀ z ∈ complexStrip 2 s, ‖Λ (u₁ z)‖ ≤ mΛ) (hΛm₂ : ∀ z ∈ complexStrip 2 s, ‖Λ (u₂ z)‖ ≤
        mΛ)
    (hΛL : ∀ z ∈ complexStrip 2 s, ‖Λ (u₁ z) - Λ (u₂ z)‖ ≤ mL * d) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    ‖Λ (homSolve T₁ u₁ θ) - Λ (homSolve T₂ u₂ θ)‖ ≤
      κ' * waveBW τ σ / α * (mL + 2 * M * mΛ / α) * d := by
  rw [homSolve_image_eq hτ hα hκ hσ hσs hT₁ Λ hΛ₁ hu₁ hp₁ hm₁ hθ,
    homSolve_image_eq hτ hα hκ hσ hσs hT₂ Λ hΛ₂ hu₂ hp₂ hm₂ hθ]
  exact homSolve_sub_le hτ hα hκ' hM hd hσ hσs hT₁' hT₂' hTd
    (Λ.differentiable.comp_differentiableOn hu₁) (Λ.differentiable.comp_differentiableOn hu₂)
    (fun i z hz => by simp only [Function.comp_apply, hp₁ i z hz]) (fun i z hz => by simp only
        [Function.comp_apply, hp₂ i z hz])
    hΛm₁ hΛm₂ hΛL hmL0 θ hθ

theorem homSolve_image_partial_sub_bound {s σ m₁ m₂ mΛ mΛ' mL' κ κ' α τ M d : ℝ} (hτ : 0 ≤ τ)
    (hα : 0 < α) (hκ : 1 ≤ κ) (hκ' : 1 ≤ κ') (hM : 0 ≤ M) (hd : 0 ≤ d) (hmL0 : 0 ≤ mL')
    (hσ : 0 < σ) (hσs : σ < s) {T₁ T₂ : (Fin 2 → ℤ) → E →L[ℂ] E}
    {T₁' T₂' : (Fin 2 → ℤ) → G →L[ℂ] G}
    (hT₁ : ∀ k, ‖T₁ k‖ ≤ κ * waveA τ k / α) (hT₂ : ∀ k, ‖T₂ k‖ ≤ κ * waveA τ k / α)
    (hT₁' : ∀ k, ‖T₁' k‖ ≤ κ' * waveA τ k / α) (hT₂' : ∀ k, ‖T₂' k‖ ≤ κ' * waveA τ k / α)
    (hTd : ∀ k, ‖T₁' k - T₂' k‖ ≤
      2 * κ' * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d)
    (Λ : E →L[ℂ] G) (hΛ₁ : ∀ k, Λ.comp (T₁ k) = (T₁' k).comp Λ)
    (hΛ₂ : ∀ k, Λ.comp (T₂ k) = (T₂' k).comp Λ) {u₁ u₂ : (Fin 2 → ℂ) → E}
    (hu₁ : DifferentiableOn ℂ u₁ (complexStrip 2 s))
    (hu₂ : DifferentiableOn ℂ u₂ (complexStrip 2 s))
    (hp₁ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u₁ (z + Pi.single i 1) = u₁ z)
    (hp₂ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u₂ (z + Pi.single i 1) = u₂ z)
    (hm₁ : ∀ z ∈ complexStrip 2 s, ‖u₁ z‖ ≤ m₁) (hm₂ : ∀ z ∈ complexStrip 2 s, ‖u₂ z‖ ≤ m₂)
    (hΛm₁ : ∀ z ∈ complexStrip 2 s, ‖Λ (u₁ z)‖ ≤ mΛ) (hΛm₂ : ∀ z ∈ complexStrip 2 s, ‖Λ (u₂ z)‖ ≤
        mΛ)
    (i : Fin 2)
    (hΛ'm₁ : ∀ z ∈ complexStrip 2 s, ‖homPartial i (fun z => Λ (u₁ z)) z‖ ≤ mΛ')
    (hΛ'm₂ : ∀ z ∈ complexStrip 2 s, ‖homPartial i (fun z => Λ (u₂ z)) z‖ ≤ mΛ')
    (hΛ'L : ∀ z ∈ complexStrip 2 s, ‖homPartial i (fun z => Λ (u₁ z)) z -
      homPartial i (fun z => Λ (u₂ z)) z‖ ≤ mL' * d) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    ‖Λ (homPartial i (homSolve T₁ u₁) θ) - Λ (homPartial i (homSolve T₂ u₂) θ)‖ ≤
      κ' * waveBW τ σ / α * (mL' + 2 * M * mΛ' / α) * d := by
  have hΛu₁ : DifferentiableOn ℂ (fun z => Λ (u₁ z)) (complexStrip 2 s) :=
    Λ.differentiable.comp_differentiableOn hu₁
  have hΛu₂ : DifferentiableOn ℂ (fun z => Λ (u₂ z)) (complexStrip 2 s) :=
    Λ.differentiable.comp_differentiableOn hu₂
  have hΛp₁ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → Λ (u₁ (z + Pi.single i 1)) = Λ (u₁ z) :=
    fun i z hz => by rw [hp₁ i z hz]
  have hΛp₂ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → Λ (u₂ (z + Pi.single i 1)) = Λ (u₂ z) :=
    fun i z hz => by rw [hp₂ i z hz]
  rw [homSolve_partial_image_eq hτ hα hκ hσ hσs hT₁ Λ hΛ₁ hu₁ hp₁ hm₁ i hθ,
    homSolve_partial_image_eq hτ hα hκ hσ hσs hT₂ Λ hΛ₂ hu₂ hp₂ hm₂ i hθ]
  have h1 := homSolve_partial hτ hα hκ' hσ hσs hT₁' hΛu₁ hΛp₁ hΛm₁ i hΛ'm₁ hθ
  have h2 := homSolve_partial hτ hα hκ' hσ hσs hT₂' hΛu₂ hΛp₂ hΛm₂ i hΛ'm₂ hθ
  have h1' : homPartial i (homSolve T₁' (fun z => Λ (u₁ z))) θ =
      homSolve T₁' (homPartial i fun z => Λ (u₁ z)) θ := h1
  have h2' : homPartial i (homSolve T₂' (fun z => Λ (u₂ z))) θ =
      homSolve T₂' (homPartial i fun z => Λ (u₂ z)) θ := h2
  rw [h1', h2']
  exact homSolve_sub_le hτ hα hκ' hM hd hσ hσs hT₁' hT₂' hTd
    (homPartial_differentiableOn i hΛu₁) (homPartial_differentiableOn i hΛu₂)
    (fun j z hz => homPartial_periodic hΛp₁ i j hz) (fun j z hz => homPartial_periodic hΛp₂ i j hz)
    hΛ'm₁ hΛ'm₂ hΛ'L hmL0 θ hθ

end KAM.Wave
