/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.SolveDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bounds for images of the solve (blueprint-W `bpW:w4:lemma1`, step *Component bounds of F*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

For a continuous linear `Λ : E → G` intertwining the multipliers (`Λ T_k = T'_k Λ`),
the image `Λ 𝒮u` is the solve `𝒮'(Λ u)` (`bpW:w4:solve` (iv)), hence

* `homSolve_image_bound`: `‖Λ 𝒮u(θ)‖ ≤ κ' B^W_σ m_Λ/α` if `‖Λ u‖ ≤ m_Λ`;
* `homSolve_image_partial_bound`: `‖Λ ∂_{θ_i}𝒮u(θ)‖ ≤ κ' B^W_σ m'_Λ/α` if `‖∂_{θ_i}Λ u‖ ≤ m'_Λ`
  (`bpW:w4:solve` (iii) in the image space).

With `Λ` the identity, `Λ = ` the matrix entries, `Λ = D` or `Λ = homLamCLM` this gives the bounds
of the seven components and of their `θ`-derivatives (`bilinear` and `dual` norms).
-/

@[expose] public section

namespace KAM.Wave

open KAM

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem homSolve_image_eq {s σ m κ α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hσ : 0 < σ) (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E} {T' : (Fin 2 → ℤ) → G →L[ℂ] G}
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α) (Λ : E →L[ℂ] G)
    (hΛ : ∀ k, Λ.comp (T k) = (T' k).comp Λ) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    Λ (homSolve T u θ) = homSolve T' (fun z => Λ (u z)) θ := by
  have hs : 0 < s := hσ.trans hσs
  obtain ⟨hsum, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT hu hp hm
  exact homSolve_intertwine (T' := T') (ρ := s - σ) hs Λ Λ hΛ hu hsum hθ

theorem homSolve_image_bound {s σ m mΛ κ κ' α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hκ' : 1 ≤ κ') (hσ : 0 < σ) (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E}
    {T' : (Fin 2 → ℤ) → G →L[ℂ] G} (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α)
    (hT' : ∀ k, ‖T' k‖ ≤ κ' * waveA τ k / α) (Λ : E →L[ℂ] G)
    (hΛ : ∀ k, Λ.comp (T k) = (T' k).comp Λ) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (hmΛ : ∀ z ∈ complexStrip 2 s, ‖Λ (u z)‖ ≤ mΛ)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    ‖Λ (homSolve T u θ)‖ ≤ κ' * waveBW τ σ * mΛ / α := by
  rw [homSolve_image_eq hτ hα hκ hσ hσs hT Λ hΛ hu hp hm hθ]
  exact (homSolve_spec hτ hα hκ' hσ hσs hT' (Λ.differentiable.comp_differentiableOn hu)
    (fun i z hz => by simp only [Function.comp_apply, hp i z hz]) hmΛ).2.2.1 θ hθ

/-- `Λ ∂_{θ_i} 𝒮u = ∂_{θ_i} 𝒮'(Λu)` on `T_{s-σ}` (no bound on `∂u` needed). -/
theorem homSolve_partial_image_eq {s σ m κ α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hσ : 0 < σ) (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E} {T' : (Fin 2 → ℤ) → G →L[ℂ] G}
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α) (Λ : E →L[ℂ] G)
    (hΛ : ∀ k, Λ.comp (T k) = (T' k).comp Λ) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (i : Fin 2) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    Λ (homPartial i (homSolve T u) θ) =
      homPartial i (homSolve T' (fun z => Λ (u z))) θ := by
  have hopen := isOpen_complexStrip 2 (s - σ)
  have hFd : DifferentiableOn ℂ (homSolve T u) (complexStrip 2 (s - σ)) :=
    (homSolve_spec hτ hα hκ hσ hσs hT hu hp hm).2.2.2.1
  have hev : (fun z => Λ (homSolve T u z)) =ᶠ[nhds θ] homSolve T' (fun z => Λ (u z)) :=
    Filter.eventually_of_mem (hopen.mem_nhds hθ) fun z hz =>
      homSolve_image_eq hτ hα hκ hσ hσs hT Λ hΛ hu hp hm hz
  have hd : DifferentiableAt ℂ (homSolve T u) θ := hFd.differentiableAt (hopen.mem_nhds hθ)
  have h1 : Λ (homPartial i (homSolve T u) θ) =
      homPartial i (fun z => Λ (homSolve T u z)) θ := by
    unfold homPartial
    have := (Λ.hasFDerivAt.comp θ hd.hasFDerivAt).fderiv
    rw [show (fun z => Λ (homSolve T u z)) = Λ ∘ homSolve T u from rfl, this]
    rfl
  rw [h1]
  unfold homPartial; rw [hev.fderiv_eq]

theorem homSolve_image_partial_bound {s σ m mΛ mΛ' κ κ' α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α)
    (hκ : 1 ≤ κ) (hκ' : 1 ≤ κ') (hσ : 0 < σ) (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E}
    {T' : (Fin 2 → ℤ) → G →L[ℂ] G} (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α)
    (hT' : ∀ k, ‖T' k‖ ≤ κ' * waveA τ k / α) (Λ : E →L[ℂ] G)
    (hΛ : ∀ k, Λ.comp (T k) = (T' k).comp Λ) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (hmΛ : ∀ z ∈ complexStrip 2 s, ‖Λ (u z)‖ ≤ mΛ)
    (i : Fin 2)
    (hmΛ' : ∀ z ∈ complexStrip 2 s, ‖homPartial i (fun z => Λ (u z)) z‖ ≤ mΛ')
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    ‖Λ (homPartial i (homSolve T u) θ)‖ ≤ κ' * waveBW τ σ * mΛ' / α := by
  have hs : 0 < s := hσ.trans hσs
  have hΛu : DifferentiableOn ℂ (fun z => Λ (u z)) (complexStrip 2 s) :=
    Λ.differentiable.comp_differentiableOn hu
  have hΛp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → Λ (u (z + Pi.single i 1)) = Λ (u z) :=
    fun i z hz => by rw [hp i z hz]
  have hopen := isOpen_complexStrip 2 (s - σ)
  have hFd : DifferentiableOn ℂ (homSolve T u) (complexStrip 2 (s - σ)) :=
    (homSolve_spec hτ hα hκ hσ hσs hT hu hp hm).2.2.2.1
  -- `Λ ∘ (𝒮u) = 𝒮'(Λu)` near `θ`
  have hev : (fun z => Λ (homSolve T u z)) =ᶠ[nhds θ] homSolve T' (fun z => Λ (u z)) :=
    Filter.eventually_of_mem (hopen.mem_nhds hθ) fun z hz =>
      homSolve_image_eq hτ hα hκ hσ hσs hT Λ hΛ hu hp hm hz
  have hd : DifferentiableAt ℂ (homSolve T u) θ := hFd.differentiableAt (hopen.mem_nhds hθ)
  have h1 : Λ (homPartial i (homSolve T u) θ) =
      homPartial i (fun z => Λ (homSolve T u z)) θ := by
    unfold homPartial
    have := (Λ.hasFDerivAt.comp θ hd.hasFDerivAt).fderiv
    rw [show (fun z => Λ (homSolve T u z)) = Λ ∘ homSolve T u from rfl, this]
    rfl
  have h2 : homPartial i (fun z => Λ (homSolve T u z)) θ =
      homPartial i (homSolve T' (fun z => Λ (u z))) θ := by
    unfold homPartial; rw [hev.fderiv_eq]
  have h3 := homSolve_partial hτ hα hκ' hσ hσs hT' hΛu hΛp hmΛ i hmΛ' hθ
  have h4 : homPartial i (homSolve T' (fun z => Λ (u z))) θ =
      homSolve T' (homPartial i fun z => Λ (u z)) θ := h3
  rw [h1, h2, h4]
  exact (homSolve_spec hτ hα hκ' hσ hσs hT' (homPartial_differentiableOn i hΛu)
    (fun j z hz => homPartial_periodic hΛp i j hz) hmΛ').2.2.1 θ hθ

end KAM.Wave
