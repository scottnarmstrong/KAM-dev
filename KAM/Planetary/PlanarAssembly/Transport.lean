/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Hamiltonian.Chart
public import KAM.Frozen.Planetary.Defs.IsCylinderTorus
public import KAM.Frozen.Planetary.Defs.IsPhysicalTorus
public import KAM.Frozen.Planetary.Defs.FastShift

/-!
# Part 12: transport of cylinder tori to physical tori

`bpP:p12:transport` (`stepP:p12:tr-an`, `tr-per`, `tr-inj`, `tr-lag`, `tr-flow`, `tr-dio`): a
fast-lattice chart `Ψ` (analytic, symplectic, with the lattice properties `hQ1`, `hQ2`) carries a
frozen cylinder torus `K` of `H` to a frozen physical torus `Ψ ∘ K` of `G`, where `G ∘ Ψ = H`
on `O`. The proof uses the frozen predicates directly.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler

namespace PlanarAssembly

/-- Direct fast-lattice transport, stronger in dimension and Hamiltonian generality.
These are the local source hypotheses of transport, not frozen-root assumptions. -/
theorem transport {a b : ℕ} {O : Set (Phase (a + b))} (hO : IsOpen O)
    {Ψ : Phase (a + b) → Phase (a + b)}
    (hΨa : AnalyticOnNhd ℝ Ψ O) (hΨs : IsSymplecticOn 1 Ψ O)
    {H G : Phase (a + b) → ℝ} (hHG : EqOn (G ∘ Ψ) H O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin a → ℤ, z + fastShift k ∈ O ∧ Ψ (z + fastShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin a → ℤ, z' = z + fastShift k)
    {U : Set (Phase (a + b))} (hUO : U ⊆ O)
    {w : Fin (a + b) → ℝ} {K : (Fin (a + b) → ℝ) → Phase (a + b)}
    (hK : IsCylinderTorus H U w K) {γ τ : ℝ} (hγ : 0 < γ)
    (hτ : (a + b : ℕ) < τ) (hw : IsDiophantine γ τ w) :
    IsPhysicalTorus G w (Ψ ∘ K) ∧ range (Ψ ∘ K) = Ψ '' range K := by
  refine ⟨?_, (range_comp Ψ K)⟩
  obtain ⟨hKa, hKU, hKper, hKinj, hKder, hKsym, hKflow⟩ := hK
  have hch : IsChart 1 Ψ O := ⟨hΨa, hΨs⟩
  have hKO : ∀ θ, K θ ∈ O := fun θ => hUO (hKU θ).1
  -- the pulled-back Hamiltonian agrees with `H` near each point of `O`
  have hpb : ∀ z ∈ O, chartPullback 1 G Ψ =ᶠ[nhds z] H := fun z hz =>
    Filter.eventuallyEq_of_mem (hO.mem_nhds hz) fun y hy => by
      simpa [chartPullback] using hHG hy
  have hdiffG : ∀ θ, DifferentiableAt ℝ G (Ψ (K θ)) := fun θ => by
    rw [← chart_field_differentiableAt_iff one_pos hch G (hKO θ)]
    exact ((hKU θ).2).congr_of_eventuallyEq (hpb _ (hKO θ))
  refine ⟨hΨa.comp hKa (fun θ _ => hKO θ), hdiffG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ k
    have := hKper θ k
    simp only [comp_apply]
    rw [this]
    exact (hQ1 _ (hKO θ) _).2
  · intro θ θ' h
    obtain ⟨k, hk⟩ := hQ2 _ (hKO θ) _ (hKO θ') h.symm
    exact hKinj θ θ' k hk
  · intro θ
    have hKd : DifferentiableAt ℝ K θ := (hKa θ (mem_univ _)).differentiableAt
    have hΨd : DifferentiableAt ℝ Ψ (K θ) := (hΨa _ (hKO θ)).differentiableAt
    rw [fderiv_comp θ hΨd hKd]
    exact (hch.bijective_fderiv one_pos (hKO θ)).1.comp (hKder θ)
  · intro θ u v
    have hKd : DifferentiableAt ℝ K θ := (hKa θ (mem_univ _)).differentiableAt
    have hΨd : DifferentiableAt ℝ Ψ (K θ) := (hΨa _ (hKO θ)).differentiableAt
    rw [fderiv_comp θ hΨd hKd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hΨs _ (hKO θ), hKsym θ u v, mul_zero]
  · refine ⟨γ, τ, hγ, ?_, hw⟩
    have : ((a + b : ℕ) : ℝ) - 1 < τ := by linarith
    exact this
  · intro θ t
    have hy : ∀ s ∈ (univ : Set ℝ), DifferentiableAt ℝ (chartPullback 1 G Ψ) (K (θ + s • w)) ∧
        HasDerivAt (fun s : ℝ => K (θ + s • w))
          (hamiltonianVectorField (chartPullback 1 G Ψ) (K (θ + s • w))) s := fun s _ => by
      have hev := hpb _ (hKO (θ + s • w))
      refine ⟨((hKU _).2).congr_of_eventuallyEq hev, ?_⟩
      have := hKflow θ s
      unfold hamiltonianVectorField at this ⊢
      rw [hev.fderiv_eq]
      exact this
    have := (chart_orbit one_pos hch (fun s _ => hKO (θ + s • w)) hy) t (mem_univ _)
    exact this.2

end PlanarAssembly

end KAM.Planetary

end
