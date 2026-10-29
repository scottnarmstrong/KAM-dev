/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.Setting
public import KAM.Iso.Confinement.RealHam

/-!
# Part 5: invariance of the tori

Blueprint `bpI:p5:invariance`.
For a torus `K` of the output of `bpI:p3:tori` (`TorusOutput`) whose real actions lie in `B`:

* `torus_flow` (step `inv-sol`): `t ↦ k(θ₁ + t ωt)`, `k = Re K ι`, solves `ẋ = X_ℝ(x)` in
  `W_B = ℝ² × B` on all of `ℝ`.
* `torus_invariant` (`bpI:p5:invariance`): `𝒯 = k(ℝ²) ⊆ W_B` and `𝒯` is invariant for
  `(X_ℝ, W_B)`, by the uniqueness theorem `KAM.ODE.gen_uniqueness`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace KAM.Iso.Confinement

open KAM KAM.ODE

section Invariance

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ}
  {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε C_K E : ℝ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
  {I ωt : Fin 2 → ℝ}

/-- The width `ρ∞ = min {s₀, 1} / 8` is positive for `s₀ > 0`. -/
private theorem rhoInf_pos (hs : 0 < s₀) : 0 < rhoInf s₀ := by
  unfold rhoInf
  have := lt_min hs one_pos
  positivity

/-- Real points of the strip: the invariance equation holds at `ι θ`, `θ ∈ ℝ²`. -/
private theorem torus_invarianceError_real (hb : BaseData B s₀ r₀ h)
    (T : TorusOutput h f ε C_K s₀ E K I ωt) (θ : Fin 2 → ℝ) :
    hamiltonianVectorFieldℂ (totalH h f) (K (realInclusion 2 θ)) =
      fderiv ℂ K (realInclusion 2 θ) (fun i => (ωt i : ℂ)) :=
  sub_eq_zero.1 (T.invariant _ (realInclusion_mem_complexStrip (rhoInf_pos hb.hs) θ))

/-- Step `inv-sol`: `t ↦ k(θ₁ + t ωt)` is a solution of `X_ℝ` in `W_B` on all of `ℝ`, if the torus
has actions in `B`. -/
theorem torus_flow (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    (T : TorusOutput h f ε C_K s₀ E K I ωt) (hmem : ∀ θ, (realRestriction K θ).2 ∈ B)
    (θ₁ : Fin 2 → ℝ) :
    IsSolutionIn (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) univ
      (fun t : ℝ => realRestriction K (θ₁ + t • ωt)) := by
  intro t _
  refine ⟨⟨mem_univ _, hmem _⟩, ?_⟩
  obtain ⟨hk, hkD⟩ := realRestriction_fderiv (rhoInf_pos hb.hs) T.holo T.real (θ₁ + t • ωt)
  have hγ : HasDerivAt (fun t : ℝ => θ₁ + t • ωt) ωt t := by
    simpa using ((hasDerivAt_id t).smul_const ωt).const_add θ₁
  have hcomp := hk.hasFDerivAt.comp_hasDerivAt t hγ
  refine hcomp.congr_deriv ?_
  refine realInclusion₂_injective 2 ?_
  symm
  rw [realHam_field_eq hb hf (subset_realAct hb.hr (hmem _)), hkD ωt,
    ← isRealOnReals_iff.mp T.real, torus_invarianceError_real hb T]
  rfl

/-- `ℝ² × U` is open. -/
private theorem isOpen_prod_realAct' (B : Set (Fin 2 → ℝ)) (r₀ : ℝ) :
    IsOpen ((univ : Set (Fin 2 → ℝ)) ×ˢ realAct B r₀) :=
  isOpen_univ.prod (isOpen_realAct B r₀)

/-- `bpI:p5:invariance`: `𝒯 ⊆ W_B` and `𝒯` is invariant for `(X_ℝ, W_B)`; `hmem` is the output of
`torus_graph_mem`. -/
theorem torus_invariant (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    (T : TorusOutput h f ε C_K s₀ E K I ωt) (hmem : ∀ θ, (realRestriction K θ).2 ∈ B) :
    range (realRestriction K) ⊆ univ ×ˢ B ∧
      IsInvariantSet (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B)
        (range (realRestriction K)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨θ, rfl⟩
    exact ⟨mem_univ _, hmem θ⟩
  · intro J y hJ hy t₁ ht₁ hyt t ht
    obtain ⟨θ, hθ⟩ := hyt
    have hW := isOpen_prod_realAct' B r₀
    have hsub : (univ : Set (Fin 2 → ℝ)) ×ˢ B ⊆ univ ×ˢ realAct B r₀ :=
      prod_mono subset_rfl (subset_realAct hb.hr)
    have hmono : ∀ {w : ℝ → P2},
        IsSolutionIn (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) J w →
        IsSolutionIn (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ realAct B r₀) J w :=
      fun hw s hs => ⟨hsub (hw s hs).1, (hw s hs).2⟩
    have hF : ContDiffOn ℝ 1 (hamiltonianVectorField (realHamiltonian h f))
        (univ ×ˢ realAct B r₀) :=
      ham_smooth_c1 hW ((realHam_contDiffOn hb hf).of_le (by norm_cast))
    have hx := torus_flow hb hf T hmem (θ - t₁ • ωt)
    have hx0 : realRestriction K ((θ - t₁ • ωt) + t₁ • ωt) = y t₁ := by
      rw [sub_add_cancel]; exact hθ
    have := gen_uniqueness hW hF hJ ht₁ (hmono hy) (hmono (hx.mono (subset_univ J)))
      hx0.symm ht
    exact ⟨_, this.symm⟩

end Invariance

end KAM.Iso.Confinement
