/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingFourier
public import KAM.Planetary.Hamiltonian.HolChart

/-!
# P Part 5: conjugating the P2 map (`stepP:p5:av-dict`)

For a P2 map `Ψ` on the half-domain, `pgAvPsi Ψ = T ∘ Ψ ∘ T⁻¹` is holomorphic and injective on
`averagingDomain`, maps it into the extension domain, commutes with the physical lattice shifts,
preserves the real slice and, with `T` conformally symplectic of factor `2π`, is again symplectic
with factor one.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ} {Ψ : CPhase (a+b) → CPhase (a+b)}

/-- The P2 half-domain. -/
abbrev avgV (d : PGData a b) (r mu : ℝ) : Set (CPhase (a+b)) :=
  oscDom (checkedCore d r mu) ((params d r mu).rhoBar/2) (pgOscEpsilon d/2) (pgOscEpsilon d/2)
    (pgOscWidth d/6)

theorem avg_diff (h : admissible d (pgRstar d) r mu)
    (hΨ : DifferentiableOn ℂ Ψ (avgV d r mu)) :
    DifferentiableOn ℂ (pgAvPsi Ψ) (averagingDomain d r mu) := by
  have : DifferentiableOn ℂ (Ψ ∘ pgOscUnnormalize) (averagingDomain d r mu) :=
    hΨ.comp differentiable_pgOscUnnormalize.differentiableOn
      (fun z hz => (mem_averagingDomain_iff h).1 hz)
  exact differentiable_pgOscNormalize.comp_differentiableOn this

theorem avg_inj (h : admissible d (pgRstar d) r mu) (hΨ : InjOn Ψ (avgV d r mu)) :
    InjOn (pgAvPsi Ψ) (averagingDomain d r mu) := by
  intro z hz z' hz' heq
  have h1 := pgOscNormalize_injective heq
  exact pgOscUnnormalize_injective
    (hΨ ((mem_averagingDomain_iff h).1 hz) ((mem_averagingDomain_iff h).1 hz') h1)

theorem avg_maps (h : admissible d (pgRstar d) r mu)
    (hΨ : MapsTo Ψ (avgV d r mu) (oscDom (checkedCore d r mu) (params d r mu).rhoBar
      (pgOscEpsilon d) (pgOscEpsilon d) (pgOscWidth d))) :
    MapsTo (pgAvPsi Ψ) (averagingDomain d r mu) (extensionDomain d (pgExtension d).delta) := by
  intro z hz
  exact normalize_mem_extensionDomain h
    (by linarith [av_rhoBar_lt_delta h, (pgExtension d).delta_pos]) le_rfl
    (hΨ ((mem_averagingDomain_iff h).1 hz))

theorem avg_periodic (h : admissible d (pgRstar d) r mu)
    (hp : ∀ z ∈ avgV d r mu, ∀ k : Fin a → ℤ,
      Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) =
        Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) :
    ∀ z ∈ averagingDomain d r mu, ∀ k : Fin a → ℤ,
      pgAvPsi Ψ (z + KAM.realInclusion₂ (a+b) (fastShift k)) =
        pgAvPsi Ψ z + KAM.realInclusion₂ (a+b) (fastShift k) := by
  intro z hz k
  have hy := (mem_averagingDomain_iff h).1 hz
  unfold pgAvPsi
  rw [pgOscUnnormalize_add, pgOscUnnormalize_lattice,
    show ((Fin.append (fun i => (k i : ℂ)) (0 : Fin b → ℂ), 0) : CPhase (a+b)) =
      (Fin.append (fun i => (k i : ℂ)) 0, 0) from rfl, hp _ hy k, pgOscNormalize_add,
    pgOscNormalize_lattice]

theorem avg_real_mem (h : admissible d (pgRstar d) r mu)
    (hr : ∀ x : Phase (a+b), KAM.realInclusion₂ (a+b) x ∈ avgV d r mu →
      Ψ (KAM.realInclusion₂ (a+b) x) ∈ range (KAM.realInclusion₂ (a+b))) :
    ∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ averagingDomain d r mu →
      pgAvPsi Ψ (KAM.realInclusion₂ (a+b) z) ∈ range (KAM.realInclusion₂ (a+b)) := by
  intro z hz
  have hy := (mem_averagingDomain_iff h).1 hz
  rw [pgOscUnnormalize_real] at hy
  obtain ⟨w, hw⟩ := hr _ hy
  unfold pgAvPsi
  rw [pgOscUnnormalize_real, ← hw]
  exact pgOscNormalize_mem_range w

theorem realAverageMap_spec {A : PGAveraging n} {z : Phase n}
    (h : A.Psi (KAM.realInclusion₂ n z) ∈ range (KAM.realInclusion₂ n)) :
    A.Psi (KAM.realInclusion₂ n z) = KAM.realInclusion₂ n (realAverageMap A z) := by
  obtain ⟨w, hw⟩ := h
  have : realAverageMap A z = w := by
    unfold realAverageMap
    rw [← hw]
    simp
  rw [this, hw]

theorem symplFormC_normalize (u v : CPhase (a+b)) :
    KAM.Canonical.symplFormC (pgOscNormalize u) (pgOscNormalize v) =
      (2*Real.pi:ℂ) * KAM.Canonical.symplFormC u v := by
  have := (pg_osc_normalization (a := a) (b := b)).2 0 u v
  rw [pgOscNormalize_eq_fun, ContinuousLinearMap.fderiv] at this
  rw [pgOscNormalize_eq, pgOscNormalize_eq]
  exact this

theorem symplFormC_unnormalize (u v : CPhase (a+b)) :
    KAM.Canonical.symplFormC (pgOscUnnormalize u) (pgOscUnnormalize v) =
      (2*Real.pi:ℂ)⁻¹ * KAM.Canonical.symplFormC u v := by
  have h2 : (2*Real.pi:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have := symplFormC_normalize (pgOscUnnormalize u) (pgOscUnnormalize v)
  rw [pgOscNormalize_unnormalize, pgOscNormalize_unnormalize] at this
  rw [this]; field_simp

theorem avg_sympl (h : admissible d (pgRstar d) r mu)
    (hΨ : DifferentiableOn ℂ Ψ (avgV d r mu))
    (hs : ∀ z ∈ avgV d r mu, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) =
      KAM.Canonical.symplFormC u v) :
    ∀ z ∈ averagingDomain d r mu, ∀ u v, KAM.Canonical.symplFormC
      (fderiv ℂ (pgAvPsi Ψ) z u) (fderiv ℂ (pgAvPsi Ψ) z v) =
      ((1:ℝ):ℂ) * KAM.Canonical.symplFormC u v := by
  intro z hz u v
  have hy := (mem_averagingDomain_iff h).1 hz
  have hΨa : DifferentiableAt ℂ Ψ (pgOscUnnormalize z) :=
    hΨ.differentiableAt ((isOpen_oscDom _ _ _ _ _).mem_nhds hy)
  have hder : HasFDerivAt (pgAvPsi Ψ) ((oscNormCLM a b).comp ((fderiv ℂ Ψ (pgOscUnnormalize z)).comp
      (oscUnnormCLM a b))) z := by
    have h1 : HasFDerivAt pgOscUnnormalize (oscUnnormCLM a b) z := by
      rw [pgOscUnnormalize_eq_fun]; exact (oscUnnormCLM a b).hasFDerivAt
    have h2 : HasFDerivAt Ψ (fderiv ℂ Ψ (pgOscUnnormalize z)) (pgOscUnnormalize z) :=
      hΨa.hasFDerivAt
    have h3 : HasFDerivAt pgOscNormalize (oscNormCLM a b) (Ψ (pgOscUnnormalize z)) := by
      rw [pgOscNormalize_eq_fun]; exact (oscNormCLM a b).hasFDerivAt
    exact h3.comp z (h2.comp z h1)
  rw [hder.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← pgOscNormalize_eq, ← pgOscNormalize_eq, symplFormC_normalize, ← pgOscUnnormalize_eq,
    ← pgOscUnnormalize_eq, hs _ hy, symplFormC_unnormalize]
  have h2 : (2*Real.pi:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp
  simp

end KAM.Planetary

end
