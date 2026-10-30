/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Reduction of holomorphic maps to a separable target

Blueprint-W `bpW:w1:holo-analytic-fd` (package W1-ANALYTIC), auxiliary file: source-faithful
infrastructure used by several nodes; the dependency graph is still being built.

Track K's finite-dimensional analyticity theorems assume a second-countable target. The blueprint
states the result for an arbitrary complex Banach space `F`. A holomorphic map `f` on an open
subset `U` of a second-countable space is continuous, so `f '' U` is separable, and `f` factors
through the closed complex span `F₀` of `f '' U`, a complete second-countable subspace
(`KAM.Wave.exists_separable_lift`). The lift is again holomorphic, because difference quotients
of `f` lie in `F₀`, which is closed.
-/

@[expose] public section

open Metric Set Filter Topology

namespace KAM.Wave

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Blueprint `bpW:w1:holo-analytic-fd`, separable reduction: a holomorphic map on an open set
factors through a closed, complete, second-countable complex subspace of its target, by a map
that is again holomorphic. -/
theorem exists_separable_lift [CompleteSpace F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) :
    ∃ (F₀ : Submodule ℂ F) (_ : IsClosed (F₀ : Set F)) (_ : SecondCountableTopology F₀)
      (f₀ : E → F₀), DifferentiableOn ℂ f₀ U ∧ ∀ z ∈ U, (f₀ z : F) = f z := by
  classical
  have hsep : TopologicalSpace.IsSeparable (f '' U) :=
    hf.continuousOn.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace U)
  set F₀ : Submodule ℂ F := (Submodule.span ℂ (f '' U)).topologicalClosure with hF₀
  have hcl : IsClosed (F₀ : Set F) := Submodule.isClosed_topologicalClosure _
  have hsep₀ : TopologicalSpace.IsSeparable (F₀ : Set F) := by
    have := (hsep.span (R := ℂ)).closure
    simpa [hF₀, Submodule.topologicalClosure_coe] using this
  have : SecondCountableTopology F₀ := hsep₀.secondCountableTopology
  have hmem : ∀ z ∈ U, f z ∈ F₀ := fun z hz =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hder : ∀ z ∈ U, ∀ v, fderiv ℂ f z v ∈ F₀ := by
    intro z hz v
    have hd := (hf.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    have hcob : Tendsto (fun n : ℕ => (n : ℂ)) atTop (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using tendsto_natCast_atTop_atTop
    have hlim := hd.lim v (c := fun n : ℕ => (n : ℂ)) (l := atTop)
      (by simpa using tendsto_natCast_atTop_atTop)
    refine hcl.mem_of_tendsto hlim ?_
    have h0 : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := tendsto_inv₀_cobounded.comp hcob
    have hev : ∀ᶠ n : ℕ in atTop, z + ((n : ℂ))⁻¹ • v ∈ U := by
      have : Tendsto (fun n : ℕ => z + ((n : ℂ))⁻¹ • v) atTop (𝓝 (z + (0 : ℂ) • v)) :=
        tendsto_const_nhds.add (h0.smul_const v)
      rw [zero_smul, add_zero] at this
      exact this.eventually (hU.mem_nhds hz)
    filter_upwards [hev] with n hn
    exact F₀.smul_mem _ (F₀.sub_mem (hmem _ hn) (hmem z hz))
  refine ⟨F₀, hcl, inferInstance, fun z => if h : z ∈ U then ⟨f z, hmem z h⟩ else 0, ?_, ?_⟩
  · intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hd := (hf.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    refine HasFDerivAt.differentiableAt (f' := (fderiv ℂ f z).codRestrict F₀ (hder z hz)) ?_
    rw [hasFDerivAt_iff_isLittleO] at hd ⊢
    refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
    filter_upwards [hd.def hc, hU.mem_nhds hz] with x hx hxU
    simpa [hxU, hz] using hx
  · intro z hz
    simp [hz]

end KAM.Wave
