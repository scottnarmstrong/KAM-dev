/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.RealFlow.AnalyticCompact

/-!
# Planar quartic torsion: compact analytic flow on a finite-dimensional space (package T9)

Blueprint P, Part 11b (`bpP:p11b:fl-an`).  The compact common-neighbourhood analytic flow of
package R2 (`p11c_analytic_flow_compact_nbhd`, stated on `Fin n → ℝ`) is transported along a
continuous linear equivalence to an arbitrary finite-dimensional real normed space; the parameter
space `(Fin 2 → ℝ) × Phase 2` of the augmented field is the case of interest.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace KAM.Planetary

open KAM.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `p11c_analytic_flow_compact_nbhd` for a finite-dimensional real normed space. -/
theorem p11cQ_flow_compact_nbhd {f : E → E} {W : Set E} (hW : IsOpen W)
    (hf : AnalyticOnNhd ℝ f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ U ⊆ W ∧ ∃ T : ℝ, 0 < T ∧ ∃ Φ : ℝ → E → E,
      AnalyticOnNhd ℝ (fun u : ℝ × E => Φ u.1 u.2) (Ioo (-T) T ×ˢ U) ∧
      ∀ y ∈ U, Φ 0 y = y ∧ IsSolutionIn f W (Ioo (-T) T) (fun t => Φ t y) := by
  set e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
    with he
  set f' : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) → ℝ :=
    fun v => e (f (e.symm v)) with hf'
  set W' : Set (Fin (Module.finrank ℝ E) → ℝ) := e.symm ⁻¹' W with hW'
  have hW'o : IsOpen W' := hW.preimage e.symm.continuous
  have hf'a : AnalyticOnNhd ℝ f' W' := fun v hv =>
    (e.analyticAt _).comp ((hf _ hv).comp (e.symm.analyticAt v))
  have hK' : IsCompact (e '' K) := hK.image e.continuous
  have hKW' : e '' K ⊆ W' := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [hW'] using hKW hx
  obtain ⟨U', hU'o, hKU', hUW', T, hT, Φ', han, hsol⟩ :=
    p11c_analytic_flow_compact_nbhd hW'o hf'a hK' hKW'
  refine ⟨e ⁻¹' U', hU'o.preimage e.continuous, fun x hx => hKU' ⟨x, hx, rfl⟩,
    fun y hy => ?_, T, hT, fun t y => e.symm (Φ' t (e y)), ?_, fun y hy => ?_⟩
  · have := hUW' hy
    simpa [hW'] using this
  · intro z hz
    have h1 := han (z.1, e z.2) ⟨hz.1, hz.2⟩
    have h2 : AnalyticAt ℝ (fun w : ℝ × E => (w.1, e w.2)) z :=
      AnalyticAt.prod analyticAt_fst ((e.analyticAt _).comp analyticAt_snd)
    exact (e.symm.analyticAt _).comp
      (AnalyticAt.comp (g := fun u : ℝ × (Fin (Module.finrank ℝ E) → ℝ) => Φ' u.1 u.2)
        (f := fun w : ℝ × E => (w.1, e w.2)) h1 h2)
  · obtain ⟨h0, hs⟩ := hsol (e y) hy
    refine ⟨by simp [h0], fun t ht => ?_⟩
    obtain ⟨hm, hd⟩ := hs t ht
    refine ⟨hm, ?_⟩
    have h2 := e.symm.hasFDerivAt.comp_hasDerivAt t hd
    exact h2.congr_deriv (by simp [hf'])

end KAM.Planetary

end
