/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.AssemblyData
public import KAM.Planetary.Quantitative.Zero

/-!
# Quantitative weak KAM assembly: real Hamiltonian and torus geometry (P11C-Q6)

Differentiability of the real Hamiltonian on the real domain, the transfer of a lattice torus
between Hamiltonians that agree on that (open) domain, and the location of the upstream tori
inside the real domain.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

variable {N : ℕ}

theorem p11c_asm_isOpen_domain (d : QuantitativeData N) : IsOpen (p11c_realDomain d) :=
  (p11c_zero_isOpen_nbhd d.K (2 * d.vartheta)).preimage
    ((realInclusion N).continuous.comp continuous_snd)

theorem p11c_asm_diffAt (d : QuantitativeData N) (hs : 0 < d.s) (h : (Fin N → ℂ) → ℂ)
    (f : (Fin N → ℂ) × (Fin N → ℂ) → ℂ)
    (hh : DifferentiableOn ℂ h (actionNbhd d.K (2 * d.vartheta)))
    (hf : DifferentiableOn ℂ f (complexStrip N d.s ×ˢ actionNbhd d.K (2 * d.vartheta)))
    {z : Phase N} (hz : z ∈ p11c_realDomain d) : DifferentiableAt ℝ (realHamiltonian h f) z := by
  have hU := p11c_zero_isOpen_nbhd d.K (2 * d.vartheta)
  have hS : IsOpen (complexStrip N d.s) := KAM.isOpen_complexStrip N d.s
  have hdh : DifferentiableAt ℂ h (realInclusion N z.2) := hh.differentiableAt (hU.mem_nhds hz)
  have hmem : realInclusion₂ N z ∈ complexStrip N d.s ×ˢ actionNbhd d.K (2 * d.vartheta) :=
    ⟨realInclusion_mem_complexStrip hs _, hz⟩
  have hdf : DifferentiableAt ℂ f (realInclusion₂ N z) :=
    hf.differentiableAt ((hS.prod hU).mem_nhds hmem)
  have e : realHamiltonian h f =
      fun z : Phase N => (h (realInclusion N z.2) + f (realInclusion₂ N z)).re := rfl
  rw [e]
  exact Complex.reCLM.differentiableAt.comp z
    (((hdh.restrictScalars ℝ).comp z ((realInclusion N).differentiableAt.comp z
      differentiableAt_snd)).add ((hdf.restrictScalars ℝ).comp z
      (realInclusion₂ N).differentiableAt))

/-- A lattice torus for `G` in an open set `O` is one for every `G'` agreeing with `G` on `O`. -/
theorem p11c_asm_transfer {O : Set (Phase N)} (hO : IsOpen O) {G G' : Phase N → ℝ}
    (hGG : ∀ z ∈ O, G' z = G z) {w : Fin N → ℝ} {K : (Fin N → ℝ) → Phase N}
    (hK : IsLatticeTorus angleShift G O w K) : IsLatticeTorus angleShift G' O w K := by
  obtain ⟨⟨han, hmem⟩, hper, hinj, hder, hlag, hflow⟩ := hK
  have hev : ∀ z ∈ O, G' =ᶠ[𝓝 z] G := fun z hz =>
    Filter.eventuallyEq_of_mem (hO.mem_nhds hz) hGG
  have hvf : ∀ z ∈ O, hamiltonianVectorField G' z = hamiltonianVectorField G z := fun z hz => by
    simp only [hamiltonianVectorField, (hev z hz).fderiv_eq]
  refine ⟨⟨han, fun θ => ⟨(hmem θ).1, ?_⟩⟩, hper, hinj, hder, hlag, fun θ t => ?_⟩
  · exact ((hmem θ).2).congr_of_eventuallyEq (hev _ (hmem θ).1)
  · rw [hvf _ (hmem (θ + t • w)).1]
    exact hflow θ t

end KAM.Planetary

end
