/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.KAMInputsBase
public import KAM.Planetary.PGAssembly.ChartMem
public import KAM.Planetary.PGAssembly.FrequencyInverse

/-!
# P Part 5: the KAM hypothesis inputs, the frequency part (`bpP:p5:kam-hyp`)

The bridge `complexFrequency_realSlice` between the complex frequency map of the jets and the real
frequency formula `freq` on `V` (the design's `complexFrequency_real`), the identification of the
frequency map of `kamH` with `(2π)⁻¹` times `complexFrequency`, and the `kamH`-only parts of
`kam_hyp`: the domain inclusion, differentiability, injectivity and the Hessian bounds.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-KH.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

variable {a b : ℕ}

/-- A complex derivative at a real point, along a real direction, is the real derivative of the
real restriction. -/
theorem fderiv_complex_realSlice {n : ℕ} {F : (Fin n → ℂ) → ℂ} {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (hF : DifferentiableAt ℂ F (KAM.realInclusion n x))
    (hev : (fun y => F (KAM.realInclusion n y)) =ᶠ[𝓝 x] fun y => (f y : ℂ)) (i : Fin n) :
    fderiv ℂ F (KAM.realInclusion n x) (Pi.single i 1) =
      ((fderiv ℝ f x (Pi.single i 1) : ℝ) : ℂ) := by
  set L := fderiv ℂ F (KAM.realInclusion n x) with hL
  have h1 : HasFDerivAt (fun y => F (KAM.realInclusion n y))
      ((L.restrictScalars ℝ).comp (KAM.realInclusion n)) x :=
    (hF.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion n).hasFDerivAt
  have h2 : HasFDerivAt (fun y => (f y : ℂ))
      ((L.restrictScalars ℝ).comp (KAM.realInclusion n)) x :=
    h1.congr_of_eventuallyEq hev.symm
  have h3 : HasFDerivAt f (Complex.reCLM.comp ((L.restrictScalars ℝ).comp
      (KAM.realInclusion n))) x := by
    have := Complex.reCLM.hasFDerivAt.comp x h2
    convert this using 1
    funext y
    simp
  have h4 := Complex.ofRealCLM.hasFDerivAt.comp x h3
  have h5 := h2.unique h4
  have h6 : fderiv ℝ f x = Complex.reCLM.comp ((L.restrictScalars ℝ).comp
      (KAM.realInclusion n)) := h3.fderiv
  have hs : KAM.realInclusion n (Pi.single i (1 : ℝ)) = Pi.single i (1 : ℂ) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have := congrArg (fun T => T (Pi.single i (1 : ℝ))) h5
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    hs] at this
  rw [h6]
  show L (Pi.single i 1) = ((L (KAM.realInclusion n (Pi.single i 1))).re : ℂ)
  rw [hs]
  exact this

theorem realInclusion_mem_actionNbhd {N : ℕ} {X : Set (Fin N → ℝ)} {δ : ℝ} (hδ : 0 < δ)
    {y : Fin N → ℝ} (hy : y ∈ X) : KAM.realInclusion N y ∈ KAM.actionNbhd X δ :=
  mem_actionNbhd_iff.2 ⟨y, hy, by simpa using hδ⟩

theorem complexFast_realSlice (d : PGData a b) {I : Fin a → ℝ} (hI : I ∈ d.V) :
    complexFast d (KAM.realInclusion a I) = KAM.realInclusion a (fastFrequency d.H0 I) := by
  have hδ := (pgExtension d).delta_pos
  have hF : DifferentiableAt ℂ (pgExtension d).H0 (KAM.realInclusion a I) :=
    (pgExtension d).h0holo.differentiableAt ((isOpen_actionNbhd _ _).mem_nhds
      (realInclusion_mem_actionNbhd hδ (subset_closure hI)))
  have hev : (fun y => (pgExtension d).H0 (KAM.realInclusion a y)) =ᶠ[𝓝 I]
      fun y => (d.H0 y : ℂ) := by
    filter_upwards [d.hV.mem_nhds hI] with y hy
    exact (pgExtension d).h0real y (realInclusion_mem_actionNbhd hδ (subset_closure hy))
  funext i
  rw [complexFast, fderiv_complex_realSlice hF hev i]
  simp [fastFrequency]

theorem jpGrad_realSlice (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℝ}
    (hI : I ∈ d.V) (ξ : Fin b → ℝ) :
    jpGrad d mu (KAM.realInclusion b ξ) (KAM.realInclusion a I) = KAM.realInclusion a
      (fun i => fderiv ℝ (fun I' => secularPolynomial d.P0 d.Omega d.beta mu I' ξ) I
        (Pi.single i 1)) := by
  have hδ := (pgExtension d).delta_pos
  have hI2 : KAM.realInclusion a I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2) :=
    realInclusion_mem_actionNbhd (by linarith) (subset_closure hI)
  have hjp : DifferentiableAt ℂ (jetPolynomial d mu)
      (Fin.append (KAM.realInclusion a I) (KAM.realInclusion b ξ)) :=
    (jetPolynomial_differentiableOn d hmu).differentiableAt
      ((isOpen_jpDom d).mem_nhds (append_mem_jpDom d hI2 _))
  have hF : DifferentiableAt ℂ (fun I' : Fin a → ℂ => jetPolynomial d mu
      (Fin.append I' (KAM.realInclusion b ξ))) (KAM.realInclusion a I) :=
    DifferentiableAt.comp (g := jetPolynomial d mu)
      (f := fun I' : Fin a → ℂ => (Fin.append I' (KAM.realInclusion b ξ) : Fin (a+b) → ℂ))
      (KAM.realInclusion a I) hjp
      (hasFDerivAt_append (KAM.realInclusion b ξ) (KAM.realInclusion a I)).differentiableAt
  have hev : (fun y => jetPolynomial d mu (Fin.append (KAM.realInclusion a y)
      (KAM.realInclusion b ξ))) =ᶠ[𝓝 I]
      fun y => (secularPolynomial d.P0 d.Omega d.beta mu y ξ : ℂ) := by
    filter_upwards [d.hV.mem_nhds hI] with y hy
    simp only [jetPolynomial, blockFast_append_complex, blockSlow_append_complex,
      jetP0_real d hmu hy, jetOmega_real d hmu hy, jetBeta_real d hmu hy, secularPolynomial,
      KAM.realInclusion_apply]
    push_cast
    ring
  funext i
  exact fderiv_complex_realSlice hF hev i

/-- The real/complex frequency bridge (the design's `complexFrequency_real`): on the real slice
over `V` the complex frequency map is the real frequency formula. -/
theorem complexFrequency_realSlice (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a+b) → ℝ} (hJ : blockFast J ∈ d.V) :
    complexFrequency d mu (KAM.realInclusion (a+b) J) =
      KAM.realInclusion (a+b) (freq d.H0 d.P0 d.Omega d.beta mu J) := by
  have hδ := (pgExtension d).delta_pos
  have hI2 : blockFast (KAM.realInclusion (a+b) J) ∈
      KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2) :=
    realInclusion_mem_actionNbhd (by linarith) (subset_closure hJ)
  have hf : blockFast (KAM.realInclusion (a+b) J) = KAM.realInclusion a (blockFast J) := rfl
  have hs : blockSlow (KAM.realInclusion (a+b) J) = KAM.realInclusion b (blockSlow J) := rfl
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · have h := congrFun (blockFast_complexFrequency d hmu hI2) k
    rw [hf, hs, complexFast_realSlice d hJ, jpGrad_realSlice d hmu hJ] at h
    simp only [blockFast] at h
    rw [h]
    simp [freq, Fin.append_left]
  · have h := congrFun (blockSlow_complexFrequency d hmu hI2) k
    rw [hf, hs] at h
    simp only [blockSlow] at h
    rw [h]
    simp only [freq, Fin.append_right, jpTheta, slowFrequency, Pi.smul_apply, Pi.add_apply,
      Matrix.mulVec, dotProduct, jetOmega_real d hmu hJ, jetBeta_real d hmu hJ,
      KAM.realInclusion_apply, smul_eq_mul]
    push_cast
    rfl

end KAM.Planetary

end
