/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.Constants
import KAM.Strip.Bridges
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Part 11 (N11-E3): the real/complex Hessian bridge and the signed Hessian bounds

`realPart_hessian_apply` identifies the real Hessian of `realPart h` at a real point with the
real part of the complex Hessian of a holomorphic `h`; `FastConvex.toRealFastConvex` restricts the
complex upper Hessian bound to the real slice; `hessian_at_sign` and `hessian` give the signed
convexity data of `signedH`-type Hamiltonians `σ h / (2π)` (here stated for the scaled function
`σ h/(2π)` directly, so the module does not depend on `Domain`).
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`, lemma `bpN:p11:hessian`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace KAM.Nekhoroshev

variable {n k : ℕ}

private theorem hessHelper_real_fderiv {F : (Fin n → ℂ) → ℂ} {J : Fin n → ℝ}
    (hF : DifferentiableAt ℂ F (KAM.realInclusion n J)) (v : Fin n → ℝ) :
    fderiv ℝ (fun I : Fin n → ℝ => (F (KAM.realInclusion n I)).re) J v =
      (fderiv ℂ F (KAM.realInclusion n J) (KAM.realInclusion n v)).re := by
  have h2 : HasFDerivAt (fun y => F (KAM.realInclusion n y))
      (((fderiv ℂ F (KAM.realInclusion n J)).restrictScalars ℝ).comp (KAM.realInclusion n)) J :=
    (hF.hasFDerivAt.restrictScalars ℝ).comp J (KAM.realInclusion n).hasFDerivAt
  have h3 : HasFDerivAt (fun y => (F (KAM.realInclusion n y)).re)
      (Complex.reCLM.comp
        (((fderiv ℂ F (KAM.realInclusion n J)).restrictScalars ℝ).comp (KAM.realInclusion n))) J :=
    Complex.reCLM.hasFDerivAt.comp J h2
  rw [h3.fderiv]
  rfl

private theorem hessHelper_contDiffAt {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {F : (Fin n → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F Ω) {I : Fin n → ℝ} (hI : KAM.realInclusion n I ∈ Ω) :
    ContDiffAt ℝ 2 (fun J : Fin n → ℝ => (F (KAM.realInclusion n J)).re) I := by
  have h1 : ContDiffAt ℂ 2 F (KAM.realInclusion n I) :=
    ((KAM.holomorphic_regularity_of_finiteDimensional hΩ hF).2.2.1.contDiffAt
      (hΩ.mem_nhds hI)).of_le (by norm_cast)
  have h2 : ContDiffAt ℝ 2 F (KAM.realInclusion n I) := h1.restrict_scalars ℝ
  have h3 := h2.comp I (KAM.realInclusion n).contDiff.contDiffAt
  exact Complex.reCLM.contDiff.contDiffAt.comp I h3

/-- For `h` holomorphic on an open set containing the real point `I`, the real Hessian of
`realPart h` is the real part of the complex Hessian on real vectors. -/
theorem realPart_hessian_apply {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h Ω) {I : Fin n → ℝ} (hI : KAM.realInclusion n I ∈ Ω)
    (u v : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (realPart h)) I u v =
      (fderiv ℂ (fderiv ℂ h) (KAM.realInclusion n I) (KAM.realInclusion n u)
        (KAM.realInclusion n v)).re := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional hΩ hh
  have hcd : ContDiffAt ℝ 2 (realPart h) I := hessHelper_contDiffAt hΩ hh hI
  have hdd : DifferentiableAt ℝ (fderiv ℝ (realPart h)) I :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : (fun J => fderiv ℝ (realPart h) J v) =ᶠ[𝓝 I]
      fun J => (fderiv ℂ h (KAM.realInclusion n J) (KAM.realInclusion n v)).re := by
    have hopen : ∀ᶠ J in 𝓝 I, KAM.realInclusion n J ∈ Ω :=
      (KAM.realInclusion n).continuous.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hI)
    filter_upwards [hopen] with J hJ
    exact hessHelper_real_fderiv (hh.differentiableAt (hΩ.mem_nhds hJ)) v
  have hdh : DifferentiableAt ℂ (fderiv ℂ h) (KAM.realInclusion n I) :=
    (hreg.1).differentiableAt (hΩ.mem_nhds hI)
  have hd1 : HasFDerivAt (fun J => fderiv ℝ (realPart h) J v)
      ((fderiv ℝ (fderiv ℝ (realPart h)) I).flip v) I := by
    have := hdd.hasFDerivAt.clm_apply (hasFDerivAt_const v I)
    simpa using this
  have hF' : DifferentiableAt ℂ (fun w => fderiv ℂ h w (KAM.realInclusion n v))
      (KAM.realInclusion n I) :=
    hdh.clm_apply (differentiableAt_const _)
  have h2 := hessHelper_real_fderiv hF' u
  have h3 : fderiv ℝ (fun J => fderiv ℝ (realPart h) J v) I u =
      fderiv ℝ (fun J => (fderiv ℂ h (KAM.realInclusion n J) (KAM.realInclusion n v)).re) I u := by
    rw [hev.fderiv_eq]
  have h4 : fderiv ℝ (fun J => fderiv ℝ (realPart h) J v) I u =
      fderiv ℝ (fderiv ℝ (realPart h)) I u v := by
    rw [hd1.fderiv]; rfl
  have h5 : fderiv ℂ (fun w => fderiv ℂ h w (KAM.realInclusion n v)) (KAM.realInclusion n I)
      (KAM.realInclusion n u) =
      fderiv ℂ (fderiv ℂ h) (KAM.realInclusion n I) (KAM.realInclusion n u)
        (KAM.realInclusion n v) := by
    have := hdh.hasFDerivAt.clm_apply (hasFDerivAt_const (KAM.realInclusion n v)
      (KAM.realInclusion n I))
    rw [this.fderiv]
    simp
  rw [← h4, h3]
  exact h2.trans (by rw [h5])

end KAM.Nekhoroshev

end
