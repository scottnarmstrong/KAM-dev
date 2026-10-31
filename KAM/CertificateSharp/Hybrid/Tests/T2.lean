/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Iso
public import KAM.CertificateSharp.V2.Tests.L1Toy

/-!
# The hybrid checker in the kernel, on the toy T2

The witness is the producer's `docs/campaign/design/hybrid/hybrid-T2.json` (format v1): the step
`ΔK̂ = 0` at `s₁ = s = 2`, the restart at `ρ₁ = ρ = 9` with `μ₁ = 0.00999999`, `params1` and
`witness1` rounded upward from the transferred numbers, the sites of the base run reused.

Two deviations from the file. The base certificate is `toyCert2H`, the toy `toyCert2` with the
file's `base.params` (the toy's own parameters except the outer displacement claim
`disp = 1.6·10⁻⁴²`, against the toy's `1.9·10⁻²⁶`; no landed sub-check reads `disp`). The three
weights of `step.weights` fail `checkWeight` (they are below `ratExpUp (2 piUpQ ρ) 8 24`, by
`5·10⁻⁶` relative at `ρ = 9`); the test takes the ceilings of `ratExpUp` (at `ρ = 9`, the toy's
weight).

Every check is a kernel computation of its own (`decide +kernel`); `toyHyb_passes` assembles them
with the landed sub-checks and the base claim, and `toyCert2H_hybrid_torus` is the soundness theorem
at the reference frequency, through `iso_g1_hybrid_R`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Hybrid

open KAM.Certificate KAM.CertificateSharp.V2

/-- `base.params` of `hybrid-T2.json`: the toy's, with the outer displacement claim. -/
def toyParamsH : CertParams := { toyCert2.params with disp := 1602620091523 / 10 ^ 54 }

/-- The base certificate of the hybrid test: the toy with `toyParamsH`. -/
def toyCert2H : TorusCertificate 2 ℚ := { toyCert2 with params := toyParamsH }

/-- The zero real polynomial. -/
def toyZeroP : CertRealPoly ℚ := ⟨0, []⟩

/-- The step of T2: `ΔK̂ = 0`. -/
def toyStepQ : CertEmbedding ℚ := ⟨[0, 0], [toyZeroP, toyZeroP], [0, 0], [toyZeroP, toyZeroP]⟩

/-- `step` of `hybrid-T2.json`. -/
def toyHybStep : HybStep where
  dK := toyStepQ
  s1 := 2
  W1 := ⟨9, 3620571072184847796340984⟩
  Winf := ⟨1, 536⟩
  WT := ⟨8, 6761204449081709109867⟩
  cl :=
    { d0 := 0, dinf := 0, d1 := 0, d1t := 0, d0R := 0, d1R := 0, d1tR := 0
      lE := 1 / 3118000000000000000000000000000000000000000
      dE0 := 1 / 1559000000000000000000000000000000000000000, o0 := 0
      dE0R := 1 / 1559000000000000000000000000000000000000000, o0R := 0, o1 := 0, o1R := 0 }
  lH := 0
  dw := 0

/-- `restart.params1` of `hybrid-T2.json`. -/
def toyParams1 : CertParams where
  tau := 1
  rho := 9
  rhoInf := 1
  M := 297 / 100
  σK := 296999999 / 100000000
  σB := 296999999 / 100000000
  σT := 2969999990001 / 1000000000000
  μ := 999999 / 100000000
  γbar := 1 / 42
  σω := 3
  nuRay := 49 / 100
  γ := 1 / 42
  s := 2
  err := 3207184092367 / 10000000000000000000000000000000000000000000000000000000
  E0 := 0
  disp := 1602620091523 / 1000000000000000000000000000000000000000000000000000000

/-- `restart.witness1` of `hybrid-T2.json` (the sites are the base run's). -/
def toyWit1 : RefinedWitR where
  base :=
    { core := { toyRefinedWit.core with Xs := 117493733 / 200000000, t := 1100000000001 / 10 ^ 12 }
      R := { toyRefinedWit.R with bT := 1010000000001 / 10 ^ 12 }
      κ := toyRefinedWit.κ
      sites := toyRefinedWit.sites }
  bF := 1 / 1000
  bT := 1 / 1000

/-- **The hybrid witness of T2.** -/
def toyHybWit : HybWit where
  R0 := toyRefinedWit.R
  step := toyHybStep
  p1 := toyParams1
  w1 := toyWit1

theorem toyHyb_transfer : transferOk 2 toyCert2H.params toyCert2H.freqBox toyHybWit = true := by
  decide +kernel

theorem toyHyb_weights : hybWeightsOk toyCert2H toyHybStep toyParams1.rho toyParams1.rhoInf
    (toyHybWit.ρT 2 toyCert2H.freqBox) = true := by decide +kernel

theorem toyHyb_poly : hybPolyOk (n := 2) toyHybStep toyCert2H.piEnc = true := by decide +kernel

theorem toyHyb_omega : hybOmegaOk toyCert2H toyHybStep = true := by decide +kernel

theorem toyHyb_cauchy :
    hybCauchyOk toyCert2H toyHybStep (toyHybWit.ρT 2 toyCert2H.freqBox) = true := by decide +kernel

theorem toyHyb_comp : hybCompOk toyCert2H toyHybStep = true := by decide +kernel

theorem toyHyb_dw :
    decide (|toyHybStep.s1 - toyCert2H.params.s| * boxNormUp toyCert2H.freqBox ≤ toyHybStep.dw) =
      true := by decide +kernel

theorem toyHyb_core : refinedCoreR 2 toyParams1 toyCert2H.freqBox toyWit1 = true := by
  decide +kernel

/-- The hybrid check on T2, from its parts. -/
theorem toyHyb_check : checkHybrid toyCert2H toyHybWit = true := by
  simp only [checkHybrid, hybStepOk, Bool.and_eq_true]
  exact ⟨⟨toyHyb_transfer, ⟨⟨⟨⟨toyHyb_weights, toyHyb_poly⟩, toyHyb_omega⟩, toyHyb_cauchy⟩,
    toyHyb_comp⟩, toyHyb_dw⟩, toyHyb_core⟩

section Disp

variable {n : ℕ} {α : Type} [CertArith α]

/-- No landed sub-check reads the displacement claim. -/
theorem landedBase_check_disp (c : TorusCertificate n α) (d : ℚ) :
    landedBase.check { c with params := { c.params with disp := d } } = landedBase.check c := rfl

omit [CertArith α] in
theorem checkHamClaim_disp (c : TorusCertificate n α) (d : ℚ) (R : RefClaim) :
    checkHamClaim { c with params := { c.params with disp := d } } R = checkHamClaim c R := rfl

theorem checkFrameMajorants_disp (c : TorusCertificate n α) (d : ℚ) (b : FrameBounds) :
    checkFrameMajorants { c with params := { c.params with disp := d } } b =
      checkFrameMajorants c b := rfl

end Disp

/-- The landed sub-checks, the Hamiltonian pass and the frame majorants of `toyCert2H` are those
of `toyCert2` (`L1Toy`, `Refined`). -/
theorem toyCert2H_base : landedBase.check toyCert2H = true :=
  (landedBase_check_disp toyCert2 _).trans L1.toyCert2_base

theorem toyCert2H_hamClaim : checkHamClaim toyCert2H toyRefinedWit.R = true :=
  (checkHamClaim_disp toyCert2 _ _).trans toyCert2_hamClaim

theorem toyCert2H_frame :
    checkFrameMajorants toyCert2H (toyRefinedWit.R.frame toyCert2H.freqBox) = true :=
  (checkFrameMajorants_disp toyCert2 _ _).trans L1.toyCert2_frame

/-- **The whole v2 certifier on T2, through the hybrid route.** -/
theorem toyHyb_passes : checkTorusCertificateV2 routeHybrid toyCert2H toyHybWit = true := by
  have h : hybTest toyCert2H toyHybWit = true := by
    simp only [hybTest, Bool.and_eq_true]
    exact ⟨⟨toyCert2H_hamClaim, toyCert2H_frame⟩, toyHyb_check⟩
  rw [checkTorusCertificateV2_routeHybrid, toyCert2H_base, h]
  rfl

/-- The same through the combined engine, naming the route. -/
theorem toyHyb_routeV2Hyb_passes :
    checkTorusCertificateV2 routeV2Hyb toyCert2H (Sum.inr (Sum.inr toyHybWit)) = true :=
  (checkTorusCertificateV2_routeV2Hyb_hybrid _ _).trans toyHyb_passes

/-- **The toy torus through the hybrid route**, within `1.6·10⁻⁴²` of `K̂` (the toy's own claim
is `1.9·10⁻²⁶`). -/
theorem toyCert2H_hybrid_torus : CertifiedTorus toyCert2H ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeHybrid toyHyb_passes toyCert2_freq (by
    have h : ((toyCert2H.params.γ : ℚ) : ℝ) = 1 / 42 := by
      rw [show toyCert2H.params.γ = 1 / 42 by decide +kernel]; norm_num
    have ht : ((toyCert2H.params.tau : ℕ) : ℝ) = 1 := by
      rw [show toyCert2H.params.tau = 1 by decide +kernel]; norm_num
    rw [h, ht]
    exact lunarNuMinus_half_isDiophantine)

/-- A claim `dE0` below the Cauchy bound `n e/(ρ − ρT)` is rejected. -/
theorem toyHyb_cauchy_rejects : hybCauchyOk toyCert2H
    { toyHybStep with cl := { toyHybStep.cl with dE0 := toyHybStep.cl.lE } }
    (toyHybWit.ρT 2 toyCert2H.freqBox) = false := by decide +kernel

/-- A restart ray budget above `ν − d_ω` is rejected. -/
theorem toyHyb_transfer_rejects : transferOk 2 toyCert2H.params toyCert2H.freqBox
    { toyHybWit with p1 := { toyParams1 with nuRay := 1 / 2 } } = false := by
  decide +kernel

/-- An outer displacement below `max {dinf, d_ω} + disp₁` is rejected. -/
theorem toyHyb_disp_rejects : transferOk 2 toyCert2H.params toyCert2H.freqBox
    { toyHybWit with p1 := { toyParams1 with disp := 2 * toyParams1.disp } } = false := by
  decide +kernel

end KAM.CertificateSharp.Hybrid

end
