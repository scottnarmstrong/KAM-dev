/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedData
public import KAM.Kepler.Basic
public import KAM.Strip.RealRestriction
public import KAM.Strip.AnalyticTaylor

/-!
# Real restriction of a holomorphic symplectic map (P11A-P10, `stepP:p11:wr-chain`)

A holomorphic map `F` that is `ℂ`-symplectic on an open set `U` and takes real points of `U` to
real points restricts to a real analytic map `FR` that is `IsSymplecticOn 1` on
`realInclusion₂ ⁻¹' U`.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section RealChart

variable {N : ℕ}

/-- Real part of a complex phase point. -/
def p11ReC (N : ℕ) : P11Phase N →L[ℝ] Phase N :=
  (ContinuousLinearMap.pi fun i : Fin N => Complex.reCLM.comp (ContinuousLinearMap.proj i)).prodMap
    (ContinuousLinearMap.pi fun i : Fin N => Complex.reCLM.comp (ContinuousLinearMap.proj i))

theorem p11ReC_realInclusion₂ (z : Phase N) : p11ReC N (KAM.realInclusion₂ N z) = z := rfl

theorem p11_symplFormC_ofReal (u v : Phase N) :
    KAM.Canonical.symplFormC (KAM.realInclusion₂ N u) (KAM.realInclusion₂ N v) =
      (KAM.symplecticForm u v : ℂ) := by
  simp [KAM.Canonical.symplFormC, KAM.symplecticForm]

/-- A holomorphic `ℂ`-symplectic map, real on real points, restricts to a real chart. -/
theorem p11_realChart {F : P11Phase N → P11Phase N} {U : Set (P11Phase N)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {FR : Phase N → Phase N}
    (hreal : ∀ z : Phase N, KAM.realInclusion₂ N z ∈ U →
      F (KAM.realInclusion₂ N z) = KAM.realInclusion₂ N (FR z))
    (hsy : ∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ F z u) (fderiv ℂ F z v) =
      KAM.Canonical.symplFormC u v) :
    AnalyticOnNhd ℝ FR (KAM.realInclusion₂ N ⁻¹' U) ∧
      KAM.Kepler.IsSymplecticOn 1 FR (KAM.realInclusion₂ N ⁻¹' U) := by
  have hW : IsOpen (KAM.realInclusion₂ N ⁻¹' U) := hU.preimage (KAM.realInclusion₂ N).continuous
  have hFan : AnalyticOnNhd ℂ F U := KAM.analyticOnNhd_of_differentiableOn hU hF
  have heq : EqOn FR (fun z => p11ReC N (F (KAM.realInclusion₂ N z)))
      (KAM.realInclusion₂ N ⁻¹' U) := fun z hz => by
    simp only [hreal z hz, p11ReC_realInclusion₂]
  have han : AnalyticOnNhd ℝ (fun z => p11ReC N (F (KAM.realInclusion₂ N z)))
      (KAM.realInclusion₂ N ⁻¹' U) := fun z hz =>
    ((p11ReC N).analyticAt _).comp
      ((hFan _ hz).restrictScalars.comp ((KAM.realInclusion₂ N).analyticAt z))
  have hanFR : AnalyticOnNhd ℝ FR (KAM.realInclusion₂ N ⁻¹' U) := han.congr hW heq.symm
  refine ⟨hanFR, fun z hz u v => ?_⟩
  have hdF : DifferentiableAt ℂ F (KAM.realInclusion₂ N z) :=
    (hF _ hz).differentiableAt (hU.mem_nhds hz)
  have hd1 : HasFDerivAt (fun x => F (KAM.realInclusion₂ N x))
      (((fderiv ℂ F (KAM.realInclusion₂ N z)).restrictScalars ℝ).comp (KAM.realInclusion₂ N)) z :=
    hdF.hasFDerivAt.restrictScalars ℝ |>.comp z (KAM.realInclusion₂ N).hasFDerivAt
  have hdFR : HasFDerivAt FR (fderiv ℝ FR z) z :=
    (hanFR z hz).differentiableAt.hasFDerivAt
  have hd2 : HasFDerivAt (fun x => KAM.realInclusion₂ N (FR x))
      ((KAM.realInclusion₂ N).comp (fderiv ℝ FR z)) z :=
    (KAM.realInclusion₂ N).hasFDerivAt.comp z hdFR
  have hev : (fun x => F (KAM.realInclusion₂ N x)) =ᶠ[nhds z]
      fun x => KAM.realInclusion₂ N (FR x) :=
    Filter.eventually_of_mem (hW.mem_nhds hz) fun x hx => hreal x hx
  have hunique := hd1.unique (hd2.congr_of_eventuallyEq hev)
  have hcomm : ∀ w : Phase N, fderiv ℂ F (KAM.realInclusion₂ N z) (KAM.realInclusion₂ N w) =
      KAM.realInclusion₂ N (fderiv ℝ FR z w) := fun w => by
    have := congrArg (fun L => L w) hunique
    simpa using this
  have key := hsy _ hz (KAM.realInclusion₂ N u) (KAM.realInclusion₂ N v)
  rw [hcomm, hcomm, p11_symplFormC_ofReal, p11_symplFormC_ofReal] at key
  rw [one_mul]
  exact_mod_cast key

end RealChart

end KAM.Planetary

end
