/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FrequencyInvBounds
public import KAM.Planetary.PGAssembly.FrequencySchur

/-!
# P Part 5: complex injectivity and row-wise inverse bounds (`bpP:p5:freq-inj`)

`freq_inj`: for `0 < mu ≤ muStar` the complex frequency map is injective on the analytic domain
(fast lower Lipschitz bound plus the slow affine formula, `freq_injOn`), and its derivative is a
continuous linear equivalence with the four bounds of the source (`jacobian_bounds`; invertibility
by finite dimension). The block inversion formula of the source is `schur_inverse_blocks`
(`FrequencySchur`); the row-wise bounds are proved directly on vectors in `FrequencyInvBounds`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FI.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

variable {a b : ℕ}

theorem freq_injOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 (pgAnalytic d).muStar) :
    InjOn (complexFrequency d mu) (analyticDomain d (pgAnalytic d)) := by
  have hspec := pgAnalytic_spec d
  set p := pgAnalytic d with hp
  obtain ⟨hρ0, hρδ, hc0, hM0, hAN, hLN, hLB, hμ0, hμ1, hμ2, -, -, -, -, -, -, e3, -, e5, hLNAN, -,
    hlow, -, hlip1, hlip2, -, hbeta, -⟩ := hspec
  have hδ := (pgExtension d).delta_pos
  have hmu0 : 0 < mu := hmu.1
  have hmuμ : mu ≤ p.muStar := hmu.2
  have hmu' : mu ∈ Icc 0 d.mu0 := ⟨hmu0.le, hmuμ.trans hμ2⟩
  intro J hJ J' hJ' heq
  have hI : blockFast J ∈ KAM.actionNbhd (closure d.V) p.rho := hJ.1
  have hI' : blockFast J' ∈ KAM.actionNbhd (closure d.V) p.rho := hJ'.1
  have hI2 := mem_actionNbhd_mono (by linarith : p.rho ≤ (pgExtension d).delta / 2) hI
  have hI2' := mem_actionNbhd_mono (by linarith : p.rho ≤ (pgExtension d).delta / 2) hI'
  have hξ : ‖blockSlow J‖ ≤ 1 := hJ.2.le
  have hξ' : ‖blockSlow J'‖ ≤ 1 := hJ'.2.le
  set I := blockFast J
  set I' := blockFast J'
  set ξ := blockSlow J
  set ξ' := blockSlow J'
  have hF := congrArg blockFast heq
  have hS := congrArg blockSlow heq
  rw [blockFast_complexFrequency d hmu' hI2, blockFast_complexFrequency d hmu' hI2'] at hF
  rw [blockSlow_complexFrequency d hmu' hI2, blockSlow_complexFrequency d hmu' hI2'] at hS
  have hmuC : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu0.ne'
  have hS' : jpTheta d mu ξ I = jpTheta d mu ξ' I' := smul_right_injective _ hmuC hS
  -- the two Lipschitz estimates of the specification
  have g1 : ‖jpGrad d mu ξ' I - jpGrad d mu ξ' I'‖ ≤ p.LN * ‖I - I'‖ :=
    (hlip1 mu hmu' I hI I' hI' ξ' hξ').1
  have g2 : ‖jpGrad d mu ξ I - jpGrad d mu ξ' I‖ ≤ p.LN * ‖ξ - ξ'‖ :=
    hlip2 mu hmu' I hI ξ ξ' hξ hξ'
  have t1 : ‖jpTheta d mu ξ' I - jpTheta d mu ξ' I'‖ ≤ p.LN * ‖I - I'‖ :=
    (hlip1 mu hmu' I hI I' hI' ξ' hξ').2
  have hbt : (jetBeta d mu I).mulVec (ξ - ξ') = jpTheta d mu ξ I - jpTheta d mu ξ' I := by
    simp [jpTheta, Matrix.mulVec_sub]
  have hβ : ‖ξ - ξ'‖ ≤ p.LB * (p.LN * ‖I - I'‖) := by
    refine (hbeta mu hmu' I hI _).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    rw [hbt, hS', ← norm_neg, neg_sub]
    exact t1
  -- fast part
  have hfa : complexFast d I - complexFast d I' =
      (mu : ℂ) • (jpGrad d mu ξ' I' - jpGrad d mu ξ I) := by
    have : complexFast d I + (mu : ℂ) • jpGrad d mu ξ I =
        complexFast d I' + (mu : ℂ) • jpGrad d mu ξ' I' := hF
    rw [smul_sub]; linear_combination this
  have hfast : p.c0 * ‖I - I'‖ ≤ mu * (p.LN * ‖I - I'‖ + p.LN * ‖ξ - ξ'‖) := by
    calc p.c0 * ‖I - I'‖ ≤ ‖complexFast d I - complexFast d I'‖ := hlow I hI I' hI'
      _ = mu * ‖jpGrad d mu ξ' I' - jpGrad d mu ξ I‖ := by
          rw [hfa, norm_real_smul_le mu hmu0.le]
      _ ≤ mu * (p.LN * ‖I - I'‖ + p.LN * ‖ξ - ξ'‖) := by
          gcongr
          calc ‖jpGrad d mu ξ' I' - jpGrad d mu ξ I‖
              = ‖-(jpGrad d mu ξ' I - jpGrad d mu ξ' I') -
                  (jpGrad d mu ξ I - jpGrad d mu ξ' I)‖ := by
                congr 1; abel
            _ ≤ p.LN * ‖I - I'‖ + p.LN * ‖ξ - ξ'‖ := by
                refine (norm_sub_le _ _).trans (add_le_add ?_ g2)
                rwa [norm_neg]
  have hmuLN : mu * p.LN ≤ p.c0 / 2 :=
    (mul_le_mul_of_nonneg_left hLNAN hmu0.le).trans
      ((mul_le_mul_of_nonneg_right hmuμ (by linarith)).trans e3)
  have hq : 2 * (mu * p.LN ^ 2 * p.LB) < p.c0 := by
    have : 2 * (mu * p.LN ^ 2 * p.LB) ≤ 2 * p.muStar * p.LN ^ 2 * p.LB := by
      have := mul_le_mul_of_nonneg_right hmuμ (by positivity : 0 ≤ 2 * p.LN ^ 2 * p.LB)
      nlinarith
    exact this.trans_lt e5
  have hD : ‖I - I'‖ = 0 := by
    have hn := norm_nonneg (I - I')
    have : p.c0 * ‖I - I'‖ ≤ mu * p.LN * ‖I - I'‖ + mu * p.LN ^ 2 * p.LB * ‖I - I'‖ := by
      have h2 : mu * p.LN * ‖ξ - ξ'‖ ≤ mu * p.LN * (p.LB * (p.LN * ‖I - I'‖)) :=
        mul_le_mul_of_nonneg_left hβ (by positivity)
      nlinarith
    by_contra hne
    have hpos : 0 < ‖I - I'‖ := lt_of_le_of_ne hn (Ne.symm hne)
    nlinarith
  have hII : I = I' := sub_eq_zero.1 (norm_eq_zero.1 hD)
  have hξξ : ξ = ξ' := by
    have : ‖ξ - ξ'‖ ≤ 0 := by rw [hD, mul_zero, mul_zero] at hβ; exact hβ
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have e1 : J = Fin.append I ξ := Fin.append_castAdd_natAdd.symm
  have e2 : J' = Fin.append I' ξ' := Fin.append_castAdd_natAdd.symm
  rw [e1, e2, hII, hξξ]

theorem freq_inj (d : PGData a b) : ∀ mu ∈ Ioc 0 (pgAnalytic d).muStar,
    InjOn (complexFrequency d mu) (analyticDomain d (pgAnalytic d)) ∧
    ∀ J ∈ analyticDomain d (pgAnalytic d),
      ∃ T : (Fin (a+b) → ℂ) ≃L[ℂ] (Fin (a+b) → ℂ),
        (∀ v, T v = fderiv ℂ (complexFrequency d mu) J v) ∧
        ‖T.toContinuousLinearMap‖ ≤ pgCU (pgAnalytic d) ∧
        ‖T.symm.toContinuousLinearMap‖ ≤ pgCU (pgAnalytic d)/mu ∧
        (∀ v, ‖blockFast (T.symm v)‖ ≤ pgCU (pgAnalytic d)*‖v‖) ∧
        (∀ v, ‖blockSlow (T v)‖ ≤ pgCU (pgAnalytic d)*mu*‖v‖) := by
  intro mu hmu
  refine ⟨freq_injOn d hmu, fun J hJ => ?_⟩
  have hspec := pgAnalytic_spec d
  have hδ := (pgExtension d).delta_pos
  have hmu0 : 0 < mu := hmu.1
  have hmu' : mu ∈ Icc 0 d.mu0 := ⟨hmu0.le, hmu.2.trans hspec.2.2.2.2.2.2.2.2.2.1⟩
  have hI2 : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) :=
    mem_actionNbhd_mono (by linarith [hspec.2.1]) hJ.1
  have hT := hasFDerivAt_complexFrequency d hmu' hI2
  obtain ⟨hup, hlow, hfast, hslow⟩ := jacobian_bounds d hmu hJ hT
  set T0 := (embFast a b).comp ((fderiv ℂ (complexFast d) (blockFast J)).comp (bfCLM a b)) +
    (mu : ℂ) • (partialsCLM (a + b)).comp (fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J) with hT0
  have hinj : Function.Injective (T0 : (Fin (a+b) → ℂ) →ₗ[ℂ] (Fin (a+b) → ℂ)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h := hlow v
    have hv' : T0 v = 0 := hv
    rw [hv', norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  have hbij : Function.Bijective (T0 : (Fin (a+b) → ℂ) →ₗ[ℂ] (Fin (a+b) → ℂ)) :=
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  let e : (Fin (a+b) → ℂ) ≃L[ℂ] (Fin (a+b) → ℂ) :=
    (LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv
  have he : ∀ v, e v = T0 v := fun v => rfl
  have hes : ∀ w, T0 (e.symm w) = w := fun w => by rw [← he]; exact e.apply_symm_apply w
  have hCU0 : 0 ≤ pgCU (pgAnalytic d) / mu := by
    have := (pgCU_ge (pgAnalytic d)).1
    have h1 := hspec.2.2.2.1
    have h2 := hspec.2.2.2.2.1
    exact div_nonneg (by linarith) hmu0.le
  refine ⟨e, fun v => ?_, ?_, ?_, ?_, ?_⟩
  · rw [he, hT.fderiv]
  · refine ContinuousLinearMap.opNorm_le_bound _ (by linarith [(pgCU_ge (pgAnalytic d)).1,
      hspec.2.2.2.1, hspec.2.2.2.2.1]) fun v => ?_
    exact hup v
  · refine ContinuousLinearMap.opNorm_le_bound _ hCU0 fun w => ?_
    have := hlow (e.symm w)
    rw [hes] at this
    exact this
  · intro w
    have := hfast (e.symm w)
    rwa [hes] at this
  · intro v
    rw [he]; exact hslow v

end KAM.Planetary

end
