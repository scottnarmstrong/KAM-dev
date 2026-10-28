/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.KAMInputsFreq

/-!
# P Part 5: the KAM hypothesis inputs, the `kamH` part (`bpP:p5:kam-hyp`)

The frequency map of `kamH` is `(2π)⁻¹` times `complexFrequency` (`freq_kamH`); the domain inclusion
of the action neighbourhood into the analytic domain, differentiability, injectivity, the Hessian
bounds with `kam_c1 ≥ 2π pgCU`, reality, and the dictionary clause `dioBase = pgD0`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-KH.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

variable {a b : ℕ} {d : PGData a b} {r mu : ℝ}

theorem kamH_eq_smul (d : PGData a b) (mu : ℝ) :
    kamH d mu = (2*Real.pi:ℂ)⁻¹ • complexIntegrable d mu := by
  funext J
  simp [kamH, div_eq_inv_mul]

theorem two_pi_ne_zero_complex : (2*Real.pi:ℂ) ≠ 0 := by
  exact_mod_cast (by positivity : (2*Real.pi:ℝ) ≠ 0)

theorem fderiv_kamH (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) :
    fderiv ℂ (kamH d mu) J = (2*Real.pi:ℂ)⁻¹ • fderiv ℂ (complexIntegrable d mu) J := by
  letI : Invertible (2*Real.pi:ℂ)⁻¹ := invertibleOfNonzero (inv_ne_zero two_pi_ne_zero_complex)
  rw [kamH_eq_smul]
  exact fderiv_const_smul_of_invertible _

theorem freq_kamH (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) :
    KAM.NormalForm.freq (kamH d mu) J = (2*Real.pi:ℂ)⁻¹ • complexFrequency d mu J := by
  funext i
  simp [KAM.NormalForm.freq, fderiv_kamH, complexFrequency]

theorem realFreq_kamH (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {J : Fin (a+b) → ℝ}
    (hJ : blockFast J ∈ d.V) :
    realFreq (kamH d mu) J = (2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J := by
  funext i
  have h : (2*Real.pi:ℂ)⁻¹ = (((2*Real.pi)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  show (KAM.NormalForm.freq (kamH d mu) (KAM.realInclusion (a+b) J) i).re = _
  rw [freq_kamH, complexFrequency_realSlice d hmu hJ]
  simp only [Pi.smul_apply, KAM.realInclusion_apply, smul_eq_mul, h]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- The dynamic parameter facts of `rstar` used for the KAM hypotheses. -/
theorem kh_dyn (h : admissible d (pgRstar d) r mu) :
    r < 1 ∧ r < (pgAnalytic d).r1/2 ∧ r < pgOscRadius d/4 ∧ 0 < (params d r mu).l1 ∧
    (params d r mu).l1 ≤ r^2/12 ∧
    (params d r mu).l1 ≤ (params d r mu).rhoBar ∧ (params d r mu).rhoBar ≤ (pgAnalytic d).rho ∧
    mu < (pgAnalytic d).muStar ∧ pgChat a b*(params d r mu).Ehat < 1 := by
  obtain ⟨-, -, -, -, hR1, -, -, -, -, -, -, hdyn⟩ := (rstar d).choose_spec
  obtain ⟨h1, h2, -, -, -, -, h7, h8, h9, h10, h11, h12, -⟩ := hdyn r mu h
  refine ⟨h.2.1.trans hR1, h1, h2, h7, ?_, h10, h9, h11, h12⟩
  have := params_ell d r mu
  linarith

theorem mu_mem_Icc (h : admissible d (pgRstar d) r mu) : mu ∈ Set.Icc 0 d.mu0 :=
  ⟨h.2.2.1.le, h.2.2.2.1.le⟩

theorem norm_blockFast_sub_le_real (J K : Fin (a + b) → ℝ) :
    ‖blockFast J - blockFast K‖ ≤ ‖J - K‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    norm_le_pi_norm (J - K) (Fin.castAdd b i)

theorem actionNbhd_sub_analytic (h : admissible d (pgRstar d) r mu) :
    KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho ⊆
      analyticDomain d (pgAnalytic d) := by
  obtain ⟨hr1, -, -, hl1, hl12, hlr, hrp, -⟩ := kh_dyn h
  have hrho : (params d r mu).rho = (params d r mu).l1/2 := rfl
  rintro J hJ
  obtain ⟨J0, ⟨hf, hs⟩, hJ⟩ := mem_actionNbhd_iff.1 hJ
  refine ⟨mem_actionNbhd_iff.2 ⟨blockFast J0, subset_closure hf.1.1, ?_⟩, ?_⟩
  · have := norm_blockFast_sub_le (J := KAM.realInclusion (a+b) J0) (K := J)
    refine lt_of_le_of_lt this (hJ.trans_le ?_)
    linarith
  · refine (pi_norm_lt_iff one_pos).2 fun j => ?_
    have h1 : (params d r mu).l1 < blockSlow J0 j ∧ blockSlow J0 j < (params d r mu).l2top :=
      hs j (mem_univ j)
    have hbs : blockSlow J0 j = J0 (Fin.natAdd a j) := rfl
    rw [hbs] at h1
    have h2 : ‖(J - KAM.realInclusion (a+b) J0) (Fin.natAdd a j)‖ < (params d r mu).l1/2 :=
      lt_of_le_of_lt (norm_le_pi_norm _ _) (by rw [hrho] at hJ; exact hJ)
    have h3 : ‖J (Fin.natAdd a j)‖ ≤ ‖(J0 (Fin.natAdd a j) : ℂ)‖ +
        ‖(J - KAM.realInclusion (a+b) J0) (Fin.natAdd a j)‖ := by
      have := norm_add_le ((KAM.realInclusion (a+b) J0) (Fin.natAdd a j))
        ((J - KAM.realInclusion (a+b) J0) (Fin.natAdd a j))
      simpa using this
    have h4 : ‖(J0 (Fin.natAdd a j) : ℂ)‖ = |J0 (Fin.natAdd a j)| := by simp
    have h5 := params_l2top d r mu
    have hr0 : 0 < r := h.1
    have h6 : |J0 (Fin.natAdd a j)| < r^2/2 := by
      rw [abs_of_pos (by have := h1.1; linarith)]
      have := h1.2
      rw [h5] at this
      linarith
    show ‖J (Fin.natAdd a j)‖ < 1
    have hr2 : r^2 < 1 := by nlinarith
    linarith

theorem analytic_mem_half {J : Fin (a+b) → ℂ} (hJ : J ∈ analyticDomain d (pgAnalytic d)) :
    blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2) :=
  mem_actionNbhd_mono (by linarith [(pgAnalytic_spec d).2.1, (pgExtension d).delta_pos]) hJ.1

theorem kamH_differentiableOn (h : admissible d (pgRstar d) r mu) :
    DifferentiableOn ℂ (kamH d mu) (KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) := by
  intro J hJ
  have hJ' := actionNbhd_sub_analytic h hJ
  rw [kamH_eq_smul]
  exact ((hasFDerivAt_complexIntegrable d (mu_mem_Icc h) (analytic_mem_half hJ')).differentiableAt.const_smul
    _).differentiableWithinAt

theorem kamH_injOn (h : admissible d (pgRstar d) r mu) :
    InjOn (fun J i => fderiv ℂ (kamH d mu) J (Pi.single i 1))
      (KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) := by
  have hmu : mu ∈ Ioc 0 (pgAnalytic d).muStar := ⟨h.2.2.1, (kh_dyn h).2.2.2.2.2.2.2.1.le⟩
  have hinj := (freq_inj d mu hmu).1
  intro J hJ J' hJ' heq
  refine hinj (actionNbhd_sub_analytic h hJ) (actionNbhd_sub_analytic h hJ') ?_
  have e : ∀ K, (fun i => fderiv ℂ (kamH d mu) K (Pi.single i 1)) =
      (2*Real.pi:ℂ)⁻¹ • complexFrequency d mu K := fun K => freq_kamH d mu K
  have heq' : (fun i => fderiv ℂ (kamH d mu) J (Pi.single i 1)) =
      (fun i => fderiv ℂ (kamH d mu) J' (Pi.single i 1)) := heq
  rw [e, e] at heq'
  exact smul_right_injective _ (inv_ne_zero two_pi_ne_zero_complex) heq'

theorem pgCU_pos (d : PGData a b) : 0 < pgCU (pgAnalytic d) := by
  obtain ⟨-, -, -, hM0, hAN, -⟩ := pgAnalytic_spec d
  have : (pgAnalytic d).M0 + (pgAnalytic d).AN + 1 ≤ pgCU (pgAnalytic d) := le_max_left _ _
  linarith

theorem kamH_hessian (h : admissible d (pgRstar d) r mu) {J : Fin (a+b) → ℂ}
    (hJ : J ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) :
    ∃ T : (Fin (a+b) → ℂ) ≃L[ℂ] (Fin (a+b) → ℂ),
      (∀ v i, T v i = fderiv ℂ (fun J i => fderiv ℂ (kamH d mu) J (Pi.single i 1)) J v i) ∧
      ‖T.toContinuousLinearMap‖ ≤ kam_c1 d ∧
      ‖T.symm.toContinuousLinearMap‖ ≤ kam_c1 d/mu ∧
      (∀ v, ‖blockSlow (T v)‖ ≤ kam_c1 d*mu*‖v‖) ∧
      (∀ v, ‖blockFast (T.symm v)‖ ≤ kam_c1 d*‖v‖) := by
  have hmu0 : 0 < mu := h.2.2.1
  have hmu : mu ∈ Ioc 0 (pgAnalytic d).muStar := ⟨hmu0, (kh_dyn h).2.2.2.2.2.2.2.1.le⟩
  obtain ⟨T0, hT0, hup, hlow, hfast, hslow⟩ :=
    (freq_inj d mu hmu).2 J (actionNbhd_sub_analytic h hJ)
  have hCU := pgCU_pos d
  have hC : 2*Real.pi*pgCU (pgAnalytic d) ≤ kam_c1 d :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC0 : 0 < kam_c1 d := by linarith [one_le_kam_c1 d]
  have hpi : 1 < 2*Real.pi := by linarith [Real.pi_gt_three]
  set c : ℂ := (2*Real.pi:ℂ) with hc
  have hc0 : c ≠ 0 := two_pi_ne_zero_complex
  have hnc : ‖c‖ = 2*Real.pi := by
    rw [hc]; simp [abs_of_pos (by positivity : 0 < 2*Real.pi)]
  let S : (Fin (a+b) → ℂ) ≃L[ℂ] (Fin (a+b) → ℂ) :=
    (LinearEquiv.smulOfNeZero ℂ (Fin (a+b) → ℂ) c⁻¹ (inv_ne_zero hc0)).toContinuousLinearEquiv
  have hS : ∀ v, S v = c⁻¹ • v := fun v => rfl
  have hSs : ∀ v, S.symm v = c • v := fun v => by
    rw [ContinuousLinearEquiv.symm_apply_eq, hS, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨T0.trans S, fun v i => ?_, ?_, ?_, fun v => ?_, fun v => ?_⟩
  · have e : (fun J i => fderiv ℂ (kamH d mu) J (Pi.single i 1)) =
        c⁻¹ • complexFrequency d mu := funext fun K => freq_kamH d mu K
    letI : Invertible c⁻¹ := invertibleOfNonzero (inv_ne_zero hc0)
    rw [e, fderiv_const_smul_of_invertible]
    simp [hS, hT0]
  · refine ContinuousLinearMap.opNorm_le_bound _ hC0.le fun v => ?_
    show ‖S (T0 v)‖ ≤ _
    rw [hS, norm_smul, norm_inv, hnc]
    have := T0.toContinuousLinearMap.le_opNorm v
    have h1 : ‖T0 v‖ ≤ pgCU (pgAnalytic d)*‖v‖ :=
      this.trans (mul_le_mul_of_nonneg_right hup (norm_nonneg _))
    calc (2*Real.pi)⁻¹*‖T0 v‖ ≤ 1*(pgCU (pgAnalytic d)*‖v‖) := by
          gcongr
          · exact (inv_le_one_of_one_le₀ hpi.le)
      _ ≤ kam_c1 d*‖v‖ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_gt_three]) (norm_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    show ‖T0.symm (S.symm v)‖ ≤ _
    rw [hSs]
    have := T0.symm.toContinuousLinearMap.le_opNorm (c • v)
    have h1 : ‖T0.symm (c • v)‖ ≤ pgCU (pgAnalytic d)/mu*‖c • v‖ :=
      this.trans (mul_le_mul_of_nonneg_right hlow (norm_nonneg _))
    rw [norm_smul, hnc] at h1
    refine h1.trans ?_
    calc pgCU (pgAnalytic d)/mu*(2*Real.pi*‖v‖) = (2*Real.pi*pgCU (pgAnalytic d))/mu*‖v‖ := by
          ring
      _ ≤ kam_c1 d/mu*‖v‖ := by gcongr
  · show ‖blockSlow (S (T0 v))‖ ≤ _
    rw [hS]
    have e : blockSlow (c⁻¹ • T0 v) = c⁻¹ • blockSlow (T0 v) := rfl
    rw [e, norm_smul, norm_inv, hnc]
    have := hslow v
    calc (2*Real.pi)⁻¹*‖blockSlow (T0 v)‖ ≤ 1*(pgCU (pgAnalytic d)*mu*‖v‖) := by
          gcongr
          · exact (inv_le_one_of_one_le₀ hpi.le)
      _ ≤ kam_c1 d*mu*‖v‖ := by
          rw [one_mul]
          have : pgCU (pgAnalytic d) ≤ kam_c1 d := by nlinarith [Real.pi_gt_three]
          gcongr
  · show ‖blockFast (T0.symm (S.symm v))‖ ≤ _
    rw [hSs]
    have := hfast (c • v)
    rw [norm_smul, hnc] at this
    refine this.trans ?_
    calc pgCU (pgAnalytic d)*(2*Real.pi*‖v‖) = (2*Real.pi*pgCU (pgAnalytic d))*‖v‖ := by ring
      _ ≤ kam_c1 d*‖v‖ := by gcongr

end KAM.Planetary

end
