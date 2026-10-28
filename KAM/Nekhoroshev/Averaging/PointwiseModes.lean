/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Identity

/-!
# Part N12: modewise variation along the orbit (`stepN:p12:pw-lambda`, first half)

Helper module of `Pointwise`. For each Fourier mode `k` the coefficient `avgU h f κ k` is
differentiable on the action ball, bounded by the `avgWenv` term, and its variation along the orbit
`γ_x` on `[0, t]` is controlled by the `avgBterm` majorant:
`‖U_k(I(u))‖ ≤ ‖U_k(I₀)‖ + (2ε/s) ∫₀ᵘ b_k(I(v)) dv`
(from the right-derivative fencing theorem, since `|İ|_∞ ≤ 2ε/s`).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal ContDiff

namespace KAM.Nekhoroshev

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

section Pieces

variable (d : AveragingData n R s h f)
include d

private theorem contDiffOn_freq'' :
    ContDiffOn ℝ 2 (KAM.frequencyMap h) (realActionDomain n R s) := by
  have hg : ContDiffOn ℝ 3 (realPart h) (realActionDomain n R s) := d.hh.2.2.2.2
  have hU := isOpen_realActionDomain (n := n) d.hR d.hs
  have hd : ContDiffOn ℝ 2 (fderiv ℝ (realPart h)) (realActionDomain n R s) :=
    hg.fderiv_of_isOpen hU (by norm_num)
  refine contDiffOn_pi.2 fun i => ?_
  exact ContDiffOn.clm_apply hd (contDiffOn_const (c := (Pi.single i (1 : ℝ) : Fin n → ℝ)))

theorem differentiableAt_avgFreq {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    DifferentiableAt ℝ (KAM.frequencyMap h) I :=
  ((contDiffOn_freq'' d).differentiableOn (by norm_num) I
    (ball_subset_realActionDomain d.hR d.hs hI)).differentiableAt
    ((isOpen_realActionDomain (n := n) d.hR d.hs).mem_nhds
      (ball_subset_realActionDomain d.hR d.hs hI))

theorem differentiableAt_avgQ (k : Fin n → ℤ) {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    DifferentiableAt ℝ (avgQ h k) I := by
  have hω := differentiableAt_avgFreq d hI
  unfold avgQ
  exact DifferentiableAt.fun_sum fun j _ => (differentiableAt_pi.1 hω j).const_mul _

theorem differentiableAt_avgU {κ : ℝ} (hκ : 0 < κ) (k : Fin n → ℤ) {I : Fin n → ℝ}
    (hI : I ∈ actionBall n R) : DifferentiableAt ℝ (avgU h f κ k) I := by
  have hopen := isOpen_actionNbhd_ball (n := n) R s
  have hmem : KAM.realInclusion n I ∈ KAM.actionNbhd (actionBall n R) s :=
    ball_subset_realActionDomain d.hR d.hs hI
  have hc : DifferentiableAt ℝ (fun J => avgCoeff f (KAM.realInclusion n J) k) I :=
    (((coef d).1 k).differentiableAt (hopen.mem_nhds hmem)).restrictScalars ℝ
      |>.comp I (KAM.realInclusion n).differentiableAt
  have hψ : DifferentiableAt ℝ (fun J => (avgPsi κ (avgQ h k J) : ℂ)) I :=
    Complex.ofRealCLM.differentiableAt.comp I
      (((corrector hκ).1.differentiable (by simp)).differentiableAt.comp I
        (differentiableAt_avgQ d k hI))
  refine differentiableAt_pi.2 fun j => ?_
  exact (hc.mul hψ).mul_const _

theorem norm_avgU_le' (κ : ℝ) (k : Fin n → ℤ) {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    ‖avgU h f κ k I‖ ≤ ‖fun j => (k j : ℝ)‖ * avgBeta s k * |avgPsi κ (avgQ h k I)| := by
  have hc := (coef d).2.1 _ (ball_subset_realActionDomain d.hR d.hs hI) k
  have hβ : 0 ≤ avgBeta s k := (Real.exp_pos _).le
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  simp only [avgU, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast]
  have hj : |(k j : ℝ)| ≤ ‖fun j => (k j : ℝ)‖ := by simpa using norm_le_pi_norm (fun j => (k j : ℝ)) j
  calc ‖avgCoeff f (KAM.realInclusion n I) k‖ * |avgPsi κ (avgQ h k I)| * |(k j : ℝ)|
      ≤ avgBeta s k * |avgPsi κ (avgQ h k I)| * ‖fun j => (k j : ℝ)‖ := by
        gcongr
        exact hc
    _ = _ := by ring

theorem continuousAt_avgBterm {κ M₂ : ℝ} (hκ : 0 < κ) (k : Fin n → ℤ) {I : Fin n → ℝ}
    (hI : I ∈ actionBall n R) : ContinuousAt (avgBterm h s M₂ κ k) I := by
  have hQ := (differentiableAt_avgQ d k hI).continuousAt
  have hψ : Continuous (avgPsi κ) := (corrector hκ).1.continuous
  have hψD : Continuous (avgPsiD κ) := by
    have : avgPsiD κ = deriv (avgPsi κ) := funext fun y => ((corrector hκ).2 y).1.deriv.symm
    rw [this]; exact (corrector hκ).1.continuous_deriv (by simp)
  unfold avgBterm
  fun_prop

theorem avgBterm_nonneg' {M₂ κ : ℝ} (hM0 : 0 ≤ M₂) (k : Fin n → ℤ) (I : Fin n → ℝ) :
    0 ≤ avgBterm h s M₂ κ k I := by
  have h0 : 0 ≤ 2 * (n : ℝ) / s := by have := d.hs; positivity
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (add_nonneg (mul_nonneg h0 (abs_nonneg _))
      (mul_nonneg (mul_nonneg hM0 (KAM.Fourier.modeSize_nonneg k)) (abs_nonneg _)))

omit d in
theorem isOpen_eIoo (a b : EReal) : IsOpen (KAM.ODE.eIoo a b) :=
  (isOpen_lt continuous_const continuous_coe_real_ereal).inter
    (isOpen_lt continuous_coe_real_ereal continuous_const)

/-- Modewise variation: `‖U_k(I(u))‖ ≤ ‖U_k(I₀)‖ + (2ε/s) ∫₀ᵘ b_k(I(v)) dv` on `[0, t]`. -/
theorem mode_bound {κ M₂ ε : ℝ} (hκ : 0 < κ)
    (hM : ∀ I ∈ closedBall (0 : Fin n → ℝ) R, ∀ i, ∑ j, |avgM h I i j| ≤ M₂)
    (hε : 0 ≤ ε) {x : AvgPhase n} (hx : x ∈ avgDomain n R) {t : ℝ}
    (htp : (t : EReal) < avgTp h f R ε x)
    (htraj : ∀ u ∈ Icc 0 t, (avgFlow h f R ε u x).2 ∈ avgG n R) (k : Fin n → ℤ) :
    ∀ u ∈ Icc 0 t, ‖avgU h f κ k (avgFlow h f R ε u x).2‖ ≤ ‖avgU h f κ k x.2‖ +
      ε * (2 / s) * ∫ v in (0 : ℝ)..u, avgBterm h s M₂ κ k (avgFlow h f R ε v x).2 := by
  have hM0 : 0 ≤ M₂ := (Finset.sum_nonneg fun j _ => abs_nonneg _).trans
    (hM 0 (by simpa using d.hR.le) ⟨0, d.hn⟩)
  set γ : ℝ → AvgPhase n := fun v => avgFlow h f R ε v x with hγ
  have hsol := (avgMaximal_spec d ε hx).isSolution
  have hUo := isOpen_eIoo (avgTm h f R ε x) (avgTp h f R ε x)
  have hsub : Icc 0 t ⊆ KAM.ODE.eIoo (avgTm h f R ε x) (avgTp h f R ε x) := fun u hu =>
    mem_eIoo_of_le d ε hx hu.1 hu.2 htp
  set c : ℝ := ε * (2 / s) with hc
  have hc0 : 0 ≤ c := by have := d.hs; positivity
  set Ψ : ℝ → ℝ := fun v => avgBterm h s M₂ κ k (γ v).2 with hΨdef
  have hΨ : ContinuousOn Ψ (KAM.ODE.eIoo (avgTm h f R ε x) (avgTp h f R ε x)) := fun v hv =>
    (ContinuousAt.comp (f := fun w => (avgFlow h f R ε w x).2) (x := v)
      (continuousAt_avgBterm d hκ k (hsol v hv).1.2)
      (hsol v hv).2.continuousAt.snd).continuousWithinAt
  have hBd : ∀ u ∈ Icc 0 t, HasDerivAt
      (fun w => ‖avgU h f κ k x.2‖ + c * ∫ v in (0 : ℝ)..w, Ψ v) (c * Ψ u) u := by
    intro u hu
    have hint : IntervalIntegrable Ψ volume 0 u := by
      refine (hΨ.mono ?_).intervalIntegrable
      rw [uIcc_of_le hu.1]; exact fun v hv => hsub ⟨hv.1, hv.2.trans hu.2⟩
    have hmeas : StronglyMeasurableAtFilter Ψ (nhds u) volume :=
      hΨ.stronglyMeasurableAtFilter hUo u (hsub hu)
    have hcont : ContinuousAt Ψ u := hΨ.continuousAt (hUo.mem_nhds (hsub hu))
    exact ((intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_mul c).const_add _
  have hUd : ∀ u ∈ Icc 0 t, HasDerivAt (fun v => avgU h f κ k (γ v).2)
      (fderiv ℝ (avgU h f κ k) (γ u).2 (ε • avgA f (γ u))) u := by
    intro u hu
    obtain ⟨hz, hder⟩ := orbit_hasDerivAt d ε hx hu.1 hu.2 htp
    have hF := (fbounds d (γ u) hz).2.2 ε
    have h1 := (hasFDerivAt_snd (𝕜 := ℝ) (E := Fin n → ℝ) (F := Fin n → ℝ)
      (p := γ u)).comp_hasDerivAt u hder
    rw [hF] at h1
    exact (differentiableAt_avgU d hκ k hz.2).hasFDerivAt.comp_hasDerivAt u h1
  have h0 : γ 0 = x := (avgMaximal_spec d ε hx).init
  intro u hu
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun v => avgU h f κ k (γ v).2)
    (f' := fun v => fderiv ℝ (avgU h f κ k) (γ v).2 (ε • avgA f (γ v)))
    (B := fun w => ‖avgU h f κ k x.2‖ + c * ∫ v in (0 : ℝ)..w, Ψ v)
    (B' := fun v => c * Ψ v) (a := 0) (b := t)
    (fun u hu => (hUd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hUd u (Ico_subset_Icc_self hu)).hasDerivWithinAt) ?_
    (fun u hu => (hBd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hBd u (Ico_subset_Icc_self hu)).hasDerivWithinAt) ?_ hu
  · simp [h0]
  · intro u hu
    have hu' : u ∈ Icc 0 t := Ico_subset_Icc_self hu
    obtain ⟨hz, -⟩ := orbit_hasDerivAt d ε hx hu'.1 hu'.2 htp
    have hmode := ((wreg d hκ hM).2.2 (γ u) hz).2 (htraj u hu') |>.2.2.2.2.2 k (ε • avgA f (γ u))
    have hA := (fbounds d (γ u) hz).1
    have hnn := avgBterm_nonneg' d (κ := κ) hM0 k (γ u).2
    have hεA : ‖ε • avgA f (γ u)‖ ≤ ε * (2 / s) := by
      rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left hA hε
    calc ‖fderiv ℝ (avgU h f κ k) (γ u).2 (ε • avgA f (γ u))‖
        ≤ avgBterm h s M₂ κ k (γ u).2 * ‖ε • avgA f (γ u)‖ := hmode
      _ ≤ avgBterm h s M₂ κ k (γ u).2 * (ε * (2 / s)) := mul_le_mul_of_nonneg_left hεA hnn
      _ = c * Ψ u := by rw [hc]; simp only [hΨdef]; ring

theorem continuousOn_bterm_orbit {κ M₂ ε : ℝ} (hκ : 0 < κ) {x : AvgPhase n}
    (hx : x ∈ avgDomain n R) {t : ℝ} (htp : (t : EReal) < avgTp h f R ε x) (k : Fin n → ℤ) :
    ContinuousOn (fun v => avgBterm h s M₂ κ k (avgFlow h f R ε v x).2) (Icc 0 t) := fun v hv =>
  (ContinuousAt.comp (f := fun w => (avgFlow h f R ε w x).2) (x := v)
    (continuousAt_avgBterm d hκ k (orbit_mapsTo d ε hx htp hv).2)
    (orbit_hasDerivAt d ε hx hv.1 hv.2 htp).2.continuousAt.snd).continuousWithinAt

end Pieces

end KAM.Nekhoroshev

end
