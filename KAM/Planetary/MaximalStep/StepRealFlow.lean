/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.StepReal
public import KAM.Planetary.MaximalStep.RealFlow

/-!
# The real flow of the angle equation (P11A-C8, `stepP:p11a:cs-lip`)

At a real parameter `b` the angle component of the time-one map at `η = 0` is the real flow of
the field `v = Re φ_1(·, b)` (uniqueness for `θ' = φ_1(θ, b)`); `v` is a trigonometric polynomial
whose derivative is bounded through the decay of the coefficients, so `real_lipschitz` applies.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ} {w : P11CVec n → P11CVec n}
  {R : P11Family n → ℂ}

/-- The real field `v(x) = Re φ_1(x, b)` of the angle equation. -/
def stepV (S : P11Step n) (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ) (b : P11Vec n)
    (x : P11Vec n) : P11Vec n :=
  fun i => (stepP1 S w R (KAM.realInclusion n x, KAM.realInclusion n b) i).re

theorem stepP1_entire (S : P11Step n) (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ)
    (b : P11CVec n) (i : Fin n) : Differentiable ℂ (fun θ => stepP1 S w R (θ, b) i) := by
  have e : (fun θ => stepP1 S w R (θ, b) i) =
      KAM.fourierSum (hmCoef S.T w (fun z => p11R1 S.T R z i) b) :=
    funext fun θ => p11Solve_eq _ _ _ _ _
  rw [e]
  exact differentiable_fourierSum_finset (S := hmModes n S.T) fun k hk => hmCoef_eq_zero hk

theorem stepV_contDiff (S : P11Step n) (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ)
    (b : P11Vec n) : ContDiff ℝ 2 (stepV S w R b) := by
  refine contDiff_pi.2 fun i => ?_
  have h1 : ContDiff ℝ 2 (fun θ : P11CVec n => stepP1 S w R (θ, KAM.realInclusion n b) i) :=
    ((contDiffOn_univ.1 (KAM.holomorphic_regularity_of_finiteDimensional isOpen_univ
      (stepP1_entire S w R (KAM.realInclusion n b) i).differentiableOn).2.2.1).restrict_scalars
      ℝ).of_le (by simp)
  exact Complex.reCLM.contDiff.comp (h1.comp (KAM.realInclusion n).contDiff)

theorem stepV_bound (H : P11StepHyp S h w R) {b : P11Vec n}
    (hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t) (x : P11Vec n) :
    ‖stepV S w R b x‖ ≤ p11StepA S := by
  have Hb := step_affHyp H hb
  refine (pi_norm_le_iff_of_nonneg (step_A_nonneg H)).2 fun i => ?_
  have := Hb.bound1 (KAM.realInclusion n x)
    (KAM.ofReal_mem_complexStrip (by linarith [S.radius, S.sigma_pos]) x)
  calc ‖stepV S w R b x i‖ = |(stepP1 S w R (KAM.realInclusion n x, KAM.realInclusion n b) i).re| :=
        Real.norm_eq_abs _
    _ ≤ ‖stepP1 S w R (KAM.realInclusion n x, KAM.realInclusion n b) i‖ :=
        Complex.abs_re_le_norm _
    _ ≤ _ := (norm_le_pi_norm _ i).trans this

theorem stepV_periodic (H : P11StepHyp S h w R) {b : P11Vec n}
    (hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t) (x : P11Vec n) (k : Fin n → ℤ) :
    stepV S w R b (x + fun i => (k i : ℝ)) = stepV S w R b x := by
  have Hb := step_affHyp H hb
  have hx := KAM.ofReal_mem_complexStrip (n := n) (ρ := S.r - S.d - S.delta)
    (by linarith [S.radius, S.sigma_pos]) x
  have := periodic_int (f := fun θ => stepP1 S w R (θ, KAM.realInclusion n b)) Hb.per1 k hx
  funext i
  have e : KAM.realInclusion n (x + fun i => (k i : ℝ)) =
      KAM.realInclusion n x + fun i => (k i : ℂ) := by ext j; simp
  simp only [stepV, e]
  exact congrArg Complex.re (congrFun this i)

theorem step_fderiv_re {b : P11Vec n} (x a : P11Vec n) (i : Fin n) :
    fderiv ℝ (stepV S w R b) x a i =
      (fderiv ℂ (fun θ => stepP1 S w R (θ, KAM.realInclusion n b) i)
        (KAM.realInclusion n x) (KAM.realInclusion n a)).re := by
  have hd : DifferentiableAt ℝ (stepV S w R b) x :=
    ((stepV_contDiff S w R b).differentiable (by norm_num)) x
  have h1 := hasFDerivAt_pi'.1 hd.hasFDerivAt i
  have hf := ((stepP1_entire S w R (KAM.realInclusion n b) i).differentiableAt
    (x := KAM.realInclusion n x)).hasFDerivAt.restrictScalars ℝ
  have h2 := Complex.reCLM.hasFDerivAt.comp x (hf.comp x (KAM.realInclusion n).hasFDerivAt)
  have h3 := h1.unique h2
  have := congrArg (fun L => L a) h3
  simpa using this

theorem stepV_fderiv (H : P11StepHyp S h w R) {b : P11Vec n}
    (hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t) (x : P11Vec n) :
    ‖fderiv ℝ (stepV S w R b) x‖ ≤
      2 * S.T * ((1 + p11Error n S.T S.d) * S.eps / S.s) * p11Lambda n (S.r - S.d) / S.D := by
  obtain ⟨c1, c2, c3, c4, -, c6, -⟩ := p11_cutoff_coeff S.n_pos (step_r_pos S) S.s_pos
    S.T_pos.le S.d_pos (step_dr S) S.eps_nonneg (step_B_open S) H.admissible H.bound
  have hr : 0 < S.r - S.d := by linarith [step_dr S]
  have hD := S.D_pos
  have hT := S.T_pos
  have hM1 : 0 ≤ (1 + p11Error n S.T S.d) * S.eps / S.s := div_nonneg (step_M_nonneg S) S.s_pos.le
  have hΛ : 0 ≤ p11Lambda n (S.r - S.d) := by
    rw [← (p11_lambda_spec S.n_pos hr).2.1]
    exact tsum_nonneg fun _ => (Real.exp_pos _).le
  have hL : 0 ≤ 2 * S.T * ((1 + p11Error n S.T S.d) * S.eps / S.s) * p11Lambda n (S.r - S.d) / S.D := by
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hL fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [step_fderiv_re x a i]
  refine ((Real.norm_eq_abs _).le.trans (Complex.abs_re_le_norm _)).trans ?_
  set M1 := (1 + p11Error n S.T S.d) * S.eps / S.s with hM1def
  set C : ℝ := 2 * S.T * M1 * ‖a‖ / S.D with hC
  have hC0 : 0 ≤ C := by positivity
  have c6' : p11Bound (KAM.complexStrip n (S.r - S.d) ×ˢ KAM.actionNbhd S.E S.t)
      (fun z => p11R1 S.T R z i) M1 := fun z hz => (norm_le_pi_norm _ i).trans (c6 z hz)
  have ha : ‖KAM.realInclusion n a‖ ≤ ‖a‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by simpa using norm_le_pi_norm a j
  have e : (fun θ => stepP1 S w R (θ, KAM.realInclusion n b) i) =
      KAM.fourierSum (hmCoef S.T w (fun z => p11R1 S.T R z i) (KAM.realInclusion n b)) :=
    funext fun θ => p11Solve_eq _ _ _ _ _
  rw [e, fderiv_fourierSum_finset (S := hmModes n S.T) (fun k hk => hmCoef_eq_zero hk)]
  have hterm : ∀ k ∈ hmModes n S.T,
      ‖hmCoef S.T w (fun z => p11R1 S.T R z i) (KAM.realInclusion n b) k *
        (2 * Real.pi * Complex.I * p11dotC k (KAM.realInclusion n a)) *
        KAM.character k (KAM.realInclusion n x)‖ ≤
      if k ≠ 0 then Real.exp (-2 * Real.pi * (S.r - S.d) * KAM.Fourier.modeSize k) * C else 0 := by
    intro k _
    by_cases hk0 : k = 0
    · simp [hk0, hmCoef]
    by_cases hkT : KAM.Fourier.modeSize k ≤ S.T
    · simp only [ne_eq, hk0, not_false_eq_true, if_true]
      have hc := norm_hmCoef_le S.D_pos hr (c2 i) c6' hb
        (fun k hk hkT => step_hdiv H _ hb k hk hkT) hk0 hkT
      have hch : ‖KAM.character k (KAM.realInclusion n x)‖ = 1 := KAM.norm_character_real k x
      have hdot : ‖p11dotC k (KAM.realInclusion n a)‖ ≤ S.T * ‖a‖ :=
        (p11_norm_dotC_le k _).trans (mul_le_mul hkT ha (norm_nonneg _) S.T_pos.le)
      have h2π : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
        rw [norm_mul, norm_mul]; simp [Real.pi_pos.le]
      rw [norm_mul, norm_mul, norm_mul, hch, h2π, mul_one]
      have hπD : 0 < Real.pi * S.D := by positivity
      calc ‖hmCoef S.T w (fun z => p11R1 S.T R z i) (KAM.realInclusion n b) k‖ *
            (2 * Real.pi * ‖p11dotC k (KAM.realInclusion n a)‖)
          ≤ (Real.exp (-(2 * Real.pi * (S.r - S.d) * KAM.Fourier.modeSize k)) * M1 /
              (Real.pi * S.D)) * (2 * Real.pi * (S.T * ‖a‖)) :=
            mul_le_mul hc (mul_le_mul_of_nonneg_left hdot (by positivity)) (by positivity)
              ((norm_nonneg _).trans hc)
        _ = Real.exp (-2 * Real.pi * (S.r - S.d) * KAM.Fourier.modeSize k) * C := by
            rw [hC]
            have : -(2 * Real.pi * (S.r - S.d) * KAM.Fourier.modeSize k) =
                -2 * Real.pi * (S.r - S.d) * KAM.Fourier.modeSize k := by ring
            rw [this]
            field_simp
    · have : hmCoef S.T w (fun z => p11R1 S.T R z i) (KAM.realInclusion n b) k = 0 := by
        simp [hmCoef, not_le.1 hkT]
      rw [this]
      simp only [zero_mul, norm_zero]
      split_ifs <;> positivity
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have hs := sum_exp_le_lambda hr ((hmModes n S.T).filter fun k => k ≠ 0)
    (fun k hk => (Finset.mem_filter.1 hk).2)
  calc _ ≤ p11Lambda n (S.r - S.d) * C := mul_le_mul_of_nonneg_right hs hC0
    _ = _ := by rw [hC]; field_simp

/-- The angle component of the time-one map at `η = 0` and real data is the real flow of `v`. -/
theorem step_flow_real (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) {b : P11Vec n}
    (hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t) (x : P11Vec n) :
    (fun i => ((p11StepMap S w R ((KAM.realInclusion n x, 0), KAM.realInclusion n b)).1 i).re) =
      p11RealFlow (stepV S w R b) 1 x := by
  have Hb := step_affHyp H hb
  have hv := stepV_contDiff S w R b
  have hv1 : ContDiff ℝ 1 (stepV S w R b) := hv.of_le (by norm_num)
  have hM := step_A_nonneg H
  have hbd := stepV_bound H hb
  obtain ⟨hs0, hsd⟩ := p11RealFlow_spec hv1 hM hbd x
  have hρ : 0 < S.r - S.d - S.delta - S.sigma := by linarith [S.radius, S.sigma_pos]
  set p1 : P11CVec n → P11CVec n := fun θ => stepP1 S w R (θ, KAM.realInclusion n b) with hp1
  set γ : ℝ → P11CVec n := fun t => KAM.realInclusion n (p11RealFlow (stepV S w R b) t x) with hγ
  have hreal' := step_hm_real H hreal
  have hfield : ∀ y : P11Vec n, p1 (KAM.realInclusion n y) =
      KAM.realInclusion n (stepV S w R b y) := fun y => by
    ext i
    refine Complex.ext (by simp [hp1, stepV]) ?_
    simpa [hp1] using (hreal' y b hb).2 i
  have hγsol : KAM.ODE.IsSolutionIn p1 (KAM.complexStrip n (S.r - S.d - S.delta - S.sigma))
      (Icc (-1) 1) γ := fun t _ => by
    refine ⟨KAM.ofReal_mem_complexStrip hρ _, ?_⟩
    have := (KAM.realInclusion n).hasFDerivAt.comp_hasDerivAt t (hsd t)
    simp only [Function.comp_def] at this
    simpa [hγ, hfield] using this
  have hzU : ((KAM.realInclusion n x, (0 : P11CVec n)) : P11Phase n) ∈
      KAM.Weighted.Dom n {0} (3 * S.s / 4) (S.r - S.d - S.delta - 3 * S.sigma / 2) :=
    (mem_Dom_iff _).2 ⟨KAM.ofReal_mem_complexStrip (by linarith [S.radius, S.sigma_pos]) x,
      by simpa using by linarith [S.s_pos]⟩
  have hu := KAM.ODE.gen_uniqueness (KAM.isOpen_complexStrip n _) (contDiffOn_p1 Hb)
    (isPreconnected_Icc.ordConnected) (t₀ := 0) (by simp : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)
    hγsol (fst_solution Hb (U_sub_half Hb hzU))
    (by
      have a := (KAM.Canonical.flow_a (smallField Hb) (U_sub_half Hb hzU)).1
      simp only [hγ, hs0, a])
  have h1 := hu ⟨by norm_num, le_rfl⟩
  funext i
  have := congrFun h1 i
  simp only [hγ] at this
  exact (congrArg Complex.re this).symm.trans (by simp)

/-- `canonical_step_real` (the sup-norm real-Lipschitz clause). -/
theorem step_real_lipschitz (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) :
    ∀ b ∈ S.E, ∀ theta : P11Vec n,
      ‖fderiv ℝ (fun x : P11Vec n => fun i =>
        ((p11StepMap S w R ((KAM.realInclusion n x, 0), KAM.realInclusion n b)).1 i).re) theta -
        ContinuousLinearMap.id ℝ _‖ ≤
        Real.exp (2 * S.T * (1 + p11Error n S.T S.d) * S.eps * p11Lambda n (S.r - S.d) /
          (S.D * S.s)) - 1 := by
  intro b hbE θ
  have hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t :=
    ⟨b, hbE, by
      have : (KAM.realInclusion n b - fun i => ((b i : ℝ) : ℂ)) = 0 := by ext; simp
      rw [this]; simpa using S.t_pos⟩
  have hD := S.D_pos
  have hs := S.s_pos
  have hr : 0 < S.r - S.d := by linarith [step_dr S]
  have hΛ : 0 ≤ p11Lambda n (S.r - S.d) := by
    rw [← (p11_lambda_spec S.n_pos hr).2.1]
    exact tsum_nonneg fun _ => (Real.exp_pos _).le
  have hL : 0 ≤ 2 * S.T * ((1 + p11Error n S.T S.d) * S.eps / S.s) *
      p11Lambda n (S.r - S.d) / S.D := by
    have := step_M_nonneg S; have := S.T_pos; positivity
  have key := real_lipschitz (stepV_contDiff S w R b) (step_A_nonneg H) hL
    (stepV_bound H hb) (stepV_fderiv H hb) (fun x k => stepV_periodic H hb x k) 1
    ⟨by norm_num, le_rfl⟩ θ
  have e : (fun x : P11Vec n => fun i =>
      ((p11StepMap S w R ((KAM.realInclusion n x, 0), KAM.realInclusion n b)).1 i).re) =
      p11RealFlow (stepV S w R b) 1 := funext fun x => step_flow_real H hreal hb x
  rw [e]
  refine key.1.trans (le_of_eq ?_)
  congr 2
  field_simp

/-- cs-lip: EXPLICIT reality guard repairs p11a2 L248/L287; no frozen type changes. -/
theorem canonical_step_real {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ}
    {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ} (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) :
    let rp := S.r-S.d-S.delta-2*S.sigma
    (∀ x : Phase n, ∀ b : P11Vec n,
      (KAM.realInclusion₂ n x,KAM.realInclusion n b) ∈ domain_def n rp (S.q*S.s) (KAM.actionNbhd S.E S.t) →
        ∀ i, ((p11StepMap S w R (KAM.realInclusion₂ n x,KAM.realInclusion n b)).1 i).im=0 ∧
          ((p11StepMap S w R (KAM.realInclusion₂ n x,KAM.realInclusion n b)).2 i).im=0) ∧
    p11Real (domain_def n rp (S.q*S.s) (KAM.actionNbhd S.E S.t)) (p11StepRemainder S h w R) ∧
    ∀ b ∈ S.E, ∀ theta : P11Vec n,
      ‖fderiv ℝ (fun x : P11Vec n => fun i =>
        ((p11StepMap S w R ((KAM.realInclusion n x,0),KAM.realInclusion n b)).1 i).re) theta-
        ContinuousLinearMap.id ℝ _‖ ≤
        Real.exp (2*S.T*(1+p11Error n S.T S.d)*S.eps*p11Lambda n (S.r-S.d)/(S.D*S.s))-1 :=
  ⟨step_real_flow H hreal, step_Rp_real H hreal, step_real_lipschitz H hreal⟩

end KAM.Planetary

end
