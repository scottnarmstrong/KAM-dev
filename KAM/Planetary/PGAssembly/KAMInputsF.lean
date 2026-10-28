/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.KAMInputsKamH

/-!
# P Part 5: the KAM hypothesis inputs, the perturbation `kamF` (`bpP:p5:kam-hyp`)

`kamF` is the normalized averaged perturbation. On the strip domain of width
`pgWidth/(12π) = 2 · pgWidth/(24π)` the oscillator polar point lies in the averaging domain
(`kamPolar_mem`), where the averaging identity gives
`kamF = (mu · pgRemainder + remainder)/(2π)` (`kamF_eq`); this yields holomorphy, periodicity
and the sup bound used for the weighted bound.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-KH.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

variable {a b : ℕ} {d : PGData a b} {r mu : ℝ}

def kamF (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (z : PGComplexPhase (a+b)) : ℂ :=
  let w := (pgAvg d r mu h).Psi (oscillatorPolarComplex ((2*Real.pi:ℂ) • z.1,z.2))
  ((pgExtension d).H0 (blockFast w.2)+mu*(pgExtension d).P mu w)/(2*Real.pi)-kamH d mu z.2

/-- The oscillator polar point attached to a point of the strip domain. -/
def kamPolarPt (z : PGComplexPhase (a+b)) : PGComplexPhase (a+b) :=
  oscillatorPolarComplex ((2*Real.pi:ℂ) • z.1, z.2)

theorem kh_avg_spec (h : admissible d (pgRstar d) r mu) :
    AveragingSpec d r mu (pgAvg d r mu h) := (pg_avg d r mu h).choose_spec

theorem kh_cpow_half_sq (x : ℂ) : (x^(1/2:ℂ))^2 = x := by
  have := Complex.cpow_nat_inv_pow x (n := 2) (by norm_num)
  simpa [one_div] using this

theorem kh_norm_cos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have e1 : Real.exp (z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have e2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  unfold Complex.cos
  rw [norm_div]
  have h := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
    mul_one, sub_zero, Complex.neg_re, Complex.neg_im, neg_zero, mul_neg, sub_neg_eq_add,
    zero_add, neg_neg] at h
  have h2 : ‖(2:ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (by norm_num)]
  linarith

theorem kh_norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have e1 : Real.exp (z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have e2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  unfold Complex.sin
  rw [norm_div, norm_mul, Complex.norm_I, mul_one]
  have h := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
    mul_one, sub_zero, Complex.neg_re, Complex.neg_im, neg_zero, mul_neg, sub_neg_eq_add,
    zero_add, neg_neg] at h
  have h2 : ‖(2:ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (by norm_num)]
  linarith

theorem kh_exp_le_two {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1/2) : Real.exp x ≤ 2 := by
  have := Real.exp_bound_div_one_sub_of_interval h0 (by linarith)
  refine this.trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem pgWidth_lt_half (d : PGData a b) : pgWidth d < 1/2 := by
  have := (pgExtension d).delta_lt
  unfold pgWidth
  linarith

theorem kamPolarPt_fst_fast (z : PGComplexPhase (a+b)) (k : Fin a) :
    (kamPolarPt z).1 (Fin.castAdd b k) = 2*Real.pi * z.1 (Fin.castAdd b k) := by
  simp [kamPolarPt, oscillatorPolarComplex, assembleComplex, Fin.append_left, blockFast]

theorem kamPolarPt_fst_slow (z : PGComplexPhase (a+b)) (k : Fin b) :
    (kamPolarPt z).1 (Fin.natAdd a k) = (2*z.2 (Fin.natAdd a k))^(1/2:ℂ) *
      Complex.sin (2*Real.pi * z.1 (Fin.natAdd a k)) := by
  simp [kamPolarPt, oscillatorPolarComplex, assembleComplex, Fin.append_right, blockSlow]

theorem kamPolarPt_snd_fast (z : PGComplexPhase (a+b)) (k : Fin a) :
    (kamPolarPt z).2 (Fin.castAdd b k) = z.2 (Fin.castAdd b k) := by
  simp [kamPolarPt, oscillatorPolarComplex, assembleComplex, Fin.append_left, blockFast]

theorem kamPolarPt_snd_slow (z : PGComplexPhase (a+b)) (k : Fin b) :
    (kamPolarPt z).2 (Fin.natAdd a k) = (2*z.2 (Fin.natAdd a k))^(1/2:ℂ) *
      Complex.cos (2*Real.pi * z.1 (Fin.natAdd a k)) := by
  simp [kamPolarPt, oscillatorPolarComplex, assembleComplex, Fin.append_right, blockSlow]

/-- Slow actions of the tube: real part and size. -/
theorem kh_slow_bounds (h : admissible d (pgRstar d) r mu) {J : Fin (a+b) → ℂ}
    (hJ : J ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) (j : Fin b) :
    (params d r mu).l1/2 < (J (Fin.natAdd a j)).re ∧ ‖J (Fin.natAdd a j)‖ < r^2/2 := by
  obtain ⟨-, -, -, hl1, -⟩ := kh_dyn h
  obtain ⟨J0, ⟨hf, hs⟩, hJ⟩ := mem_actionNbhd_iff.1 hJ
  have hrho : (params d r mu).rho = (params d r mu).l1/2 := rfl
  have h1 : (params d r mu).l1 < blockSlow J0 j ∧ blockSlow J0 j < (params d r mu).l2top :=
    hs j (mem_univ j)
  have h2 : ‖J (Fin.natAdd a j) - (J0 (Fin.natAdd a j) : ℂ)‖ < (params d r mu).l1/2 := by
    have := norm_le_pi_norm (J - KAM.realInclusion (a+b) J0) (Fin.natAdd a j)
    simp only [Pi.sub_apply, KAM.realInclusion_apply] at this
    rw [hrho] at hJ
    exact lt_of_le_of_lt this hJ
  have h3 := params_l2top d r mu
  have hbs : blockSlow J0 j = J0 (Fin.natAdd a j) := rfl
  rw [hbs] at h1
  constructor
  · have := (abs_le.1 (Complex.abs_re_le_norm (J (Fin.natAdd a j) - (J0 (Fin.natAdd a j) : ℂ)))).1
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith [h1.1]
  · have := norm_add_le ((J0 (Fin.natAdd a j) : ℂ))
      (J (Fin.natAdd a j) - (J0 (Fin.natAdd a j) : ℂ))
    rw [add_sub_cancel] at this
    have h4 : ‖(J0 (Fin.natAdd a j) : ℂ)‖ = |J0 (Fin.natAdd a j)| := by simp
    rw [h4, abs_of_pos (by linarith [h1.1])] at this
    have := h1.2
    rw [h3] at this
    linarith

theorem kh_fast_bounds (h : admissible d (pgRstar d) r mu) {J : Fin (a+b) → ℂ}
    (hJ : J ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) :
    ∃ I0 ∈ checkedCore d r mu, ‖blockFast J - KAM.realInclusion a I0‖ < (params d r mu).rho := by
  obtain ⟨J0, ⟨hf, -⟩, hJ⟩ := mem_actionNbhd_iff.1 hJ
  exact ⟨blockFast J0, hf, lt_of_le_of_lt
    (norm_blockFast_sub_le (J := KAM.realInclusion (a+b) J0) (K := J)) hJ⟩

/-- The polar point lies in the averaging domain and has controlled oscillator coordinates. -/
theorem kamPolar_mem (h : admissible d (pgRstar d) r mu) {z : PGComplexPhase (a+b)}
    (hz1 : z.1 ∈ KAM.complexStrip (a+b) (pgWidth d/(12*Real.pi)))
    (hz2 : z.2 ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) :
    kamPolarPt z ∈ averagingDomain d r mu ∧ ∀ j,
      ‖(kamPolarPt z).2 (Fin.natAdd a j)‖ < 2*r ∧ ‖(kamPolarPt z).1 (Fin.natAdd a j)‖ < 2*r := by
  obtain ⟨hr1, -, hrad, hl1, hl12, hlr, -, -⟩ := kh_dyn h
  have hr0 : 0 < r := h.1
  have hw := pgWidth_pos d
  have hw2 := pgWidth_lt_half d
  have hpi := Real.pi_pos
  have hrho : (params d r mu).rho = (params d r mu).l1/2 := rfl
  have hcomp : ∀ j, ‖(kamPolarPt z).2 (Fin.natAdd a j)‖ < 2*r ∧
      ‖(kamPolarPt z).1 (Fin.natAdd a j)‖ < 2*r := by
    intro j
    obtain ⟨-, hn⟩ := kh_slow_bounds h hz2 j
    have hu : ‖(2*z.2 (Fin.natAdd a j))^(1/2:ℂ)‖ < r := by
      have e : ‖(2*z.2 (Fin.natAdd a j))^(1/2:ℂ)‖^2 = 2*‖z.2 (Fin.natAdd a j)‖ := by
        rw [← norm_pow, kh_cpow_half_sq, norm_mul]; simp
      have : ‖(2*z.2 (Fin.natAdd a j))^(1/2:ℂ)‖^2 < r^2 := by rw [e]; linarith
      exact lt_of_pow_lt_pow_left₀ 2 hr0.le this
    have him : |(2*Real.pi * z.1 (Fin.natAdd a j)).im| ≤ 1/2 := by
      have h1 : |(z.1 (Fin.natAdd a j)).im| < pgWidth d/(12*Real.pi) := hz1 _
      have : (2*Real.pi * z.1 (Fin.natAdd a j)).im = 2*Real.pi * (z.1 (Fin.natAdd a j)).im := by
        simp [Complex.mul_im]
      rw [this, abs_mul, abs_of_pos (by positivity)]
      have : 2*Real.pi*(pgWidth d/(12*Real.pi)) = pgWidth d/6 := by field_simp; ring
      nlinarith
    have hex : Real.exp |(2*Real.pi * z.1 (Fin.natAdd a j)).im| ≤ 2 := kh_exp_le_two (abs_nonneg _) him
    rw [kamPolarPt_snd_slow, kamPolarPt_fst_slow]
    refine ⟨?_, ?_⟩
    · rw [norm_mul]
      calc _ ≤ ‖(2*z.2 (Fin.natAdd a j))^(1/2:ℂ)‖*2 := by
            gcongr; exact (kh_norm_cos_le _).trans hex
        _ < 2*r := by linarith
    · rw [norm_mul]
      calc _ ≤ ‖(2*z.2 (Fin.natAdd a j))^(1/2:ℂ)‖*2 := by
            gcongr; exact (kh_norm_sin_le _).trans hex
        _ < 2*r := by linarith
  refine ⟨⟨?_, ?_, ?_⟩, hcomp⟩
  · obtain ⟨I0, hI0, hI⟩ := kh_fast_bounds h hz2
    refine mem_actionNbhd_iff.2 ⟨I0, hI0, ?_⟩
    have : blockFast (kamPolarPt z).2 = blockFast z.2 := by
      funext i; exact kamPolarPt_snd_fast z i
    rw [this]
    refine hI.trans_le ?_
    rw [hrho]; linarith
  · have : blockFast (kamPolarPt z).1 = (2*Real.pi:ℂ) • blockFast z.1 := by
      funext i; exact kamPolarPt_fst_fast z i
    rw [this]
    have hh := (strip_smul_iff (S := pgWidth d/(12*Real.pi)) (by positivity : 0 < 2*Real.pi)
      (blockFast z.1)).2 (fun i => hz1 _)
    have e : 2*Real.pi*(pgWidth d/(12*Real.pi)) = pgWidth d/6 := by field_simp; ring
    rw [e] at hh
    push_cast at hh
    exact hh
  · have h2r : 2*r < pgOscRadius d/2 := by linarith
    rw [Prod.norm_def, max_lt_iff]
    constructor <;> refine (pi_norm_lt_iff (by have := pgOscRadius_pos d; positivity)).2 fun j => ?_
    · exact (hcomp j).1.trans h2r
    · exact (hcomp j).2.trans h2r

theorem kh_ext_fast_mem {w : PGComplexPhase (a+b)} (hw : w ∈ extensionDomain d (pgExtension d).delta) :
    blockFast w.2 ∈ KAM.actionNbhd (closure d.V) (pgExtension d).delta := by
  obtain ⟨w0, hw0, -, hw⟩ := hw
  refine mem_actionNbhd_iff.2 ⟨blockFast w0.2, hw0, lt_of_le_of_lt ?_ hw⟩
  refine (norm_blockFast_sub_le (J := KAM.realInclusion (a+b) w0.2) (K := w.2)).trans ?_
  have : w.2 - KAM.realInclusion (a+b) w0.2 = (w - KAM.realInclusion₂ (a+b) w0).2 := rfl
  rw [this]
  exact norm_snd_le _

/-- On the strip domain the averaging identity reduces `kamF` to the two remainders. -/
theorem kamF_eq (h : admissible d (pgRstar d) r mu) {z : PGComplexPhase (a+b)}
    (hz1 : z.1 ∈ KAM.complexStrip (a+b) (pgWidth d/(12*Real.pi)))
    (hz2 : z.2 ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) :
    kamF d r mu h z = (mu * pgRemainder d mu (blockFast z.2)
      (blockSlow (kamPolarPt z).1, blockSlow (kamPolarPt z).2) +
      (pgAvg d r mu h).remainder (kamPolarPt z))/(2*Real.pi) := by
  obtain ⟨hav, -⟩ := kamPolar_mem h hz1 hz2
  have e := (kh_avg_spec h).2.2.2.1 (kamPolarPt z) hav
  have hact : (Fin.append (blockFast (kamPolarPt z).2)
      (fun j => ((blockSlow (kamPolarPt z).1 j)^2 + (blockSlow (kamPolarPt z).2 j)^2)/2) :
        Fin (a+b) → ℂ) = z.2 := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · rw [Fin.append_left]; exact kamPolarPt_snd_fast z k
    · rw [Fin.append_right]
      have h1 : blockSlow (kamPolarPt z).1 k = _ := kamPolarPt_fst_slow z k
      have h2 : blockSlow (kamPolarPt z).2 k = _ := kamPolarPt_snd_slow z k
      rw [h1, h2]
      have hu := kh_cpow_half_sq (2*z.2 (Fin.natAdd a k))
      have hs := Complex.sin_sq_add_cos_sq (2*Real.pi * z.1 (Fin.natAdd a k))
      linear_combination ((2*z.2 (Fin.natAdd a k))^(1/2:ℂ))^2/2 * hs + (1/2) * hu
  rw [hact] at e
  have e' : (pgExtension d).H0 (blockFast ((pgAvg d r mu h).Psi (kamPolarPt z)).2) +
      mu * (pgExtension d).P mu ((pgAvg d r mu h).Psi (kamPolarPt z)) =
      complexIntegrable d mu z.2 + mu * pgRemainder d mu (blockFast z.2)
        (blockSlow (kamPolarPt z).1, blockSlow (kamPolarPt z).2) +
        (pgAvg d r mu h).remainder (kamPolarPt z) := by
    have hf : blockFast (kamPolarPt z).2 = blockFast z.2 := by
      funext i; exact kamPolarPt_snd_fast z i
    rw [hf] at e
    exact e
  show ((pgExtension d).H0 (blockFast ((pgAvg d r mu h).Psi (kamPolarPt z)).2) +
      mu * (pgExtension d).P mu ((pgAvg d r mu h).Psi (kamPolarPt z)))/(2*Real.pi) -
      kamH d mu z.2 = _
  rw [e', kamH]
  ring

theorem kamF_sup (h : admissible d (pgRstar d) r mu) {z : PGComplexPhase (a+b)}
    (hz1 : z.1 ∈ KAM.complexStrip (a+b) (pgWidth d/(12*Real.pi)))
    (hz2 : z.2 ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) :
    ‖kamF d r mu h z‖ ≤ (2^5*(pgAnalytic d).CQ + 2*(pgAnalytic d).LP)*mu*r^5/(2*Real.pi) := by
  obtain ⟨hav, hcomp⟩ := kamPolar_mem h hz1 hz2
  obtain ⟨-, hr1, -, hl1, hl12, hlr, hrp, -⟩ := kh_dyn h
  have hr0 : 0 < r := h.1
  have hmu0 : 0 < mu := h.2.2.1
  have hspec := pgAnalytic_spec d
  obtain ⟨hρ0, hρδ, hc0, hM0, hAN, hLN, hLB, hμ0, hμ1, hμ2, hLP1, -, hCQ, hr1p, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hrem⟩ := hspec
  have hrho : (params d r mu).rho = (params d r mu).l1/2 := rfl
  obtain ⟨I0, hI0, hI⟩ := kh_fast_bounds h hz2
  have hfast : blockFast (kamPolarPt z).2 ∈ KAM.actionNbhd (closure d.V)
      ((pgExtension d).delta/4) := by
    have : blockFast (kamPolarPt z).2 = blockFast z.2 := by
      funext i; exact kamPolarPt_snd_fast z i
    rw [this]
    refine mem_actionNbhd_iff.2 ⟨I0, subset_closure hI0.1.1, hI.trans_le ?_⟩
    rw [hrho]; linarith
  have hx : ‖(blockSlow (kamPolarPt z).1, blockSlow (kamPolarPt z).2)‖ ≤ 2*r := by
    rw [Prod.norm_def, max_le_iff]
    constructor <;> refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    · exact (hcomp j).2.le
    · exact (hcomp j).1.le
  have hR := hrem mu (mu_mem_Icc h) _ (by
      have : blockFast (kamPolarPt z).2 = blockFast z.2 := by
        funext i; exact kamPolarPt_snd_fast z i
      rw [this] at hfast; exact hfast) _ (hx.trans (by linarith))
  have hA := (kh_avg_spec h).2.2.2.2.2.1 (kamPolarPt z) hav
  rw [kamF_eq h hz1 hz2]
  have hpi := Real.pi_pos
  rw [norm_div]
  have h2 : ‖(2*Real.pi:ℂ)‖ = 2*Real.pi := by simp [abs_of_pos hpi]
  rw [h2]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmu0]
  have hx5 : ‖(blockSlow (kamPolarPt z).1, blockSlow (kamPolarPt z).2)‖^5 ≤ (2*r)^5 :=
    pow_le_pow_left₀ (norm_nonneg _) hx 5
  have hR' : ‖pgRemainder d mu (blockFast z.2)
      (blockSlow (kamPolarPt z).1, blockSlow (kamPolarPt z).2)‖ ≤ (pgAnalytic d).CQ*(2*r)^5 :=
    hR.trans (mul_le_mul_of_nonneg_left hx5 hCQ.le)
  have h3 : mu*‖pgRemainder d mu (blockFast z.2)
      (blockSlow (kamPolarPt z).1, blockSlow (kamPolarPt z).2)‖ ≤ mu*((pgAnalytic d).CQ*(2*r)^5) :=
    mul_le_mul_of_nonneg_left hR' hmu0.le
  nlinarith

theorem kamPolarPt_differentiableAt {z : PGComplexPhase (a+b)}
    (hs : ∀ j, 0 < (z.2 (Fin.natAdd a j)).re) :
    DifferentiableAt ℂ kamPolarPt z := by
  have hsl : ∀ k, (2*z.2 (Fin.natAdd a k)) ∈ Complex.slitPlane := fun k => by
    rw [Complex.mem_slitPlane_iff]; left; simp [hs k]
  have h1 : ∀ k, DifferentiableAt ℂ (fun w : PGComplexPhase (a+b) =>
      2*w.2 (Fin.natAdd a k)) z := fun k => by fun_prop
  have h2 : ∀ k, DifferentiableAt ℂ (fun w : PGComplexPhase (a+b) =>
      2*(Real.pi:ℂ) * w.1 (Fin.natAdd a k)) z := fun k => by fun_prop
  have hc : ∀ k, DifferentiableAt ℂ (fun w : PGComplexPhase (a+b) =>
      (2*w.2 (Fin.natAdd a k))^(1/2:ℂ)) z := fun k => (h1 k).cpow_const (hsl k)
  refine DifferentiableAt.prodMk (differentiableAt_pi.2 fun i => ?_)
    (differentiableAt_pi.2 fun i => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · show DifferentiableAt ℂ (fun w : PGComplexPhase (a+b) => (kamPolarPt w).1 (Fin.castAdd b k)) z
      simp only [kamPolarPt_fst_fast]
      fun_prop
    · show DifferentiableAt ℂ (fun w : PGComplexPhase (a+b) => (kamPolarPt w).1 (Fin.natAdd a k)) z
      simp only [kamPolarPt_fst_slow]
      exact (hc k).mul (h2 k).csin
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · show DifferentiableAt ℂ (fun w : PGComplexPhase (a+b) => (kamPolarPt w).2 (Fin.castAdd b k)) z
      simp only [kamPolarPt_snd_fast]
      fun_prop
    · show DifferentiableAt ℂ (fun w : PGComplexPhase (a+b) => (kamPolarPt w).2 (Fin.natAdd a k)) z
      simp only [kamPolarPt_snd_slow]
      exact (hc k).mul (h2 k).ccos

/-- The strip domain of width `pgWidth/(12π)`. -/
theorem kamF_differentiableOn (h : admissible d (pgRstar d) r mu) :
    DifferentiableOn ℂ (kamF d r mu h)
      {z | z.1 ∈ KAM.complexStrip (a+b) (pgWidth d/(12*Real.pi)) ∧
        z.2 ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho} := by
  set S : Set (PGComplexPhase (a+b)) :=
    {z | z.1 ∈ KAM.complexStrip (a+b) (pgWidth d/(12*Real.pi)) ∧
        z.2 ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho} with hS
  have hmu := mu_mem_Icc h
  have hspec := kh_avg_spec h
  have hpt : DifferentiableOn ℂ kamPolarPt S := fun z hz => by
    obtain ⟨-, -, -, hl1, -⟩ := kh_dyn h
    exact (kamPolarPt_differentiableAt (fun j =>
      lt_trans (by linarith) (kh_slow_bounds h hz.2 j).1)).differentiableWithinAt
  have hmaps : MapsTo kamPolarPt S (averagingDomain d r mu) := fun z hz =>
    (kamPolar_mem h hz.1 hz.2).1
  have hQ : DifferentiableOn ℂ ((pgAvg d r mu h).Psi ∘ kamPolarPt) S :=
    hspec.1.comp hpt hmaps
  have hmaps2 : MapsTo ((pgAvg d r mu h).Psi ∘ kamPolarPt) S
      (extensionDomain d (pgExtension d).delta) := fun z hz => hspec.2.2.1 (hmaps hz)
  have hP := ((pgExtension d).holo mu hmu).comp hQ hmaps2
  have hH0 : DifferentiableOn ℂ (fun w : PGComplexPhase (a+b) =>
      (pgExtension d).H0 (blockFast w.2)) (extensionDomain d (pgExtension d).delta) :=
    (pgExtension d).h0holo.comp
      (differentiable_blockFast.comp differentiable_snd).differentiableOn
      (fun w hw => kh_ext_fast_mem hw)
  have hH := hH0.comp hQ hmaps2
  have hK : DifferentiableOn ℂ (fun z : PGComplexPhase (a+b) => kamH d mu z.2) S :=
    (kamH_differentiableOn h).comp differentiable_snd.differentiableOn (fun z hz => hz.2)
  have h1 := hH.add (hP.const_mul (mu:ℂ))
  have h2 := h1.mul (differentiableOn_const ((2*Real.pi:ℂ)⁻¹))
  have := h2.sub hK
  refine this.congr fun z hz => ?_
  simp [kamF, kamPolarPt, Function.comp_def, div_eq_mul_inv]

end KAM.Planetary

end
