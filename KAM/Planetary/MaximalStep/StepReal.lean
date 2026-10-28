/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Step

/-!
# Reality of the canonical step (P11A-C8, `stepP:p11a:cs-lip`, reality clauses)

With the explicit guard `p11Real ... R`: the cutoff coefficients, the homological generators, the
averages, the time-one map at real points and the remainder are real at real points.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ} {w : P11CVec n → P11CVec n}
  {R : P11Family n → ℂ}

theorem step_R1_eq (H : P11StepHyp S h w R) {b : P11CVec n} (hb : b ∈ KAM.actionNbhd S.E S.t)
    (θ : P11CVec n) (i : Fin n) :
    p11R1 S.T R (θ, b) i = ((2 / S.s : ℝ) : ℂ) *
      (p11Cutoff S.T R ((θ, ((S.s / 2 : ℝ) : ℂ) • Pi.single i 1), b) -
        p11Cutoff S.T R ((θ, 0), b)) := by
  obtain ⟨-, -, -, -, -, -, c7⟩ := p11_cutoff_coeff S.n_pos (step_r_pos S) S.s_pos S.T_pos.le
    S.d_pos (step_dr S) S.eps_nonneg (step_B_open S) H.admissible H.bound
  have hs : (S.s : ℂ) ≠ 0 := by exact_mod_cast S.s_pos.ne'
  rw [c7 ((θ, ((S.s / 2 : ℝ) : ℂ) • Pi.single i 1), b) hb, c7 ((θ, 0), b) hb]
  simp [Pi.single_apply]
  field_simp

theorem step_R_real (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) :
    ∀ x b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t →
      (p11R0 S.T R (KAM.realInclusion n x, KAM.realInclusion n b)).im = 0 ∧
      ∀ i, (p11R1 S.T R (KAM.realInclusion n x, KAM.realInclusion n b) i).im = 0 := by
  obtain ⟨-, -, -, cu4⟩ := p11_cutoff S.n_pos (step_r_pos S) S.s_pos S.T_pos.le S.d_pos
    (step_dr S) S.eps_nonneg (q := 1/2) (by norm_num) (by norm_num) (step_B_open S)
    H.admissible H.bound
  have hc := cu4 hreal
  intro x b hb
  have hr : 0 < S.r - S.d := by linarith [step_dr S]
  have hmem : ∀ y : P11Vec n, ‖KAM.realInclusion n y‖ < S.s →
      (KAM.realInclusion₂ n (x, y), KAM.realInclusion n b) ∈
        domain_def n (S.r - S.d) S.s (KAM.actionNbhd S.E S.t) := fun y hy =>
    p11_mem_domain_def.mpr ⟨KAM.ofReal_mem_complexStrip hr x, hy, hb⟩
  have h0 : ‖KAM.realInclusion n (0 : P11Vec n)‖ < S.s := by simpa using S.s_pos
  have c0 := hc (x, 0) b (by simpa using hmem 0 h0)
  have e0 : p11R0 S.T R (KAM.realInclusion n x, KAM.realInclusion n b) =
      p11Cutoff S.T R (KAM.realInclusion₂ n (x, 0), KAM.realInclusion n b) := by simp [p11R0]
  refine ⟨by rw [e0]; exact c0, fun i => ?_⟩
  set y : P11Vec n := Pi.single i (S.s / 2) with hy
  have hyc : KAM.realInclusion n y = ((S.s / 2 : ℝ) : ℂ) • (Pi.single i 1 : P11CVec n) := by
    ext j; by_cases hj : j = i <;> simp [hy, Pi.single_apply, hj]
  have hyn : ‖KAM.realInclusion n y‖ < S.s := by
    rw [hyc]; exact norm_half_single S.s_pos i
  have c1 := hc (x, y) b (hmem y hyn)
  rw [step_R1_eq H hb, Complex.im_ofReal_mul, ← hyc]
  have : (p11Cutoff S.T R ((KAM.realInclusion n x, KAM.realInclusion n y),
      KAM.realInclusion n b) -
      p11Cutoff S.T R ((KAM.realInclusion n x, 0), KAM.realInclusion n b)).im = 0 := by
    rw [Complex.sub_im]
    simp only [KAM.realInclusion₂_apply, map_zero] at c0 c1
    rw [c1, c0]; simp
  rw [this, mul_zero]

theorem step_hm_real (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) :
    ∀ x b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t →
      (stepP0 S w R (KAM.realInclusion n x, KAM.realInclusion n b)).im = 0 ∧
      ∀ i, (stepP1 S w R (KAM.realInclusion n x, KAM.realInclusion n b) i).im = 0 := by
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := p11_cutoff_coeff S.n_pos (step_r_pos S) S.s_pos
    S.T_pos.le S.d_pos (step_dr S) S.eps_nonneg (step_B_open S) H.admissible H.bound
  have hr : 0 < S.r - S.d := by linarith [step_dr S]
  have hR := step_R_real H hreal
  intro x b hb
  refine ⟨?_, fun i => ?_⟩
  · exact homological_maximal_real hr S.T_pos S.D_pos (step_B_open S) w H.holw (step_hdiv H) _
      c1 c3 H.realw (fun x' b' hb' => (hR x' b' hb').1) x b hb
  · exact homological_maximal_real hr S.T_pos S.D_pos (step_B_open S) w H.holw (step_hdiv H) _
      (c2 i) (c4 i) H.realw (fun x' b' hb' => (hR x' b' hb').2 i) x b hb

theorem coeff_zero_real {b : P11CVec n} {P : P11CVec n × P11CVec n → ℂ}
    (hP : ∀ x : P11Vec n, (P (KAM.realInclusion n x, b)).im = 0) :
    (KAM.Weighted.coeff P b 0).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold KAM.Weighted.coeff KAM.torusCoeffW KAM.torusAverage
  rw [← integral_conj]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) ?_
  intro x _
  have h' : (starRingEnd ℂ) (P (fun j => (x j : ℂ), b)) = P (fun j => (x j : ℂ), b) :=
    Complex.conj_eq_iff_im.2 (hP x)
  simpa [KAM.character_zero] using h'

theorem step_avg_real (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) (b : P11Vec n)
    (hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t) :
    (p11DeltaH S.T R (KAM.realInclusion n b)).im = 0 ∧
      ∀ i, (p11DeltaW S.T R (KAM.realInclusion n b) i).im = 0 := by
  have hR := step_R_real H hreal
  refine ⟨coeff_zero_real fun x => (hR x b hb).1, fun i => ?_⟩
  exact coeff_zero_real (P := fun z => p11R1 S.T R z i) fun x => (hR x b hb).2 i

theorem step_real_flow (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) :
    ∀ x : Phase n, ∀ b : P11Vec n,
      (KAM.realInclusion₂ n x, KAM.realInclusion n b) ∈
        domain_def n (S.r - S.d - S.delta - 2 * S.sigma) (S.q * S.s) (KAM.actionNbhd S.E S.t) →
      ∀ i, ((p11StepMap S w R (KAM.realInclusion₂ n x, KAM.realInclusion n b)).1 i).im = 0 ∧
        ((p11StepMap S w R (KAM.realInclusion₂ n x, KAM.realInclusion n b)).2 i).im = 0 := by
  intro x b hz
  have hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t := hz.2
  have Hb := step_affHyp H hb
  have hreal' := step_hm_real H hreal
  have hRO : KAM.Canonical.RealOn (KAM.Weighted.Dom n {0} S.s (S.r - S.d - S.delta))
      (p11Affine (fun θ => stepP0 S w R (θ, KAM.realInclusion n b))
        (fun θ => stepP1 S w R (θ, KAM.realInclusion n b))) := by
    intro x' _
    obtain ⟨a0, a1⟩ := hreal' x'.1 b hb
    simp only [p11Affine, KAM.realInclusion₂_apply, Complex.add_im, Complex.im_sum,
      Complex.mul_im, a0, a1]
    simp [KAM.realInclusion]
  exact (affine_flow Hb).2.2.2.2.2.2.2.2.2 hRO x (step_z_mem S hz.1)

theorem step_Rp_real (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) :
    p11Real (domain_def n (S.r - S.d - S.delta - 2 * S.sigma) (S.q * S.s)
      (KAM.actionNbhd S.E S.t)) (p11StepRemainder S h w R) := by
  intro x b hz
  have hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t := hz.2
  have hF := step_real_flow H hreal x b hz
  have hmaps := step_mapsU H _ hz
  -- the image point is real
  set Fz := p11StepMap S w R (KAM.realInclusion₂ n x, KAM.realInclusion n b) with hFz
  set y : Phase n := (fun i => (Fz.1 i).re, fun i => (Fz.2 i).re) with hy
  have hFy : KAM.realInclusion₂ n y = Fz := by
    ext i
    · simp [y, KAM.realInclusion₂]
      exact Complex.ext rfl (by simpa using (hF i).1.symm)
    · simp [y, KAM.realInclusion₂]
      exact Complex.ext rfl (by simpa using (hF i).2.symm)
  have hRy : (R (Fz, KAM.realInclusion n b)).im = 0 := by
    have hm : (KAM.realInclusion₂ n y, KAM.realInclusion n b) ∈
        domain_def n S.r S.s (KAM.actionNbhd S.E S.t) := by
      rw [hFy]
      exact domain_def_mono (show S.r - S.d - S.delta - 2 * S.sigma + S.sigma ≤ S.r by
        linarith [S.d_pos, S.delta_pos, S.sigma_pos]) hmaps
    have := hreal y b hm
    rwa [hFy] at this
  obtain ⟨hΔH, hΔW⟩ := step_avg_real H hreal b hb
  have hw := H.realw b hb
  have hh := H.realh b hb
  have hηx : ∀ i, ((KAM.realInclusion₂ n x).2 i).im = 0 := fun i => by simp [KAM.realInclusion₂]
  have e : p11StepRemainder S h w R (KAM.realInclusion₂ n x, KAM.realInclusion n b) =
      (h (KAM.realInclusion n b) + ∑ i, w (KAM.realInclusion n b) i * Fz.2 i +
        R (Fz, KAM.realInclusion n b)) -
      ((h (KAM.realInclusion n b) + p11DeltaH S.T R (KAM.realInclusion n b)) +
        ∑ i, (w (KAM.realInclusion n b) i + p11DeltaW S.T R (KAM.realInclusion n b) i) *
          (KAM.realInclusion₂ n x).2 i) := rfl
  rw [e]
  simp only [Complex.sub_im, Complex.add_im, Complex.im_sum, Complex.mul_im, hh, hw, hΔH,
    hΔW, hRy, (hF _).2, hηx]
  simp

end KAM.Planetary

end
