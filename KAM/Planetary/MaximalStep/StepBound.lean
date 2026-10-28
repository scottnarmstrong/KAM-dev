/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.StepLie

/-!
# The size of the Lie integrand (P11A-C8, `stepP:p11a:cs-u`)

For `b ∈ B`, the function `u_t = (1-t) w + R(·, b)` with `w = -(R_* - ⟨R_*⟩)` is holomorphic on
`D(r-d, s)` and bounded there by `U = ε (5 + 4 E_T)`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ}

/-- The average `⟨R_*⟩(η, b) = ΔH(b) + ΔW(b) · η`. -/
def stepAvg (S : P11Step n) (R : P11Family n → ℂ) (b η : P11CVec n) : ℂ :=
  p11DeltaH S.T R b + ∑ i, p11DeltaW S.T R b i * η i

/-- `w = {N_b, φ} = -(R_* - ⟨R_*⟩)` as an explicit function of the phase point. -/
def stepW (S : P11Step n) (R : P11Family n → ℂ) (b : P11CVec n) (y : P11Phase n) : ℂ :=
  -(p11Cutoff S.T R (y, b) - stepAvg S R b y.2)

/-- `u_t = (1-t) w + R(·, b)`. -/
def stepU (S : P11Step n) (R : P11Family n → ℂ) (b : P11CVec n) (t : ℝ) (y : P11Phase n) : ℂ :=
  ((1 - t : ℝ) : ℂ) * stepW S R b y + R (y, b)

theorem coeff_congr_param {b : P11CVec n} {u v : P11CVec n × P11CVec n → ℂ}
    (h : ∀ θ, u (θ, b) = v (θ, b)) (k : Fin n → ℤ) :
    KAM.Weighted.coeff u b k = KAM.Weighted.coeff v b k := by
  simp only [KAM.Weighted.coeff, h]

variable {S : P11Step n} {h : P11CVec n → ℂ} {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ}

theorem step_avg_eq (H : P11StepHyp S h w R) {b : P11CVec n} (hb : b ∈ KAM.actionNbhd S.E S.t)
    (η : P11CVec n) :
    p11AngleAverage (fun u => p11Cutoff S.T R ((u.1, η), u.2)) b = stepAvg S R b η := by
  have cc := p11_cutoff_coeff S.n_pos (step_r_pos S) S.s_pos S.T_pos.le S.d_pos (step_dr S)
    S.eps_nonneg (step_B_open S) H.admissible H.bound
  obtain ⟨c1, c2, -, -, -, -, c7⟩ := cc
  have hr : 0 < S.r - S.d := by have := S.radius; have := S.delta_pos; have := S.sigma_pos; linarith
  have hcont : ∀ f : P11CVec n × P11CVec n → ℂ,
      p11AngleClass (S.r - S.d) (KAM.actionNbhd S.E S.t) f →
      Continuous fun x : Fin n → ℝ => f (fun j => (x j : ℂ), b) := fun f hf =>
    hf.1.continuousOn.comp_continuous (f := fun x : Fin n → ℝ => ((fun j => (x j : ℂ), b) :
      P11CVec n × P11CVec n)) (by fun_prop) fun x => ⟨KAM.ofReal_mem_complexStrip hr x, hb⟩
  have e : ∀ θ, p11Cutoff S.T R ((θ, η), b) = p11R0 S.T R (θ, b) +
      ∑ i, η i * p11R1 S.T R (θ, b) i := fun θ => by
    rw [c7 ((θ, η), b) hb]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  unfold p11AngleAverage
  rw [coeff_congr_param (v := fun u => p11R0 S.T R u + ∑ i, η i * p11R1 S.T R u i) e 0]
  rw [coeff_add_sum (g := fun i u => p11R1 S.T R u i) η (hcont _ c1) (fun i => hcont _ (c2 i)) 0]
  unfold stepAvg p11DeltaH p11DeltaW p11AngleAverage
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem step_avg_le (H : P11StepHyp S h w R) {b : P11CVec n} (hb : b ∈ KAM.actionNbhd S.E S.t)
    {η : P11CVec n} (hη : ‖η‖ < S.s) :
    ‖stepAvg S R b η‖ ≤ 2 * (1 + p11Error n S.T S.d) * S.eps := by
  obtain ⟨cu1, cu2, -, -⟩ := p11_cutoff S.n_pos (step_r_pos S) S.s_pos S.T_pos.le S.d_pos
    (step_dr S) S.eps_nonneg (q := 1/2) (by norm_num) (by norm_num) (step_B_open S)
    H.admissible H.bound
  have hr : 0 < S.r - S.d := by have := S.radius; have := S.delta_pos; have := S.sigma_pos; linarith
  have hP : p11AngleClass (S.r - S.d) (KAM.actionNbhd S.E S.t)
      (fun u => p11Cutoff S.T R ((u.1, η), u.2)) := by
    refine ⟨?_, fun j z hz => ?_⟩
    · refine cu1.1.comp (f := fun u : P11CVec n × P11CVec n => ((u.1, η), u.2)) (by fun_prop) ?_
      rintro ⟨θ, b'⟩ ⟨h1, h2⟩
      exact p11_mem_domain_def.mpr ⟨h1, hη, h2⟩
    · exact cu1.2 j ((z.1, η), z.2) (p11_mem_domain_def.mpr ⟨hz.1, hη, hz.2⟩)
  have hbd : p11Bound (KAM.complexStrip n (S.r - S.d) ×ˢ KAM.actionNbhd S.E S.t)
      (fun u => p11Cutoff S.T R ((u.1, η), u.2)) (2 * (1 + p11Error n S.T S.d) * S.eps) :=
    fun u hu => cu2 _ (p11_mem_domain_def.mpr ⟨hu.1, hη, hu.2⟩)
  have := norm_coeff_le hr hP hbd hb 0
  rw [← step_avg_eq H hb η]
  simpa [KAM.Fourier.modeSize, p11AngleAverage] using this

theorem step_W_le (H : P11StepHyp S h w R) {b : P11CVec n} (hb : b ∈ KAM.actionNbhd S.E S.t)
    {y : P11Phase n} (hy : y ∈ KAM.Weighted.Dom n {0} S.s (S.r - S.d)) :
    ‖stepW S R b y‖ ≤ 4 * (1 + p11Error n S.T S.d) * S.eps := by
  obtain ⟨cu1, cu2, -, -⟩ := p11_cutoff S.n_pos (step_r_pos S) S.s_pos S.T_pos.le S.d_pos
    (step_dr S) S.eps_nonneg (q := 1/2) (by norm_num) (by norm_num) (step_B_open S)
    H.admissible H.bound
  obtain ⟨hy1, hy2⟩ := mem_Dom_iff y |>.1 hy
  have h1 := cu2 (y, b) (p11_mem_domain_def.mpr ⟨hy1, hy2, hb⟩)
  have h2 := step_avg_le H hb hy2
  unfold stepW
  rw [norm_neg]
  refine (norm_sub_le _ _).trans ?_
  linarith

end KAM.Planetary

end
