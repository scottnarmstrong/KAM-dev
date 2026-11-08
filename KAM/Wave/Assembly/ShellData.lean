/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellGeom

/-!
# W8: sizes of the shell data (blueprint `bpW:w8:const`, `bpW:w8:shell-data` (i))

Blueprint labels `bpW:w8:const`, `bpW:w8:shells`, and the W5/W6-free part (i)
of `bpW:w8:shell-data` (milestone W8).

Signs of the W8 constants (`w8T0_pos`, …) and, for `t₀ = w8T0 m hm u`, the size facts of
`bpW:w8:shell-data` (i): `0 < t_n ≤ t₀ ≤ 4^{-64}`, `α_n ≤ min(α₀, t_n)`, `r_n ≤ 1`,
`r_n² ≤ α_n/4`, `κ_n ≤ 1`, `ε^♯_n ≤ γ α_n`, `ρ_n² ≤ 2 c_A t_n < ρ₁²/2` (`w8_shellData_sizes`).
Parts (iii), (iv) of `bpW:w8:shell-data` are statements about W5's Proposition `bpW:w5:initial`
and W6's Lemma `bpW:w6:prep-step` and are not treated here.
-/

public section

open Set

namespace KAM.Wave

variable {m : ℝ} (hm : 0 < m) (u : W8UpstreamConsts)

include hm in
theorem w8CF_pos : 0 < w8CF m := birkCF_pos m hm (by norm_num)

theorem w8M_pos : 0 < w8M m hm := by
  have h1 : 0 < lam m hm 1 := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < lam m hm 2 := Real.sqrt_pos.2 (by positivity)
  unfold w8M waveMomega waveMOmega
  positivity

include hm in
theorem w8E1_ge_one : 1 ≤ w8E1 m := by
  have hC := waveCubicConst_nonneg 1
  have hF := (w8CF_pos hm).le
  unfold w8E1 w8CKp w8CStar
  have : 0 ≤ 6 * (2 * w8cA) ^ (5 / 2 : ℝ) * (66 * waveCubicConst 1 * w8CF m) := by
    unfold w8cA; positivity
  linarith

theorem w8E3_pos : 0 < w8E3 m hm := by
  have := w8M_pos hm
  have := w8E1_ge_one hm
  unfold w8E3; positivity

theorem w8E4_pos : 0 < w8E4 u := by
  have := u.gam_pos; have := u.gam1_pos; have := u.cF_pos; have := u.cFnat_pos
  unfold w8E4 w8SigmaP w8Sigma0; positivity

theorem w8E5_pos : 0 < w8E5 m hm u := by
  have := w8E3_pos hm; have := w8E4_pos u; have := u.gam_pos
  unfold w8E5; positivity

include hm in
theorem w8Rho1_pos : 0 < w8Rho1 m := by
  have := w8CF_pos hm
  unfold w8Rho1; positivity

/-- `α₀ > 0` (W7 (C4)). -/
theorem w8Alpha0_pos : 0 < measAlpha0 m hm := by
  have h1 := measBetaStar_pos hm
  have h2 := measTheta_pos m hm
  have h3 := measCX_pos m hm
  have h4 : (0 : ℝ) < measKstar m hm := by linarith [measKstar_pos m hm]
  unfold measAlpha0
  refine Real.rpow_pos_of_pos (lt_min (lt_min (by norm_num) (by positivity)) (by positivity)) _

/-- `t₀ > 0` (blueprint `bpW:w8:const`; Step `stepW:w8:p-pos`). -/
theorem w8T0_pos : 0 < w8T0 m hm u := by
  have := w8Alpha0_pos hm
  have := w8Rho1_pos hm
  have := w8E3_pos hm
  have := w8E5_pos hm u
  have := u.gam_pos
  unfold w8T0
  refine lt_min (lt_min (lt_min (lt_min (by norm_num) (Real.rpow_pos_of_pos ‹_› _)) ?_) ?_) ?_
  · unfold w8cA; positivity
  · positivity
  · positivity

/-- The five entries of `t₀` bound it (blueprint `bpW:w8:const`). -/
theorem w8T0_le :
    w8T0 m hm u ≤ (1 / 4 : ℝ) ^ 64 ∧ w8T0 m hm u ≤ measAlpha0 m hm ^ (64 / 95 : ℝ) ∧
      w8T0 m hm u ≤ w8Rho1 m ^ 2 / (8 * w8cA) ∧ w8T0 m hm u ≤ (u.gam / w8E3 m hm) ^ 64 ∧
      w8T0 m hm u ≤ (7 / (256 * w8E5 m hm u)) ^ 64 := by
  unfold w8T0
  refine ⟨?_, ?_, ?_, ?_, min_le_right _ _⟩
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans
      (min_le_left _ _)))
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans
      (min_le_right _ _)))
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  · exact (min_le_left _ _).trans (min_le_right _ _)

/-- `x ≤ y^64` with `x ≥ 0`, `y ≥ 0` gives `x^{1/64} ≤ y`. -/
theorem rpow_one_div_64_le_of_le_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ y ^ 64) :
    x ^ (1 / 64 : ℝ) ≤ y := by
  have e : (1 / 64 : ℝ) = ((64 : ℕ) : ℝ)⁻¹ := by norm_num
  calc x ^ (1 / 64 : ℝ) ≤ (y ^ 64) ^ (1 / 64 : ℝ) := Real.rpow_le_rpow hx h (by norm_num)
    _ = y := by rw [e]; exact Real.pow_rpow_inv_natCast hy (by norm_num)

/-- `t_n^{1/64} ≤ t₀^{1/64}` and `t_n ≤ 1` for `t₀ = w8T0 m hm u`. -/
theorem w8tn_facts (n : ℕ) :
    0 < w8tn (w8T0 m hm u) n ∧ w8tn (w8T0 m hm u) n ≤ w8T0 m hm u ∧
      w8T0 m hm u ≤ (1 / 4 : ℝ) ^ 64 ∧ w8tn (w8T0 m hm u) n ≤ 1 ∧
      w8tn (w8T0 m hm u) n ^ (1 / 64 : ℝ) ≤ w8T0 m hm u ^ (1 / 64 : ℝ) := by
  have hT := w8T0_pos hm u
  have h1 := w8tn_pos hT n
  have h2 := w8tn_le hT n
  have h3 := (w8T0_le hm u).1
  refine ⟨h1, h2, h3, ?_, Real.rpow_le_rpow h1.le h2 (by norm_num)⟩
  have : (1 / 4 : ℝ) ^ 64 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- (`bpW:w8:shell-data` (i), Step `stepW:w8:sd-size`) `α_n ≤ α₀` and `α_n ≤ t_n`. -/
theorem w8alpha_le (n : ℕ) :
    w8alpha (w8T0 m hm u) n ≤ measAlpha0 m hm ∧
      w8alpha (w8T0 m hm u) n ≤ w8tn (w8T0 m hm u) n := by
  obtain ⟨h1, h2, -, h4, -⟩ := w8tn_facts hm u n
  have hT := w8T0_pos hm u
  have ha0 := (w8Alpha0_pos hm).le
  refine ⟨?_, ?_⟩
  · calc w8alpha (w8T0 m hm u) n ≤ w8T0 m hm u ^ (95 / 64 : ℝ) :=
          Real.rpow_le_rpow h1.le h2 (by norm_num)
      _ ≤ (measAlpha0 m hm ^ (64 / 95 : ℝ)) ^ (95 / 64 : ℝ) :=
          Real.rpow_le_rpow hT.le (w8T0_le hm u).2.1 (by norm_num)
      _ = measAlpha0 m hm := by
          rw [← Real.rpow_mul ha0]; norm_num
  · calc w8alpha (w8T0 m hm u) n ≤ w8tn (w8T0 m hm u) n ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge h1 h4 (by norm_num)
      _ = _ := Real.rpow_one _

/-- (`bpW:w8:shell-data` (i)) `r_n ≤ 1` and `r_n² = t_n^{1/64} α_n ≤ α_n/4`. -/
theorem w8rn_le (n : ℕ) :
    w8rn (w8T0 m hm u) n ≤ 1 ∧ w8rn (w8T0 m hm u) n ^ 2 ≤ w8alpha (w8T0 m hm u) n / 4 := by
  obtain ⟨h1, -, h3, h4, h5⟩ := w8tn_facts hm u n
  have hT := w8T0_pos hm u
  refine ⟨Real.rpow_le_one h1.le h4 (by norm_num), ?_⟩
  have hsq : w8rn (w8T0 m hm u) n ^ 2 =
      w8tn (w8T0 m hm u) n ^ (1 / 64 : ℝ) * w8alpha (w8T0 m hm u) n := by
    rw [w8rn, w8alpha, ← Real.rpow_natCast, ← Real.rpow_mul h1.le, ← Real.rpow_add h1]
    norm_num
  have hq : w8T0 m hm u ^ (1 / 64 : ℝ) ≤ 1 / 4 :=
    rpow_one_div_64_le_of_le_pow hT.le (by norm_num) h3
  have hα := (w8alpha_pos hT n).le
  rw [hsq]
  nlinarith

/-- (`bpW:w8:shell-data` (i)) `κ_n ≤ 1`, hence `ε^♯_n ≤ γ α_n`. -/
theorem w8kappa_le (n : ℕ) :
    w8kappa m hm u (w8T0 m hm u) n ≤ 1 ∧
      w8epsSharp m hm (w8T0 m hm u) n ≤ u.gam * w8alpha (w8T0 m hm u) n := by
  obtain ⟨h1, -, -, -, h5⟩ := w8tn_facts hm u n
  have hT := w8T0_pos hm u
  have hE := w8E3_pos hm
  have hg := u.gam_pos
  have hα := w8alpha_pos hT n
  have hq : w8T0 m hm u ^ (1 / 64 : ℝ) ≤ u.gam / w8E3 m hm :=
    rpow_one_div_64_le_of_le_pow hT.le (by positivity) (w8T0_le hm u).2.2.2.1
  have hk : w8kappa m hm u (w8T0 m hm u) n ≤ 1 := by
    rw [w8kappa_eq m hm u hT]
    calc w8E3 m hm / u.gam * w8tn (w8T0 m hm u) n ^ (1 / 64 : ℝ)
        ≤ w8E3 m hm / u.gam * (u.gam / w8E3 m hm) := by gcongr; exact h5.trans hq
      _ = 1 := by field_simp
  refine ⟨hk, ?_⟩
  have e : w8epsSharp m hm (w8T0 m hm u) n =
      w8kappa m hm u (w8T0 m hm u) n * (u.gam * w8alpha (w8T0 m hm u) n) := by
    rw [w8kappa]; field_simp
  rw [e]
  have : 0 < u.gam * w8alpha (w8T0 m hm u) n := by positivity
  nlinarith

/-- (`bpW:w8:shell-data` (i)) `ρ_n² ≤ 2 c_A t_n < ρ₁²/2`. -/
theorem w8rho_sq_le (n : ℕ) :
    w8rho (w8T0 m hm u) n ^ 2 ≤ 2 * w8cA * w8tn (w8T0 m hm u) n ∧
      2 * w8cA * w8tn (w8T0 m hm u) n < w8Rho1 m ^ 2 / 2 := by
  obtain ⟨h1, h2, -, -, -⟩ := w8tn_facts hm u n
  obtain ⟨-, hr⟩ := w8rn_le hm u n
  obtain ⟨-, hαt⟩ := w8alpha_le hm u n
  have hρ := w8Rho1_pos hm
  have hcA : (0 : ℝ) < w8cA := by unfold w8cA; norm_num
  have hr2 : w8rn (w8T0 m hm u) n ^ 2 ≤ w8tn (w8T0 m hm u) n := by
    have := (w8alpha_pos (w8T0_pos hm u) n).le
    linarith
  refine ⟨?_, ?_⟩
  · rw [w8rho, Real.sq_sqrt (by positivity)]
    nlinarith
  · have h3 := (w8T0_le hm u).2.2.1
    have : 2 * w8cA * w8tn (w8T0 m hm u) n ≤ w8Rho1 m ^ 2 / 4 := by
      calc 2 * w8cA * w8tn (w8T0 m hm u) n ≤ 2 * w8cA * (w8Rho1 m ^ 2 / (8 * w8cA)) := by
            gcongr; exact h2.trans h3
        _ = w8Rho1 m ^ 2 / 4 := by field_simp; ring
    have : 0 < w8Rho1 m ^ 2 := by positivity
    linarith

/-- **Shell data, sizes** (blueprint `bpW:w8:shell-data` (i), W5/W6-free part), for
`t₀ = w8T0 m hm u`. -/
theorem w8_shellData_sizes (n : ℕ) :
    let t0 := w8T0 m hm u
    (0 < w8tn t0 n ∧ w8tn t0 n ≤ t0 ∧ t0 ≤ (1 / 4 : ℝ) ^ 64) ∧
      (w8alpha t0 n ≤ measAlpha0 m hm ∧ w8alpha t0 n ≤ w8tn t0 n) ∧
      w8rn t0 n ≤ 1 ∧ w8rn t0 n ^ 2 ≤ w8alpha t0 n / 4 ∧
      w8kappa m hm u t0 n ≤ 1 ∧ w8epsSharp m hm t0 n ≤ u.gam * w8alpha t0 n ∧
      w8rho t0 n ^ 2 ≤ 2 * w8cA * w8tn t0 n ∧ 2 * w8cA * w8tn t0 n < w8Rho1 m ^ 2 / 2 := by
  obtain ⟨h1, h2, h3, -, -⟩ := w8tn_facts hm u n
  exact ⟨⟨h1, h2, h3⟩, w8alpha_le hm u n, (w8rn_le hm u n).1, (w8rn_le hm u n).2,
    (w8kappa_le hm u n).1, (w8kappa_le hm u n).2, (w8rho_sq_le hm u n).1,
    (w8rho_sq_le hm u n).2⟩

end KAM.Wave

end
