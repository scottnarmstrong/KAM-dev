/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Recon.ReconAnalytic
public import KAM.Wave.Normal.Analysis.PdeForward

/-!
# Reconstruction functionals (blueprint `bpW:w2:derived`, `bpW:w2:functionals`)

Infrastructure used by several nodes; the dependency graph is still being built. Blueprint label
`bpW:w2:derived`, `bpW:w2:functionals` (milestone W2, PDE reconstruction).

* `KAM.Wave.reconUx`, `KAM.Wave.reconUxx`: the termwise `x`-derivatives `D¹`, `D²` of the series
  `reconU` (Definition `bpW:w2:derived`); `KAM.Wave.reconUx_eq_iter`, `KAM.Wave.reconUxx_eq_iter`
  identify them with `reconUIter 1`, `reconUIter 2`.
* `KAM.Wave.reconWave_functionals` (Lemma `bpW:w2:functionals`): the four real analytic maps
  `Ψ⁰, Ψ¹, Ψ², Ψᵛ : ℝ → ℓ²` with pairings, norm bounds, derivative and boundary values.
* `KAM.Wave.reconWaveC0`, `KAM.Wave.reconWaveBound`: the constants `c₀` and `M_m`.
-/

@[expose] public noncomputable section

open Real
open scoped ENNReal

namespace KAM.Wave

/-- `D¹ y (x) = Σ_j κ(y)_j / √λ_j · √(2/π) j cos (j x)` (blueprint `bpW:w2:derived`). -/
def reconUx (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) : ℝ :=
  ∑' j : ℕ+, coeff y j / Real.sqrt (lam m hm j) * (Real.sqrt (2 / π) * (j : ℝ) * Real.cos (j * x))

/-- `D² y (x) = -Σ_j κ(y)_j / √λ_j · √(2/π) j² sin (j x)` (blueprint `bpW:w2:derived`). -/
def reconUxx (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) : ℝ :=
  ∑' j : ℕ+, -(coeff y j / Real.sqrt (lam m hm j) *
    (Real.sqrt (2 / π) * (j : ℝ) ^ 2 * Real.sin (j * x)))

/-- The constant `c₀ = √(2/π) (e² - 1)^{-1/2}` of `bpW:w2:functionals`. -/
def reconWaveC0 : ℝ := Real.sqrt (2 / π) / Real.sqrt (Real.exp 2 - 1)

/-- The constant `M_m = c₀ (2 + (1 + m)^{1/4})` of `bpW:w2:curve`, with `(1 + m)^{1/4}` written as
`√√(1 + m)`. -/
def reconWaveBound (m : ℝ) : ℝ := reconWaveC0 * (2 + Real.sqrt (Real.sqrt (1 + m)))

lemma sineModeIter_one_eq (j : ℕ+) (x : ℝ) :
    sineModeIter 1 j x = Real.sqrt (2 / π) * (j : ℝ) * Real.cos (j * x) := by
  unfold sineModeIter
  have : (j : ℝ) * x + ((1 : ℕ) : ℝ) * π / 2 = (j : ℝ) * x + π / 2 := by push_cast; ring
  rw [this, Real.sin_add_pi_div_two]
  simp

lemma sineModeIter_two_eq (j : ℕ+) (x : ℝ) :
    sineModeIter 2 j x = -(Real.sqrt (2 / π) * (j : ℝ) ^ 2 * Real.sin (j * x)) := by
  rw [wave_sineModeIter_two]
  unfold sineMode
  ring

theorem reconUx_eq_iter (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    reconUx m hm y = reconUIter m hm 1 y := by
  funext x
  refine Eq.trans ?_ (hasSum_reconUIter m hm 1 y x).tsum_eq
  exact tsum_congr fun j => by rw [sineModeIter_one_eq]

theorem reconUxx_eq_iter (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    reconUxx m hm y = reconUIter m hm 2 y := by
  funext x
  refine Eq.trans ?_ (hasSum_reconUIter m hm 2 y x).tsum_eq
  refine tsum_congr fun j => ?_
  rw [sineModeIter_two_eq]
  ring

/-! ### Geometric sum and coordinate bounds -/

lemma hasSum_exp_neg_two_pnat :
    HasSum (fun j : ℕ+ => Real.exp (-2 * (j : ℝ))) (1 / (Real.exp 2 - 1)) := by
  have hr : Real.exp (-2) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num)
  have hg := (hasSum_geometric_of_lt_one (Real.exp_pos (-2)).le hr).mul_left (Real.exp (-2))
  have e2 : Real.exp 2 - 1 > 0 := by
    have := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num); linarith
  have hval : Real.exp (-2) * (1 - Real.exp (-2))⁻¹ = 1 / (Real.exp 2 - 1) := by
    rw [Real.exp_neg]
    have h2 : Real.exp 2 ≠ 0 := (Real.exp_pos 2).ne'
    have : Real.exp 2 - 1 ≠ 0 := e2.ne'
    field_simp
  rw [hval] at hg
  have := (Equiv.hasSum_iff (Equiv.pnatEquivNat)).2 hg
  convert this using 1
  funext j
  simp only [Function.comp_apply, Equiv.pnatEquivNat_apply]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have : ((j.natPred : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [PNat.natPred]; have := j.pos; push_cast [Nat.cast_sub (show 1 ≤ (j : ℕ) from j.pos)]; ring
  rw [this]; ring

lemma ellWeight_one_one_eq (j : ℕ+) : ellWeight 1 1 j = (j : ℝ) * Real.exp j := by
  unfold ellWeight
  simp

lemma sqrt_lam_sq (m : ℝ) (hm : 0 < m) (j : ℕ+) :
    Real.sqrt (lam m hm j) ^ 2 = lam m hm j :=
  Real.sq_sqrt (lt_of_lt_of_le one_pos (one_le_lam m hm j)).le

lemma lam_le_sqrt_mul (m : ℝ) (hm : 0 < m) (j : ℕ+) :
    lam m hm j ≤ Real.sqrt (1 + m) * j := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  unfold lam
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  have hjj : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hjj hm.le]

lemma reconFeatureU_coord_sq_le {k : ℕ} (hk : k ≤ 1) (m : ℝ) (hm : 0 < m) (x : ℝ) (j : ℕ+) :
    reconFeatureU m hm k x j ^ 2 ≤ 2 / π * Real.exp (-2 * (j : ℝ)) := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hjk : (j : ℝ) ^ k ≤ j := by
    interval_cases k
    · simpa using hj
    · simp
  have hβ : |betaU m hm j| ≤ 1 := by
    have h1 : 1 ≤ Real.sqrt (lam m hm j) := Real.one_le_sqrt.2 (one_le_lam m hm j)
    rw [betaU, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ h1
  have hit : |sineModeIter k j x| ≤ Real.sqrt (2 / π) * j :=
    (wave_abs_sineModeIter_le k j x).trans (by gcongr)
  have hω : 0 < ellWeight 1 1 j := waveEllWeight_pos 1 1 j
  have hc : |reconFeatureU m hm k x j| ≤ Real.sqrt (2 / π) * Real.exp (-(j : ℝ)) := by
    show |sineFeatCoord 1 1 (betaU m hm) k x j| ≤ _
    unfold sineFeatCoord
    rw [abs_div, abs_of_pos hω, div_le_iff₀ hω, abs_mul, ellWeight_one_one_eq]
    calc |betaU m hm j| * |sineModeIter k j x|
        ≤ 1 * (Real.sqrt (2 / π) * j) := by gcongr
      _ = Real.sqrt (2 / π) * Real.exp (-(j : ℝ)) * ((j : ℝ) * Real.exp j) := by
        have h1 : Real.exp (-(j : ℝ)) * Real.exp j = 1 := by rw [← Real.exp_add]; simp
        calc 1 * (Real.sqrt (2 / π) * j)
            = Real.sqrt (2 / π) * j * (Real.exp (-(j : ℝ)) * Real.exp j) := by rw [h1]; ring
          _ = _ := by ring
  calc reconFeatureU m hm k x j ^ 2 = |reconFeatureU m hm k x j| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (2 / π) * Real.exp (-(j : ℝ))) ^ 2 := by gcongr
    _ = 2 / π * Real.exp (-2 * (j : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      congr 2
      push_cast; ring

lemma reconFeatureV_coord_sq_le (m : ℝ) (hm : 0 < m) (x : ℝ) (j : ℕ+) :
    reconFeatureV m hm 0 x j ^ 2 ≤ Real.sqrt (1 + m) * (2 / π * Real.exp (-2 * (j : ℝ))) := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hω : 0 < ellWeight 1 1 j := waveEllWeight_pos 1 1 j
  have hit : sineModeIter 0 j x ^ 2 ≤ 2 / π := by
    have := wave_abs_sineModeIter_le 0 j x
    simp only [pow_zero, mul_one] at this
    calc sineModeIter 0 j x ^ 2 = |sineModeIter 0 j x| ^ 2 := (sq_abs _).symm
      _ ≤ Real.sqrt (2 / π) ^ 2 := by gcongr
      _ = 2 / π := Real.sq_sqrt (by positivity)
  have hc : reconFeatureV m hm 0 x j ^ 2 =
      lam m hm j * sineModeIter 0 j x ^ 2 / ellWeight 1 1 j ^ 2 := by
    show sineFeatCoord 1 1 (betaV m hm) 0 x j ^ 2 = _
    unfold sineFeatCoord betaV
    rw [div_pow, mul_pow, sqrt_lam_sq]
  rw [hc, div_le_iff₀ (by positivity), ellWeight_one_one_eq]
  have hl := lam_le_sqrt_mul m hm j
  have hs : 0 ≤ Real.sqrt (1 + m) := Real.sqrt_nonneg _
  have he : Real.exp (-2 * (j : ℝ)) * Real.exp j ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
  calc lam m hm j * sineModeIter 0 j x ^ 2
      ≤ (Real.sqrt (1 + m) * j) * (2 / π) := by
        gcongr
    _ ≤ Real.sqrt (1 + m) * (2 / π) * (j : ℝ) ^ 2 := by
        have : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
        have h2 : 0 ≤ Real.sqrt (1 + m) * (2 / π) := by positivity
        nlinarith
    _ = Real.sqrt (1 + m) * (2 / π * Real.exp (-2 * (j : ℝ))) * ((j : ℝ) * Real.exp j) ^ 2 := by
        calc Real.sqrt (1 + m) * (2 / π) * (j : ℝ) ^ 2
            = Real.sqrt (1 + m) * (2 / π) * (j : ℝ) ^ 2 *
              (Real.exp (-2 * (j : ℝ)) * Real.exp j ^ 2) := by rw [he]; ring
          _ = _ := by ring

lemma norm_le_sqrt_tsum_of_sq_le {Ψ : lp (fun _ : ℕ+ => ℝ) 2} {b : ℕ+ → ℝ} (hb : Summable b)
    (h : ∀ j, Ψ j ^ 2 ≤ b j) : ‖Ψ‖ ≤ Real.sqrt (∑' j, b j) := by
  rw [wave_lp_norm_eq_sqrt]
  refine Real.sqrt_le_sqrt (Summable.tsum_le_tsum h ?_ hb)
  simpa [Real.rpow_two] using (lp.memℓp Ψ).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)

lemma sqrt_tsum_const_mul (A : ℝ) (hA : 0 ≤ A) :
    Real.sqrt (∑' j : ℕ+, A * (2 / π * Real.exp (-2 * (j : ℝ)))) = Real.sqrt A * reconWaveC0 := by
  have hE : 0 < Real.exp 2 - 1 := by
    have := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num); linarith
  rw [tsum_mul_left, tsum_mul_left, hasSum_exp_neg_two_pnat.tsum_eq, reconWaveC0,
    Real.sqrt_mul hA, Real.sqrt_mul (by positivity), Real.sqrt_div' _ hE.le]
  rw [Real.sqrt_one]
  ring

lemma summable_const_mul_exp (A : ℝ) :
    Summable fun j : ℕ+ => A * (2 / π * Real.exp (-2 * (j : ℝ))) :=
  (hasSum_exp_neg_two_pnat.summable.mul_left (2 / π)).mul_left A

lemma reconWaveC0_nonneg : 0 ≤ reconWaveC0 := by
  unfold reconWaveC0; positivity

/-- `‖Ψ^k(x)‖ ≤ c₀` for `k = 0, 1` (blueprint `bpW:w2:functionals` (ii)). -/
theorem norm_reconFeatureU_le {k : ℕ} (hk : k ≤ 1) (m : ℝ) (hm : 0 < m) (x : ℝ) :
    ‖reconFeatureU m hm k x‖ ≤ reconWaveC0 := by
  have h := norm_le_sqrt_tsum_of_sq_le (summable_const_mul_exp 1)
    (fun j => by simpa using reconFeatureU_coord_sq_le hk m hm x j)
  rwa [sqrt_tsum_const_mul 1 zero_le_one, Real.sqrt_one, one_mul] at h

/-- `‖Ψ^V(x)‖ ≤ (1 + m)^{1/4} c₀` (blueprint `bpW:w2:functionals` (ii)). -/
theorem norm_reconFeatureV_le (m : ℝ) (hm : 0 < m) (x : ℝ) :
    ‖reconFeatureV m hm 0 x‖ ≤ Real.sqrt (Real.sqrt (1 + m)) * reconWaveC0 := by
  have h := norm_le_sqrt_tsum_of_sq_le (summable_const_mul_exp (Real.sqrt (1 + m)))
    (fun j => reconFeatureV_coord_sq_le m hm x j)
  rwa [sqrt_tsum_const_mul _ (Real.sqrt_nonneg _)] at h

lemma reconU_eq_inner (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    reconU m hm y x = inner ℝ (reconFeatureU m hm 0 x) y :=
  (reconUIter_zero m hm y x).symm

lemma reconUx_eq_inner (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    reconUx m hm y x = inner ℝ (reconFeatureU m hm 1 x) y := by
  rw [reconUx_eq_iter]; rfl

lemma reconUxx_eq_inner (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    reconUxx m hm y x = inner ℝ (reconFeatureU m hm 2 x) y := by
  rw [reconUxx_eq_iter]; rfl

lemma reconV_eq_inner (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    reconV m hm y x = inner ℝ (reconFeatureV m hm 0 x) y :=
  (reconVIter_zero m hm y x).symm

theorem abs_reconU_le (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    |reconU m hm y x| ≤ reconWaveC0 * ‖y‖ := by
  rw [reconU_eq_inner]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_reconFeatureU_le zero_le_one m hm x) (norm_nonneg _))

theorem abs_reconUx_le (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    |reconUx m hm y x| ≤ reconWaveC0 * ‖y‖ := by
  rw [reconUx_eq_inner]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_reconFeatureU_le le_rfl m hm x) (norm_nonneg _))

theorem abs_reconV_le (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    |reconV m hm y x| ≤ Real.sqrt (Real.sqrt (1 + m)) * reconWaveC0 * ‖y‖ := by
  rw [reconV_eq_inner]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_reconFeatureV_le m hm x) (norm_nonneg _))

/-! ### Absolute convergence, derivatives, boundary values -/

theorem summable_abs_reconU_terms (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    Summable fun j : ℕ+ => |coeff y j / Real.sqrt (lam m hm j) * sineMode j x| := by
  simpa only [sineModeIter_zero] using summable_abs_reconUIter m hm 0 y x

theorem summable_abs_reconUx_terms (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    Summable fun j : ℕ+ => |coeff y j / Real.sqrt (lam m hm j) *
      (Real.sqrt (2 / π) * (j : ℝ) * Real.cos (j * x))| := by
  simpa only [sineModeIter_one_eq] using summable_abs_reconUIter m hm 1 y x

theorem summable_abs_reconUxx_terms (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    Summable fun j : ℕ+ => |-(coeff y j / Real.sqrt (lam m hm j) *
      (Real.sqrt (2 / π) * (j : ℝ) ^ 2 * Real.sin (j * x)))| := by
  refine (summable_abs_reconUIter m hm 2 y x).congr fun j => ?_
  rw [sineModeIter_two_eq]
  simp [mul_neg]

theorem summable_abs_reconV_terms (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    Summable fun j : ℕ+ => |Real.sqrt (lam m hm j) * coeff y j * sineMode j x| := by
  simpa only [sineModeIter_zero] using summable_abs_reconVIter m hm 0 y x

/-- `D⁰ y = reconU y` has derivative `D¹ y (x)` (blueprint `bpW:w2:functionals` (iii)). -/
theorem hasDerivAt_reconU_reconUx (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasDerivAt (reconU m hm y) (reconUx m hm y x) x := by
  rw [reconUx_eq_iter]; exact hasDerivAt_reconU m hm y x

/-- `D¹ y` has derivative `D² y (x)` (blueprint `bpW:w2:functionals` (iii)). -/
theorem hasDerivAt_reconUx_reconUxx (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasDerivAt (reconUx m hm y) (reconUxx m hm y x) x := by
  rw [reconUx_eq_iter, reconUxx_eq_iter]; exact hasDerivAt_reconUIter m hm 1 y x

/-- `D⁰ y (0) = 0` (blueprint `bpW:w2:functionals` (iv)). -/
theorem reconU_apply_zero (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    reconU m hm y 0 = 0 := by
  unfold reconU sineMode
  simp

/-- `D⁰ y (π) = 0` (blueprint `bpW:w2:functionals` (iv)). -/
theorem reconU_apply_pi (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    reconU m hm y π = 0 := by
  unfold reconU sineMode
  simp [Real.sin_nat_mul_pi]

/-- **Reconstruction functionals** (blueprint `bpW:w2:functionals`): the four real analytic
features `Ψ⁰, Ψ¹, Ψ², Ψᵛ` represent `D⁰, D¹, D², V_m`; norm bounds, derivatives, boundary values.
-/
theorem reconWave_functionals (m : ℝ) (hm : 0 < m) :
    AnalyticOnNhd ℝ (reconFeatureU m hm 0) Set.univ ∧
    AnalyticOnNhd ℝ (reconFeatureU m hm 1) Set.univ ∧
    AnalyticOnNhd ℝ (reconFeatureU m hm 2) Set.univ ∧
    AnalyticOnNhd ℝ (reconFeatureV m hm 0) Set.univ ∧
    (∀ (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ),
      reconU m hm y x = inner ℝ (reconFeatureU m hm 0 x) y ∧
      reconUx m hm y x = inner ℝ (reconFeatureU m hm 1 x) y ∧
      reconUxx m hm y x = inner ℝ (reconFeatureU m hm 2 x) y ∧
      reconV m hm y x = inner ℝ (reconFeatureV m hm 0 x) y) ∧
    (∀ x : ℝ, ‖reconFeatureU m hm 0 x‖ ≤ reconWaveC0 ∧ ‖reconFeatureU m hm 1 x‖ ≤ reconWaveC0 ∧
      ‖reconFeatureV m hm 0 x‖ ≤ Real.sqrt (Real.sqrt (1 + m)) * reconWaveC0) ∧
    (∀ (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ),
      HasDerivAt (reconU m hm y) (reconUx m hm y x) x ∧
      HasDerivAt (reconUx m hm y) (reconUxx m hm y x) x) ∧
    ∀ y : lp (fun _ : ℕ+ => ℝ) 2, reconU m hm y 0 = 0 ∧ reconU m hm y π = 0 := by
  refine ⟨fun x _ => sineFeatureR_analyticAt 1 1 (betaU m hm) one_pos (polyBounded_betaU m hm) 0 x,
    fun x _ => sineFeatureR_analyticAt 1 1 (betaU m hm) one_pos (polyBounded_betaU m hm) 1 x,
    fun x _ => sineFeatureR_analyticAt 1 1 (betaU m hm) one_pos (polyBounded_betaU m hm) 2 x,
    fun x _ => sineFeatureR_analyticAt 1 1 (betaV m hm) one_pos (polyBounded_betaV m hm) 0 x,
    fun y x => ⟨reconU_eq_inner m hm y x, reconUx_eq_inner m hm y x, reconUxx_eq_inner m hm y x,
      reconV_eq_inner m hm y x⟩,
    fun x => ⟨norm_reconFeatureU_le zero_le_one m hm x, norm_reconFeatureU_le le_rfl m hm x,
      norm_reconFeatureV_le m hm x⟩,
    fun y x => ⟨hasDerivAt_reconU_reconUx m hm y x, hasDerivAt_reconUx_reconUxx m hm y x⟩,
    fun y => ⟨reconU_apply_zero m hm y, reconU_apply_pi m hm y⟩⟩

end KAM.Wave

end
