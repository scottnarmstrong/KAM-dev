/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import KAM.Wave.Normal.Analysis.SineProducts

/-!
# `G` and its gradient as absolutely convergent sums (blueprint `bpW:w0n:gradient`)

Infrastructure used by several nodes; the dependency graph is still being built.

The quantities `U_m(q)`, `𝒢(q)_l`, `G(q)` of the blueprint (`bpW:w0:reconstruction`, `bpW:w0:Gq`,
`bpW:w0:H`) for a *sequence* `q : ℕ+ → ℝ` (not only `ℓ^{1,1}`) are
`KAM.Wave.waveU`, `KAM.Wave.waveCubic`, `KAM.Wave.waveG`. On `q ∈ ℓ^{1,1}` they agree with the
frozen `KAM.Wave.reconU`, `KAM.Wave.cubicGrad` (`KAM.Wave.reconU_eq_waveU`,
`KAM.Wave.cubicGrad_eq_waveCubic`).

For `q ∈ ℓ^{a,p}`, `a > 0`:

* `KAM.Wave.waveG_hasSum`, `KAM.Wave.waveCubic_hasSum`: the quadruple and triple series for `G`
  and `𝒢`, both absolutely convergent (the blueprint assumes `p ≥ 0`; the proof needs only `a > 0`,
  so every `p ∈ ℝ` is covered);
* `KAM.Wave.integral_waveU_cube_mul_sineMode`: `∫ U^3 φ_l = √λ_l 𝒢(q)_l`;
* `KAM.Wave.hasDerivAt_waveG_coord`: `G(q + t e_l)` is differentiable at `t = 0` with derivative
  `𝒢(q)_l` (the Gâteaux derivative along the coordinate `l`).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

section Defs

variable (m : ℝ) (hm : 0 < m)

/-- `ĉ_j = c_j / √λ_j`. -/
def waveHat (c : ℕ+ → ℝ) (j : ℕ+) : ℝ := c j / Real.sqrt (lam m hm j)

/-- `U_m(q)(x) = Σ_j q_j/√λ_j φ_j(x)` for a real sequence `q` (blueprint `bpW:w0:reconstruction`).
-/
def waveU (c : ℕ+ → ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℕ+, c j / Real.sqrt (lam m hm j) * sineMode j x

/-- `𝒢(q)_l = λ_l^{-1/2} ∫₀^π U_m(q)^3 φ_l` (blueprint `bpW:w0:Gq`) for a real sequence `q`. -/
def waveCubic (c : ℕ+ → ℝ) (l : ℕ+) : ℝ :=
  (∫ x in (0 : ℝ)..π, waveU m hm c x ^ 3 * sineMode l x) / Real.sqrt (lam m hm l)

/-- `G(q) = ¼ ∫₀^π U_m(q)^4` (blueprint `bpW:w0:H`) for a real sequence `q`. -/
def waveG (c : ℕ+ → ℝ) : ℝ :=
  (1 / 4) * ∫ x in (0 : ℝ)..π, waveU m hm c x ^ 4

lemma reconU_eq_waveU (y : lp (fun _ : ℕ+ => ℝ) 2) :
    reconU m hm y = waveU m hm (coeff y) := rfl

lemma cubicGrad_eq_waveCubic (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    cubicGrad m hm y l = waveCubic m hm (coeff y) l := by
  simp only [cubicGrad, waveCubic, reconU_eq_waveU]

lemma waveU_eq_series (c : ℕ+ → ℝ) :
    waveU m hm c = waveSineSeries 0 (waveHat m hm c) := by
  funext x
  rw [waveSineSeries_zero_eq]
  rfl

lemma wave_sqrt_lam_pos (j : ℕ+) : 0 < Real.sqrt (lam m hm j) :=
  Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (one_le_lam m hm j))

lemma abs_waveHat_le (c : ℕ+ → ℝ) (j : ℕ+) : |waveHat m hm c j| ≤ |c j| := by
  have h1 : 1 ≤ Real.sqrt (lam m hm j) := Real.one_le_sqrt.2 (one_le_lam m hm j)
  unfold waveHat
  rw [abs_div, abs_of_pos (lt_of_lt_of_le one_pos h1)]
  exact div_le_self (abs_nonneg _) h1

/-- `c ∈ ℓ^{a,p}` implies `c/√λ ∈ ℓ^{a,p}` with no larger norm. -/
lemma waveEll_waveHat {a p : ℝ} {c : ℕ+ → ℝ} (hc : WaveEll a p c) :
    WaveEll a p (waveHat m hm c) := by
  have := (waveEll_mul_poly (β := betaU m hm) (B := 1) (ν := 0) zero_le_one
    (fun j => by
      have h1 : 1 ≤ Real.sqrt (lam m hm j) := Real.one_le_sqrt.2 (one_le_lam m hm j)
      simp only [betaU, Real.rpow_zero, mul_one]
      rw [abs_of_pos (inv_pos.2 (lt_of_lt_of_le one_pos h1))]
      exact inv_le_one_of_one_le₀ h1) hc).1
  simp only [sub_zero] at this
  refine this.congr fun j => ?_
  simp [waveHat, betaU, div_eq_inv_mul]

lemma summable_abs_waveHat {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c) :
    Summable fun j => |waveHat m hm c j| := by
  simpa using waveEll_summable_pow_mul ha (waveEll_waveHat m hm hc) 0

end Defs

section Gradient

variable {m : ℝ} (hm : 0 < m)

/-- The quadruple series for `G` (core form, from absolute summability of `ĉ`). -/
theorem waveG_hasSum_of_summable {c : ℕ+ → ℝ} (hh : Summable fun j => |waveHat m hm c j|) :
    HasSum (fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ => (1 / 4) *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 *
            (waveHat m hm c t.2.2.1 * waveHat m hm c t.2.2.2))) *
          waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2)) (waveG m hm c) ∧
    Summable fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ => |(1 / 4) *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 *
            (waveHat m hm c t.2.2.1 * waveHat m hm c t.2.2.2))) *
          waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2)| := by
  refine ⟨?_, ?_⟩
  · unfold waveG
    rw [waveU_eq_series]
    exact (hasSum_integral_fourth_pow hh).mul_left _
  · refine ((summable_abs_fourth_terms hh).mul_left |(1 / 4 : ℝ)|).congr fun t => ?_
    simp only [abs_mul]

/-- The triple series for `𝒢_l` (core form). -/
theorem waveCubic_hasSum_of_summable {c : ℕ+ → ℝ}
    (hh : Summable fun j => |waveHat m hm c j|) (l : ℕ+) :
    HasSum (fun t : ℕ+ × ℕ+ × ℕ+ => (Real.sqrt (lam m hm l))⁻¹ *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 * waveHat m hm c t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l)) (waveCubic m hm c l) ∧
    Summable fun t : ℕ+ × ℕ+ × ℕ+ => |(Real.sqrt (lam m hm l))⁻¹ *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 * waveHat m hm c t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l)| := by
  refine ⟨?_, ?_⟩
  · unfold waveCubic
    rw [waveU_eq_series, div_eq_inv_mul]
    exact (hasSum_integral_cube_mul_sineMode hh l).mul_left _
  · refine ((summable_abs_cube_terms hh l).mul_left |(Real.sqrt (lam m hm l))⁻¹|).congr fun t => ?_
    simp only [abs_mul]

end Gradient

section Wrappers

variable {m : ℝ} (hm : 0 < m) {a p : ℝ}

/-- `bpW:w0n:gradient`: `G(q) = ¼ Σ_{i,j,k,l} g_{ijkl} q̂_i q̂_j q̂_k q̂_l`, absolutely convergent,
for `q ∈ ℓ^{a,p}`, `a > 0` (any `p`). -/
theorem waveG_hasSum (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c) :
    HasSum (fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ => (1 / 4) *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 *
            (waveHat m hm c t.2.2.1 * waveHat m hm c t.2.2.2))) *
          waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2)) (waveG m hm c) ∧
    Summable fun t : ℕ+ × ℕ+ × ℕ+ × ℕ+ => |(1 / 4) *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 *
            (waveHat m hm c t.2.2.1 * waveHat m hm c t.2.2.2))) *
          waveQuartic t.1 t.2.1 t.2.2.1 t.2.2.2)| :=
  waveG_hasSum_of_summable hm (summable_abs_waveHat m hm ha hc)

/-- `bpW:w0n:gradient`: `𝒢(q)_l = λ_l^{-1/2} Σ_{i,j,k} g_{ijkl} q̂_i q̂_j q̂_k`, absolutely
convergent, for `q ∈ ℓ^{a,p}`, `a > 0` (any `p`). -/
theorem waveCubic_hasSum (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c) (l : ℕ+) :
    HasSum (fun t : ℕ+ × ℕ+ × ℕ+ => (Real.sqrt (lam m hm l))⁻¹ *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 * waveHat m hm c t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l)) (waveCubic m hm c l) ∧
    Summable fun t : ℕ+ × ℕ+ × ℕ+ => |(Real.sqrt (lam m hm l))⁻¹ *
        ((waveHat m hm c t.1 * (waveHat m hm c t.2.1 * waveHat m hm c t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l)| :=
  waveCubic_hasSum_of_summable hm (summable_abs_waveHat m hm ha hc) l

/-- `bpW:w0n:gradient`: `∫₀^π U_m(q)^3 φ_l = √λ_l 𝒢(q)_l`. -/
theorem integral_waveU_cube_mul_sineMode (c : ℕ+ → ℝ) (l : ℕ+) :
    ∫ x in (0 : ℝ)..π, waveU m hm c x ^ 3 * sineMode l x
      = Real.sqrt (lam m hm l) * waveCubic m hm c l := by
  have := (wave_sqrt_lam_pos m hm l).ne'
  unfold waveCubic
  field_simp

/-- The coordinate shift `q + t e_l`. -/
def waveCoordShift (l : ℕ+) (t : ℝ) (c : ℕ+ → ℝ) : ℕ+ → ℝ :=
  fun j => c j + t * (if j = l then 1 else 0)

lemma waveU_coordShift {c : ℕ+ → ℝ} (hh : Summable fun j => |waveHat m hm c j|) (l : ℕ+) (t x : ℝ) :
    waveU m hm (waveCoordShift l t c) x
      = waveU m hm c x + t * ((Real.sqrt (lam m hm l))⁻¹ * sineMode l x) := by
  unfold waveU
  have e : ∀ j : ℕ+, (waveCoordShift l t c j) / Real.sqrt (lam m hm j) * sineMode j x =
      c j / Real.sqrt (lam m hm j) * sineMode j x
        + (if j = l then t * ((Real.sqrt (lam m hm l))⁻¹ * sineMode l x) else 0) := by
    intro j
    by_cases hj : j = l
    · subst hj
      simp only [waveCoordShift, ite_true]
      ring
    · simp [waveCoordShift, hj]
  have hs1 : Summable fun j : ℕ+ => c j / Real.sqrt (lam m hm j) * sineMode j x :=
    (wave_summable_abs_mul_sineMode hh x).of_abs
  have hs2 : Summable fun j : ℕ+ =>
      (if j = l then t * ((Real.sqrt (lam m hm l))⁻¹ * sineMode l x) else 0) :=
    (hasSum_ite_eq l _).summable
  rw [tsum_congr e, hs1.tsum_add hs2, tsum_ite_eq]

lemma wave_hasDerivAt_integral_pow_four {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) :
    HasDerivAt (fun t : ℝ => ∫ x in (0 : ℝ)..π, (u x + t * v x) ^ 4)
      (4 * ∫ x in (0 : ℝ)..π, u x ^ 3 * v x) 0 := by
  set A0 := ∫ x in (0 : ℝ)..π, u x ^ 4
  set A1 := 4 * ∫ x in (0 : ℝ)..π, u x ^ 3 * v x
  set A2 := 6 * ∫ x in (0 : ℝ)..π, u x ^ 2 * v x ^ 2
  set A3 := 4 * ∫ x in (0 : ℝ)..π, u x * v x ^ 3
  set A4 := ∫ x in (0 : ℝ)..π, v x ^ 4
  have e : ∀ t : ℝ, ∫ x in (0 : ℝ)..π, (u x + t * v x) ^ 4
      = A0 + t * A1 + t ^ 2 * A2 + t ^ 3 * A3 + t ^ 4 * A4 := by
    intro t
    have hx : ∀ x : ℝ, (u x + t * v x) ^ 4 = u x ^ 4 + t * (4 * (u x ^ 3 * v x))
        + t ^ 2 * (6 * (u x ^ 2 * v x ^ 2)) + t ^ 3 * (4 * (u x * v x ^ 3)) + t ^ 4 * v x ^ 4 :=
      fun x => by ring
    have i0 : IntervalIntegrable (fun x => u x ^ 4) MeasureTheory.volume 0 π :=
      (by fun_prop : Continuous fun x => u x ^ 4).intervalIntegrable _ _
    have i1 : IntervalIntegrable (fun x => t * (4 * (u x ^ 3 * v x))) MeasureTheory.volume 0 π :=
      (by fun_prop : Continuous fun x => t * (4 * (u x ^ 3 * v x))).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x => t ^ 2 * (6 * (u x ^ 2 * v x ^ 2))) MeasureTheory.volume
        0 π := (by fun_prop : Continuous fun x => t ^ 2 * (6 * (u x ^ 2 * v x ^
            2))).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun x => t ^ 3 * (4 * (u x * v x ^ 3))) MeasureTheory.volume
        0 π := (by fun_prop : Continuous fun x => t ^ 3 * (4 * (u x * v x ^
            3))).intervalIntegrable _ _
    have i4 : IntervalIntegrable (fun x => t ^ 4 * v x ^ 4) MeasureTheory.volume 0 π :=
      (by fun_prop : Continuous fun x => t ^ 4 * v x ^ 4).intervalIntegrable _ _
    simp_rw [hx]
    rw [intervalIntegral.integral_add (((i0.add i1).add i2).add i3) i4,
      intervalIntegral.integral_add ((i0.add i1).add i2) i3,
      intervalIntegral.integral_add (i0.add i1) i2, intervalIntegral.integral_add i0 i1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  simp_rw [e]
  have := ((((hasDerivAt_const (0 : ℝ) A0).add ((hasDerivAt_id (0 : ℝ)).mul_const A1)).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const A2)).add ((hasDerivAt_pow 3 (0 : ℝ)).mul_const A3)).add
    ((hasDerivAt_pow 4 (0 : ℝ)).mul_const A4)
  convert this using 1 <;> first | (funext t; simp) | simp

/-- `bpW:w0n:gradient` (core form): the coordinate derivative `∂G/∂q_l = 𝒢(q)_l`. -/
theorem hasDerivAt_waveG_coord_of_summable {c : ℕ+ → ℝ}
    (hh : Summable fun j => |waveHat m hm c j|) (l : ℕ+) :
    HasDerivAt (fun t : ℝ => waveG m hm (waveCoordShift l t c)) (waveCubic m hm c l) 0 := by
  have hu : Continuous (waveU m hm c) := by
    rw [waveU_eq_series]; exact continuous_waveSineSeries_zero hh
  have hv : Continuous fun x => (Real.sqrt (lam m hm l))⁻¹ * sineMode l x :=
    continuous_const.mul (wave_continuous_sineMode l)
  have key := (wave_hasDerivAt_integral_pow_four hu hv).const_mul (1 / 4 : ℝ)
  have e : (fun t : ℝ => waveG m hm (waveCoordShift l t c)) =
      fun t => (1 / 4 : ℝ) * ∫ x in (0 : ℝ)..π,
        (waveU m hm c x + t * ((Real.sqrt (lam m hm l))⁻¹ * sineMode l x)) ^ 4 := by
    funext t
    unfold waveG
    congr 1
    exact intervalIntegral.integral_congr fun x _ => by
      simp only [waveU_coordShift hm hh]
  rw [e]
  convert key using 1
  unfold waveCubic
  have : ∀ x, waveU m hm c x ^ 3 * ((Real.sqrt (lam m hm l))⁻¹ * sineMode l x)
      = (Real.sqrt (lam m hm l))⁻¹ * (waveU m hm c x ^ 3 * sineMode l x) := fun x => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, div_eq_inv_mul]
  ring

/-- `bpW:w0n:gradient`: `G` is Gâteaux differentiable along every coordinate with
`∂G/∂q_l = 𝒢(q)_l`, for `q ∈ ℓ^{a,p}`, `a > 0` (any `p`). -/
theorem hasDerivAt_waveG_coord (ha : 0 < a) {c : ℕ+ → ℝ} (hc : WaveEll a p c) (l : ℕ+) :
    HasDerivAt (fun t : ℝ => waveG m hm (waveCoordShift l t c)) (waveCubic m hm c l) 0 :=
  hasDerivAt_waveG_coord_of_summable hm (summable_abs_waveHat m hm ha hc) l

end Wrappers

end KAM.Wave

end
