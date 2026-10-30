/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.CubicBound

/-!
# Trilinearity and the identification `𝒢 = T(q,q,q)` (blueprint `bpW:w0n:cubic-bound`)

Infrastructure used by several nodes; the dependency graph is still being built.

* `KAM.Wave.waveEll_add`, `KAM.Wave.waveEll_smul`: `ℓ^{a,p}` is a vector space;
* `KAM.Wave.waveTrilinear_add_left` (and `_mid`, `_right`), `KAM.Wave.waveTrilinear_smul_left`
  (and `_mid`, `_right`): `T` is additive and homogeneous in each argument;
* `KAM.Wave.waveTrilinear_swap_left_mid`, `KAM.Wave.waveTrilinear_swap_mid_right`: symmetry;
* `KAM.Wave.waveCubic_eq_trilinear`: for `a > 0`, `𝒢(q) = T(q,q,q)`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

lemma waveEll_add {a p : ℝ} {c d : ℕ+ → ℝ} (hc : WaveEll a p c) (hd : WaveEll a p d) :
    WaveEll a p (fun j => c j + d j) := by
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) ((hc.add hd).mul_left 2)
  have : ellWeight a p j * (c j + d j) = ellWeight a p j * c j + ellWeight a p j * d j := by ring
  rw [this]
  nlinarith [sq_nonneg (ellWeight a p j * c j - ellWeight a p j * d j)]

lemma waveEll_smul {a p : ℝ} (r : ℝ) {c : ℕ+ → ℝ} (hc : WaveEll a p c) :
    WaveEll a p (fun j => r * c j) := by
  refine (hc.mul_left (r ^ 2)).congr fun j => ?_
  ring

lemma waveHat_add (m : ℝ) (hm : 0 < m) (c d : ℕ+ → ℝ) (j : ℕ+) :
    waveHat m hm (fun j => c j + d j) j = waveHat m hm c j + waveHat m hm d j := by
  unfold waveHat; ring

lemma waveHat_smul (m : ℝ) (hm : 0 < m) (r : ℝ) (c : ℕ+ → ℝ) (j : ℕ+) :
    waveHat m hm (fun j => r * c j) j = r * waveHat m hm c j := by
  unfold waveHat; ring

/-- The series of `T` with the prefactor removed is summable. -/
lemma wave_trilinear_terms_summable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)
    {q q' q'' : ℕ+ → ℝ} (hq : WaveEll a p q) (hq' : WaveEll a p q') (hq'' : WaveEll a p q'')
    (l : ℕ+) :
    Summable fun t : ℕ+ × ℕ+ × ℕ+ =>
      (waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
        waveQuartic t.1 t.2.1 t.2.2 l := by
  have h := (wave_trilinear_bound m hm ha hp hq hq' hq'').1 l
  have hpos : 0 < Real.sqrt (lam m hm l) := wave_sqrt_lam_pos m hm l
  refine (h.of_abs.mul_left (Real.sqrt (lam m hm l))).congr fun t => ?_
  field_simp

section Linear

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)
  {q r q' q'' : ℕ+ → ℝ}
include ha hp

theorem waveTrilinear_add_left (hq : WaveEll a p q) (hr : WaveEll a p r)
    (hq' : WaveEll a p q') (hq'' : WaveEll a p q'') (l : ℕ+) :
    waveTrilinear m hm (fun j => q j + r j) q' q'' l =
      waveTrilinear m hm q q' q'' l + waveTrilinear m hm r q' q'' l := by
  unfold waveTrilinear
  rw [← mul_add, ← Summable.tsum_add
    (wave_trilinear_terms_summable m hm ha hp hq hq' hq'' l)
    (wave_trilinear_terms_summable m hm ha hp hr hq' hq'' l)]
  congr 1
  refine tsum_congr fun t => ?_
  simp only [waveHat_add]; ring

theorem waveTrilinear_add_mid (hq : WaveEll a p q) (hq' : WaveEll a p q') (hr : WaveEll a p r)
    (hq'' : WaveEll a p q'') (l : ℕ+) :
    waveTrilinear m hm q (fun j => q' j + r j) q'' l =
      waveTrilinear m hm q q' q'' l + waveTrilinear m hm q r q'' l := by
  unfold waveTrilinear
  rw [← mul_add, ← Summable.tsum_add
    (wave_trilinear_terms_summable m hm ha hp hq hq' hq'' l)
    (wave_trilinear_terms_summable m hm ha hp hq hr hq'' l)]
  congr 1
  refine tsum_congr fun t => ?_
  simp only [waveHat_add]; ring

theorem waveTrilinear_add_right (hq : WaveEll a p q) (hq' : WaveEll a p q') (hq'' : WaveEll a p q'')
    (hr : WaveEll a p r) (l : ℕ+) :
    waveTrilinear m hm q q' (fun j => q'' j + r j) l =
      waveTrilinear m hm q q' q'' l + waveTrilinear m hm q q' r l := by
  unfold waveTrilinear
  rw [← mul_add, ← Summable.tsum_add
    (wave_trilinear_terms_summable m hm ha hp hq hq' hq'' l)
    (wave_trilinear_terms_summable m hm ha hp hq hq' hr l)]
  congr 1
  refine tsum_congr fun t => ?_
  simp only [waveHat_add]; ring

end Linear

theorem waveTrilinear_smul_left (m : ℝ) (hm : 0 < m) (c : ℝ) (q q' q'' : ℕ+ → ℝ) (l : ℕ+) :
    waveTrilinear m hm (fun j => c * q j) q' q'' l = c * waveTrilinear m hm q q' q'' l := by
  unfold waveTrilinear
  have e : (∑' t : ℕ+ × ℕ+ × ℕ+, (waveHat m hm (fun j => c * q j) t.1 * (waveHat m hm q' t.2.1 *
      waveHat m hm q'' t.2.2)) * waveQuartic t.1 t.2.1 t.2.2 l) =
      c * ∑' t : ℕ+ × ℕ+ × ℕ+,
        (waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by simp only [waveHat_smul]; ring
  rw [e]; ring

theorem waveTrilinear_smul_mid (m : ℝ) (hm : 0 < m) (c : ℝ) (q q' q'' : ℕ+ → ℝ) (l : ℕ+) :
    waveTrilinear m hm q (fun j => c * q' j) q'' l = c * waveTrilinear m hm q q' q'' l := by
  unfold waveTrilinear
  have e : (∑' t : ℕ+ × ℕ+ × ℕ+, (waveHat m hm q t.1 * (waveHat m hm (fun j => c * q' j) t.2.1 *
      waveHat m hm q'' t.2.2)) * waveQuartic t.1 t.2.1 t.2.2 l) =
      c * ∑' t : ℕ+ × ℕ+ × ℕ+,
        (waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by simp only [waveHat_smul]; ring
  rw [e]; ring

theorem waveTrilinear_smul_right (m : ℝ) (hm : 0 < m) (c : ℝ) (q q' q'' : ℕ+ → ℝ) (l : ℕ+) :
    waveTrilinear m hm q q' (fun j => c * q'' j) l = c * waveTrilinear m hm q q' q'' l := by
  unfold waveTrilinear
  have e : (∑' t : ℕ+ × ℕ+ × ℕ+, (waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm (fun
      j => c * q'' j) t.2.2)) * waveQuartic t.1 t.2.1 t.2.2 l) =
      c * ∑' t : ℕ+ × ℕ+ × ℕ+,
        (waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by simp only [waveHat_smul]; ring
  rw [e]; ring

lemma waveQuartic_comm12 (i j k l : ℕ+) : waveQuartic i j k l = waveQuartic j i k l := by
  unfold waveQuartic
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

lemma waveQuartic_comm23 (i j k l : ℕ+) : waveQuartic i j k l = waveQuartic i k j l := by
  unfold waveQuartic
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

/-- Symmetry of `T` in the first two arguments. -/
theorem waveTrilinear_swap_left_mid (m : ℝ) (hm : 0 < m) (q q' q'' : ℕ+ → ℝ) (l : ℕ+) :
    waveTrilinear m hm q q' q'' l = waveTrilinear m hm q' q q'' l := by
  unfold waveTrilinear
  congr 1
  let e : ℕ+ × ℕ+ × ℕ+ ≃ ℕ+ × ℕ+ × ℕ+ :=
    { toFun := fun t => (t.2.1, t.1, t.2.2)
      invFun := fun t => (t.2.1, t.1, t.2.2)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun t => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [waveQuartic_comm12 t.2.1 t.1]
  ring

/-- Symmetry of `T` in the last two arguments. -/
theorem waveTrilinear_swap_mid_right (m : ℝ) (hm : 0 < m) (q q' q'' : ℕ+ → ℝ) (l : ℕ+) :
    waveTrilinear m hm q q' q'' l = waveTrilinear m hm q q'' q' l := by
  unfold waveTrilinear
  congr 1
  let e : ℕ+ × ℕ+ × ℕ+ ≃ ℕ+ × ℕ+ × ℕ+ :=
    { toFun := fun t => (t.1, t.2.2, t.2.1)
      invFun := fun t => (t.1, t.2.2, t.2.1)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun t => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [waveQuartic_comm23 t.1 t.2.2 t.2.1]
  ring

/-- `bpW:w0n:cubic-bound`: for `a > 0`, `p ≥ 1/2` and real `q ∈ ℓ^{a,p}`, `𝒢(q) = T(q,q,q)`. -/
theorem waveCubic_eq_trilinear (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℝ}
    (hc : WaveEll a p c) (l : ℕ+) :
    waveCubic m hm c l = waveTrilinear m hm c c c l := by
  have h := (waveCubic_hasSum hm ha hc l).1
  unfold waveTrilinear
  rw [← tsum_mul_left]
  exact h.tsum_eq.symm

end KAM.Wave

end
