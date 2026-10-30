/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.CubicSelect
public import KAM.Wave.Normal.Analysis.CubicTools

/-!
# The cubic gradient is a bounded trilinear map (blueprint `bpW:w0n:cubic-bound`)

Infrastructure used by several nodes; the dependency graph is still being built.

`KAM.Wave.waveTrilinear` is the symmetric trilinear map `T` of the blueprint,
`T(q,q',q'')_l = λ_l^{-1/2} Σ_{ijk} g_{ijkl} q̂_i q̂'_j q̂''_k`. `KAM.Wave.wave_trilinear_bound`:
for `a ≥ 0`, `p ≥ 1/2` and `q, q', q'' ∈ ℓ^{a,p}` the defining series converge absolutely,
`T(q,q',q'') ∈ ℓ^{a,p+1}` and `‖T(q,q',q'')‖_{a,p+1} ≤ C_* ‖q‖‖q'‖‖q''‖`,
`C_* = K_{p+1/2}² / π` (`KAM.Wave.waveCubicConst`).

The convolution inequality of `bpW:w0n:algebra` enters only through the local helper
`KAM.Wave.w0a_convAlgebra_nonneg` (nonnegative case), which is proved in module `ConvAlgebra`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- The symmetric trilinear map `T` of `bpW:w0n:cubic-bound`:
`T(q,q',q'')_l = λ_l^{-1/2} Σ_{i,j,k ≥ 1} g_{ijkl} q̂_i q̂'_j q̂''_k`. -/
def waveTrilinear (m : ℝ) (hm : 0 < m) (q q' q'' : ℕ+ → ℝ) (l : ℕ+) : ℝ :=
  (Real.sqrt (lam m hm l))⁻¹ * ∑' t : ℕ+ × ℕ+ × ℕ+,
    (waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
      waveQuartic t.1 t.2.1 t.2.2 l

/-- The constant `C_* = K_{p+1/2}² / π` of `bpW:w0n:cubic-bound`. -/
def waveCubicConst (p : ℝ) : ℝ := w0aAlgConst (p + 1 / 2) ^ 2 / π

lemma waveCubicConst_nonneg (p : ℝ) : 0 ≤ waveCubicConst p := by
  unfold waveCubicConst; positivity

/-- Pointwise bound `|T_l| ≤ λ_l^{-1/2} (1/2π) ((x * y) * z)_l` and absolute convergence
(`stepW:w0n:selection`), for the even majorants `x, y, z`. -/
lemma wave_trilinear_pointwise (m : ℝ) (hm : 0 < m) {q q' q'' : ℕ+ → ℝ}
    {x y z : ℤ → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ i, 0 ≤ y i) (hz0 : ∀ i, 0 ≤ z i)
    (hxe : ∀ i, x (-i) = x i) (hye : ∀ i, y (-i) = y i) (hze : ∀ i, z (-i) = z i)
    (hx1 : Summable x) (hy1 : Summable y) (hz1 : Summable z)
    (hxq : ∀ n : ℕ+, x ((n : ℕ) : ℤ) = |waveHat m hm q n|)
    (hyq : ∀ n : ℕ+, y ((n : ℕ) : ℤ) = |waveHat m hm q' n|)
    (hzq : ∀ n : ℕ+, z ((n : ℕ) : ℤ) = |waveHat m hm q'' n|) (l : ℕ+) :
    (Summable fun t : ℕ+ × ℕ+ × ℕ+ => |(Real.sqrt (lam m hm l))⁻¹ *
        ((waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l)|) ∧
    |waveTrilinear m hm q q' q'' l| ≤
      (Real.sqrt (lam m hm l))⁻¹ * ((1 / (2 * π)) * w0aConv (w0aConv x y) z ((l : ℕ) : ℤ)) := by
  have hpi := Real.pi_pos
  have hsl : 0 < (Real.sqrt (lam m hm l))⁻¹ := inv_pos.2 (wave_sqrt_lam_pos m hm l)
  obtain ⟨hsum, hle⟩ := wave_selection_sum_le hx0 hy0 hz0 hxe hye hze hx1 hy1 hz1 l
  set P : ℕ+ × ℕ+ × ℕ+ → ℝ := fun t =>
    (∑ ε : Bool × Bool × Bool,
        (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)
          + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ) then (1 : ℝ) else 0)) *
        (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ))) with hP
  -- the absolute value of a term
  have habs : ∀ t : ℕ+ × ℕ+ × ℕ+,
      |(Real.sqrt (lam m hm l))⁻¹ *
        ((waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l)|
      = (Real.sqrt (lam m hm l))⁻¹ *
        (|waveQuartic t.1 t.2.1 t.2.2 l| *
          (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ)))) := by
    intro t
    rw [abs_mul, abs_of_pos hsl, abs_mul, abs_mul, abs_mul, hxq, hyq, hzq]
    ring
  have hbound : ∀ t : ℕ+ × ℕ+ × ℕ+,
      |waveQuartic t.1 t.2.1 t.2.2 l| *
          (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ)))
        ≤ (1 / (2 * π)) * P t := by
    intro t
    have h1 := abs_waveQuartic_le_signs t.1 t.2.1 t.2.2 l
    have hnn : 0 ≤ x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ)) :=
      mul_nonneg (hx0 _) (mul_nonneg (hy0 _) (hz0 _))
    calc _ ≤ ((1 / (2 * π)) * ∑ ε : Bool × Bool × Bool,
          (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)
            + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ) then (1 : ℝ) else 0)) *
          (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ))) :=
          mul_le_mul_of_nonneg_right h1 hnn
      _ = _ := by simp only [hP]; ring
  have hsum' : Summable fun t : ℕ+ × ℕ+ × ℕ+ =>
      (Real.sqrt (lam m hm l))⁻¹ * ((1 / (2 * π)) * P t) :=
    (hsum.mul_left (1 / (2 * π))).mul_left _
  have habs_sum : Summable fun t : ℕ+ × ℕ+ × ℕ+ => |(Real.sqrt (lam m hm l))⁻¹ *
        ((waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l)| := by
    refine Summable.of_nonneg_of_le (fun t => abs_nonneg _) (fun t => ?_) hsum'
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hbound t) hsl.le
  refine ⟨habs_sum, ?_⟩
  unfold waveTrilinear
  rw [abs_mul, abs_of_pos hsl]
  refine mul_le_mul_of_nonneg_left ?_ hsl.le
  have habs2 : ∀ t : ℕ+ × ℕ+ × ℕ+,
      |(waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l|
      = |waveQuartic t.1 t.2.1 t.2.2 l| *
          (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ))) := by
    intro t
    rw [abs_mul, abs_mul, abs_mul, hxq, hyq, hzq]
    ring
  have hsu : Summable fun t : ℕ+ × ℕ+ × ℕ+ =>
      |(waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l| :=
    Summable.of_nonneg_of_le (fun t => abs_nonneg _) (fun t => by rw [habs2]; exact hbound t)
      (hsum.mul_left (1 / (2 * π)))
  calc |∑' t : ℕ+ × ℕ+ × ℕ+, (waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q''
      t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l|
      ≤ ∑' t : ℕ+ × ℕ+ × ℕ+,
        |(waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
          (f := fun t : ℕ+ × ℕ+ × ℕ+ =>
            (waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
              waveQuartic t.1 t.2.1 t.2.2 l) hsu
    _ ≤ ∑' t : ℕ+ × ℕ+ × ℕ+, (1 / (2 * π)) * P t :=
        Summable.tsum_le_tsum (fun t => by rw [habs2]; exact hbound t) hsu
          (hsum.mul_left (1 / (2 * π)))
    _ = (1 / (2 * π)) * ∑' t : ℕ+ × ℕ+ × ℕ+, P t := tsum_mul_left
    _ ≤ (1 / (2 * π)) * w0aConv (w0aConv x y) z ((l : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-- `bpW:w0n:cubic-bound`: for `a ≥ 0`, `p ≥ 1/2`, the series defining `T` converge absolutely,
`T(q,q',q'') ∈ ℓ^{a,p+1}` and `‖T(q,q',q'')‖_{a,p+1} ≤ C_* ‖q‖_{a,p}‖q'‖_{a,p}‖q''‖_{a,p}` with
`C_* = K_{p+1/2}²/π`. -/
theorem wave_trilinear_bound (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)
    {q q' q'' : ℕ+ → ℝ} (hq : WaveEll a p q) (hq' : WaveEll a p q') (hq'' : WaveEll a p q'') :
    (∀ l : ℕ+, Summable fun t : ℕ+ × ℕ+ × ℕ+ => |(Real.sqrt (lam m hm l))⁻¹ *
        ((waveHat m hm q t.1 * (waveHat m hm q' t.2.1 * waveHat m hm q'' t.2.2)) *
          waveQuartic t.1 t.2.1 t.2.2 l)|) ∧
    WaveEll a (p + 1) (waveTrilinear m hm q q' q'') ∧
    waveEllNorm a (p + 1) (waveTrilinear m hm q q' q'') ≤
      waveCubicConst p * (waveEllNorm a p q * waveEllNorm a p q' * waveEllNorm a p q'') := by
  have hpi := Real.pi_pos
  have hs1 : 1 ≤ p + 1 / 2 := by linarith
  obtain ⟨hxw, hxL⟩ := waveEvenAbs_weighted m hm hq
  obtain ⟨hyw, hyL⟩ := waveEvenAbs_weighted m hm hq'
  obtain ⟨hzw, hzL⟩ := waveEvenAbs_weighted m hm hq''
  have hx0 : ∀ i, 0 ≤ waveEvenAbs (waveHat m hm q) i := waveEvenAbs_nonneg _
  have hy0 : ∀ i, 0 ≤ waveEvenAbs (waveHat m hm q') i := waveEvenAbs_nonneg _
  have hz0 : ∀ i, 0 ≤ waveEvenAbs (waveHat m hm q'') i := waveEvenAbs_nonneg _
  have hxe : ∀ i, waveEvenAbs (waveHat m hm q) (-i) = waveEvenAbs (waveHat m hm q) i :=
    waveEvenAbs_neg _
  have hye : ∀ i, waveEvenAbs (waveHat m hm q') (-i) = waveEvenAbs (waveHat m hm q') i :=
    waveEvenAbs_neg _
  have hze : ∀ i, waveEvenAbs (waveHat m hm q'') (-i) = waveEvenAbs (waveHat m hm q'') i :=
    waveEvenAbs_neg _
  have hx1 := wave_summable_of_weighted ha hs1 hx0 hxw
  have hy1 := wave_summable_of_weighted ha hs1 hy0 hyw
  have hz1 := wave_summable_of_weighted ha hs1 hz0 hzw
  have hpt := fun l : ℕ+ => wave_trilinear_pointwise m hm hx0 hy0 hz0 hxe hye hze hx1 hy1 hz1
    (fun n => waveEvenAbs_pnat _ n) (fun n => waveEvenAbs_pnat _ n)
    (fun n => waveEvenAbs_pnat _ n) l
  refine ⟨fun l => (hpt l).1, ?_⟩
  -- algebra
  obtain ⟨hA1s, hA1L⟩ := w0a_convAlgebra_nonneg ha hs1 hx0 hy0 hxw hyw
  have hA10 : ∀ i, 0 ≤ w0aConv (waveEvenAbs (waveHat m hm q)) (waveEvenAbs (waveHat m hm q')) i :=
    fun i => tsum_nonneg fun j => mul_nonneg (hx0 _) (hy0 _)
  obtain ⟨hA2s, hA2L⟩ := w0a_convAlgebra_nonneg ha hs1 hA10 hz0 hA1s hzw
  have hA1e : ∀ i, w0aConv (waveEvenAbs (waveHat m hm q)) (waveEvenAbs (waveHat m hm q')) (-i)
      = w0aConv (waveEvenAbs (waveHat m hm q)) (waveEvenAbs (waveHat m hm q')) i :=
    w0aConv_even hxe hye
  have hA2e : ∀ i, w0aConv (w0aConv (waveEvenAbs (waveHat m hm q))
        (waveEvenAbs (waveHat m hm q'))) (waveEvenAbs (waveHat m hm q'')) (-i)
      = w0aConv (w0aConv (waveEvenAbs (waveHat m hm q)) (waveEvenAbs (waveHat m hm q')))
        (waveEvenAbs (waveHat m hm q'')) i := w0aConv_even hA1e hze
  have hX30 : ∀ i, 0 ≤ w0aConv (w0aConv (waveEvenAbs (waveHat m hm q))
        (waveEvenAbs (waveHat m hm q'))) (waveEvenAbs (waveHat m hm q'')) i :=
    fun i => tsum_nonneg fun j => mul_nonneg (hA10 _) (hz0 _)
  have hLx0 : 0 ≤ w0aL2 (fun i => w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q) i) :=
    Real.sqrt_nonneg _
  have hLy0 : 0 ≤ w0aL2 (fun i => w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q') i) :=
    Real.sqrt_nonneg _
  have hLz0 : 0 ≤ w0aL2 (fun i => w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q'') i) :=
    Real.sqrt_nonneg _
  have hLA0 : 0 ≤ w0aL2 (fun i => w0aW2 a (p + 1 / 2) i *
      w0aConv (waveEvenAbs (waveHat m hm q)) (waveEvenAbs (waveHat m hm q')) i) :=
          Real.sqrt_nonneg _
  have hN1 := waveEllNorm_nonneg a p q
  have hN2 := waveEllNorm_nonneg a p q'
  have hN3 := waveEllNorm_nonneg a p q''
  have hK0 : 0 ≤ w0aAlgConst (p + 1 / 2) := by unfold w0aAlgConst; positivity
  have hr2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  generalize w0aConv (w0aConv (waveEvenAbs (waveHat m hm q)) (waveEvenAbs (waveHat m hm q')))
    (waveEvenAbs (waveHat m hm q'')) = X3 at hA2s hA2L hA2e hpt hX30
  set K := w0aAlgConst (p + 1 / 2) with hKd
  set N1 := waveEllNorm a p q
  set N2 := waveEllNorm a p q'
  set N3 := waveEllNorm a p q''
  have hL : w0aL2 (fun l => w0aW2 a (p + 1 / 2) l * X3 l) ≤ K ^ 2 * (2 * Real.sqrt 2) * (N1 * N2 *
      N3) := by
    calc _ ≤ K * w0aL2 (fun i => w0aW2 a (p + 1 / 2) i *
            w0aConv (waveEvenAbs (waveHat m hm q)) (waveEvenAbs (waveHat m hm q')) i) *
          w0aL2 (fun i => w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q'') i) := hA2L
      _ ≤ K * (K * w0aL2 (fun i => w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q) i) *
            w0aL2 (fun i => w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q') i)) *
          w0aL2 (fun i => w0aW2 a (p + 1 / 2) i * waveEvenAbs (waveHat m hm q'') i) := by
          gcongr
      _ ≤ K * (K * (Real.sqrt 2 * N1) * (Real.sqrt 2 * N2)) * (Real.sqrt 2 * N3) := by
          gcongr
      _ = K ^ 2 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt 2 * (N1 * N2 * N3) := by ring
      _ = _ := by rw [hr2]; ring
  set T := waveTrilinear m hm q q' q'' with hTd
  have hTsq : ∀ l : ℕ+, (ellWeight a (p + 1) l * T l) ^ 2 ≤
      (1 / (4 * π ^ 2)) * (w0aW2 a (p + 1 / 2) ((l : ℕ) : ℤ) * X3 ((l : ℕ) : ℤ)) ^ 2 := by
    intro l
    have hT := (hpt l).2
    have hl : 0 < lam m hm l := lt_of_lt_of_le (by positivity) (wave_pnat_le_lam m hm l)
    have hln : (0 : ℝ) < (l : ℕ+) := by positivity
    have hEw : ellWeight a (p + 1) l ^ 2 = ellWeight a (p + 1 / 2) l ^ 2 * (l : ℝ) := by
      have : p + 1 = (p + 1 / 2) + 1 / 2 := by ring
      rw [this, wave_ellWeight_add_half, mul_pow, Real.sq_sqrt hln.le]
    have hdiv : (l : ℝ) / lam m hm l ≤ 1 := (div_le_one hl).2 (wave_pnat_le_lam m hm l)
    have hU : ((Real.sqrt (lam m hm l))⁻¹ * ((1 / (2 * π)) * X3 ((l : ℕ) : ℤ))) ^ 2 =
        (lam m hm l)⁻¹ * ((1 / (4 * π ^ 2)) * X3 ((l : ℕ) : ℤ) ^ 2) := by
      rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hl.le]
      field_simp
      ring
    have hT2 : T l ^ 2 ≤ ((Real.sqrt (lam m hm l))⁻¹ * ((1 / (2 * π)) * X3 ((l : ℕ) : ℤ))) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hT 2
      rwa [sq_abs] at this
    rw [mul_pow, hEw, w0aW2_pnat]
    calc ellWeight a (p + 1 / 2) l ^ 2 * (l : ℝ) * T l ^ 2
        ≤ ellWeight a (p + 1 / 2) l ^ 2 * (l : ℝ) *
          ((lam m hm l)⁻¹ * ((1 / (4 * π ^ 2)) * X3 ((l : ℕ) : ℤ) ^ 2)) := by
          rw [← hU]; gcongr
      _ = (1 / (4 * π ^ 2)) * (ellWeight a (p + 1 / 2) l ^ 2 * X3 ((l : ℕ) : ℤ) ^ 2) *
          ((l : ℝ) / lam m hm l) := by ring
      _ ≤ (1 / (4 * π ^ 2)) * (ellWeight a (p + 1 / 2) l ^ 2 * X3 ((l : ℕ) : ℤ) ^ 2) * 1 := by
          gcongr
      _ = _ := by ring
  have inj : Function.Injective (fun n : ℕ+ => ((n : ℕ) : ℤ)) := fun a b h => by
    have h' : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := h
    exact PNat.coe_injective (by exact_mod_cast h')
  have hf'sum : Summable fun n : ℕ+ =>
      (w0aW2 a (p + 1 / 2) ((n : ℕ) : ℤ) * X3 ((n : ℕ) : ℤ)) ^ 2 := hA2s.comp_injective inj
  have hTsum : Summable fun l : ℕ+ => (ellWeight a (p + 1) l * T l) ^ 2 :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hTsq (hf'sum.mul_left _)
  refine ⟨hTsum, ?_⟩
  have hint := w0aHasSum_int_even_pnat'
    (f := fun i : ℤ => (w0aW2 a (p + 1 / 2) i * X3 i) ^ 2)
    (fun i => by simp only [w0aW2_neg, hA2e]) hf'sum.hasSum
  have hLsq : w0aL2 (fun l => w0aW2 a (p + 1 / 2) l * X3 l) ^ 2 =
      ∑' i : ℤ, (w0aW2 a (p + 1 / 2) i * X3 i) ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg _)
  have hS2 : 2 * ∑' n : ℕ+, (w0aW2 a (p + 1 / 2) ((n : ℕ) : ℤ) * X3 ((n : ℕ) : ℤ)) ^ 2 ≤
      w0aL2 (fun l => w0aW2 a (p + 1 / 2) l * X3 l) ^ 2 := by
    rw [hLsq, hint.tsum_eq]
    nlinarith [sq_nonneg (w0aW2 a (p + 1 / 2) 0 * X3 0)]
  have hL0 : 0 ≤ w0aL2 (fun l => w0aW2 a (p + 1 / 2) l * X3 l) := Real.sqrt_nonneg _
  have hsumle : ∑' l : ℕ+, (ellWeight a (p + 1) l * T l) ^ 2 ≤ (K ^ 2 * (N1 * N2 * N3) / π) ^ 2 :=
      by
    calc ∑' l : ℕ+, (ellWeight a (p + 1) l * T l) ^ 2
        ≤ ∑' n : ℕ+, (1 / (4 * π ^ 2)) *
            (w0aW2 a (p + 1 / 2) ((n : ℕ) : ℤ) * X3 ((n : ℕ) : ℤ)) ^ 2 :=
          Summable.tsum_le_tsum hTsq hTsum (hf'sum.mul_left _)
      _ = (1 / (4 * π ^ 2)) * ∑' n : ℕ+,
            (w0aW2 a (p + 1 / 2) ((n : ℕ) : ℤ) * X3 ((n : ℕ) : ℤ)) ^ 2 := tsum_mul_left
      _ ≤ (1 / (4 * π ^ 2)) * (w0aL2 (fun l => w0aW2 a (p + 1 / 2) l * X3 l) ^ 2 / 2) := by
          gcongr; linarith
      _ ≤ (1 / (4 * π ^ 2)) * ((K ^ 2 * (2 * Real.sqrt 2) * (N1 * N2 * N3)) ^ 2 / 2) := by
          gcongr
      _ = (K ^ 2 * (N1 * N2 * N3) / π) ^ 2 := by
          have : (2 * Real.sqrt 2) ^ 2 = 8 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
          calc _ = (1 / (4 * π ^ 2)) * ((K ^ 2 * (N1 * N2 * N3)) ^ 2 * (2 * Real.sqrt 2) ^ 2 / 2)
              := by
                ring
            _ = _ := by rw [this]; field_simp; ring
  unfold waveEllNorm
  have hcc : waveCubicConst p * (N1 * N2 * N3) = K ^ 2 * (N1 * N2 * N3) / π := by
    unfold waveCubicConst; ring
  rw [hcc]
  calc Real.sqrt (∑' l : ℕ+, (ellWeight a (p + 1) l * T l) ^ 2)
      ≤ Real.sqrt ((K ^ 2 * (N1 * N2 * N3) / π) ^ 2) := Real.sqrt_le_sqrt hsumle
    _ = _ := Real.sqrt_sq (by positivity)

end KAM.Wave

end
