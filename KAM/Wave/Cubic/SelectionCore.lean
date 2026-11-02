/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.CubicBound

/-!
# Weighted-norm steps for the selection-rule trilinear maps
(blueprint `bpW:w1:selection`, steps `stepW:w1:maj1`, `stepW:w1:smooth1`)

Three coefficient-free steps shared by every selection-rule trilinear map:

* `KAM.Wave.waveEvenAbs_weighted_eq`: the even majorant of a real sequence whose weighted squares
  are `u` has two-sided weighted norm at most `√2 (Σ u)^{1/2}` (`stepW:w1:maj1`);
* `KAM.Wave.waveTripleConv_weighted`: the triple convolution `(x * y) * z` of the algebra
  `ℓ^{a,s}_b` (`s ≥ 1`) is controlled by `K_s² ∏ ‖·‖` (`stepW:w1:smooth1`);
* `KAM.Wave.waveSel_norm_step`: a pointwise bound `t_l ≤ M l^{-1/2} X_l` by an even `X` gives
  `Σ_{l ≥ 1} (ω_{a,p+1}(l) t_l)² ≤ M² ‖X‖²_{a,p+1/2} / 2`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

lemma waveEvenAbs_weighted_eq {a s : ℝ} {f : ℕ+ → ℝ} {u : ℕ+ → ℝ}
    (hg : ∀ n : ℕ+, (ellWeight a s n * |f n|) ^ 2 = u n) (hu : Summable u) :
    Summable (fun i : ℤ => (waveTwoWeight a s i * waveEvenAbs f i) ^ 2) ∧
      w0aL2 (fun i : ℤ => waveTwoWeight a s i * waveEvenAbs f i) ≤
        Real.sqrt 2 * Real.sqrt (∑' n : ℕ+, u n) := by
  set F : ℤ → ℝ := fun i => (waveTwoWeight a s i * waveEvenAbs f i) ^ 2 with hF
  have hev : ∀ i, F (-i) = F i := fun i => by simp [hF, w0a_twoWeight_neg, waveEvenAbs_neg]
  have h0 : F 0 = 0 := by simp [hF, waveEvenAbs_zero]
  have hFn : ∀ n : ℕ+, F ((n : ℕ) : ℤ) = u n := fun n => by
    simp only [hF, waveTwoWeight_pnat, waveEvenAbs_pnat]
    exact hg n
  have hFs : Summable fun n : ℕ+ => F ((n : ℕ) : ℤ) := hu.congr fun n => (hFn n).symm
  have hS := w0aHasSum_int_even_pnat hev h0 hFs.hasSum
  refine ⟨hS.summable, ?_⟩
  have hL : ∑' i : ℤ, F i = 2 * ∑' n : ℕ+, u n := by
    rw [hS.tsum_eq]
    exact congrArg _ (tsum_congr hFn)
  unfold w0aL2
  rw [hL, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem waveTripleConv_weighted {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {x y z : ℤ → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ i, 0 ≤ y i) (hz0 : ∀ i, 0 ≤ z i)
    (hxw : Summable fun i => (waveTwoWeight a s i * x i) ^ 2)
    (hyw : Summable fun i => (waveTwoWeight a s i * y i) ^ 2)
    (hzw : Summable fun i => (waveTwoWeight a s i * z i) ^ 2) :
    Summable (fun l => (waveTwoWeight a s l * waveConv (waveConv x y) z l) ^ 2) ∧
      w0aL2 (fun l => waveTwoWeight a s l * waveConv (waveConv x y) z l) ≤
        waveAlgConst s ^ 2 * (w0aL2 (fun i => waveTwoWeight a s i * x i) *
          w0aL2 (fun i => waveTwoWeight a s i * y i) *
          w0aL2 (fun i => waveTwoWeight a s i * z i)) := by
  obtain ⟨hA1s, hA1L⟩ := w0a_convAlgebra_nonneg ha hs hx0 hy0 hxw hyw
  have hA10 : ∀ i, 0 ≤ waveConv x y i := fun i => tsum_nonneg fun j => mul_nonneg (hx0 _) (hy0 _)
  obtain ⟨hA2s, hA2L⟩ := w0a_convAlgebra_nonneg ha hs hA10 hz0 hA1s hzw
  refine ⟨hA2s, ?_⟩
  have hK0 : 0 ≤ waveAlgConst s := by unfold waveAlgConst; positivity
  have hLz : 0 ≤ w0aL2 (fun i => waveTwoWeight a s i * z i) := Real.sqrt_nonneg _
  calc _ ≤ _ := hA2L
    _ ≤ waveAlgConst s * (waveAlgConst s * w0aL2 (fun i => waveTwoWeight a s i * x i) *
          w0aL2 (fun i => waveTwoWeight a s i * y i)) *
          w0aL2 (fun i => waveTwoWeight a s i * z i) := by gcongr
    _ = _ := by ring

theorem waveSel_norm_step {a p M : ℝ} {t : ℕ+ → ℝ} (ht0 : ∀ l, 0 ≤ t l)
    {X : ℤ → ℝ} (hXe : ∀ i, X (-i) = X i)
    (hXs : Summable fun i => (waveTwoWeight a (p + 1 / 2) i * X i) ^ 2)
    (hle : ∀ l : ℕ+, t l ≤ M * (Real.sqrt (l : ℝ))⁻¹ * X ((l : ℕ) : ℤ)) :
    Summable (fun l : ℕ+ => (ellWeight a (p + 1) l * t l) ^ 2) ∧
      ∑' l : ℕ+, (ellWeight a (p + 1) l * t l) ^ 2 ≤
        M ^ 2 * w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * X i) ^ 2 / 2 := by
  set F : ℤ → ℝ := fun i => (waveTwoWeight a (p + 1 / 2) i * X i) ^ 2 with hF
  have hFev : ∀ i, F (-i) = F i := fun i => by simp [hF, w0a_twoWeight_neg, hXe]
  have inj : Function.Injective (fun n : ℕ+ => ((n : ℕ) : ℤ)) := fun a b h => by
    have h' : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := h
    exact PNat.coe_injective (by exact_mod_cast h')
  have hFs : Summable fun n : ℕ+ => F ((n : ℕ) : ℤ) := hXs.comp_injective inj
  have hpt : ∀ l : ℕ+, (ellWeight a (p + 1) l * t l) ^ 2 ≤ M ^ 2 * F ((l : ℕ) : ℤ) := by
    intro l
    have hln : (0 : ℝ) < (l : ℝ) := by positivity
    have hsl : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.2 hln
    have hw : ellWeight a (p + 1) l = ellWeight a (p + 1 / 2) l * Real.sqrt (l : ℝ) := by
      have : p + 1 = (p + 1 / 2) + 1 / 2 := by ring
      rw [this, wave_ellWeight_add_half]
    have hwp : 0 < ellWeight a (p + 1 / 2) l := ellWeight_pos _ _ l
    have h1 : ellWeight a (p + 1) l * t l ≤ M * (ellWeight a (p + 1 / 2) l * X ((l : ℕ) : ℤ)) := by
      rw [hw]
      calc ellWeight a (p + 1 / 2) l * Real.sqrt (l : ℝ) * t l
          ≤ ellWeight a (p + 1 / 2) l * Real.sqrt (l : ℝ) *
            (M * (Real.sqrt (l : ℝ))⁻¹ * X ((l : ℕ) : ℤ)) := by gcongr; exact hle l
        _ = _ := by field_simp
    have h0 : 0 ≤ ellWeight a (p + 1) l * t l := mul_nonneg (ellWeight_pos _ _ l).le (ht0 l)
    have := pow_le_pow_left₀ h0 h1 2
    calc _ ≤ _ := this
      _ = M ^ 2 * F ((l : ℕ) : ℤ) := by
        simp only [hF, waveTwoWeight_pnat]; ring
  have hsum : Summable fun l : ℕ+ => (ellWeight a (p + 1) l * t l) ^ 2 :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hpt (hFs.mul_left _)
  refine ⟨hsum, ?_⟩
  have hint := w0aHasSum_int_even_pnat' hFev hFs.hasSum
  have hLsq : w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * X i) ^ 2 = ∑' i : ℤ, F i :=
    Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg _)
  have hF0 : 0 ≤ F 0 := sq_nonneg _
  calc ∑' l : ℕ+, (ellWeight a (p + 1) l * t l) ^ 2
      ≤ ∑' l : ℕ+, M ^ 2 * F ((l : ℕ) : ℤ) := Summable.tsum_le_tsum hpt hsum (hFs.mul_left _)
    _ = M ^ 2 * ∑' l : ℕ+, F ((l : ℕ) : ℤ) := tsum_mul_left
    _ ≤ M ^ 2 * (w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * X i) ^ 2 / 2) := by
        gcongr
        rw [hLsq, hint.tsum_eq]
        linarith
    _ = _ := by ring

end KAM.Wave

end
