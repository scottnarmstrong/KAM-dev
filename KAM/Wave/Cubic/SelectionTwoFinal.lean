/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.SelectionTwoSided

/-!
# Selection-rule trilinear maps, two-sided (blueprint `bpW:w1:selection` (b))

For `c : ℤ⁴ → ℂ` with `|c_{ijkl}| ≤ M |ijkl|^{-1/2} Σ_ε [l = ε₁ i + ε₂ j + ε₃ k]` (indices nonzero)
and `w, w', w'' ∈ ℓ^{a,p}_b` (`a ≥ 0`, `p ≥ 1/2`, `s = p + 1/2`), the sums
`T_c(w,w',w'')_l = Σ_{i,j,k ≠ 0} c_{ijkl} w_i w'_j w''_k` (`l ≠ 0`) converge absolutely and, with
`T_c(·)_0 = 0` (`KAM.Wave.waveSelTwo`), `‖T_c(w,w',w'')‖_{a,p+1} ≤ 64 M K_s² ‖w‖‖w'‖‖w''‖`
(`KAM.Wave.waveSel_twoSided`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The two-sided trilinear sums with `T_c(·)_0 = 0`. -/
def waveSelTwo (c : ℤ → ℤ → ℤ → ℤ → ℂ) (w w' w'' : ℤ → ℂ) (l : ℤ) : ℂ :=
  if l = 0 then 0 else waveSelSumZ c w w' w'' l

lemma waveTwoMaj_pnat (w : ℤ → ℂ) (n : ℕ+) :
    waveTwoMaj w ((n : ℕ) : ℤ) =
      (‖w ((n : ℕ) : ℤ)‖ + ‖w (-((n : ℕ) : ℤ))‖) * (Real.sqrt (n : ℝ))⁻¹ := by
  simp [waveTwoMaj, div_eq_mul_inv]

lemma waveTwoMaj_bound (w : ℤ → ℂ) (b : Bool) (n : ℕ+) :
    ‖w (waveSign b * ((n : ℕ) : ℤ))‖ * (Real.sqrt (n : ℝ))⁻¹ ≤ waveTwoMaj w ((n : ℕ) : ℤ) := by
  rw [waveTwoMaj_pnat]
  have hs : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
  cases b
  · simp only [waveSign, boolSign, Bool.false_eq_true, if_false, neg_one_mul]
    gcongr
    linarith [norm_nonneg (w ((n : ℕ) : ℤ))]
  · simp only [waveSign, boolSign, if_true, one_mul]
    gcongr
    linarith [norm_nonneg (w (-((n : ℕ) : ℤ)))]

/-- `bpW:w1:selection` (b), two-sided: absolute convergence of the triple sums, membership of
`T_c(w,w',w'')` in `ℓ^{a,p+1}_b` and the bound `64 M K_s² ‖w‖‖w'‖‖w''‖`, `s = p + 1/2`. -/
theorem waveSel_twoSided {a p M : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (hM : 0 ≤ M)
    {c : ℤ → ℤ → ℤ → ℤ → ℂ}
    (hc : ∀ i j k l : ℤ, i ≠ 0 → j ≠ 0 → k ≠ 0 → l ≠ 0 → ‖c i j k l‖ ≤
      M * ((|(i : ℝ)| * |(j : ℝ)| * |(k : ℝ)| * |(l : ℝ)|) ^ (-(1 / 2 : ℝ))) *
        waveSelCountZ l i j k)
    {w w' w'' : ℤ → ℂ} (hw : WaveTwoMem a p w) (hw' : WaveTwoMem a p w')
    (hw'' : WaveTwoMem a p w'') :
    (∀ l : ℤ, l ≠ 0 → Summable fun t : ℤ × ℤ × ℤ => ‖if t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0 then
        c t.1 t.2.1 t.2.2 l * (w t.1 * (w' t.2.1 * w'' t.2.2)) else 0‖) ∧
      WaveTwoMem a (p + 1) (waveSelTwo c w w' w'') ∧
      waveTwoNorm a (p + 1) (waveSelTwo c w w' w'') ≤
        64 * M * waveAlgConst (p + 1 / 2) ^ 2 *
          (waveTwoNorm a p w * waveTwoNorm a p w' * waveTwoNorm a p w'') := by
  have hs1 : 1 ≤ p + 1 / 2 := by linarith
  obtain ⟨hxw, hxL⟩ := waveTwoMaj_weighted hw
  obtain ⟨hyw, hyL⟩ := waveTwoMaj_weighted hw'
  obtain ⟨hzw, hzL⟩ := waveTwoMaj_weighted hw''
  have hx0 := waveTwoMaj_nonneg w
  have hy0 := waveTwoMaj_nonneg w'
  have hz0 := waveTwoMaj_nonneg w''
  have hxe := waveTwoMaj_neg w
  have hye := waveTwoMaj_neg w'
  have hze := waveTwoMaj_neg w''
  have hx1 := w0a_summable_of_weighted ha hs1 hx0 hxw
  have hy1 := w0a_summable_of_weighted ha hs1 hy0 hyw
  have hz1 := w0a_summable_of_weighted ha hs1 hz0 hzw
  have hpt := fun l (hl : l ≠ 0) => waveSelSumZ_pointwise hM hc hx0 hy0 hz0 hxe hye hze hx1 hy1 hz1
    (waveTwoMaj_bound w) (waveTwoMaj_bound w') (waveTwoMaj_bound w'') hl
  refine ⟨fun l hl => (hpt l hl).1, ?_⟩
  obtain ⟨hXs, hXL⟩ := waveTripleConv_weighted ha hs1 hx0 hy0 hz0 hxw hyw hzw
  have hA1e : ∀ i, waveConv (waveTwoMaj w) (waveTwoMaj w') (-i) =
      waveConv (waveTwoMaj w) (waveTwoMaj w') i := w0a_conv_even hxe hye
  have hXe : ∀ i, waveConv (waveConv (waveTwoMaj w) (waveTwoMaj w')) (waveTwoMaj w'') (-i) =
      waveConv (waveConv (waveTwoMaj w) (waveTwoMaj w')) (waveTwoMaj w'') i :=
    w0a_conv_even hA1e hze
  set X3 := waveConv (waveConv (waveTwoMaj w) (waveTwoMaj w')) (waveTwoMaj w'') with hX3
  set s := p + 1 / 2 with hs
  -- pointwise bound on the squares
  set F : ℤ → ℝ := fun l => (waveTwoWeight a (p + 1) l * ‖waveSelTwo c w w' w'' l‖) ^ 2 with hF
  set G : ℤ → ℝ := fun l => (8 * M) ^ 2 * (waveTwoWeight a s l * X3 l) ^ 2 with hG
  have hFG : ∀ l, F l ≤ G l := by
    intro l
    by_cases hl : l = 0
    · subst hl
      simp only [hF, hG, waveSelTwo, if_true, norm_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
      positivity
    · have hr : (0 : ℝ) < |(l : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast abs_pos.2 hl
      have hsq : 0 < Real.sqrt |(l : ℝ)| := Real.sqrt_pos.2 hr
      have hT := (hpt l hl).2
      have hXabs : X3 |l| = X3 l := by
        rcases abs_choice l with h | h <;> rw [h]; exact hXe l
      rw [hXabs] at hT
      have hw1 : waveTwoWeight a (p + 1) l = waveTwoWeight a s l * Real.sqrt |(l : ℝ)| := by
        rw [waveTwoWeight_of_ne_zero a _ hl, waveTwoWeight_of_ne_zero a _ hl, hs,
          show p + 1 = (p + 1 / 2) + 1 / 2 by ring, Real.rpow_add hr, Real.sqrt_eq_rpow]
        ring
      have hwp := waveTwoWeight_pos a s l
      have h1 : waveTwoWeight a (p + 1) l * ‖waveSelTwo c w w' w'' l‖ ≤
          8 * M * (waveTwoWeight a s l * X3 l) := by
        have e : waveSelTwo c w w' w'' l = waveSelSumZ c w w' w'' l := by simp [waveSelTwo, hl]
        rw [e, hw1]
        calc waveTwoWeight a s l * Real.sqrt |(l : ℝ)| * ‖waveSelSumZ c w w' w'' l‖
            ≤ waveTwoWeight a s l * Real.sqrt |(l : ℝ)| *
              (8 * (M * (Real.sqrt |(l : ℝ)|)⁻¹ * X3 l)) := by gcongr
          _ = _ := by field_simp
      have h0 : 0 ≤ waveTwoWeight a (p + 1) l * ‖waveSelTwo c w w' w'' l‖ :=
        mul_nonneg (waveTwoWeight_pos _ _ _).le (norm_nonneg _)
      have := pow_le_pow_left₀ h0 h1 2
      calc F l ≤ _ := this
        _ = G l := by simp only [hG]; ring
  have hGs : Summable G := hXs.mul_left _
  have hFs : Summable F := Summable.of_nonneg_of_le (fun l => sq_nonneg _) hFG hGs
  refine ⟨hFs, ?_⟩
  have hLsq : w0aL2 (fun l => waveTwoWeight a s l * X3 l) ^ 2 =
      ∑' l, (waveTwoWeight a s l * X3 l) ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun l => sq_nonneg _)
  have hsumF : ∑' l, F l ≤ (8 * M * w0aL2 (fun l => waveTwoWeight a s l * X3 l)) ^ 2 := by
    calc ∑' l, F l ≤ ∑' l, G l := Summable.tsum_le_tsum hFG hFs hGs
      _ = (8 * M) ^ 2 * ∑' l, (waveTwoWeight a s l * X3 l) ^ 2 := tsum_mul_left
      _ = _ := by rw [← hLsq]; ring
  have hxL' : w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w i) ≤ 2 * waveTwoNorm a p w := hxL
  have hyL' : w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w' i) ≤ 2 * waveTwoNorm a p w' := hyL
  have hzL' : w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w'' i) ≤
      2 * waveTwoNorm a p w'' := hzL
  have hK0 : 0 ≤ waveAlgConst s := waveAlgConst_nonneg s
  have hLx0 : 0 ≤ w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w i) := Real.sqrt_nonneg _
  have hLy0 : 0 ≤ w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w' i) := Real.sqrt_nonneg _
  have hLz0 : 0 ≤ w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w'' i) := Real.sqrt_nonneg _
  have hN1 := waveTwoNorm_nonneg a p w
  have hN2 := waveTwoNorm_nonneg a p w'
  have hN3 := waveTwoNorm_nonneg a p w''
  have hLX : w0aL2 (fun l => waveTwoWeight a s l * X3 l) ≤
      waveAlgConst s ^ 2 *
        (8 * (waveTwoNorm a p w * waveTwoNorm a p w' * waveTwoNorm a p w'')) := by
    calc _ ≤ waveAlgConst s ^ 2 * (w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w i) *
          w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w' i) *
          w0aL2 (fun i => waveTwoWeight a s i * waveTwoMaj w'' i)) := hXL
      _ ≤ waveAlgConst s ^ 2 * ((2 * waveTwoNorm a p w) * (2 * waveTwoNorm a p w') *
          (2 * waveTwoNorm a p w'')) := by gcongr
      _ = _ := by ring
  have hL0 : 0 ≤ w0aL2 (fun l => waveTwoWeight a s l * X3 l) := Real.sqrt_nonneg _
  change Real.sqrt (∑' l, (waveTwoWeight a (p + 1) l * ‖waveSelTwo c w w' w'' l‖) ^ 2) ≤ _
  calc Real.sqrt (∑' l, (waveTwoWeight a (p + 1) l * ‖waveSelTwo c w w' w'' l‖) ^ 2)
      ≤ Real.sqrt ((8 * M * w0aL2 (fun l => waveTwoWeight a s l * X3 l)) ^ 2) :=
        Real.sqrt_le_sqrt hsumF
    _ = 8 * M * w0aL2 (fun l => waveTwoWeight a s l * X3 l) := Real.sqrt_sq (by positivity)
    _ ≤ 8 * M * (waveAlgConst s ^ 2 *
        (8 * (waveTwoNorm a p w * waveTwoNorm a p w' * waveTwoNorm a p w''))) := by gcongr
    _ = _ := by ring

end KAM.Wave

end
