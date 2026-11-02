/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.SelectionCore
public import KAM.Wave.Seq.Transport

/-!
# Selection-rule trilinear maps, one-sided (blueprint `bpW:w1:selection` (a))

For `c : ℕ+⁴ → 𝕜` with `|c_{ijkl}| ≤ M (ijkl)^{-1/2} Σ_ε [l = ε₁ i + ε₂ j + ε₃ k]` and
`q, q', q'' ∈ ℓ^{a,p}_𝕜` (`a ≥ 0`, `p ≥ 1/2`, `s = p + 1/2`), the sums
`T_c(q,q',q'')_l = Σ_{ijk} c_{ijkl} q_i q'_j q''_k` converge absolutely and
`‖T_c(q,q',q'')‖_{a,p+1} ≤ 2 M K_s² ‖q‖_{a,p} ‖q'‖_{a,p} ‖q''‖_{a,p}`
(`KAM.Wave.waveSel_oneSided`). Here `𝕜` is any `RCLike` field, so the statement covers `ℝ`
and `ℂ`. The sign-pattern count `Σ_ε [l = …]` is `KAM.Wave.waveSelCount`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K]

/-- The number `Σ_{ε ∈ {±1}³} [l = ε₁ i + ε₂ j + ε₃ k]` of selection-rule patterns. -/
def waveSelCount (l : ℕ+) (t : ℕ+ × ℕ+ × ℕ+) : ℝ :=
  ∑ ε : Bool × Bool × Bool,
    (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)
      + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ) then (1 : ℝ) else 0)

/-- The triple sums `T_c(q,q',q'')_l = Σ_{i,j,k ≥ 1} c_{ijkl} q_i q'_j q''_k` (a `tsum`). -/
def waveSelSum (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K) (q q' q'' : ℕ+ → K) (l : ℕ+) : K :=
  ∑' t : ℕ+ × ℕ+ × ℕ+, c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2))

lemma waveSelCount_nonneg (l : ℕ+) (t : ℕ+ × ℕ+ × ℕ+) : 0 ≤ waveSelCount l t :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma wave_rpow_neg_half_prod (i j k l : ℕ+) :
    ((i : ℝ) * j * k * l) ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt i)⁻¹ * ((Real.sqrt j)⁻¹ * ((Real.sqrt k)⁻¹ * (Real.sqrt l)⁻¹)) := by
  have hi : (0 : ℝ) ≤ i := by positivity
  have hj : (0 : ℝ) ≤ j := by positivity
  have hk : (0 : ℝ) ≤ k := by positivity
  have hl : (0 : ℝ) ≤ l := by positivity
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  simp only [mul_inv]
  ring

lemma wave_isEll_iff_summable (a p : ℝ) (w : ℕ+ → K) :
    IsEll a p w ↔ Summable fun j : ℕ+ => (ellWeight a p j * ‖w j‖) ^ 2 := by
  unfold IsEll
  rw [memℓp_gen_iff (by simp : 0 < (2 : ENNReal).toReal)]
  have : ∀ j : ℕ+, ‖(ellWeight a p j : K) * w j‖ ^ (2 : ENNReal).toReal =
      (ellWeight a p j * ‖w j‖) ^ 2 := fun j => by
    rw [norm_mul, norm_ellWeight_cast]
    simp
  simp only [this]

lemma wave_ellTsumNorm_eq (a p : ℝ) (w : ℕ+ → K) :
    ellTsumNorm a p w = Real.sqrt (∑' j : ℕ+, (ellWeight a p j * ‖w j‖) ^ 2) := rfl

/-- `bpW:w1:selection` (a), one-sided: absolute convergence of the triple sums, membership of
`T_c(q,q',q'')` in `ℓ^{a,p+1}` and the bound `2 M K_s² ‖q‖‖q'‖‖q''‖`, `s = p + 1/2`. -/
theorem waveSel_oneSided {a p M : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (hM : 0 ≤ M)
    {c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K}
    (hc : ∀ i j k l : ℕ+, ‖c i j k l‖ ≤
      M * (((i : ℝ) * j * k * l) ^ (-(1 / 2 : ℝ))) * waveSelCount l (i, j, k))
    {q q' q'' : ℕ+ → K} (hq : IsEll a p q) (hq' : IsEll a p q') (hq'' : IsEll a p q'') :
    (∀ l : ℕ+, Summable fun t : ℕ+ × ℕ+ × ℕ+ =>
        ‖c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2))‖) ∧
      IsEll a (p + 1) (waveSelSum c q q' q'') ∧
      ellTsumNorm a (p + 1) (waveSelSum c q q' q'') ≤
        2 * M * waveAlgConst (p + 1 / 2) ^ 2 *
          (ellTsumNorm a p q * ellTsumNorm a p q' * ellTsumNorm a p q'') := by
  have hs1 : 1 ≤ p + 1 / 2 := by linarith
  have hsq := (wave_isEll_iff_summable a p q).1 hq
  have hsq' := (wave_isEll_iff_summable a p q').1 hq'
  have hsq'' := (wave_isEll_iff_summable a p q'').1 hq''
  -- the even majorants `x_i = ‖q_{|i|}‖ / √|i|`
  have hmaj : ∀ (w : ℕ+ → K), Summable (fun j : ℕ+ => (ellWeight a p j * ‖w j‖) ^ 2) →
      (∀ n : ℕ+, (ellWeight a (p + 1 / 2) n * |‖w n‖ * (Real.sqrt (n : ℝ))⁻¹|) ^ 2 =
        (ellWeight a p n * ‖w n‖) ^ 2) := by
    intro w _ n
    have hn : (0 : ℝ) < n := by positivity
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn
    rw [abs_of_nonneg (by positivity), wave_ellWeight_add_half]
    congr 1
    field_simp
  obtain ⟨hxw, hxL⟩ := waveEvenAbs_weighted_eq (hmaj q hsq) hsq
  obtain ⟨hyw, hyL⟩ := waveEvenAbs_weighted_eq (hmaj q' hsq') hsq'
  obtain ⟨hzw, hzL⟩ := waveEvenAbs_weighted_eq (hmaj q'' hsq'') hsq''
  set fx : ℕ+ → ℝ := fun n => ‖q n‖ * (Real.sqrt (n : ℝ))⁻¹ with hfx
  set fy : ℕ+ → ℝ := fun n => ‖q' n‖ * (Real.sqrt (n : ℝ))⁻¹ with hfy
  set fz : ℕ+ → ℝ := fun n => ‖q'' n‖ * (Real.sqrt (n : ℝ))⁻¹ with hfz
  have hx0 := waveEvenAbs_nonneg fx
  have hy0 := waveEvenAbs_nonneg fy
  have hz0 := waveEvenAbs_nonneg fz
  have hxe := waveEvenAbs_neg fx
  have hye := waveEvenAbs_neg fy
  have hze := waveEvenAbs_neg fz
  have hxn : ∀ n : ℕ+, waveEvenAbs fx ((n : ℕ) : ℤ) = fx n := fun n => by
    rw [waveEvenAbs_pnat, abs_of_nonneg (by positivity)]
  have hyn : ∀ n : ℕ+, waveEvenAbs fy ((n : ℕ) : ℤ) = fy n := fun n => by
    rw [waveEvenAbs_pnat, abs_of_nonneg (by positivity)]
  have hzn : ∀ n : ℕ+, waveEvenAbs fz ((n : ℕ) : ℤ) = fz n := fun n => by
    rw [waveEvenAbs_pnat, abs_of_nonneg (by positivity)]
  have hx1 := w0a_summable_of_weighted ha hs1 hx0 hxw
  have hy1 := w0a_summable_of_weighted ha hs1 hy0 hyw
  have hz1 := w0a_summable_of_weighted ha hs1 hz0 hzw
  -- pointwise estimate
  have hpt : ∀ l : ℕ+,
      (Summable fun t : ℕ+ × ℕ+ × ℕ+ => ‖c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2))‖) ∧
      ‖waveSelSum c q q' q'' l‖ ≤ M * (Real.sqrt (l : ℝ))⁻¹ *
        waveConv (waveConv (waveEvenAbs fx) (waveEvenAbs fy)) (waveEvenAbs fz) ((l : ℕ) : ℤ) := by
    intro l
    obtain ⟨hsum, hle⟩ := wave_selection_sum_le hx0 hy0 hz0 hxe hye hze hx1 hy1 hz1 l
    set P : ℕ+ × ℕ+ × ℕ+ → ℝ := fun t =>
      waveSelCount l t * (waveEvenAbs fx ((t.1 : ℕ) : ℤ) *
        (waveEvenAbs fy ((t.2.1 : ℕ) : ℤ) * waveEvenAbs fz ((t.2.2 : ℕ) : ℤ))) with hP
    have hsum' : Summable P := hsum
    have hle' : ∑' t, P t ≤
        waveConv (waveConv (waveEvenAbs fx) (waveEvenAbs fy)) (waveEvenAbs fz) ((l : ℕ) : ℤ) := hle
    have hsl : 0 < (Real.sqrt (l : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
    have hterm : ∀ t : ℕ+ × ℕ+ × ℕ+,
        ‖c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2))‖ ≤
          M * (Real.sqrt (l : ℝ))⁻¹ * P t := by
      intro t
      have h1 := hc t.1 t.2.1 t.2.2 l
      rw [wave_rpow_neg_half_prod] at h1
      have hnn : 0 ≤ ‖q t.1‖ * (‖q' t.2.1‖ * ‖q'' t.2.2‖) := by positivity
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖c t.1 t.2.1 t.2.2 l‖ * (‖q t.1‖ * (‖q' t.2.1‖ * ‖q'' t.2.2‖))
          ≤ (M * ((Real.sqrt t.1)⁻¹ * ((Real.sqrt t.2.1)⁻¹ * ((Real.sqrt t.2.2)⁻¹ *
              (Real.sqrt l)⁻¹))) * waveSelCount l (t.1, t.2.1, t.2.2)) *
            (‖q t.1‖ * (‖q' t.2.1‖ * ‖q'' t.2.2‖)) := mul_le_mul_of_nonneg_right h1 hnn
        _ = _ := by
          simp only [hP]
          rw [hxn, hyn, hzn]
          simp only [hfx, hfy, hfz]
          ring
    have hsumn : Summable fun t : ℕ+ × ℕ+ × ℕ+ =>
        ‖c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2))‖ :=
      Summable.of_nonneg_of_le (fun t => norm_nonneg _) hterm (hsum'.mul_left _)
    refine ⟨hsumn, ?_⟩
    unfold waveSelSum
    calc _ ≤ ∑' t : ℕ+ × ℕ+ × ℕ+,
          ‖c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2))‖ := norm_tsum_le_tsum_norm hsumn
      _ ≤ ∑' t, M * (Real.sqrt (l : ℝ))⁻¹ * P t :=
          Summable.tsum_le_tsum hterm hsumn (hsum'.mul_left _)
      _ = M * (Real.sqrt (l : ℝ))⁻¹ * ∑' t, P t := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hle' (mul_nonneg hM hsl.le)
  refine ⟨fun l => (hpt l).1, ?_⟩
  -- the triple convolution
  obtain ⟨hXs, hXL⟩ := waveTripleConv_weighted ha hs1 hx0 hy0 hz0 hxw hyw hzw
  have hA1e : ∀ i, waveConv (waveEvenAbs fx) (waveEvenAbs fy) (-i) =
      waveConv (waveEvenAbs fx) (waveEvenAbs fy) i := w0a_conv_even hxe hye
  have hXe : ∀ i, waveConv (waveConv (waveEvenAbs fx) (waveEvenAbs fy)) (waveEvenAbs fz) (-i) =
      waveConv (waveConv (waveEvenAbs fx) (waveEvenAbs fy)) (waveEvenAbs fz) i :=
    w0a_conv_even hA1e hze
  obtain ⟨hTs, hTL⟩ := waveSel_norm_step (a := a) (p := p) (M := M)
    (t := fun l => ‖waveSelSum c q q' q'' l‖) (fun l => norm_nonneg _) hXe hXs
    (fun l => (hpt l).2)
  have hIs : IsEll a (p + 1) (waveSelSum c q q' q'') := by
    rw [wave_isEll_iff_summable]; exact hTs
  refine ⟨hIs, ?_⟩
  -- the constants
  set Nq := ellTsumNorm a p q with hNq
  set Nq' := ellTsumNorm a p q' with hNq'
  set Nq'' := ellTsumNorm a p q'' with hNq''
  have hNq0 : 0 ≤ Nq := Real.sqrt_nonneg _
  have hNq0' : 0 ≤ Nq' := Real.sqrt_nonneg _
  have hNq0'' : 0 ≤ Nq'' := Real.sqrt_nonneg _
  have hxL' : w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fx i) ≤
      Real.sqrt 2 * Nq := by
    rw [hNq, wave_ellTsumNorm_eq]; exact hxL
  have hyL' : w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fy i) ≤
      Real.sqrt 2 * Nq' := by
    rw [hNq', wave_ellTsumNorm_eq]; exact hyL
  have hzL' : w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fz i) ≤
      Real.sqrt 2 * Nq'' := by
    rw [hNq'', wave_ellTsumNorm_eq]; exact hzL
  have hK0 : 0 ≤ waveAlgConst (p + 1 / 2) := by unfold waveAlgConst; positivity
  have hr2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  set K := waveAlgConst (p + 1 / 2) with hKd
  set L := w0aL2 (fun l => waveTwoWeight a (p + 1 / 2) l *
    waveConv (waveConv (waveEvenAbs fx) (waveEvenAbs fy)) (waveEvenAbs fz) l) with hL
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hLx0 : 0 ≤ w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fx i) :=
    Real.sqrt_nonneg _
  have hLy0 : 0 ≤ w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fy i) :=
    Real.sqrt_nonneg _
  have hLz0 : 0 ≤ w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fz i) :=
    Real.sqrt_nonneg _
  have hLle : L ≤ K ^ 2 * (2 * Real.sqrt 2) * (Nq * Nq' * Nq'') := by
    calc L ≤ K ^ 2 * (w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fx i) *
          w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fy i) *
          w0aL2 (fun i => waveTwoWeight a (p + 1 / 2) i * waveEvenAbs fz i)) := hXL
      _ ≤ K ^ 2 * ((Real.sqrt 2 * Nq) * (Real.sqrt 2 * Nq') * (Real.sqrt 2 * Nq'')) := by
          gcongr
      _ = K ^ 2 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt 2 * (Nq * Nq' * Nq'') := by ring
      _ = _ := by rw [hr2]; ring
  have hsumle : ∑' l : ℕ+, (ellWeight a (p + 1) l * ‖waveSelSum c q q' q'' l‖) ^ 2 ≤
      (2 * M * K ^ 2 * (Nq * Nq' * Nq'')) ^ 2 := by
    refine hTL.trans ?_
    have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    calc M ^ 2 * L ^ 2 / 2 ≤ M ^ 2 * (K ^ 2 * (2 * Real.sqrt 2) * (Nq * Nq' * Nq'')) ^ 2 / 2 := by
          gcongr
      _ = _ := by
          have : (K ^ 2 * (2 * Real.sqrt 2) * (Nq * Nq' * Nq'')) ^ 2 =
              8 * (K ^ 2 * (Nq * Nq' * Nq'')) ^ 2 := by
            rw [mul_pow, mul_pow, h8]; ring
          rw [this]; ring
  rw [wave_ellTsumNorm_eq]
  calc Real.sqrt (∑' l : ℕ+, (ellWeight a (p + 1) l * ‖waveSelSum c q q' q'' l‖) ^ 2)
      ≤ Real.sqrt ((2 * M * K ^ 2 * (Nq * Nq' * Nq'')) ^ 2) := Real.sqrt_le_sqrt hsumle
    _ = _ := Real.sqrt_sq (by positivity)

/-! Multilinearity and symmetry of `T_c` (the last sentence of `bpW:w1:selection`). -/

theorem waveSelSum_smul_left (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K) (r : K) (q q' q'' : ℕ+ → K) (l : ℕ+) :
    waveSelSum c (fun j => r * q j) q' q'' l = r * waveSelSum c q q' q'' l := by
  unfold waveSelSum
  rw [← tsum_mul_left]
  exact tsum_congr fun t => by ring

theorem waveSelSum_smul_mid (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K) (r : K) (q q' q'' : ℕ+ → K) (l : ℕ+) :
    waveSelSum c q (fun j => r * q' j) q'' l = r * waveSelSum c q q' q'' l := by
  unfold waveSelSum
  rw [← tsum_mul_left]
  exact tsum_congr fun t => by ring

theorem waveSelSum_smul_right (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K) (r : K) (q q' q'' : ℕ+ → K) (l : ℕ+) :
    waveSelSum c q q' (fun j => r * q'' j) l = r * waveSelSum c q q' q'' l := by
  unfold waveSelSum
  rw [← tsum_mul_left]
  exact tsum_congr fun t => by ring

theorem waveSelSum_add_left (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K) (q r q' q'' : ℕ+ → K) (l : ℕ+)
    (hq : Summable fun t : ℕ+ × ℕ+ × ℕ+ => c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2)))
    (hr : Summable fun t : ℕ+ × ℕ+ × ℕ+ => c t.1 t.2.1 t.2.2 l * (r t.1 * (q' t.2.1 * q'' t.2.2))) :
    waveSelSum c (fun j => q j + r j) q' q'' l =
      waveSelSum c q q' q'' l + waveSelSum c r q' q'' l := by
  unfold waveSelSum
  rw [← Summable.tsum_add hq hr]
  exact tsum_congr fun t => by ring

theorem waveSelSum_add_mid (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K) (q q' r q'' : ℕ+ → K) (l : ℕ+)
    (hq : Summable fun t : ℕ+ × ℕ+ × ℕ+ => c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2)))
    (hr : Summable fun t : ℕ+ × ℕ+ × ℕ+ => c t.1 t.2.1 t.2.2 l * (q t.1 * (r t.2.1 * q'' t.2.2))) :
    waveSelSum c q (fun j => q' j + r j) q'' l =
      waveSelSum c q q' q'' l + waveSelSum c q r q'' l := by
  unfold waveSelSum
  rw [← Summable.tsum_add hq hr]
  exact tsum_congr fun t => by ring

theorem waveSelSum_add_right (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K) (q q' q'' r : ℕ+ → K) (l : ℕ+)
    (hq : Summable fun t : ℕ+ × ℕ+ × ℕ+ => c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * q'' t.2.2)))
    (hr : Summable fun t : ℕ+ × ℕ+ × ℕ+ => c t.1 t.2.1 t.2.2 l * (q t.1 * (q' t.2.1 * r t.2.2))) :
    waveSelSum c q q' (fun j => q'' j + r j) l =
      waveSelSum c q q' q'' l + waveSelSum c q q' r l := by
  unfold waveSelSum
  rw [← Summable.tsum_add hq hr]
  exact tsum_congr fun t => by ring

/-- Symmetry of `T_c` in the first two arguments when `c` is symmetric in the first two indices. -/
theorem waveSelSum_swap_left_mid (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K)
    (hc : ∀ i j k l, c i j k l = c j i k l) (q q' q'' : ℕ+ → K) (l : ℕ+) :
    waveSelSum c q q' q'' l = waveSelSum c q' q q'' l := by
  unfold waveSelSum
  let e : ℕ+ × ℕ+ × ℕ+ ≃ ℕ+ × ℕ+ × ℕ+ :=
    { toFun := fun t => (t.2.1, t.1, t.2.2)
      invFun := fun t => (t.2.1, t.1, t.2.2)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun t => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [hc t.2.1 t.1]
  ring

/-- Symmetry of `T_c` in the last two arguments when `c` is symmetric in the last two indices
among the first three. -/
theorem waveSelSum_swap_mid_right (c : ℕ+ → ℕ+ → ℕ+ → ℕ+ → K)
    (hc : ∀ i j k l, c i j k l = c i k j l) (q q' q'' : ℕ+ → K) (l : ℕ+) :
    waveSelSum c q q' q'' l = waveSelSum c q q'' q' l := by
  unfold waveSelSum
  let e : ℕ+ × ℕ+ × ℕ+ ≃ ℕ+ × ℕ+ × ℕ+ :=
    { toFun := fun t => (t.1, t.2.2, t.2.1)
      invFun := fun t => (t.1, t.2.2, t.2.1)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun t => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [hc t.1 t.2.2]
  ring

end KAM.Wave

end
