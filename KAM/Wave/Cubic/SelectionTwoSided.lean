/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.SelectionTwoMaj
public import KAM.Wave.Cubic.SelectionOneSided

/-!
# Selection-rule trilinear maps, two-sided (blueprint `bpW:w1:selection` (b)), pointwise part

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is
still being built.

For `l ≠ 0`, the triple sum over `(ℤ ∖ 0)³` of `‖c_{ijkl} w_i w'_j w''_k‖` is reindexed by sign
patterns and `ℕ+³` (`KAM.Wave.waveSignZEmb`) and bounded by `8 M |l|^{-1/2} ((x̃ * ỹ) * z̃)_{|l|}`
(`KAM.Wave.waveSelSumZ_pointwise`), using the one-sided selection estimate
`KAM.Wave.wave_selection_sum_le`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- Number of patterns `Σ_{ε ∈ {±1}³} [l = ε₁ i + ε₂ j + ε₃ k]` for integer arguments. -/
def waveSelCountZ (l i j k : ℤ) : ℝ :=
  ∑ ε : Bool × Bool × Bool,
    (if l = waveSign ε.1 * i + waveSign ε.2.1 * j + waveSign ε.2.2 * k then (1 : ℝ) else 0)

/-- The two-sided triple sums `Σ_{i,j,k ≠ 0} c_{ijkl} w_i w'_j w''_k` (a `tsum`). -/
def waveSelSumZ (c : ℤ → ℤ → ℤ → ℤ → ℂ) (w w' w'' : ℤ → ℂ) (l : ℤ) : ℂ :=
  ∑' t : ℤ × ℤ × ℤ, if t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0 then
    c t.1 t.2.1 t.2.2 l * (w t.1 * (w' t.2.1 * w'' t.2.2)) else 0

lemma waveSign_mul_sign (b b' : Bool) (n : ℤ) :
    waveSign b * (waveSign b' * n) = waveSign (!(xor b b')) * n := by
  cases b <;> cases b' <;> simp [waveSign, boolSign]

lemma waveSign_not (b : Bool) : waveSign (!b) = -waveSign b := by
  cases b <;> simp [waveSign, boolSign]

/-- The reindexing `(δ, (i', j', k')) ↦ (δ₁ i', δ₂ j', δ₃ k')` of `(ℤ ∖ 0)³`. -/
def waveSignZEmb (p : (Bool × Bool × Bool) × (ℕ+ × ℕ+ × ℕ+)) : ℤ × ℤ × ℤ :=
  (waveSign p.1.1 * ((p.2.1 : ℕ) : ℤ), waveSign p.1.2.1 * ((p.2.2.1 : ℕ) : ℤ),
    waveSign p.1.2.2 * ((p.2.2.2 : ℕ) : ℤ))

lemma waveSignZEmb_injective : Function.Injective waveSignZEmb := by
  rintro ⟨⟨e1, e2, e3⟩, i, j, k⟩ ⟨⟨f1, f2, f3⟩, i', j', k'⟩ h
  simp only [waveSignZEmb, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨a1, b1⟩ := waveSign_mul_inj h1
  obtain ⟨a2, b2⟩ := waveSign_mul_inj h2
  obtain ⟨a3, b3⟩ := waveSign_mul_inj h3
  subst a1 a2 a3 b1 b2 b3
  rfl

lemma waveSign_exists {z : ℤ} (hz : z ≠ 0) :
    ∃ (b : Bool) (n : ℕ+), z = waveSign b * ((n : ℕ) : ℤ) := by
  rcases lt_or_gt_of_ne hz with h | h
  · refine ⟨false, ⟨z.natAbs, Int.natAbs_pos.2 hz⟩, ?_⟩
    simp only [waveSign, boolSign, Bool.false_eq_true, if_false, PNat.mk_coe]
    omega
  · refine ⟨true, ⟨z.natAbs, Int.natAbs_pos.2 hz⟩, ?_⟩
    simp only [waveSign, boolSign, if_true, PNat.mk_coe]
    omega

lemma waveSignZEmb_surj {t : ℤ × ℤ × ℤ} (h1 : t.1 ≠ 0) (h2 : t.2.1 ≠ 0) (h3 : t.2.2 ≠ 0) :
    t ∈ Set.range waveSignZEmb := by
  obtain ⟨b1, n1, e1⟩ := waveSign_exists h1
  obtain ⟨b2, n2, e2⟩ := waveSign_exists h2
  obtain ⟨b3, n3, e3⟩ := waveSign_exists h3
  exact ⟨((b1, b2, b3), (n1, n2, n3)), by simp [waveSignZEmb, ← e1, ← e2, ← e3]⟩

lemma waveSignZEmb_ne_zero (p : (Bool × Bool × Bool) × (ℕ+ × ℕ+ × ℕ+)) :
    (waveSignZEmb p).1 ≠ 0 ∧ (waveSignZEmb p).2.1 ≠ 0 ∧ (waveSignZEmb p).2.2 ≠ 0 := by
  have hn : ∀ (b : Bool) (n : ℕ+), waveSign b * ((n : ℕ) : ℤ) ≠ 0 := fun b n => by
    have := n.pos
    cases b <;> simp [waveSign, boolSign]
  exact ⟨hn _ _, hn _ _, hn _ _⟩

lemma waveSelCountZ_emb (l : ℕ+) (δ : Bool × Bool × Bool) (t : ℕ+ × ℕ+ × ℕ+) :
    waveSelCountZ ((l : ℕ) : ℤ) (waveSignZEmb (δ, t)).1 (waveSignZEmb (δ, t)).2.1
      (waveSignZEmb (δ, t)).2.2 = waveSelCount l t := by
  unfold waveSelCountZ waveSelCount waveSignZEmb
  let e : Bool × Bool × Bool ≃ Bool × Bool × Bool :=
    { toFun := fun ε => (!(xor ε.1 δ.1), !(xor ε.2.1 δ.2.1), !(xor ε.2.2 δ.2.2))
      invFun := fun ε => (!(xor ε.1 δ.1), !(xor ε.2.1 δ.2.1), !(xor ε.2.2 δ.2.2))
      left_inv := fun ε => by
        simp
      right_inv := fun ε => by
        simp }
  conv_rhs => rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [e, Equiv.coe_fn_mk, waveSign_mul_sign]

lemma waveSelCountZ_neg (l i j k : ℤ) : waveSelCountZ (-l) i j k = waveSelCountZ l i j k := by
  unfold waveSelCountZ
  let e : Bool × Bool × Bool ≃ Bool × Bool × Bool :=
    { toFun := fun ε => (!ε.1, !ε.2.1, !ε.2.2)
      invFun := fun ε => (!ε.1, !ε.2.1, !ε.2.2)
      left_inv := fun ε => by simp
      right_inv := fun ε => by simp }
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [e, Equiv.coe_fn_mk, waveSign_not]
  exact if_congr (by constructor <;> intro h <;> linarith) rfl rfl

lemma abs_waveSign_mul_cast (b : Bool) (n : ℕ+) :
    |(((waveSign b * ((n : ℕ) : ℤ) : ℤ) : ℝ))| = ((n : ℕ) : ℝ) := by
  cases b <;> simp [waveSign, boolSign]

/-- The positive integer `|l|` for `l ≠ 0`. -/
def waveAbsPNat (l : ℤ) (hl : l ≠ 0) : ℕ+ := ⟨l.natAbs, Int.natAbs_pos.2 hl⟩

lemma waveSelCountZ_abs (l : ℤ) (hl : l ≠ 0) (δ : Bool × Bool × Bool) (t : ℕ+ × ℕ+ × ℕ+) :
    waveSelCountZ l (waveSignZEmb (δ, t)).1 (waveSignZEmb (δ, t)).2.1 (waveSignZEmb (δ, t)).2.2 =
      waveSelCount (waveAbsPNat l hl) t := by
  rcases Int.natAbs_eq l with h | h
  · have h' : l = (((waveAbsPNat l hl : ℕ+) : ℕ) : ℤ) := h
    calc _ = waveSelCountZ (((waveAbsPNat l hl : ℕ+) : ℕ) : ℤ) (waveSignZEmb (δ, t)).1
          (waveSignZEmb (δ, t)).2.1 (waveSignZEmb (δ, t)).2.2 :=
          congrArg (fun m => waveSelCountZ m _ _ _) h'
      _ = _ := waveSelCountZ_emb _ δ t
  · have h' : l = -(((waveAbsPNat l hl : ℕ+) : ℕ) : ℤ) := h
    calc _ = waveSelCountZ (-(((waveAbsPNat l hl : ℕ+) : ℕ) : ℤ)) (waveSignZEmb (δ, t)).1
          (waveSignZEmb (δ, t)).2.1 (waveSignZEmb (δ, t)).2.2 :=
          congrArg (fun m => waveSelCountZ m _ _ _) h'
      _ = _ := by rw [waveSelCountZ_neg]; exact waveSelCountZ_emb _ δ t

/-- Pointwise bound for the two-sided triple sums: for `l ≠ 0` the series converges absolutely
and `‖T_c(w,w',w'')_l‖ ≤ 8 M |l|^{-1/2} ((x̃ * ỹ) * z̃)_{|l|}` for even nonnegative summable
majorants `x, y, z` (`stepW:w1:sel2`). -/
theorem waveSelSumZ_pointwise {M : ℝ} (hM : 0 ≤ M) {c : ℤ → ℤ → ℤ → ℤ → ℂ}
    (hc : ∀ i j k l : ℤ, i ≠ 0 → j ≠ 0 → k ≠ 0 → l ≠ 0 → ‖c i j k l‖ ≤
      M * ((|(i : ℝ)| * |(j : ℝ)| * |(k : ℝ)| * |(l : ℝ)|) ^ (-(1 / 2 : ℝ))) *
        waveSelCountZ l i j k)
    {w w' w'' : ℤ → ℂ} {x y z : ℤ → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ i, 0 ≤ y i) (hz0 : ∀ i, 0 ≤ z i)
    (hxe : ∀ i, x (-i) = x i) (hye : ∀ i, y (-i) = y i) (hze : ∀ i, z (-i) = z i)
    (hx1 : Summable x) (hy1 : Summable y) (hz1 : Summable z)
    (hxw : ∀ (b : Bool) (n : ℕ+), ‖w (waveSign b * ((n : ℕ) : ℤ))‖ * (Real.sqrt (n : ℝ))⁻¹ ≤
      x ((n : ℕ) : ℤ))
    (hyw : ∀ (b : Bool) (n : ℕ+), ‖w' (waveSign b * ((n : ℕ) : ℤ))‖ * (Real.sqrt (n : ℝ))⁻¹ ≤
      y ((n : ℕ) : ℤ))
    (hzw : ∀ (b : Bool) (n : ℕ+), ‖w'' (waveSign b * ((n : ℕ) : ℤ))‖ * (Real.sqrt (n : ℝ))⁻¹ ≤
      z ((n : ℕ) : ℤ))
    {l : ℤ} (hl : l ≠ 0) :
    (Summable fun t : ℤ × ℤ × ℤ => ‖if t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0 then
        c t.1 t.2.1 t.2.2 l * (w t.1 * (w' t.2.1 * w'' t.2.2)) else 0‖) ∧
      ‖waveSelSumZ c w w' w'' l‖ ≤
        8 * (M * (Real.sqrt |(l : ℝ)|)⁻¹ * waveConv (waveConv x y) z |l|) := by
  set L : ℕ+ := waveAbsPNat l hl with hL
  have hLz : ((L : ℕ) : ℤ) = |l| := Int.natCast_natAbs l
  have hLr : ((L : ℕ) : ℝ) = |(l : ℝ)| := by
    have : (((L : ℕ) : ℤ) : ℝ) = ((|l| : ℤ) : ℝ) := by rw [hLz]
    rw [Int.cast_abs] at this
    simpa using this
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  have hsl : 0 < (Real.sqrt (L : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hLpos)
  obtain ⟨hsum, hle⟩ := wave_selection_sum_le hx0 hy0 hz0 hxe hye hze hx1 hy1 hz1 L
  set P : ℕ+ × ℕ+ × ℕ+ → ℝ := fun t => waveSelCount L t *
    (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ))) with hP
  have hsumP : Summable P := hsum
  have hleP : ∑' t, P t ≤ waveConv (waveConv x y) z ((L : ℕ) : ℤ) := hle
  set B : ℕ+ × ℕ+ × ℕ+ → ℝ := fun t => M * (Real.sqrt (L : ℝ))⁻¹ * P t with hB
  have hB0 : ∀ t, 0 ≤ B t := fun t => by
    have := waveSelCount_nonneg L t
    have hnn : 0 ≤ x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ)) :=
      mul_nonneg (hx0 _) (mul_nonneg (hy0 _) (hz0 _))
    simp only [hB, hP]
    positivity
  have hBs : Summable B := hsumP.mul_left _
  -- the guarded term
  set term : ℤ × ℤ × ℤ → ℂ := fun t => if t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0 then
        c t.1 t.2.1 t.2.2 l * (w t.1 * (w' t.2.1 * w'' t.2.2)) else 0 with hterm
  have hpt : ∀ p : (Bool × Bool × Bool) × (ℕ+ × ℕ+ × ℕ+), ‖term (waveSignZEmb p)‖ ≤ B p.2 := by
    rintro ⟨δ, i, j, k⟩
    have hnz := waveSignZEmb_ne_zero (δ, i, j, k)
    simp only [hterm, hnz.1, hnz.2.1, hnz.2.2, ne_eq, not_false_eq_true, and_self, if_true]
    simp only [waveSignZEmb]
    have h1 := hc (waveSign δ.1 * ((i : ℕ) : ℤ)) (waveSign δ.2.1 * ((j : ℕ) : ℤ))
      (waveSign δ.2.2 * ((k : ℕ) : ℤ)) l hnz.1 hnz.2.1 hnz.2.2 hl
    have hcnt := waveSelCountZ_abs l hl δ (i, j, k)
    simp only [waveSignZEmb] at hcnt
    rw [hcnt, abs_waveSign_mul_cast, abs_waveSign_mul_cast, abs_waveSign_mul_cast,
      ← hLr] at h1
    rw [wave_rpow_neg_half_prod] at h1
    have hnn : 0 ≤ ‖w (waveSign δ.1 * ((i : ℕ) : ℤ))‖ *
        (‖w' (waveSign δ.2.1 * ((j : ℕ) : ℤ))‖ * ‖w'' (waveSign δ.2.2 * ((k : ℕ) : ℤ))‖) := by
      positivity
    rw [norm_mul, norm_mul, norm_mul]
    have hi := hxw δ.1 i
    have hj := hyw δ.2.1 j
    have hk := hzw δ.2.2 k
    have hsi : 0 ≤ (Real.sqrt (i : ℝ))⁻¹ := by positivity
    have hsj : 0 ≤ (Real.sqrt (j : ℝ))⁻¹ := by positivity
    have hsk : 0 ≤ (Real.sqrt (k : ℝ))⁻¹ := by positivity
    have hN := waveSelCount_nonneg L (i, j, k)
    calc ‖c (waveSign δ.1 * ((i : ℕ) : ℤ)) (waveSign δ.2.1 * ((j : ℕ) : ℤ))
          (waveSign δ.2.2 * ((k : ℕ) : ℤ)) l‖ *
          (‖w (waveSign δ.1 * ((i : ℕ) : ℤ))‖ *
            (‖w' (waveSign δ.2.1 * ((j : ℕ) : ℤ))‖ * ‖w'' (waveSign δ.2.2 * ((k : ℕ) : ℤ))‖))
        ≤ (M * ((Real.sqrt i)⁻¹ * ((Real.sqrt j)⁻¹ * ((Real.sqrt k)⁻¹ * (Real.sqrt L)⁻¹))) *
            waveSelCount L (i, j, k)) *
          (‖w (waveSign δ.1 * ((i : ℕ) : ℤ))‖ *
            (‖w' (waveSign δ.2.1 * ((j : ℕ) : ℤ))‖ * ‖w'' (waveSign δ.2.2 * ((k : ℕ) : ℤ))‖)) :=
          mul_le_mul_of_nonneg_right h1 hnn
      _ = M * (Real.sqrt L)⁻¹ * waveSelCount L (i, j, k) *
          ((‖w (waveSign δ.1 * ((i : ℕ) : ℤ))‖ * (Real.sqrt i)⁻¹) *
            ((‖w' (waveSign δ.2.1 * ((j : ℕ) : ℤ))‖ * (Real.sqrt j)⁻¹) *
              (‖w'' (waveSign δ.2.2 * ((k : ℕ) : ℤ))‖ * (Real.sqrt k)⁻¹))) := by ring
      _ ≤ M * (Real.sqrt L)⁻¹ * waveSelCount L (i, j, k) *
          (x ((i : ℕ) : ℤ) * (y ((j : ℕ) : ℤ) * z ((k : ℕ) : ℤ))) := by
          gcongr <;> first | exact hx0 _ | exact hy0 _
      _ = B (i, j, k) := by simp only [hB, hP]; ring
  -- summability over sign patterns
  have hprodS : Summable fun p : (Bool × Bool × Bool) × (ℕ+ × ℕ+ × ℕ+) => B p.2 := by
    have := summable_mul_of_summable_norm (f := fun _ : Bool × Bool × Bool => (1 : ℝ))
      (g := B) (by simp only [norm_one]; exact Summable.of_finite)
      (by simpa [Real.norm_of_nonneg (hB0 _)] using hBs)
    simpa using this
  have hsupp : ∀ t ∉ Set.range waveSignZEmb, ‖term t‖ = 0 := by
    intro t ht
    have : ¬ (t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0) := fun h => ht (waveSignZEmb_surj h.1 h.2.1 h.2.2)
    simp [hterm, this]
  have hS' : Summable fun p => ‖term (waveSignZEmb p)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hprodS
  have hS : Summable fun t => ‖term t‖ :=
    (waveSignZEmb_injective.summable_iff hsupp).1 hS'
  refine ⟨hS, ?_⟩
  have hsupp' : Function.support (fun t => ‖term t‖) ⊆ Set.range waveSignZEmb := fun t ht => by
    by_contra h; exact ht (hsupp t h)
  calc ‖waveSelSumZ c w w' w'' l‖ ≤ ∑' t, ‖term t‖ := norm_tsum_le_tsum_norm hS
    _ = ∑' p, ‖term (waveSignZEmb p)‖ := (waveSignZEmb_injective.tsum_eq hsupp').symm
    _ ≤ ∑' p : (Bool × Bool × Bool) × (ℕ+ × ℕ+ × ℕ+), B p.2 :=
        Summable.tsum_le_tsum hpt hS' hprodS
    _ = 8 * ∑' t, B t := by
        have hn : Summable fun x : ℕ+ × ℕ+ × ℕ+ => ‖B x‖ := by
          simpa [Real.norm_of_nonneg (hB0 _)] using hBs
        have := tsum_mul_tsum_of_summable_norm (f := fun _ : Bool × Bool × Bool => (1 : ℝ))
          (g := B) (by simp only [norm_one]; exact Summable.of_finite) hn
        simp only [one_mul] at this
        rw [← this, tsum_fintype]
        simp
    _ ≤ _ := by
        have e : ∑' t, B t = M * (Real.sqrt (L : ℝ))⁻¹ * ∑' t, P t := tsum_mul_left
        rw [e, hLr]
        rw [hLz] at hleP
        have h2 : 0 ≤ M * (Real.sqrt |(l : ℝ)|)⁻¹ := by
          have : 0 ≤ (Real.sqrt |(l : ℝ)|)⁻¹ := by positivity
          positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hleP h2) (by norm_num)

end KAM.Wave

end
