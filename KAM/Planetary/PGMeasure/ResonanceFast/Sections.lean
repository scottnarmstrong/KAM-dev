/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.ResonanceLarge.Sections

/-!
# P Part 4: fast-coordinate sections of the fast-dominant resonances (`stepP:p4:dm-A`)

For a mode `k ∈ 𝒦_A` (`k₁ ≠ 0` and `μ Λ_N Λ_g |k|₁ ≤ ‖k₁‖/2`) and a fast index `j` with
`|k₁,j| = ‖k₁‖`, the resonance function moves along `y ↦ y + s e_j` by at least `|k₁,j||s|/2`
(`N1` and the bi-Lipschitz bound of `g`), so every line in direction `e_j` meets the frequency
coordinate resonant set `ℛ'_k` in a set of diameter at most `4 α_k`. Design
`docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RA.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- The fast-dominant modes `𝒦_A`: `k₁ ≠ 0` and `μ Λ_N Λ_g |k|₁ ≤ ‖k₁‖/2`. -/
def fastModes (a b : ℕ) (mu LN Lg : ℝ) : Set (Fin (a+b) → ℤ) :=
  {k | blockFast k ≠ 0 ∧ mu*LN*Lg*l1 k ≤ ‖kFast k‖/2}

/-- `stepP:p4:dm-A`: the fast part of the frequency, minus `y`, is `μ Λ_N Λ_g`-Lipschitz in `y`. -/
theorem fast_dev_y (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1) {y y' : Fin a → ℝ}
    (hy : y ∈ freqCore d) (hy' : y' ∈ freqCore d) {xi : Fin b → ℝ} (hxi : ‖xi‖ ≤ d.lambda0) :
    ‖(fastPart d mu (d.g y') xi - y') - (fastPart d mu (d.g y) xi - y)‖ ≤
      mu * d.LN * d.Lg * ‖y' - y‖ := by
  obtain ⟨c1, c2⟩ := freqCore_spec d hy
  obtain ⟨c1', c2'⟩ := freqCore_spec d hy'
  have h1 := (d.N1 mu hmu _ c1' _ c1 xi hxi).1
  have h2 := dist_g_le d hy' hy
  have hmu0 := hmu.1
  unfold fastPart
  rw [c2, c2'] at h1
  refine h1.trans ?_
  calc mu * d.LN * ‖d.g y' - d.g y‖ ≤ mu * d.LN * (d.Lg * ‖y' - y‖) :=
        mul_le_mul_of_nonneg_left h2 (by nlinarith [d.hLN])
    _ = _ := by ring

theorem sub_eq_single_of_line {z z' : Fin (a+b) → ℝ} (j : Fin a)
    (hline : ∀ l, l ≠ Fin.castAdd b j → z l = z' l) :
    blockFast z' - blockFast z = Pi.single j (z' (Fin.castAdd b j) - z (Fin.castAdd b j)) ∧
      blockSlow z' = blockSlow z := by
  refine ⟨?_, funext fun i => (hline _ (castAdd_ne_natAdd j i).symm).symm⟩
  funext i
  by_cases hij : i = j
  · subst hij; simp [blockFast]
  · have hne : Fin.castAdd b i ≠ Fin.castAdd b j := fun h => hij (Fin.castAdd_injective _ _ h)
    simp [blockFast, hij, hline _ hne]

/-- `stepP:p4:dm-A`: two points of one fast line through `ℛ'_k` are within `4 α` in `y_j`. -/
theorem fastSection_line_diam (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {lambda : ℝ} (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0) {Q : Set (Fin b → ℝ)}
    (hQsub : Q ⊆ actionShell b (-lambda) lambda) {k : Fin (a+b) → ℤ}
    (hk : k ∈ fastModes a b mu d.LN d.Lg) {alpha : ℝ} {j : Fin a}
    (hj : |kFast k j| = ‖kFast k‖) {z z' : Fin (a+b) → ℝ}
    (hz : z ∈ resonanceSet d mu Q k alpha) (hz' : z' ∈ resonanceSet d mu Q k alpha)
    (hline : ∀ l, l ≠ Fin.castAdd b j → z l = z' l) :
    |z (Fin.castAdd b j) - z' (Fin.castAdd b j)| ≤ 4 * alpha := by
  have hmu0 := hmu.1
  obtain ⟨hk1, hkl⟩ := hk
  have hk1' := one_le_norm_kFast hk1
  obtain ⟨hy1, hQ1, hp1⟩ := hz
  obtain ⟨hy2, hQ2, hp2⟩ := hz'
  obtain ⟨hd1, hd2⟩ := sub_eq_single_of_line j hline
  set s : ℝ := z' (Fin.castAdd b j) - z (Fin.castAdd b j) with hs
  have hξ : ‖blockSlow z‖ ≤ d.lambda0 :=
    (norm_le_of_mem_actionShell hl (hQsub hQ1)).trans hl0
  have hnorm : ‖blockFast z' - blockFast z‖ = |s| := by
    rw [hd1, Pi.norm_single, Real.norm_eq_abs]
  -- the increment of the resonance function
  have hdiff : pullFreq d mu k z' - pullFreq d mu k z =
      kFast k j * s +
      (∑ i, kFast k i * ((fastPart d mu (d.g (blockFast z')) (blockSlow z) i - blockFast z' i) -
        (fastPart d mu (d.g (blockFast z)) (blockSlow z) i - blockFast z i)) +
      mu * ∑ i, kSlow k i * (slowFrequency d.Omega d.beta mu (d.g (blockFast z')) (blockSlow z) i -
        slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i)) := by
    rw [pullFreq_eq, pullFreq_eq, hd2]
    have hlin : ∑ i, kFast k i * (blockFast z' i - blockFast z i) = kFast k j * s := by
      calc ∑ i, kFast k i * (blockFast z' i - blockFast z i)
          = ∑ i, kFast k i * (Pi.single j s : Fin a → ℝ) i :=
            Finset.sum_congr rfl fun i _ => by rw [← Pi.sub_apply, hd1]
        _ = kFast k j * s := by simp [Pi.single_apply]
    simp only [mul_sub, Finset.sum_sub_distrib] at hlin ⊢
    linarith
  have hbd : |∑ i, kFast k i * ((fastPart d mu (d.g (blockFast z')) (blockSlow z) i -
        blockFast z' i) - (fastPart d mu (d.g (blockFast z)) (blockSlow z) i - blockFast z i)) +
      mu * ∑ i, kSlow k i * (slowFrequency d.Omega d.beta mu (d.g (blockFast z')) (blockSlow z) i -
        slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i)| ≤
      mu * d.LN * d.Lg * l1 k * |s| := by
    set e := (fun i => (fastPart d mu (d.g (blockFast z')) (blockSlow z) i - blockFast z' i) -
        (fastPart d mu (d.g (blockFast z)) (blockSlow z) i - blockFast z i)) with he
    set f := (fun i => slowFrequency d.Omega d.beta mu (d.g (blockFast z')) (blockSlow z) i -
        slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i) with hf
    have he1 : ‖e‖ ≤ mu * d.LN * d.Lg * |s| := by
      have := fast_dev_y d hmu hy1 hy2 hξ
      rw [hnorm] at this
      exact this
    have hf1 : ‖f‖ ≤ d.LN * d.Lg * |s| := by
      have := slow_lip_y d hmu hy2 hy1 hξ
      rw [hnorm] at *
      exact this
    have hA : |∑ i, kFast k i * e i| ≤ (∑ i, |kFast k i|) * ‖e‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm e i) (abs_nonneg _)
    have hB : |∑ i, kSlow k i * f i| ≤ (∑ i, |kSlow k i|) * ‖f‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm f i) (abs_nonneg _)
    have hp : 0 ≤ ∑ i, |kFast k i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hq : 0 ≤ ∑ i, |kSlow k i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hLN := d.hLN
    have hLg := d.hLg
    have hP : (∑ i, |kFast k i|) * ‖e‖ ≤ (∑ i, |kFast k i|) * (mu * d.LN * d.Lg * |s|) :=
      mul_le_mul_of_nonneg_left he1 hp
    have hQ : (∑ i, |kSlow k i|) * ‖f‖ ≤ (∑ i, |kSlow k i|) * (d.LN * d.Lg * |s|) :=
      mul_le_mul_of_nonneg_left hf1 hq
    have hmuB : mu * |∑ i, kSlow k i * f i| ≤ mu * ((∑ i, |kSlow k i|) * (d.LN * d.Lg * |s|)) :=
      mul_le_mul_of_nonneg_left (hB.trans hQ) hmu0.le
    calc _ ≤ |∑ i, kFast k i * e i| + |mu * ∑ i, kSlow k i * f i| := abs_add_le _ _
      _ = |∑ i, kFast k i * e i| + mu * |∑ i, kSlow k i * f i| := by rw [abs_mul, abs_of_pos hmu0]
      _ ≤ _ := by
        rw [l1_split]
        nlinarith
  have hE : mu * d.LN * d.Lg * l1 k * |s| ≤ |kFast k j| * |s| / 2 := by
    rw [hj]
    have := mul_le_mul_of_nonneg_right hkl (abs_nonneg s)
    linarith
  have hlow : |kFast k j| * |s| / 2 ≤ |pullFreq d mu k z' - pullFreq d mu k z| := by
    rw [hdiff]
    have h1 : |kFast k j * s| = |kFast k j| * |s| := abs_mul _ _
    have h2 := abs_sub_abs_le_abs_sub (kFast k j * s) (-(∑ i, kFast k i * ((fastPart d mu
      (d.g (blockFast z')) (blockSlow z) i - blockFast z' i) - (fastPart d mu
      (d.g (blockFast z)) (blockSlow z) i - blockFast z i)) + mu * ∑ i, kSlow k i *
      (slowFrequency d.Omega d.beta mu (d.g (blockFast z')) (blockSlow z) i -
        slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i)))
    rw [sub_neg_eq_add, abs_neg] at h2
    linarith
  have hup : |pullFreq d mu k z' - pullFreq d mu k z| < 2 * alpha := by
    have := abs_sub (pullFreq d mu k z') (pullFreq d mu k z)
    linarith
  have hs4 : |kFast k j| * |s| < 4 * alpha := by linarith
  have hkj : 1 ≤ |kFast k j| := by rw [hj]; exact hk1'
  have hs0 := abs_nonneg s
  have hα : 0 < alpha := lt_of_le_of_lt (abs_nonneg _) hp1
  rw [abs_sub_comm]
  nlinarith

end KAM.Planetary

end
