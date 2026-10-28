/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.Setting
public import KAM.Planetary.PGMeasure.ResonanceLarge.Structure

/-!
# P Part 4: the frequency-coordinate resonance function (`stepP:p4:dm-y`)

In coordinates `z = (y, ξ)` with `y = fastFrequency H₀ I` the resonance function of a mode `k` is
`pullFreq d μ k z = k · freq (g y, ξ)`; `resonanceSet` is the part of `ω(core) × Q` where it is
smaller than a threshold. This file fixes the carriers and the decomposition of `pullFreq` into its
fast and slow parts, using only the literal premises `N1`, `N2`, `N3` and `hRybound` of
`MeasureData`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RB.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Finset

namespace KAM.Planetary

variable {a b : ℕ}

/-- The image of the core under the fast frequency map. -/
def freqCore (d : MeasureData a b) : Set (Fin a → ℝ) := fastFrequency d.H0 '' d.core

/-- The fast block of the frequency map at `(I, ξ)`. -/
def fastPart (d : MeasureData a b) (mu : ℝ) (I : Fin a → ℝ) (xi : Fin b → ℝ) : Fin a → ℝ :=
  blockFast (freq d.H0 d.P0 d.Omega d.beta mu (Fin.append I xi))

/-- The resonance function `k · freq (g y, ξ)` at the flat point `z = (y, ξ)`. -/
def pullFreq (d : MeasureData a b) (mu : ℝ) (k : Fin (a+b) → ℤ) (z : Fin (a+b) → ℝ) : ℝ :=
  ∑ i, (k i : ℝ) *
    freq d.H0 d.P0 d.Omega d.beta mu (Fin.append (d.g (blockFast z)) (blockSlow z)) i

/-- The resonant part of `ω(core) × Q` for the mode `k` and threshold `alpha`. -/
def resonanceSet (d : MeasureData a b) (mu : ℝ) (Q : Set (Fin b → ℝ)) (k : Fin (a+b) → ℤ)
    (alpha : ℝ) : Set (Fin (a+b) → ℝ) :=
  {z | blockFast z ∈ freqCore d ∧ blockSlow z ∈ Q ∧ |pullFreq d mu k z| < alpha}

theorem blockFast_append (I : Fin a → ℝ) (xi : Fin b → ℝ) : blockFast (Fin.append I xi) = I :=
  funext fun i => Fin.append_left I xi i

theorem blockSlow_append (I : Fin a → ℝ) (xi : Fin b → ℝ) : blockSlow (Fin.append I xi) = xi :=
  funext fun i => Fin.append_right I xi i

theorem pullFreq_eq (d : MeasureData a b) (mu : ℝ) (k : Fin (a+b) → ℤ) (z : Fin (a+b) → ℝ) :
    pullFreq d mu k z =
      ∑ i, kFast k i * fastPart d mu (d.g (blockFast z)) (blockSlow z) i +
      mu * ∑ i, kSlow k i *
        slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i := by
  unfold pullFreq
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  all_goals
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [kSlow, freq, blockFast_append, blockSlow_append]
    try ring

/-- Points of the frequency image of the core come from core actions. -/
theorem freqCore_spec (d : MeasureData a b) {y : Fin a → ℝ} (hy : y ∈ freqCore d) :
    d.g y ∈ d.core ∧ fastFrequency d.H0 (d.g y) = y := by
  obtain ⟨I, hI, rfl⟩ := hy
  have hW : I ∈ d.W := d.hVW (subset_closure (d.hcoreV hI))
  rw [d.hinv I hW]
  exact ⟨hI, rfl⟩

theorem norm_le_Ry_of_mem_freqCore (d : MeasureData a b) {y : Fin a → ℝ} (hy : y ∈ freqCore d) :
    ‖y‖ ≤ d.Ry := by
  obtain ⟨I, hI, rfl⟩ := hy
  exact d.hRybound _ ⟨I, subset_closure (d.hcoreV hI), rfl⟩

/-! ### Lipschitz estimates in frequency coordinates -/

theorem norm_blockFast_le (w : Fin (a+b) → ℝ) : ‖blockFast w‖ ≤ ‖w‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun i => norm_le_pi_norm w (Fin.castAdd b i)

theorem norm_blockSlow_le (w : Fin (a+b) → ℝ) : ‖blockSlow w‖ ≤ ‖w‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun i => norm_le_pi_norm w (Fin.natAdd a i)

theorem dist_g_le (d : MeasureData a b) {y y' : Fin a → ℝ} (hy : y ∈ freqCore d)
    (hy' : y' ∈ freqCore d) : ‖d.g y - d.g y'‖ ≤ d.Lg * ‖y - y'‖ := by
  obtain ⟨I, hI, rfl⟩ := hy
  obtain ⟨I', hI', rfl⟩ := hy'
  exact d.hglip _ ⟨I, subset_closure (d.hcoreV hI), rfl⟩ _ ⟨I', subset_closure (d.hcoreV hI'), rfl⟩

theorem continuousOn_g (d : MeasureData a b) : ContinuousOn d.g (freqCore d) :=
  (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal d.Lg) fun y hy y' hy' => by
    rw [Real.coe_toNNReal _ (by linarith [d.hLg])]
    simpa [dist_eq_norm] using dist_g_le d hy hy').continuousOn

theorem fast_lip_y (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1) {y y' : Fin a → ℝ}
    (hy : y ∈ freqCore d) (hy' : y' ∈ freqCore d) {xi : Fin b → ℝ} (hxi : ‖xi‖ ≤ d.lambda0) :
    ‖fastPart d mu (d.g y) xi - fastPart d mu (d.g y') xi‖ ≤ (1 + mu * d.LN * d.Lg) * ‖y - y'‖ := by
  obtain ⟨c1, c2⟩ := freqCore_spec d hy
  obtain ⟨c1', c2'⟩ := freqCore_spec d hy'
  have h1 := (d.N1 mu hmu _ c1 _ c1' xi hxi).1
  have h2 := dist_g_le d hy hy'
  have hmu0 := hmu.1
  unfold fastPart
  rw [c2, c2'] at h1
  calc _ = ‖(blockFast (freq d.H0 d.P0 d.Omega d.beta mu (Fin.append (d.g y) xi)) - y -
          (blockFast (freq d.H0 d.P0 d.Omega d.beta mu (Fin.append (d.g y') xi)) - y')) +
          (y - y')‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (by
        have : mu * d.LN * ‖d.g y - d.g y'‖ ≤ mu * d.LN * (d.Lg * ‖y - y'‖) :=
          mul_le_mul_of_nonneg_left h2 (by nlinarith [d.hLN])
        nlinarith)

theorem fast_lip_xi (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1) {I : Fin a → ℝ}
    (hI : I ∈ d.core) {xi xi' : Fin b → ℝ} (hxi : ‖xi‖ ≤ d.lambda0) (hxi' : ‖xi'‖ ≤ d.lambda0) :
    ‖fastPart d mu I xi - fastPart d mu I xi'‖ ≤ mu * d.LN * ‖xi - xi'‖ :=
  d.N2 mu hmu I hI xi xi' hxi hxi'

theorem slow_lip_y (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1) {y y' : Fin a → ℝ}
    (hy : y ∈ freqCore d) (hy' : y' ∈ freqCore d) {xi : Fin b → ℝ} (hxi : ‖xi‖ ≤ d.lambda0) :
    ‖slowFrequency d.Omega d.beta mu (d.g y) xi - slowFrequency d.Omega d.beta mu (d.g y') xi‖ ≤
      d.LN * d.Lg * ‖y - y'‖ := by
  obtain ⟨c1, -⟩ := freqCore_spec d hy
  obtain ⟨c1', -⟩ := freqCore_spec d hy'
  refine (d.N1 mu hmu _ c1 _ c1' xi hxi).2.trans ?_
  calc d.LN * ‖d.g y - d.g y'‖ ≤ d.LN * (d.Lg * ‖y - y'‖) :=
        mul_le_mul_of_nonneg_left (dist_g_le d hy hy') (by linarith [d.hLN])
    _ = _ := by ring

theorem beta_entry (d : MeasureData a b) (mu : ℝ) (I : Fin a → ℝ) (i j : Fin b) :
    d.beta mu I i j * d.lambda0 =
      slowFrequency d.Omega d.beta mu I (Pi.single j d.lambda0) i -
        slowFrequency d.Omega d.beta mu I 0 i := by
  simp [slowFrequency]
  ring

theorem beta_lip_y (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1) {y y' : Fin a → ℝ}
    (hy : y ∈ freqCore d) (hy' : y' ∈ freqCore d) (i j : Fin b) :
    |d.beta mu (d.g y) i j - d.beta mu (d.g y') i j| ≤
      (2 * d.LN * d.Lg / d.lambda0) * ‖y - y'‖ := by
  have hl := d.hlambda0
  have hn : ‖(Pi.single j d.lambda0 : Fin b → ℝ)‖ ≤ d.lambda0 := by
    rw [Pi.norm_single, Real.norm_eq_abs, abs_of_pos hl]
  have hn0 : ‖(0 : Fin b → ℝ)‖ ≤ d.lambda0 := by simpa using hl.le
  have e1 := (norm_le_pi_norm (slowFrequency d.Omega d.beta mu (d.g y) (Pi.single j d.lambda0) -
    slowFrequency d.Omega d.beta mu (d.g y') (Pi.single j d.lambda0)) i).trans
    (slow_lip_y d hmu hy hy' hn)
  have e2 := (norm_le_pi_norm (slowFrequency d.Omega d.beta mu (d.g y) 0 -
    slowFrequency d.Omega d.beta mu (d.g y') 0) i).trans (slow_lip_y d hmu hy hy' hn0)
  rw [Real.norm_eq_abs, Pi.sub_apply] at e1 e2
  have key : (d.beta mu (d.g y) i j - d.beta mu (d.g y') i j) * d.lambda0 =
      (slowFrequency d.Omega d.beta mu (d.g y) (Pi.single j d.lambda0) i -
        slowFrequency d.Omega d.beta mu (d.g y') (Pi.single j d.lambda0) i) -
      (slowFrequency d.Omega d.beta mu (d.g y) 0 i - slowFrequency d.Omega d.beta mu (d.g y') 0 i) := by
    rw [sub_mul, beta_entry, beta_entry]; ring
  have h3 : |d.beta mu (d.g y) i j - d.beta mu (d.g y') i j| * d.lambda0 ≤
      2 * d.LN * d.Lg * ‖y - y'‖ := by
    have h4 : |d.beta mu (d.g y) i j - d.beta mu (d.g y') i j| * d.lambda0 =
        |(d.beta mu (d.g y) i j - d.beta mu (d.g y') i j) * d.lambda0| := by
      rw [abs_mul, abs_of_pos hl]
    rw [h4, key]
    refine (abs_sub _ _).trans ?_
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hl]
  exact h3

end KAM.Planetary

end
