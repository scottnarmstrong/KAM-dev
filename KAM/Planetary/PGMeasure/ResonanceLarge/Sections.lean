/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.ResonanceLarge.Measurable
public import KAM.Planetary.PGMeasure.ResonanceLarge.LineSlice

/-!
# P Part 4: slow-coordinate sections of the large-mode resonances (`stepP:p4:dm-B`)

For a large mode `k` and a slow index `j`, `largeSection` is the part of the resonant set
`ℛ'_k` (in frequency coordinates) where `|(β(μ, g y)ᵀ k₂)_j| ≥ ‖k₂‖/L_β`. Along the line
`ξ ↦ ξ + s e_j` (with `y` and the other slow coordinates fixed, so `I = g y` is fixed) the
resonance function moves by `μ s (βᵀ k₂)_j + k₁ · (fast increment)`, which `N2` and the structure
of the large modes bound below by `μ |s| ‖k₂‖/(2 L_β)`. Hence every such line meets the section in a
set of diameter `≤ 4 L_β α/(μ ‖k₂‖)`, and Tonelli bounds the volume. Design
`docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RB.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- `stepP:p4:dm-B`: the part `ℛ_{k,j}` of `ℛ'_k` where the `j`-th slow column coefficient of
`βᵀ k₂` is at least `‖k₂‖/L_β` in modulus. -/
def largeSection (d : MeasureData a b) (mu : ℝ) (Q : Set (Fin b → ℝ)) (k : Fin (a+b) → ℤ)
    (alpha : ℝ) (j : Fin b) : Set (Fin (a+b) → ℝ) :=
  resonanceSet d mu Q k alpha ∩ {z | ‖kSlow k‖ / d.LB ≤ |colCoeff d mu (kSlow k) j z|}

theorem norm_le_of_mem_actionShell {lambda : ℝ} (hl : 0 < lambda) {xi : Fin b → ℝ}
    (hxi : xi ∈ actionShell b (-lambda) lambda) : ‖xi‖ ≤ lambda :=
  (pi_norm_le_iff_of_nonneg hl.le).mpr fun i => by
    have := hxi i (mem_univ i)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨this.1.le, this.2.le⟩

theorem measurableSet_largeSection (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {Q : Set (Fin b → ℝ)} (hQm : MeasurableSet Q) (hQ : ∀ xi ∈ Q, ‖xi‖ ≤ d.lambda0)
    (k : Fin (a+b) → ℤ) (alpha : ℝ) (j : Fin b) :
    MeasurableSet (largeSection d mu Q k alpha j) := by
  have h1 : MeasurableSet (sliceDomain d Q ∩ pullFreq d mu k ⁻¹' {x | |x| < alpha}) :=
    measurableSet_inter_preimage (measurableSet_sliceDomain d hQm) (continuousOn_pullFreq d hmu
        hQ k)
      (measurableSet_lt (by fun_prop) measurable_const)
  have h2 := measurableSet_inter_preimage h1
    ((continuousOn_colCoeff d hmu (kSlow k) j).mono fun z hz => ⟨hz.1.1, mem_univ _⟩)
    (T := {x | ‖kSlow k‖ / d.LB ≤ |x|}) (measurableSet_le measurable_const (by fun_prop))
  convert h2 using 1
  ext z
  simp only [largeSection, resonanceSet, sliceDomain, mem_inter_iff, Set.mem_preimage,
      Set.mem_ofPred_eq]
  tauto

/-- The slow increment of the frequency along `e_j`. -/
theorem slow_diff_single (d : MeasureData a b) (mu : ℝ) (I : Fin a → ℝ) (xi : Fin b → ℝ) (j : Fin b)
    (s : ℝ) (i : Fin b) :
    slowFrequency d.Omega d.beta mu I (xi + Pi.single j s) i - slowFrequency d.Omega d.beta mu
        I xi i =
      d.beta mu I i j * s := by
  simp [slowFrequency, Matrix.mulVec_add, Matrix.mulVec, dotProduct]
  ring

theorem castAdd_ne_natAdd (i : Fin a) (j : Fin b) : Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- Two points of one slow line through `ℛ_{k,j}` are within `4 L_β α/(μ ‖k₂‖)` in the `ξ_j` slot
(`stepP:p4:dm-B`). -/
theorem largeSection_line_diam (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {lambda : ℝ} (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0) {Q : Set (Fin b → ℝ)}
    (hQsub : Q ⊆ actionShell b (-lambda) lambda) {k : Fin (a+b) → ℤ}
    (hk : k ∈ largeModes a b mu d.LN d.Lg) {alpha : ℝ} (j : Fin b)
    {z z' : Fin (a+b) → ℝ} (hz : z ∈ largeSection d mu Q k alpha j)
    (hz' : z' ∈ largeSection d mu Q k alpha j)
    (hline : ∀ l, l ≠ Fin.natAdd a j → z l = z' l) :
    |z (Fin.natAdd a j) - z' (Fin.natAdd a j)| ≤
      4 * d.LB * alpha / (mu * ‖kSlow k‖) := by
  have hmu0 := hmu.1
  have hQ : ∀ xi ∈ Q, ‖xi‖ ≤ d.lambda0 := fun xi hxi =>
    (norm_le_of_mem_actionShell hl (hQsub hxi)).trans hl0
  obtain ⟨-, -, hS3, hS4⟩ := large_mode_structure d.ha d.hb hmu0 d.hLN d.hLB d.hLg
    ((hmu.2.trans d.small)) hk
  have hl1pos : 0 < l1 k := by
    have := (large_mode_structure d.ha d.hb hmu0 d.hLN d.hLB d.hLg (hmu.2.trans d.small) hk).1
    by_contra hc
    have h0 : l1 k = 0 := le_antisymm (not_lt.mp hc) (l1_nonneg k)
    rw [h0] at this; linarith
  have hkS : 0 < ‖kSlow k‖ := by
    have hbR : (0:ℝ) < b := by exact_mod_cast d.hb
    by_contra hc
    have : ‖kSlow k‖ = 0 := le_antisymm (not_lt.mp hc) (norm_nonneg _)
    rw [this] at hS3; nlinarith
  have hLB : 0 < d.LB := by linarith [d.hLB]
  -- the two points share `y`, and `ξ' = ξ + e_j s`
  have hy : blockFast z' = blockFast z := funext fun i =>
    (hline _ (castAdd_ne_natAdd i j)).symm
  set s : ℝ := z' (Fin.natAdd a j) - z (Fin.natAdd a j) with hs
  have hxi : blockSlow z' = blockSlow z + Pi.single j s := by
    funext i
    by_cases hij : i = j
    · subst hij; simp [blockSlow, hs]
    · have hne : Fin.natAdd a i ≠ Fin.natAdd a j := fun h => hij (Fin.ext (by
        have := congrArg Fin.val h
        simp at this
        omega))
      have := hline (Fin.natAdd a i) hne
      simp [blockSlow, hij, this]
  obtain ⟨⟨hy1, hQ1, hp1⟩, hc1⟩ := hz
  obtain ⟨⟨_, hQ2, hp2⟩, hc2⟩ := hz'
  obtain ⟨hIcore, -⟩ := freqCore_spec d hy1
  have hξ : ‖blockSlow z‖ ≤ d.lambda0 := hQ _ hQ1
  have hξ' : ‖blockSlow z'‖ ≤ d.lambda0 := hQ _ hQ2
  have hcol : colCoeff d mu (kSlow k) j z' = colCoeff d mu (kSlow k) j z := by
    simp only [colCoeff, hy]
  have hc2 : ‖kSlow k‖ / d.LB ≤ |colCoeff d mu (kSlow k) j z'| := hc2
  rw [hcol] at hc2
  have hdiff : pullFreq d mu k z' - pullFreq d mu k z =
      ∑ i, kFast k i * (fastPart d mu (d.g (blockFast z)) (blockSlow z') i -
        fastPart d mu (d.g (blockFast z)) (blockSlow z) i) +
      mu * (s * colCoeff d mu (kSlow k) j z) := by
    rw [pullFreq_eq, pullFreq_eq, hy]
    have hf : ∑ i, kFast k i * (fastPart d mu (d.g (blockFast z)) (blockSlow z') i -
        fastPart d mu (d.g (blockFast z)) (blockSlow z) i) =
        ∑ i, kFast k i * fastPart d mu (d.g (blockFast z)) (blockSlow z') i -
        ∑ i, kFast k i * fastPart d mu (d.g (blockFast z)) (blockSlow z) i := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    have hsl : ∑ i, kSlow k i * slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow
        z') i -
        ∑ i, kSlow k i * slowFrequency d.Omega d.beta mu (d.g (blockFast z)) (blockSlow z) i =
        s * colCoeff d mu (kSlow k) j z := by
      rw [← Finset.sum_sub_distrib, colCoeff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_sub, hxi, slow_diff_single]
      ring
    rw [hf, ← hsl]
    ring
  have hA : |∑ i, kFast k i * (fastPart d mu (d.g (blockFast z)) (blockSlow z') i -
        fastPart d mu (d.g (blockFast z)) (blockSlow z) i)| ≤
      (∑ i, |kFast k i|) * (mu * d.LN * |s|) := by
    have hN := fast_lip_xi d hmu hIcore hξ' hξ
    have hn : ‖blockSlow z' - blockSlow z‖ = |s| := by
      rw [hxi, add_sub_cancel_left, Pi.norm_single, Real.norm_eq_abs]
    rw [hn] at hN
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h := norm_le_pi_norm (fastPart d mu (d.g (blockFast z)) (blockSlow z') -
      fastPart d mu (d.g (blockFast z)) (blockSlow z)) i
    rw [Real.norm_eq_abs] at h
    exact h.trans hN
  have hD : |pullFreq d mu k z' - pullFreq d mu k z| < 2 * alpha := by
    have := abs_sub (pullFreq d mu k z') (pullFreq d mu k z)
    linarith
  have hlow : mu * |s| * (‖kSlow k‖ / (2 * d.LB)) ≤ |pullFreq d mu k z' - pullFreq d mu k z| := by
    rw [hdiff]
    have h1 : |mu * (s * colCoeff d mu (kSlow k) j z)| ≤
        |∑ i, kFast k i * (fastPart d mu (d.g (blockFast z)) (blockSlow z') i -
        fastPart d mu (d.g (blockFast z)) (blockSlow z) i) +
        mu * (s * colCoeff d mu (kSlow k) j z)| + |∑ i, kFast k i *
        (fastPart d mu (d.g (blockFast z)) (blockSlow z') i -
        fastPart d mu (d.g (blockFast z)) (blockSlow z) i)| := by
      have := abs_sub (∑ i, kFast k i * (fastPart d mu (d.g (blockFast z)) (blockSlow z') i -
        fastPart d mu (d.g (blockFast z)) (blockSlow z) i) +
        mu * (s * colCoeff d mu (kSlow k) j z)) (∑ i, kFast k i *
        (fastPart d mu (d.g (blockFast z)) (blockSlow z') i -
        fastPart d mu (d.g (blockFast z)) (blockSlow z) i))
      simpa using this
    have h2 : |mu * (s * colCoeff d mu (kSlow k) j z)| = mu * |s| * |colCoeff d mu (kSlow k) j
        z| := by
      rw [abs_mul, abs_mul, abs_of_pos hmu0]; ring
    have h3 : (∑ i, |kFast k i|) * (mu * d.LN * |s|) ≤ mu * |s| * (‖kSlow k‖ / (2 * d.LB)) := by
      have : d.LN * ∑ i, |kFast k i| ≤ ‖kSlow k‖ / (2 * d.LB) := hS4
      have hs0 : 0 ≤ mu * |s| := by positivity
      nlinarith
    have h4 : mu * |s| * (‖kSlow k‖ / d.LB) ≤ mu * |s| * |colCoeff d mu (kSlow k) j z| :=
      mul_le_mul_of_nonneg_left hc1 (by positivity)
    have h5 : ‖kSlow k‖ / (2 * d.LB) = ‖kSlow k‖ / d.LB - ‖kSlow k‖ / (2 * d.LB) := by
      field_simp; ring
    have h6 : mu * |s| * (‖kSlow k‖ / (2 * d.LB)) =
        mu * |s| * (‖kSlow k‖ / d.LB) - mu * |s| * (‖kSlow k‖ / (2 * d.LB)) := by
      rw [← mul_sub, ← h5]
    linarith
  have hfin : mu * |s| * ‖kSlow k‖ < 4 * d.LB * alpha := by
    have : mu * |s| * (‖kSlow k‖ / (2 * d.LB)) < 2 * alpha := hlow.trans_lt hD
    have h7 : mu * |s| * (‖kSlow k‖ / (2 * d.LB)) * (2 * d.LB) = mu * |s| * ‖kSlow k‖ := by
      field_simp
    nlinarith
  rw [abs_sub_comm, le_div_iff₀ (by positivity)]
  nlinarith

/-- The box radii: `R_y` on the fast coordinates, `λ` on the slow ones. -/
def boxRadius (a b : ℕ) (Ry lambda : ℝ) : Fin (a+b) → ℝ :=
  Fin.append (fun _ : Fin a => Ry) (fun _ : Fin b => lambda)

theorem prod_erase_boxRadius {Ry lambda : ℝ} (hl : 0 < lambda) (j : Fin b) :
    ∏ l ∈ Finset.univ.erase (Fin.natAdd a j), 2 * boxRadius a b Ry lambda l =
      (2 * Ry) ^ a * (2 * lambda) ^ (b - 1) := by
  have hall : ∏ l, 2 * boxRadius a b Ry lambda l = (2 * Ry) ^ a * (2 * lambda) ^ b := by
    rw [Fin.prod_univ_add]
    simp [boxRadius]
  have h := Finset.mul_prod_erase Finset.univ (fun l => 2 * boxRadius a b Ry lambda l)
    (Finset.mem_univ (Fin.natAdd a j))
  have hj : 2 * boxRadius a b Ry lambda (Fin.natAdd a j) = 2 * lambda := by simp [boxRadius]
  rw [hj, hall] at h
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by have := j.pos; omega⟩
  simp only [pow_succ, Nat.add_sub_cancel] at h ⊢
  have h2 : (2 * lambda) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2
  linarith

/-- Volume of one slow section `ℛ_{k,j}` (`stepP:p4:dm-B`). -/
theorem volume_largeSection_le (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {lambda : ℝ} (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0) {Q : Set (Fin b → ℝ)}
    (hQm : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda)
    {k : Fin (a+b) → ℤ} (hk : k ∈ largeModes a b mu d.LN d.Lg) {alpha : ℝ} (ha : 0 < alpha)
    (j : Fin b) :
    volume (largeSection d mu Q k alpha j) ≤
      ENNReal.ofReal (4 * d.LB * alpha / (mu * ‖kSlow k‖) *
        ((2 * d.Ry) ^ a * (2 * lambda) ^ (b - 1))) := by
  have hmu0 := hmu.1
  have hQ : ∀ xi ∈ Q, ‖xi‖ ≤ d.lambda0 := fun xi hxi =>
    (norm_le_of_mem_actionShell hl (hQsub hxi)).trans hl0
  have hkS : 0 < ‖kSlow k‖ := by
    obtain ⟨-, -, hS3, -⟩ := large_mode_structure d.ha d.hb hmu0 d.hLN d.hLB d.hLg
      (hmu.2.trans d.small) hk
    have hbR : (0:ℝ) < b := by exact_mod_cast d.hb
    have h1 := (large_mode_structure d.ha d.hb hmu0 d.hLN d.hLB d.hLg (hmu.2.trans d.small) hk).1
    by_contra hc
    have h0 : ‖kSlow k‖ = 0 := le_antisymm (not_lt.mp hc) (norm_nonneg _)
    rw [h0] at hS3
    have := l1_nonneg k
    nlinarith
  have hRy : 0 ≤ d.Ry := d.hRy.le
  have hrho : ∀ l, 0 ≤ boxRadius a b d.Ry lambda l := fun l => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [boxRadius, hRy, hl.le]
  have hbox : ∀ z ∈ largeSection d mu Q k alpha j, ∀ l, |z l| ≤ boxRadius a b d.Ry lambda l := by
    intro z hz l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l
    · simp only [boxRadius, Fin.append_left]
      have h1 := norm_le_Ry_of_mem_freqCore d hz.1.1
      have h2 := norm_le_pi_norm (blockFast z) i
      rw [Real.norm_eq_abs] at h2
      exact h2.trans h1
    · simp only [boxRadius, Fin.append_right]
      have h1 := norm_le_of_mem_actionShell hl (hQsub hz.1.2.1)
      have h2 := norm_le_pi_norm (blockSlow z) i
      rw [Real.norm_eq_abs] at h2
      exact h2.trans h1
  have hδ : 0 ≤ 4 * d.LB * alpha / (mu * ‖kSlow k‖) := by
    have := d.hLB; positivity
  have key := volume_le_of_line_diam (Fin.natAdd a j) _ hrho
    (measurableSet_largeSection d hmu hQm hQ k alpha j) hbox hδ
    (fun z hz z' hz' hl' => largeSection_line_diam d hmu hl hl0 hQsub hk j hz hz'
      (fun l hl'' => hl' l hl''))
  rw [prod_erase_boxRadius hl j, ← ENNReal.ofReal_mul hδ] at key
  exact key

end KAM.Planetary

end
