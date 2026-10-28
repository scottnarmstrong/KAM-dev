/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.LatticeTail
public import KAM.Planetary.PGMeasure.ResonanceFast.Pullback
public import KAM.Planetary.PGMeasure.ResonanceFast.Sections
public import KAM.Planetary.PGMeasure.ResonanceLarge.LineSlice
public import KAM.Planetary.PGMeasure.ResonanceLarge.Measurable

/-!
# P Part 4: the fast-dominant resonances `ℛ^(A)` (`stepP:p4:dm-y`, `stepP:p4:dm-A`)

Internal helpers for `two_scale_diophantine_measure` (consumed by P4-M). Design
`docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RA.

* `pullMap`, `volume_pullMap_image_le`, `mem_pullMap_image_of_resonant` (`stepP:p4:dm-y`): the
  change to frequency coordinates, with the Lipschitz-image factor `Λ_g^(a+b)`.
* `fastSection_line_diam`, `volume_resonanceSet_fast_le` (`stepP:p4:dm-A`): slicing in `y_j`.
* `fast_modes_measure_le` (`stepP:p4:dm-A`, final display; Lemma `lattice-tail`(a)): the union of
  the frequency-coordinate resonant sets `ℛ'_k`, `k ∈ 𝒦_A`, has measure at most
  `4 (2R_y)^(a-1) S₁ α₁ (2λ)^b`; the factors `Λ_g^n` and `1/vol core` of `c₁` are applied by P4-M.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

theorem measurableSet_resonanceSet (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {Q : Set (Fin b → ℝ)} (hQm : MeasurableSet Q) (hQ : ∀ xi ∈ Q, ‖xi‖ ≤ d.lambda0)
    (k : Fin (a+b) → ℤ) (alpha : ℝ) : MeasurableSet (resonanceSet d mu Q k alpha) := by
  have h1 : MeasurableSet (sliceDomain d Q ∩ pullFreq d mu k ⁻¹' {x | |x| < alpha}) :=
    measurableSet_inter_preimage (measurableSet_sliceDomain d hQm) (continuousOn_pullFreq d hmu
        hQ k)
      (measurableSet_lt (by fun_prop) measurable_const)
  convert h1 using 1
  ext z
  simp only [resonanceSet, sliceDomain, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  tauto

theorem prod_erase_box (d : MeasureData a b) (lambda : ℝ)
    (i : Fin (a+b)) (hi : ∃ j : Fin a, i = Fin.castAdd b j) :
    ∏ l ∈ Finset.univ.erase i, 2 * (Fin.append (fun _ : Fin a => d.Ry) (fun _ : Fin b => lambda)
      l) = (2 * d.Ry) ^ (a - 1) * (2 * lambda) ^ b := by
  obtain ⟨j, rfl⟩ := hi
  have hRy := d.hRy
  have h := Finset.mul_prod_erase Finset.univ (fun l => 2 * (Fin.append (fun _ : Fin a => d.Ry)
    (fun _ : Fin b => lambda) l)) (Finset.mem_univ (Fin.castAdd b j))
  rw [Fin.prod_univ_add] at h
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at h
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := j.pos; omega⟩
  rw [Nat.add_sub_cancel]
  rw [pow_succ] at h
  have h2 : 2 * d.Ry * ∏ l ∈ Finset.univ.erase (Fin.castAdd b j), 2 * (Fin.append
      (fun _ : Fin (a' + 1) => d.Ry) (fun _ : Fin b => lambda) l) =
      2 * d.Ry * ((2 * d.Ry) ^ a' * (2 * lambda) ^ b) := by
    rw [h]; ring
  exact mul_left_cancel₀ (by positivity) h2

/-- `stepP:p4:dm-A`, per mode: `μ(ℛ'_k) ≤ 4 α (2R_y)^(a-1) (2λ)^b` for `k ∈ 𝒦_A`. -/
theorem volume_resonanceSet_fast_le (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {lambda : ℝ} (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0) {Q : Set (Fin b → ℝ)}
    (hQm : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda)
    {k : Fin (a+b) → ℤ} (hk : k ∈ fastModes a b mu d.LN d.Lg) {alpha : ℝ} (ha : 0 < alpha) :
    volume (resonanceSet d mu Q k alpha) ≤
      ENNReal.ofReal (4 * alpha * ((2 * d.Ry) ^ (a - 1) * (2 * lambda) ^ b)) := by
  have hQ : ∀ xi ∈ Q, ‖xi‖ ≤ d.lambda0 := fun xi hxi =>
    (norm_le_of_mem_actionShell hl (hQsub hxi)).trans hl0
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => |kFast k j|)
    ⟨⟨0, d.ha⟩, Finset.mem_univ _⟩
  have hjn : |kFast k j| = ‖kFast k‖ := by
    refine le_antisymm (by simpa using norm_le_pi_norm (kFast k) j) ?_
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_
    simpa using hj i (Finset.mem_univ _)
  have hRy := d.hRy
  set rho : Fin (a+b) → ℝ := Fin.append (fun _ : Fin a => d.Ry) (fun _ : Fin b => lambda) with hrho
  have hrho0 : ∀ l, 0 ≤ rho l := fun l => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [hrho, hl.le, hRy.le]
  have hbox : ∀ z ∈ resonanceSet d mu Q k alpha, ∀ l, |z l| ≤ rho l := by
    intro z hz l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l
    · have := (norm_le_pi_norm (blockFast z) i).trans
        ((norm_le_Ry_of_mem_freqCore d hz.1))
      simpa [hrho, blockFast] using this
    · have := (norm_le_pi_norm (blockSlow z) i).trans
        (norm_le_of_mem_actionShell hl (hQsub hz.2.1))
      simpa [hrho, blockSlow] using this
  have h := volume_le_of_line_diam (Fin.castAdd b j) rho hrho0
    (measurableSet_resonanceSet d hmu hQm hQ k alpha) hbox (delta := 4 * alpha) (by linarith)
    (fun z hz z' hz' hline => fastSection_line_diam d hmu hl hl0 hQsub hk hjn hz hz' hline)
  rw [← ENNReal.ofReal_mul (by linarith)] at h
  have hp : ∏ l ∈ Finset.univ.erase (Fin.castAdd b j), 2 * rho l =
      (2 * d.Ry) ^ (a - 1) * (2 * lambda) ^ b := prod_erase_box d lambda _ ⟨j, rfl⟩
  rwa [hp] at h

theorem latticeWeight_eq_inv (k : Fin (a+b) → ℤ) (tau : ℝ) :
    latticeWeight tau k = (l1 k ^ tau)⁻¹ := by
  unfold latticeWeight
  exact Real.rpow_neg (l1_nonneg k) tau

/-- `stepP:p4:dm-A` and Lemma `lattice-tail`(a): the union over the fast-dominant modes of the
frequency-coordinate resonant sets (without the factors `Λ_g^n` and `1/vol core` of `c₁`). -/
theorem fast_modes_measure_le (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {lambda : ℝ} (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0) {Q : Set (Fin b → ℝ)}
    (hQm : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda)
    {alpha1 : ℝ} (ha : 0 < alpha1) :
    volume (⋃ k ∈ fastModes a b mu d.LN d.Lg, resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau)) ≤
      ENNReal.ofReal (4 * (2 * d.Ry) ^ (a - 1) * latticeS (a + b) d.tau * alpha1 *
        (2 * lambda) ^ b) := by
  have hn : 0 < a + b := by have := d.ha; omega
  obtain ⟨hsumm, htsum, -⟩ := lattice_tail hn d.htau
  set c : ℝ := 4 * alpha1 * ((2 * d.Ry) ^ (a - 1) * (2 * lambda) ^ b) with hc
  have hRy := d.hRy
  have hc0 : 0 ≤ c := by positivity
  have hne : ∀ k ∈ fastModes a b mu d.LN d.Lg, k ≠ 0 := by
    rintro k ⟨hk, -⟩ rfl
    exact hk rfl
  have hcover : (⋃ k ∈ fastModes a b mu d.LN d.Lg,
      resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau)) ⊆
      ⋃ k : {k : Fin (a+b) → ℤ // k ≠ 0}, ⋃ (_ : k.1 ∈ fastModes a b mu d.LN d.Lg),
        resonanceSet d mu Q k.1 (alpha1 / l1 k.1 ^ d.tau) := by
    intro z hz
    simp only [mem_iUnion] at hz ⊢
    obtain ⟨k, hk, hz⟩ := hz
    exact ⟨⟨k, hne k hk⟩, hk, hz⟩
  refine (measure_mono hcover).trans ((measure_iUnion_le _).trans ?_)
  have hterm : ∀ k : {k : Fin (a+b) → ℤ // k ≠ 0},
      volume (⋃ (_ : k.1 ∈ fastModes a b mu d.LN d.Lg),
        resonanceSet d mu Q k.1 (alpha1 / l1 k.1 ^ d.tau)) ≤
      ENNReal.ofReal (c * latticeWeight d.tau k.1) := by
    intro k
    by_cases hk : k.1 ∈ fastModes a b mu d.LN d.Lg
    · have hl1 : 0 < l1 k.1 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hk.1
        have h1 : (1 : ℝ) ≤ |(k.1 (Fin.castAdd b i) : ℝ)| := by
          have : (1 : ℤ) ≤ |k.1 (Fin.castAdd b i)| := Int.one_le_abs hi
          exact_mod_cast this
        exact lt_of_lt_of_le one_pos (h1.trans (Finset.single_le_sum
          (f := fun i => |(k.1 i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)))
      have hpos : 0 < alpha1 / l1 k.1 ^ d.tau := by positivity
      have := volume_resonanceSet_fast_le d hmu hl hl0 hQm hQsub hk hpos
      simp only [hk, iUnion_true]
      refine this.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hc, latticeWeight_eq_inv, div_eq_mul_inv]
      ring
    · simp [hk]
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hw : ∀ k : {k : Fin (a+b) → ℤ // k ≠ 0}, 0 ≤ latticeWeight d.tau k.1 :=
    fun k => Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hc0 (hw k)) (hsumm.mul_left c),
    tsum_mul_left]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (mul_le_mul_of_nonneg_left htsum hc0).trans (le_of_eq ?_)
  rw [hc]
  unfold latticeS
  ring

end KAM.Planetary

end
