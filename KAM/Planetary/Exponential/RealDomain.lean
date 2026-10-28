/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Planetary.AMD.Elements
public import KAM.Planetary.Exponential.Dictionary
public import KAM.Planetary.Exponential.Setting

/-!
# P14 package E3: the real domain is collision free

Blueprint P, Part 14 (`bpP:p14:real-domain`).  For enlargement data `EnlargedData B kappa e A`, the
enlarged cylinder lies in the collision-free part of the Poincaré chart domain, the physical
point has eccentricity `< e`, every body is at distance `≥ d/2` from the origin, and every two
distinct bodies are at distance `≥ d/2` (both index orders).  The last source inclusion, that the
original cylinder lies in the enlarged one, is `original_cylinder_subset`.
-/

@[expose] public noncomputable section

open Set KAM.Kepler

namespace KAM.Planetary

variable {n : ℕ}

/-- Action window and slow bound of a point of the enlarged cylinder. -/
private theorem rd_action_data (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {w : Phase (n + n)} (hw : w ∈ enlargedCylinder B kappa A)
    (i : Fin n) :
    0 < fast w.2 i ∧ B.lower i - 2 * kappa ≤ fast w.2 i ∧ fast w.2 i ≤ B.upper i + 2 * kappa ∧
      ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2 < fast w.2 i * (1 - Real.sqrt (1 - e ^ 2)) := by
  obtain ⟨hwa, hwA⟩ := hw
  obtain ⟨hlo, hup⟩ := hwa i
  have hl : 0 < B.lower i := (hB.1 i).2.1
  have hk := hd.small i
  have hkp := hd.kappa_pos
  have hpos : 0 < fast w.2 i := by linarith
  refine ⟨hpos, hlo, hup, ?_⟩
  have h1 : ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2 ≤ chartAMD w :=
    Finset.single_le_sum (f := fun j => ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hs : Real.sqrt (1 - e ^ 2) ≤ 1 :=
    Real.sqrt_le_one.2 (by nlinarith [sq_nonneg e])
  have h2 := hd.deficit i
  have h3 : (B.lower i - 2 * kappa) * (1 - Real.sqrt (1 - e ^ 2)) ≤
      fast w.2 i * (1 - Real.sqrt (1 - e ^ 2)) :=
    mul_le_mul_of_nonneg_right hlo (by linarith)
  linarith

private theorem rd_mem_dom (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {w : Phase (n + n)} (hw : w ∈ enlargedCylinder B kappa A) :
    w ∈ poincareProdDom n := by
  intro i
  obtain ⟨h0, -, -, h3⟩ := rd_action_data B hB hd hw i
  have hs := Real.sqrt_nonneg (1 - e ^ 2)
  refine ⟨by simpa [planetBlock] using h0, ?_⟩
  simp only [poincareGamma, planetBlock]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

/-- The physical eccentricity bound and the radial window at one body. -/
private theorem rd_body (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) {w : Phase (n + n)} (hw : w ∈ enlargedCylinder B kappa A)
    (i : Fin n) :
    planeLength (keplerEccVector B.mass (poincareProd B.mass 1 w) i) < e ∧
    ((B.lower i - 2 * kappa) / B.mass i) ^ 2 * (1 - e) ≤
      planeLength (bodyVector (poincareProd B.mass 1 w).1 i) ∧
    planeLength (bodyVector (poincareProd B.mass 1 w).1 i) ≤
      ((B.upper i + 2 * kappa) / B.mass i) ^ 2 * (1 + e) := by
  have hm : ∀ j, 0 < B.mass j := fun j => (hB.1 j).1
  have hdom := rd_mem_dom B hB hd hw
  obtain ⟨hpro, hfacts, -⟩ := sec_domain_chart_facts hm hdom
  obtain ⟨hact, hax, hcr⟩ := hfacts i
  obtain ⟨h0, hlo, hup, hG⟩ := rd_action_data B hB hd hw i
  obtain ⟨-, -, -, -, hecc2, -, -, -, hlow, hhigh, -⟩ := elements i (hpro i)
  have he0 : 0 < e := lt_trans hB.2.1 hd.ecc_lt
  have he1 := hd.ecc_one
  have hs0 : 0 ≤ Real.sqrt (1 - e ^ 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 - e ^ 2) ^ 2 = 1 - e ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hecc : planeLength (keplerEccVector B.mass (poincareProd B.mass 1 w) i) < e := by
    have hne := planeLength_nonneg (keplerEccVector B.mass (poincareProd B.mass 1 w) i)
    rw [hact, hcr] at hecc2
    have hc : fast w.2 i * Real.sqrt (1 - e ^ 2) <
        fast w.2 i - ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2 := by linarith
    have hc2 : (fast w.2 i * Real.sqrt (1 - e ^ 2)) ^ 2 <
        (fast w.2 i - ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2) ^ 2 :=
      pow_lt_pow_left₀ hc (by positivity) (by norm_num)
    have hq : planeLength (keplerEccVector B.mass (poincareProd B.mass 1 w) i) ^ 2 < e ^ 2 := by
      rw [hecc2, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add']
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    by_contra hcon
    have hcon := not_lt.1 hcon
    nlinarith
  have hmi := hm i
  have hne := planeLength_nonneg (keplerEccVector B.mass (poincareProd B.mass 1 w) i)
  have haxis : keplerAxis B.mass (poincareProd B.mass 1 w) i = (fast w.2 i / B.mass i) ^ 2 := by
    rw [hax, div_pow]
  have hlo' : 0 ≤ (B.lower i - 2 * kappa) / B.mass i := by
    have := (hB.1 i).2.1; have := hd.small i; have := hd.kappa_pos
    exact div_nonneg (by linarith) hmi.le
  have hq : 0 ≤ fast w.2 i / B.mass i := by positivity
  refine ⟨hecc, ?_, ?_⟩
  · have h1 : ((B.lower i - 2 * kappa) / B.mass i) ^ 2 ≤ (fast w.2 i / B.mass i) ^ 2 :=
      pow_le_pow_left₀ hlo' (div_le_div_of_nonneg_right hlo hmi.le) 2
    rw [haxis] at hlow
    have h2 : 0 ≤ (fast w.2 i / B.mass i) ^ 2 := sq_nonneg _
    nlinarith
  · have h1 : (fast w.2 i / B.mass i) ^ 2 ≤ ((B.upper i + 2 * kappa) / B.mass i) ^ 2 :=
      pow_le_pow_left₀ hq (div_le_div_of_nonneg_right hup hmi.le) 2
    rw [haxis] at hhigh
    have h2 : 0 ≤ (fast w.2 i / B.mass i) ^ 2 := sq_nonneg _
    nlinarith

theorem real_domain (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) :
    enlargedCylinder B kappa A ⊆ chartSafe B.mass ∧
    ∀ w ∈ enlargedCylinder B kappa A,
      (∀ i,
        planeLength (keplerEccVector B.mass (poincareProd B.mass 1 w) i) < e ∧
        B.distance / 2 ≤ planeLength (bodyVector (poincareProd B.mass 1 w).1 i)) ∧
      ∀ i j, i ≠ j → B.distance / 2 ≤
        planeLength (bodyVector (poincareProd B.mass 1 w).1 i -
          bodyVector (poincareProd B.mass 1 w).1 j) := by
  have hdist : 0 < B.distance := hB.2.2.2.2.2.2.1
  have hsep : ∀ w ∈ enlargedCylinder B kappa A, ∀ i j, i < j → B.distance / 2 ≤
      planeLength (bodyVector (poincareProd B.mass 1 w).1 i -
        bodyVector (poincareProd B.mass 1 w).1 j) := by
    intro w hw i j hij
    obtain ⟨-, -, hiu⟩ := rd_body B hB hd hw i
    obtain ⟨-, hjl, -⟩ := rd_body B hB hd hw j
    have h1 := abs_planeLength_sub_le (bodyVector (poincareProd B.mass 1 w).1 j)
      (bodyVector (poincareProd B.mass 1 w).1 i)
    rw [planeLength_sub_comm] at h1
    have h2 := hd.gaps i j hij
    have h3 := neg_abs_le (planeLength (bodyVector (poincareProd B.mass 1 w).1 j) -
      planeLength (bodyVector (poincareProd B.mass 1 w).1 i))
    have h4 := le_abs_self (planeLength (bodyVector (poincareProd B.mass 1 w).1 j) -
      planeLength (bodyVector (poincareProd B.mass 1 w).1 i))
    linarith
  have hrad : ∀ w ∈ enlargedCylinder B kappa A, ∀ i, B.distance / 2 ≤
      planeLength (bodyVector (poincareProd B.mass 1 w).1 i) := fun w hw i =>
    le_trans (hd.radii i) (rd_body B hB hd hw i).2.1
  have hsep' : ∀ w ∈ enlargedCylinder B kappa A, ∀ i j, i ≠ j → B.distance / 2 ≤
      planeLength (bodyVector (poincareProd B.mass 1 w).1 i -
        bodyVector (poincareProd B.mass 1 w).1 j) := by
    intro w hw i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hsep w hw i j h
    · rw [planeLength_sub_comm]; exact hsep w hw j i h
  refine ⟨fun w hw => ⟨rd_mem_dom B hB hd hw, ⟨?_, ?_⟩⟩, fun w hw => ⟨fun i =>
    ⟨(rd_body B hB hd hw i).1, hrad w hw i⟩, hsep' w hw⟩⟩
  · exact fun i => lt_of_lt_of_le (by positivity) (hrad w hw i)
  · intro i j hij
    exact lt_of_lt_of_le (by positivity) (hsep' w hw i j hij)

theorem original_cylinder_subset (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) :
    {w : Phase (n+n) | (∀ i, B.lower i ≤ fast w.2 i ∧ fast w.2 i ≤ B.upper i) ∧
      chartAMD w ≤ B.outerAMD} ⊆ enlargedCylinder B kappa A := by
  intro w ⟨h1, h2⟩
  have hk := hd.kappa_pos
  refine ⟨fun i => ⟨by linarith [(h1 i).1], by linarith [(h1 i).2]⟩, ?_⟩
  linarith [hd.amd_lt]

end KAM.Planetary

end
