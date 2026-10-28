/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries
public import KAM.Planetary.PlanarTorsion.Asymptotics.Homogeneity
public import KAM.Planetary.PlanarTorsion.Asymptotics.Relative
public import KAM.Planetary.PlanarTorsion.Asymptotics.Limits
public import KAM.Planetary.PlanarTorsion.Asymptotics.Normalize

/-!
# Planar quartic torsion: asymptotics of `beta` (P11C, package T19)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, steps `as-in`, `as-pi`, `as-c`, `as-ent`,
`as-det`): `asymptotics` (the three entry limits and the determinant limit `-117/16`, each with
relative error `O(α ^ 2)`, and homogeneity of degree `-2`), `asymptotics_uniform_ratio` (constants
depending on the mass ratio only) and `asymptotics_general_axes` (the determinant limit at general
axes `a`, with `α = a₀ / a₁`).

The entry limits come from `as_ent` (`AsymptoticEntries`), the determinant from `Limits`, the
homogeneity and the normalisation of the physical scales from `Homogeneity` and `Normalize`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function Filter Asymptotics
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler

theorem asymptotics (p : PlanarData) (hp : p.Valid) :
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 0 0) (fun a => 3 * p.m 1 / (4 * p.m0 * p.m 0) * a) ∧
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 0 1) (fun a => -9 / (4 * p.m0) * a ^ (3 / 2 : ℝ)) ∧
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 1 1) (fun a => -3 * p.m 0 / (p.m0 * p.m 1) * a ^ 2) ∧
    p11c_relativeError (fun a => (p11c_beta p ![a, 1]).det) (fun a => -117 / (16 * p.m0 ^ 2) * a ^ 3) ∧
    (∀ a ∈ p11c_axes, ∀ s : ℝ, 0 < s → p11c_beta p (s • a) = (s ^ (-2 : ℤ)) • p11c_beta p a) := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := as_ent p hp
  have hm0 := hp.2.1
  have hm := hp.2.2 0
  have hm1 := hp.2.2 1
  refine ⟨?_, ?_, ?_, ?_, fun a ha s hs => p11cAs_beta_smul p hp a ha hs⟩
  · refine p11cAs_rel (c := 3 * p.m 1 / (4 * p.m0 * p.m 0)) (e := 1) (by positivity)
      (p11cAe_pos.mono fun a _ => by simp) ?_
    exact p11cAe_congr_exp (by norm_num) (h4.congr_left fun a => by simp)
  · refine p11cAs_rel (c := -9 / (4 * p.m0)) (e := 3 / 2)
      (div_ne_zero (by norm_num) (by positivity)) (Eventually.of_forall fun a => rfl) ?_
    exact p11cAe_congr_exp (by norm_num) (h5.congr_left fun a => by ring)
  · refine p11cAs_rel (c := -3 * p.m 0 / (p.m0 * p.m 1)) (e := 2)
      (div_ne_zero (mul_ne_zero (by norm_num) hm.ne') (by positivity))
      (Eventually.of_forall fun a => by simp only [Real.rpow_two, sq]) ?_
    exact p11cAe_congr_exp (by norm_num)
      (h6.congr_left fun a => by simp only [Real.rpow_two]; ring)
  · refine p11cAs_rel (c := -117 / (16 * p.m0 ^ 2)) (e := 3)
      (div_ne_zero (by norm_num) (by positivity)) ?_ ?_
    · exact Eventually.of_forall fun a => by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    · exact p11cAe_congr_exp (by norm_num) ((p11cAs_det p hp).congr_left fun a => by
      rw [show a ^ (3 : ℝ) = a ^ 3 by simp])

/-- Uniformity only in the mass ratio, as claimed by asymptotics; absolute physical scales cancel. -/
theorem asymptotics_uniform_ratio (ratio : ℝ) (hratio : 0 < ratio) :
    ∃ C alpha0 : ℝ, 0 < C ∧ 0 < alpha0 ∧ alpha0 ≤ 1 ∧
      ∀ p : PlanarData, p.Valid → p.m 0 / p.m 1 = ratio → ∀ a ∈ Ioo (0 : ℝ) alpha0,
        |(p11c_beta p ![a, 1]).det / (-117 / (16 * p.m0 ^ 2) * a ^ 3) - 1| ≤ C * a ^ 2 ∧
        |p11c_beta p ![a, 1] 0 0 / (3 * p.m 1 / (4 * p.m0 * p.m 0) * a) - 1| ≤ C * a ^ 2 ∧
        |p11c_beta p ![a, 1] 0 1 / (-9 / (4 * p.m0) * a ^ (3 / 2 : ℝ)) - 1| ≤ C * a ^ 2 ∧
        |p11c_beta p ![a, 1] 1 1 / (-3 * p.m 0 / (p.m0 * p.m 1) * a ^ 2) - 1| ≤ C * a ^ 2 := by
  have hu := p11cAs_unit_valid hratio
  obtain ⟨r0, r1, r2, r3, -⟩ := asymptotics _ hu
  obtain ⟨C0, d0, hC0, hd0, hd0', e0⟩ := p11cAs_rel_explicit r0
  obtain ⟨C1, d1, hC1, hd1, hd1', e1⟩ := p11cAs_rel_explicit r1
  obtain ⟨C2, d2, hC2, hd2, hd2', e2⟩ := p11cAs_rel_explicit r2
  obtain ⟨C3, d3, hC3, hd3, hd3', e3⟩ := p11cAs_rel_explicit r3
  refine ⟨C0 + C1 + C2 + C3, min (min d0 d1) (min d2 d3), by positivity,
    lt_min (lt_min hd0 hd1) (lt_min hd2 hd3), (min_le_left _ _).trans
    ((min_le_left _ _).trans hd0'), fun p hp hm a ha => ?_⟩
  have hma : 0 < a := ha.1
  have h0 : a < d0 := ha.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h1 : a < d1 := ha.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h2 : a < d2 := ha.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : a < d3 := ha.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hm0 := hp.2.1
  have hmm1 := hp.2.2 1
  have hmm0 : p.m 0 = ratio * p.m 1 := by
    have := hmm1.ne'
    field_simp at hm; linarith
  have hB := p11cAs_beta_ratio p hp hratio hm hma
  have hne : (p.m0)⁻¹ ≠ 0 := inv_ne_zero hm0.ne'
  have ent : ∀ i j, p11c_beta p ![a, 1] i j =
      (p.m0)⁻¹ * p11c_beta (p11cAs_unit ratio) ![a, 1] i j := fun i j => by
    rw [hB]; rfl
  have hdet : (p11c_beta p ![a, 1]).det =
      (p.m0)⁻¹ ^ 2 * (p11c_beta (p11cAs_unit ratio) ![a, 1]).det := by
    rw [hB, Matrix.det_smul]; simp
  have hs : 0 ≤ a ^ 2 := sq_nonneg a
  have hmono : ∀ C : ℝ, 0 ≤ C → ∀ D : ℝ, C ≤ D → C * a ^ 2 ≤ D * a ^ 2 :=
    fun C _ D h => mul_le_mul_of_nonneg_right h hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e3 a ⟨hma, h3⟩
    rw [hdet, show -117 / (16 * p.m0 ^ 2) * a ^ 3 = (p.m0)⁻¹ ^ 2 *
      (-117 / (16 * (p11cAs_unit ratio).m0 ^ 2) * a ^ 3) by
        simp only [p11cAs_unit]; field_simp, mul_div_mul_left _ _ (pow_ne_zero 2 hne)]
    exact this.trans (hmono _ hC3.le _ (by linarith))
  · have := e0 a ⟨hma, h0⟩
    rw [ent, show 3 * p.m 1 / (4 * p.m0 * p.m 0) * a = (p.m0)⁻¹ *
      (3 * (p11cAs_unit ratio).m 1 / (4 * (p11cAs_unit ratio).m0 * (p11cAs_unit ratio).m 0) * a) by
        simp only [p11cAs_unit, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hmm0]; field_simp, mul_div_mul_left _ _ hne]
    exact this.trans (hmono _ hC0.le _ (by linarith))
  · have := e1 a ⟨hma, h1⟩
    rw [ent, show -9 / (4 * p.m0) * a ^ (3 / 2 : ℝ) = (p.m0)⁻¹ *
      (-9 / (4 * (p11cAs_unit ratio).m0) * a ^ (3 / 2 : ℝ)) by
        simp only [p11cAs_unit]; field_simp, mul_div_mul_left _ _ hne]
    exact this.trans (hmono _ hC1.le _ (by linarith))
  · have := e2 a ⟨hma, h2⟩
    rw [ent, show -3 * p.m 0 / (p.m0 * p.m 1) * a ^ 2 = (p.m0)⁻¹ *
      (-3 * (p11cAs_unit ratio).m 0 / ((p11cAs_unit ratio).m0 * (p11cAs_unit ratio).m 1) *
        a ^ 2) by
        simp only [p11cAs_unit, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hmm0]; field_simp, mul_div_mul_left _ _ hne]
    exact this.trans (hmono _ hC2.le _ (by linarith))

theorem asymptotics_general_axes (ratio : ℝ) (hratio : 0 < ratio) :
    ∃ C alpha0 : ℝ, 0 < C ∧ 0 < alpha0 ∧ ∀ p : PlanarData,
      p.Valid → p.m 0 / p.m 1 = ratio → ∀ a ∈ p11c_axes, a 0 / a 1 < alpha0 →
        |(p11c_beta p a).det / (-117 / (16 * p.m0 ^ 2) * a 0 ^ 3 / a 1 ^ 7) - 1| ≤
          C * (a 0 / a 1) ^ 2 := by
  obtain ⟨C, α0, hC, hα0, -, H⟩ := asymptotics_uniform_ratio ratio hratio
  refine ⟨C, α0, hC, hα0, fun p hp hm a ha hlt => ?_⟩
  have h0 := ha.1
  have h1 := h0.trans ha.2
  have hα : 0 < a 0 / a 1 := div_pos h0 h1
  have hdec : a = a 1 • ![a 0 / a 1, 1] := by
    ext i; fin_cases i
    · simp; field_simp
    · simp
  have hB := p11cAs_beta_smul p hp ![a 0 / a 1, 1] (by
    refine ⟨?_, ?_⟩ <;> simp [hα, ha.2, div_lt_one h1]) h1
  have hH := (H p hp hm (a 0 / a 1) ⟨hα, hlt⟩).1
  have hm0 := hp.2.1
  rw [← hdec] at hB
  rw [hB, Matrix.det_smul]
  have hz : ((a 1 ^ (-2 : ℤ)) ^ Fintype.card (Fin 2)) ≠ 0 := by
    simp only [Fintype.card_fin]; positivity
  have hL : -117 / (16 * p.m0 ^ 2) * a 0 ^ 3 / a 1 ^ 7 =
      (a 1 ^ (-2 : ℤ)) ^ Fintype.card (Fin 2) *
        (-117 / (16 * p.m0 ^ 2) * (a 0 / a 1) ^ 3) := by
    simp only [Fintype.card_fin, zpow_neg, zpow_ofNat]
    field_simp
  rw [hL, mul_div_mul_left _ _ hz]
  exact hH

end KAM.Planetary

end
