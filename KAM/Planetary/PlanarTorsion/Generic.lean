/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Asymptotics
public import KAM.Planetary.PlanarTorsion.Birkhoff.Defs
public import KAM.Planetary.Nondegeneracy.GoodAxes
public import KAM.Planetary.Nondegeneracy.AnalyticZeros

/-!
# Planar quartic torsion: genericity of the torsion determinant (P11C, package T20)

Blueprint P, Part 11b (`bpP:p11b:torsion`, steps `to-an`, `to-pt`, `to-id`): `torsion`.  The
determinant of `p11c_beta` is analytic on the axis cone (`to-an`), negative at a point deep in the
hierarchy by `asymptotics_uniform_ratio` (`to-pt`), and the analytic zero-set theorem
`Nondegeneracy.generic` on the connected cone `p11c_axes` gives the open dense full-measure
statements (`to-id`), also simultaneously with the nonresonance polynomial `p11c_phi4`, which is
nonzero at an upstream good point (`Nondegeneracy.good_point`).
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function Filter
namespace KAM.Planetary
open KAM KAM.Kepler

theorem p11cGe_sigma1_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) : AnalyticAt ℝ (fun b => p11c_sigma p b 1) a := by
  have h := (((p11c_Q_analyticAt p hp ha 0 0).add (p11c_Q_analyticAt p hp ha 1 1)).sub
    (p11c_sigma0_analyticAt p hp ha))
  refine h.congr ?_
  filter_upwards [p11c_axes_isOpen.mem_nhds ha] with b hb
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith [(p11c_sigma_sum_prod p hp hb).1]

theorem p11cGe_phi4_analytic (p : PlanarData) (hp : p.Valid) :
    AnalyticOnNhd ℝ (fun a => p11c_phi4 p a) p11c_axes := by
  intro a ha
  refine Finset.analyticAt_fun_prod _ fun k _ => ?_
  simp only [Fin.sum_univ_two]
  exact (analyticAt_const.mul (p11c_sigma0_analyticAt p hp ha)).add
    (analyticAt_const.mul (p11cGe_sigma1_analyticAt p hp ha))

theorem p11cGe_axes_eq : p11c_axes = SecularForm.axes 2 := by
  ext a
  refine ⟨p11c_axes_mem, fun ha => ⟨ha.1 0, ha.2 (show (0 : Fin 2) < 1 by decide)⟩⟩

theorem p11cGe_phi4_exists (p : PlanarData) (hp : p.Valid) :
    ∃ a ∈ p11c_axes, p11c_phi4 p a ≠ 0 := by
  obtain ⟨a, ha, -, hnr⟩ := Nondegeneracy.good_point (p11cSecularData p hp) le_rfl
    (ε := 1 / 2) (by norm_num) (by norm_num)
  have ha' : a ∈ p11c_axes := p11cGe_axes_eq ▸ ha
  refine ⟨a, ha', Finset.prod_ne_zero_iff.2 fun k hk => ?_⟩
  rw [Finset.mem_filter] at hk
  have := hnr.2 (fun i => ((k i).val : ℤ) - 4) hk.2
  rw [← p11c_sigma_eq_sigma p hp ha'] at this
  simpa using this

/-- Nonresonance of the adapter product is exactly `nr4` of the spectrum `p11c_sigma`:
the integer-mode enumeration (`Fin 9` encoding) against `SecularSpectrum.k4 2`. -/
theorem p11cGe_phi4_ne_zero_iff_nr4 (p : PlanarData) (a : Fin 2 → ℝ) :
    p11c_phi4 p a ≠ 0 ↔ SecularSpectrum.nr4 (p11c_sigma p a) := by
  unfold p11c_phi4 SecularSpectrum.nr4
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h
    have hk : ∀ k : Fin 2 → ℤ, k ∈ SecularSpectrum.k4 2 →
        ∑ i, (k i : ℝ) * p11c_sigma p a i ≠ 0 := by
      intro k hk
      obtain ⟨hk0, hk4⟩ := hk
      have hbd : ∀ i, -4 ≤ k i ∧ k i ≤ 4 := by
        intro i
        have : |k i| ≤ ∑ j, |k j| :=
          Finset.single_le_sum (f := fun j => |k j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        exact abs_le.1 (this.trans hk4)
      let k' : Fin 2 → Fin 9 := fun i => ⟨(k i + 4).toNat, by have := hbd i; omega⟩
      have hk'v : ∀ i, ((k' i).val : ℤ) - 4 = k i := by
        intro i
        have := hbd i
        simp only [k']
        omega
      have hmem : k' ∈ (Finset.univ : Finset (Fin 2 → Fin 9)).filter
          (fun k => 0 < (∑ i, |((k i).val : ℤ) - 4|) ∧
            (∑ i, |((k i).val : ℤ) - 4|) ≤ 4) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hk'v]
        exact ⟨hk0, hk4⟩
      have hne := h k' hmem
      have hcast : ∀ i, (((k' i).val : ℝ) - 4) = (k i : ℝ) := fun i => by
        exact_mod_cast hk'v i
      simpa only [hcast] using hne
    refine ⟨fun i j hij => ?_, hk⟩
    by_contra hne
    have hk1 := hk ![1, -1] ⟨by simp [Fin.sum_univ_two], by simp [Fin.sum_univ_two]⟩
    apply hk1
    have : ∀ x y : Fin 2, x ≠ y → x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 := by decide
    rcases this i j hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Fin.sum_univ_two, hij]
  · rintro ⟨-, h⟩ k hk
    rw [Finset.mem_filter] at hk
    have := h (fun i => ((k i).val : ℤ) - 4) hk.2
    simpa using this

/-- Locus bridge (design P11C L187, U9 L54): on the axis cone the nonzero locus of the adapter
`p11c_phi4` is that of the Part-9 product `SecularSpectrum.good` of the secular spectrum. -/
theorem p11cGe_phi4_ne_zero_iff_good (p : PlanarData) (hp : p.Valid) :
    ∀ a ∈ p11c_axes, p11c_phi4 p a ≠ 0 ↔
      SecularSpectrum.good (SecularSpectrum.sigma (p11cSecularData p hp) a) ≠ 0 := by
  intro a ha
  rw [p11cGe_phi4_ne_zero_iff_nr4, SecularSpectrum.good_ne_zero_iff,
    p11c_sigma_eq_sigma p hp ha]

theorem p11cGe_det_analytic (p : PlanarData) (hp : p.Valid) :
    AnalyticOnNhd ℝ (fun a => (p11c_beta p a).det) p11c_axes := by
  intro a ha
  have h := (beta_properties p hp).1
  simp only [Matrix.det_fin_two]
  exact ((h 0 0 a ha).mul (h 1 1 a ha)).sub ((h 0 1 a ha).mul (h 1 0 a ha))

theorem p11cGe_det_neg (p : PlanarData) (hp : p.Valid) :
    ∃ a ∈ p11c_axes, (p11c_beta p a).det < 0 := by
  obtain ⟨C, α0, hC, hα0, hα1, H⟩ :=
    asymptotics_uniform_ratio (p.m 0 / p.m 1) (div_pos (hp.2.2 0) (hp.2.2 1))
  set t : ℝ := min (α0 / 2) (1 / (C + 1)) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by positivity)
  have htα : t < α0 := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t ≤ 1 / 2 := (min_le_left _ _).trans (by linarith)
  have htC : t ≤ 1 / (C + 1) := min_le_right _ _
  have h1 := (H p hp rfl t ⟨ht0, htα⟩).1
  have hCt : C * t ^ 2 < 1 := by
    have : C * t ≤ C / (C + 1) := by
      rw [← mul_one_div]; exact mul_le_mul_of_nonneg_left htC hC.le
    have h2 : C / (C + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith [mul_nonneg hC.le ht0.le]
  have hg : -117 / (16 * p.m0 ^ 2) * t ^ 3 < 0 := by
    have := hp.2.1
    have : 0 < 117 / (16 * p.m0 ^ 2) * t ^ 3 := by positivity
    rw [neg_div]
    linarith [neg_mul (117 / (16 * p.m0 ^ 2)) (t ^ 3)]
  have hpos : 0 < (p11c_beta p ![t, 1]).det / (-117 / (16 * p.m0 ^ 2) * t ^ 3) := by
    have := (abs_lt.1 (h1.trans_lt hCt)).1
    linarith
  refine ⟨![t, 1], ⟨by simpa using ht0, by simp; linarith⟩, ?_⟩
  by_contra hcon
  exact absurd hpos (not_lt.2 (div_nonpos_of_nonneg_of_nonpos (not_lt.1 hcon) hg.le))

theorem torsion (p : PlanarData) (hp : p.Valid) :
    AnalyticOnNhd ℝ (fun a => (p11c_beta p a).det) p11c_axes ∧
    (∃ a ∈ p11c_axes, (p11c_beta p a).det < 0) ∧
    IsOpen {a ∈ p11c_axes | (p11c_beta p a).det ≠ 0} ∧
    p11c_axes ⊆ closure {a ∈ p11c_axes | (p11c_beta p a).det ≠ 0} ∧
    volume {a ∈ p11c_axes | (p11c_beta p a).det = 0} = 0 ∧
    IsOpen {a ∈ p11c_axes | p11c_phi4 p a * (p11c_beta p a).det ≠ 0} ∧
    p11c_axes ⊆ closure {a ∈ p11c_axes | p11c_phi4 p a * (p11c_beta p a).det ≠ 0} ∧
    volume {a ∈ p11c_axes | p11c_phi4 p a * (p11c_beta p a).det = 0} = 0 := by
  have hB := p11c_axes_isOpen
  have hBc : IsConnected p11c_axes := p11cGe_axes_eq ▸ Nondegeneracy.isConnected_axes 2
  have han := p11cGe_det_analytic p hp
  obtain ⟨a1, ha1, hd⟩ := p11cGe_det_neg p hp
  obtain ⟨a2, ha2, hph⟩ := p11cGe_phi4_exists p hp
  have g1 := Nondegeneracy.generic (r := 1) hB hBc (f := fun _ a => (p11c_beta p a).det)
    (fun _ => han) (fun _ => ⟨a1, ha1, hd.ne⟩)
  have g2 := Nondegeneracy.generic (r := 2) hB hBc
    (f := ![fun a => p11c_phi4 p a, fun a => (p11c_beta p a).det])
    (by rw [Fin.forall_fin_two]; exact ⟨p11cGe_phi4_analytic p hp, han⟩)
    (by rw [Fin.forall_fin_two]; exact ⟨⟨a2, ha2, hph⟩, ⟨a1, ha1, hd.ne⟩⟩)
  refine ⟨han, ⟨a1, ha1, hd⟩, ?_⟩
  have e1 : {a ∈ p11c_axes | ∀ _ : Fin 1, (p11c_beta p a).det ≠ 0} =
      {a ∈ p11c_axes | (p11c_beta p a).det ≠ 0} := by ext a; simp
  have e2 : {a ∈ p11c_axes | ∃ _ : Fin 1, (p11c_beta p a).det = 0} =
      {a ∈ p11c_axes | (p11c_beta p a).det = 0} := by ext a; simp
  have e3 : {a ∈ p11c_axes | ∀ j : Fin 2, (![fun a => p11c_phi4 p a,
      fun a => (p11c_beta p a).det] : Fin 2 → (Fin 2 → ℝ) → ℝ) j a ≠ 0} =
      {a ∈ p11c_axes | p11c_phi4 p a * (p11c_beta p a).det ≠ 0} := by
    ext a; simp [Fin.forall_fin_two]
  have e4 : {a ∈ p11c_axes | ∃ j : Fin 2, (![fun a => p11c_phi4 p a,
      fun a => (p11c_beta p a).det] : Fin 2 → (Fin 2 → ℝ) → ℝ) j a = 0} =
      {a ∈ p11c_axes | p11c_phi4 p a * (p11c_beta p a).det = 0} := by
    ext a; simp [Fin.exists_fin_two, mul_eq_zero]
  rw [e1, e2] at g1
  rw [e3, e4] at g2
  exact ⟨g1.1, g1.2.1, g1.2.2, g2.1, g2.2.1, g2.2.2⟩

end KAM.Planetary

end
