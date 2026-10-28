/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Hamiltonian.Chart

/-!
# Liouville's theorem for symplectic charts on `Phase d`

`bpP:p1:liouville` (`chart_measure_image`, `measurableSet_chart_image`), `bpP:p1:liouville-lattice`
(`liouville_lattice`, `liouville_lattice_measurableSet`) and the Kepler consumer form
`measure_chart_image`. Lebesgue measurability is obtained from the Borel part and the fact that a
differentiable map sends null sets to null sets; the Borel part uses a countable cover of `O` by
open sets on which `Ψ` is injective.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

section Liouville

variable {d : ℕ}

/-- Lebesgue measure on `Phase d` is an additive Haar measure. Instance search does NOT find this
(probe: `#synth` fails on the product `volume`); provers use
`haveI := isAddHaarMeasure_volume_phase d` locally (never a global instance on the Mathlib
product type). -/
theorem isAddHaarMeasure_volume_phase (d : ℕ) : (volume : Measure (Phase d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- `Q = {z : z₁ ∈ [0,1)^d}`. -/
def unitCell (d : ℕ) : Set (Phase d) := {z | ∀ i, z.1 i ∈ Ico (0 : ℝ) 1}

theorem IsChart.exists_open_injOn {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O) {z : Phase d} (hz : z ∈ O) :
    ∃ U : Set (Phase d), IsOpen U ∧ z ∈ U ∧ U ⊆ O ∧ InjOn Ψ U := by
  have hb := hΨ.bijective_fderiv hc hz
  have hdiff : HasFDerivAt Ψ (fderiv ℝ Ψ z) z :=
    ((hΨ.1 z hz).differentiableAt).hasFDerivAt
  let L : Phase d ≃L[ℝ] Phase d :=
    (LinearEquiv.ofBijective (fderiv ℝ Ψ z : Phase d →ₗ[ℝ] Phase d) hb).toContinuousLinearEquiv
  have hL : (L : Phase d →L[ℝ] Phase d) = fderiv ℝ Ψ z := rfl
  have hcd : ContDiffAt ℝ 1 Ψ z := (hΨ.1 z hz).contDiffAt.of_le le_top
  have hdiff' : HasFDerivAt Ψ (L : Phase d →L[ℝ] Phase d) z := hL ▸ hdiff
  let e := hcd.toOpenPartialHomeomorph Ψ hdiff' one_ne_zero
  refine ⟨e.source ∩ O, e.open_source.inter hO,
    ⟨hcd.mem_toOpenPartialHomeomorph_source hdiff' one_ne_zero, hz⟩, inter_subset_right, ?_⟩
  exact e.injOn.mono inter_subset_left

/-- `bpP:p1:liouville`, Borel part (`stepP:p1:li-borel`). -/
theorem measurableSet_chart_image {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O) {A : Set (Phase d)} (hAO : A ⊆ O)
    (hA : MeasurableSet A) : MeasurableSet (Ψ '' A) := by
  choose! U hUo hzU hUO hUinj using fun z (hz : z ∈ O) => hΨ.exists_open_injOn hc hO hz
  have hf : ∀ x ∈ O, U x ∈ nhdsWithin x O := fun x hx =>
    mem_nhdsWithin_of_mem_nhds ((hUo x hx).mem_nhds (hzU x hx))
  obtain ⟨t, htO, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hf
  have : Ψ '' A = ⋃ x ∈ t, Ψ '' (A ∩ U x) := by
    ext y
    simp only [mem_image, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨x, hx, hax⟩ := mem_iUnion₂.1 (hcov (hAO ha))
      exact ⟨x, hx, a, ⟨ha, hax⟩, rfl⟩
    · rintro ⟨x, -, a, ⟨ha, -⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [this]
  refine MeasurableSet.biUnion htc fun x hx => ?_
  refine MeasurableSet.image_of_continuousOn_injOn (hA.inter (hUo x (htO hx)).measurableSet) ?_
    ((hUinj x (htO hx)).mono inter_subset_right)
  exact hΨ.1.continuousOn.mono (fun a ha => hAO ha.1)

/-- `bpP:p1:liouville`, Lebesgue part (`stepP:p1:li-meas`, `li-vol`). -/
theorem chart_measure_image {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O) {A : Set (Phase d)} (hAO : A ⊆ O)
    (hA : NullMeasurableSet A) :
    NullMeasurableSet (Ψ '' A) ∧ volume (Ψ '' A) ≤ ENNReal.ofReal (c ^ d) * volume A ∧
      (InjOn Ψ A → volume (Ψ '' A) = ENNReal.ofReal (c ^ d) * volume A) := by
  have := isAddHaarMeasure_volume_phase d
  obtain ⟨B, hBA, hBm, hBA'⟩ := hA.exists_measurable_subset_ae_eq
  have hN : volume (A \ B) = 0 := by
    have := (ae_eq_set.1 hBA').2
    simpa using this
  have hdiff : ∀ x ∈ B, HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) B x := fun x hx =>
    ((hΨ.1 x (hAO (hBA hx))).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hdet : ∀ x ∈ B, ENNReal.ofReal |(fderiv ℝ Ψ x : Phase d →ₗ[ℝ] Phase d).det| =
      ENNReal.ofReal (c ^ d) := fun x hx => by
    rw [hΨ.abs_det_fderiv hc (hAO (hBA hx))]
  have hint : (∫⁻ x in B, ENNReal.ofReal |(fderiv ℝ Ψ x : Phase d →ₗ[ℝ] Phase d).det|)
      = ENNReal.ofReal (c ^ d) * volume B := by
    rw [setLIntegral_congr_fun hBm hdet, setLIntegral_const, mul_comm]
  have hBmeas : MeasurableSet (Ψ '' B) :=
    measurableSet_chart_image hc hO hΨ (hBA.trans hAO) hBm
  have hnull : volume (Ψ '' (A \ B)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      (fun x hx => (hΨ.1 x (hAO hx.1)).differentiableAt.differentiableWithinAt) hN
  have hunion : Ψ '' A = Ψ '' B ∪ Ψ '' (A \ B) := by
    rw [← image_union, union_sdiff_cancel hBA]
  have hvol : volume B = volume A := measure_congr hBA'
  have hAeq : volume (Ψ '' A) = volume (Ψ '' B) := by
    rw [hunion]
    refine le_antisymm ((measure_union_le _ _).trans (by simp [hnull]))
      (measure_mono subset_union_left)
  refine ⟨?_, ?_, fun hinj => ?_⟩
  · rw [hunion]
    exact hBmeas.nullMeasurableSet.union (NullMeasurableSet.of_null hnull)
  · rw [hAeq, ← hvol, ← hint]
    exact addHaar_image_le_lintegral_abs_det_fderiv volume hBm hdiff
  · rw [hAeq, ← hvol, ← hint]
    exact (lintegral_abs_det_fderiv_eq_addHaar_image volume hBm hdiff (hinj.mono hBA)).symm

theorem measurableSet_unitCell (d : ℕ) : MeasurableSet (unitCell d) := by
  have : unitCell d = ⋂ i, (fun z : Phase d => z.1 i) ⁻¹' Ico (0 : ℝ) 1 := by
    ext z; simp [unitCell]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ico.preimage ((measurable_pi_apply i).comp measurable_fst)

/-- Every point of a `ι`-periodic set is translated into the unit cell by an integer shift. -/
theorem exists_shift_mem_unitCell {A : Set (Phase d)}
    (hAper : ∀ k : Fin d → ℤ, (fun z => z + angleShift k) '' A = A) {z : Phase d} (hz : z ∈ A) :
    ∃ m : Fin d → ℤ, z + angleShift m ∈ A ∩ unitCell d := by
  refine ⟨fun i => -⌊z.1 i⌋, ?_, fun i => ?_⟩
  · rw [← hAper (fun i => -⌊z.1 i⌋)]
    exact mem_image_of_mem _ hz
  · have h : (z + angleShift (fun i => -⌊z.1 i⌋)).1 i = Int.fract (z.1 i) := by
      simp [angleShift, Int.fract, sub_eq_add_neg]
    rw [h]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem injOn_unitCell {O : Set (Phase d)} {Ψ : Phase d → Phase d}
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ m : Fin d → ℤ, z' = z + angleShift m)
    {A : Set (Phase d)} (hAO : A ⊆ O) : InjOn Ψ (A ∩ unitCell d) := by
  rintro z ⟨hzA, hzQ⟩ z' ⟨hz'A, hz'Q⟩ h
  obtain ⟨m, hm⟩ := hQ2 z (hAO hzA) z' (hAO hz'A) h.symm
  have hm0 : m = 0 := by
    funext i
    have h1 := congrArg (fun w : Phase d => w.1 i) hm
    simp only [Prod.fst_add, Pi.add_apply, angleShift] at h1
    have a := hzQ i
    have b := hz'Q i
    have h2 : ((m i : ℤ) : ℝ) = z'.1 i - z.1 i := by linarith
    have h3 : ((m i : ℤ) : ℝ) < 1 := by rw [h2]; linarith [a.1, b.2]
    have h4 : (-1 : ℝ) < ((m i : ℤ) : ℝ) := by rw [h2]; linarith [a.2, b.1]
    have h5 : m i < 1 := by exact_mod_cast h3
    have h6 : -1 < m i := by exact_mod_cast h4
    simp only [Pi.zero_apply]; omega
  subst hm0
  have h0 : angleShift (0 : Fin d → ℤ) = 0 := Prod.ext (funext fun i => by simp [angleShift]) rfl
  rw [h0, add_zero] at hm
  exact hm.symm

/-- `bpP:p1:liouville-lattice` (Lebesgue version). -/
theorem liouville_lattice {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + angleShift k ∈ O ∧ Ψ (z + angleShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ m : Fin d → ℤ, z' = z + angleShift m)
    {A : Set (Phase d)} (hA : NullMeasurableSet A) (hAO : A ⊆ O)
    (hAper : ∀ k : Fin d → ℤ, (fun z => z + angleShift k) '' A = A) :
    NullMeasurableSet (Ψ '' A) ∧ Ψ '' A = Ψ '' (A ∩ unitCell d) ∧
      volume (Ψ '' A) = ENNReal.ofReal (c ^ d) * volume (A ∩ unitCell d) ∧
      (0 < volume (Ψ '' A) ↔ 0 < volume A) ∧
      (Bornology.IsBounded (A ∩ unitCell d) → volume (Ψ '' A) < ⊤) := by
  have := isAddHaarMeasure_volume_phase d
  have himg : Ψ '' A = Ψ '' (A ∩ unitCell d) := by
    refine Subset.antisymm ?_ (image_mono inter_subset_left)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨m, hm⟩ := exists_shift_mem_unitCell hAper hz
    exact ⟨_, hm, (hQ1 z (hAO hz) m).2⟩
  have hAQ : NullMeasurableSet (A ∩ unitCell d) :=
    hA.inter (measurableSet_unitCell d).nullMeasurableSet
  have hAQO : A ∩ unitCell d ⊆ O := inter_subset_left.trans hAO
  have hvol : volume (Ψ '' A) = ENNReal.ofReal (c ^ d) * volume (A ∩ unitCell d) := by
    rw [himg]
    exact (chart_measure_image hc hO hΨ hAQO hAQ).2.2 (injOn_unitCell hQ2 hAO)
  have hpos : 0 < ENNReal.ofReal (c ^ d) := ENNReal.ofReal_pos.2 (pow_pos hc _)
  refine ⟨(chart_measure_image hc hO hΨ hAO hA).1, himg, hvol, ?_, fun hb => ?_⟩
  · rw [hvol, ENNReal.mul_pos_iff]
    simp only [hpos, true_and]
    refine ⟨fun h => lt_of_lt_of_le h (measure_mono inter_subset_left), fun h => ?_⟩
    by_contra h0
    have h0 : volume (A ∩ unitCell d) = 0 := by simpa using h0
    have hcov : A ⊆ ⋃ m : Fin d → ℤ, (fun w => w + angleShift m) ⁻¹' (A ∩ unitCell d) := by
      intro z hz
      obtain ⟨m, hm⟩ := exists_shift_mem_unitCell hAper hz
      exact mem_iUnion.2 ⟨m, hm⟩
    have : volume A = 0 := measure_mono_null hcov (measure_iUnion_null fun m => by
      rw [measure_preimage_add_right]; exact h0)
    exact absurd h (by simp [this])
  · rw [hvol]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb.measure_lt_top

/-- `bpP:p1:liouville-lattice` (Borel version; `MeasurableSet.image_of_continuousOn_injOn`). -/
theorem liouville_lattice_measurableSet {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : IsChart c Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + angleShift k ∈ O ∧ Ψ (z + angleShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ m : Fin d → ℤ, z' = z + angleShift m)
    {A : Set (Phase d)} (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hAper : ∀ k : Fin d → ℤ, (fun z => z + angleShift k) '' A = A) :
    MeasurableSet (Ψ '' A) := by
  have := hA
  rw [(liouville_lattice hc hO hΨ hQ1 hQ2 hA.nullMeasurableSet hAO hAper).2.1]
  exact measurableSet_chart_image hc hO hΨ (inter_subset_left.trans hAO)
    (hA.inter (measurableSet_unitCell d))

/-- The Kepler design's consumer form of `bpP:p1:liouville-lattice` (P6-5 (b)), adopted VERBATIM
(signature of `KeplerSignaturesP.lean`); FULL position lattice only (audit F6 caveat). -/
theorem measure_chart_image {d : ℕ} {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} (hO : IsOpen O)
    {Ψ : Phase d → Phase d} (hΨ : AnalyticOnNhd ℝ Ψ O) (hs : IsSymplecticOn c Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + ((fun i => (k i : ℝ)), 0) ∈ O ∧
      Ψ (z + ((fun i => (k i : ℝ)), 0)) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin d → ℤ, z' = z + ((fun i => (k i : ℝ)), 0))
    {A : Set (Phase d)} (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hAper : ∀ k : Fin d → ℤ, (fun z => z + ((fun i => (k i : ℝ)), 0)) '' A = A) :
    MeasurableSet (Ψ '' A) ∧
      MeasureTheory.volume (Ψ '' A) =
        ENNReal.ofReal (c ^ d) * MeasureTheory.volume (A ∩ {z | ∀ i, z.1 i ∈ Ico (0 : ℝ) 1}) ∧
      (0 < MeasureTheory.volume (Ψ '' A) ↔ 0 < MeasureTheory.volume A) := by
  have hΨ' : IsChart c Ψ O := ⟨hΨ, hs⟩
  have h := liouville_lattice hc hO hΨ' hQ1 hQ2 hA.nullMeasurableSet hAO hAper
  exact ⟨liouville_lattice_measurableSet hc hO hΨ' hQ1 hQ2 hA hAO hAper, h.2.2.1, h.2.2.2.1⟩

end Liouville

end KAM.Planetary
