/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import KAM.Frozen.Defs.FundamentalDomain

/-!
# Track R: reduction of angles modulo `ℤⁿ`

`volume_le_volume_fundamentalDomain_inter`: if a measurable set `E ⊆ ℝⁿ × ℝⁿ` meets each orbit of
the angle translations `z ↦ z + (k, 0)`, `k ∈ ℤⁿ`, at most once, has its actions in `B`, and every
integer angle translate of a point of `E` lies in `S`, then `meas E ≤ meas([0,1)ⁿ × B ∩ S)`; the
measurable form `exists_measurableSet_subset_fundamentalDomain_inter` exhibits a measurable
`F ⊆ [0,1)ⁿ × B ∩ S` with `meas E ≤ meas F`.
The map `(θ, I) ↦ (fract θ, I)` is a translation on each piece `{⌊θ⌋ = k}` of `E`, and the
translated pieces are pairwise disjoint.
-/

@[expose] public section

open MeasureTheory Set

namespace KAM.Russmann

variable {n : ℕ}

/-- The angle translation `(k, 0)` by an integer vector. -/
def angleTranslate (k : Fin n → ℤ) : (Fin n → ℝ) × (Fin n → ℝ) := (fun i => (k i : ℝ), 0)

/-- The points whose angles have integer part `k`. -/
def floorCell (k : Fin n → ℤ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | ∀ i, ⌊z.1 i⌋ = k i}

theorem measurableSet_floorCell (k : Fin n → ℤ) : MeasurableSet (floorCell k) := by
  have : floorCell k = ⋂ i, (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ⌊z.1 i⌋) ⁻¹' {k i} := by
    ext z; simp [floorCell]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (Int.measurable_floor.comp ((measurable_pi_apply i).comp measurable_fst))
      (measurableSet_singleton _)

theorem angleTranslate_add (k l : Fin n → ℤ) :
    angleTranslate (k + l) = angleTranslate k + angleTranslate l := by
  ext i <;> simp [angleTranslate]

theorem angleTranslate_eq_zero {k : Fin n → ℤ} (h : angleTranslate k = 0) : k = 0 := by
  funext i
  have := congrFun (congrArg Prod.fst h) i
  simpa [angleTranslate] using this

/-- **Reduction modulo `ℤⁿ`, measurable form.** A measurable set meeting each `ℤⁿ`-orbit of angle
translations at most once, with actions in `B`, is carried by `(θ, I) ↦ (fract θ, I)` onto a
measurable set `F ⊆ [0,1)ⁿ × B` of the same volume (at least), contained in `S` as soon as `S`
contains every integer angle translate of `E`. -/
theorem exists_measurableSet_subset_fundamentalDomain_inter
    {E S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {B : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hinj : ∀ z ∈ E, ∀ z' ∈ E, ∀ k : Fin n → ℤ, z = z' + angleTranslate k → k = 0)
    (hS : ∀ z ∈ E, ∀ k : Fin n → ℤ, z + angleTranslate k ∈ S)
    (hB : ∀ z ∈ E, z.2 ∈ B) :
    ∃ F : Set ((Fin n → ℝ) × (Fin n → ℝ)), MeasurableSet F ∧
      F ⊆ fundamentalDomain B ∩ S ∧ volume E ≤ volume F := by
  set A : (Fin n → ℤ) → Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    fun k => (fun w => angleTranslate k + w) ⁻¹' (E ∩ floorCell k) with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (hE.inter (measurableSet_floorCell k)).preimage (measurable_const_add _)
  have hAvol : ∀ k, volume (A k) = volume (E ∩ floorCell k) := fun k => by
    rw [Measure.volume_eq_prod]
    exact measure_preimage_add _ _ _
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro k l hkl
    refine Set.disjoint_left.2 fun w hk hl => hkl ?_
    have e : angleTranslate k + w = (angleTranslate l + w) + angleTranslate (k - l) := by
      rw [add_comm (angleTranslate l) w, add_assoc, ← angleTranslate_add, add_comm]; simp
    have := hinj _ hk.1 _ hl.1 _ e
    exact sub_eq_zero.1 this
  have hcover : E ⊆ ⋃ k, E ∩ floorCell k := fun z hz =>
    mem_iUnion.2 ⟨fun i => ⌊z.1 i⌋, hz, fun i => rfl⟩
  have hsub : (⋃ k, A k) ⊆ fundamentalDomain B ∩ S := by
    intro w hw
    obtain ⟨k, hk⟩ := mem_iUnion.1 hw
    obtain ⟨hzE, hzk⟩ := hk
    have hw' : w = (angleTranslate k + w) + angleTranslate (-k) := by
      rw [add_comm (angleTranslate k) w, add_assoc, ← angleTranslate_add]
      ext i <;> simp [angleTranslate]
    refine ⟨⟨fun i _ => ?_, ?_⟩, hw' ▸ hS _ hzE (-k)⟩
    · have hfl := hzk i
      have e1 : w.1 i = (angleTranslate k + w).1 i - k i := by simp [angleTranslate]
      rw [e1, ← hfl]
      exact ⟨by linarith [Int.floor_le ((angleTranslate k + w).1 i)],
        by linarith [Int.lt_floor_add_one ((angleTranslate k + w).1 i)]⟩
    · have := hB _ hzE
      simpa [angleTranslate] using this
  refine ⟨⋃ k, A k, MeasurableSet.iUnion hAm, hsub, ?_⟩
  calc volume E ≤ volume (⋃ k, E ∩ floorCell k) := measure_mono hcover
    _ ≤ ∑' k, volume (E ∩ floorCell k) := measure_iUnion_le _
    _ = ∑' k, volume (A k) := by simp_rw [hAvol]
    _ = volume (⋃ k, A k) := (measure_iUnion hdisj hAm).symm

/-- **Reduction modulo `ℤⁿ`.** A measurable set meeting each `ℤⁿ`-orbit of angle translations at
most once, with actions in `B`, has volume at most that of the part of `S` over `[0,1)ⁿ × B`, as
soon as `S` contains every integer angle translate of `E`. -/
theorem volume_le_volume_fundamentalDomain_inter {E S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {B : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hinj : ∀ z ∈ E, ∀ z' ∈ E, ∀ k : Fin n → ℤ, z = z' + angleTranslate k → k = 0)
    (hS : ∀ z ∈ E, ∀ k : Fin n → ℤ, z + angleTranslate k ∈ S)
    (hB : ∀ z ∈ E, z.2 ∈ B) :
    volume E ≤ volume (fundamentalDomain B ∩ S) := by
  obtain ⟨F, -, hF, hvol⟩ := exists_measurableSet_subset_fundamentalDomain_inter hE hinj hS hB
  exact hvol.trans (measure_mono hF)

end KAM.Russmann

end
