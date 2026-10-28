/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Planetary.Hamiltonian.Liouville
public import KAM.Planetary.PGAssembly.ExtensionTubeP

/-!
# P Part 5: tiling by the fast lattice (`stepP:p5:ct-dec`, `stepP:p5:ct-count`)

A measurable set `E` whose fast `2π`-lattice translates are pairwise disjoint: the measure of
the union of its translates inside the fast cell `0 ≤ z₁,i < 2π` equals the measure of `E`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CT.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- The fast fundamental cell `0 ≤ z₁,i < 2π` (`i` a fast index). -/
def ctFastCell (a b : ℕ) : Set (Phase (a + b)) :=
  {z | ∀ i : Fin a, 0 ≤ z.1 (Fin.castAdd b i) ∧ z.1 (Fin.castAdd b i) < 2 * Real.pi}

theorem measurableSet_ctFastCell : MeasurableSet (ctFastCell a b) := by
  have : ctFastCell a b = ⋂ i : Fin a,
      (fun z : Phase (a + b) => z.1 (Fin.castAdd b i)) ⁻¹' Ico (0 : ℝ) (2 * Real.pi) := by
    ext z; simp [ctFastCell]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ico.preimage ((measurable_pi_apply _).comp measurable_fst)

theorem exists_fastShift_mem_fastCell (z : Phase (a + b)) :
    ∃ k : Fin a → ℤ, z + fastShift k ∈ ctFastCell a b := by
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨fun i => -⌊z.1 (Fin.castAdd b i) / (2 * Real.pi)⌋, fun i => ?_⟩
  have h1 := (le_div_iff₀ hp).1 (Int.floor_le (z.1 (Fin.castAdd b i) / (2 * Real.pi)))
  have h2 := (div_lt_iff₀ hp).1 (Int.lt_floor_add_one (z.1 (Fin.castAdd b i) / (2 * Real.pi)))
  simp only [Prod.fst_add, Pi.add_apply, fastShift_fst_castAdd, Int.cast_neg]
  constructor <;> nlinarith

theorem fastShift_unique {z : Phase (a + b)} {k k' : Fin a → ℤ}
    (hk : z + fastShift k ∈ ctFastCell a b) (hk' : z + fastShift k' ∈ ctFastCell a b) : k = k' := by
  have hp : 0 < 2 * Real.pi := by positivity
  funext i
  obtain ⟨h1, h2⟩ := hk i
  obtain ⟨h3, h4⟩ := hk' i
  simp only [Prod.fst_add, Pi.add_apply, fastShift_fst_castAdd] at h1 h2 h3 h4
  have a1 : (k i : ℝ) < k' i + 1 := lt_of_mul_lt_mul_left (a := 2 * Real.pi)
    (by linarith) hp.le
  have a2 : (k' i : ℝ) < k i + 1 := lt_of_mul_lt_mul_left (a := 2 * Real.pi)
    (by linarith) hp.le
  have b1 : k i < k' i + 1 := by exact_mod_cast a1
  have b2 : k' i < k i + 1 := by exact_mod_cast a2
  omega

/-- Union of the fast translates of `E`, cut to the fast cell, has the measure of `E`. -/
theorem volume_fastTranslates_inter_fastCell {E : Set (Phase (a + b))} (hE : MeasurableSet E)
    (hdisj : ∀ k k' : Fin a → ℤ, ∀ x, x ∈ (fun z => z + fastShift k) '' E →
      x ∈ (fun z => z + fastShift k') '' E → k = k') :
    volume ((⋃ k : Fin a → ℤ, (fun z : Phase (a + b) => z + fastShift k) '' E) ∩
      ctFastCell a b) = volume E := by
  have := isAddHaarMeasure_volume_phase (a + b)
  have himg : ∀ (k : Fin a → ℤ) (X : Set (Phase (a + b))),
      (fun z : Phase (a + b) => z + fastShift k) '' X =
        (fun z => z + -fastShift k) ⁻¹' X := fun k X => image_add_right
  have hmeasτ : ∀ k : Fin a → ℤ, MeasurableSet
      ((fun z : Phase (a + b) => z + fastShift k) '' E) := fun k => by
    rw [himg]; exact (measurable_add_const _) hE
  have hvol : ∀ (k : Fin a → ℤ) (X : Set (Phase (a + b))),
      volume ((fun z : Phase (a + b) => z + fastShift k) '' X) = volume X := fun k X => by
    rw [himg, measure_preimage_add_right]
  have hcell : ∀ k : Fin a → ℤ, MeasurableSet
      ((fun z : Phase (a + b) => z + fastShift k) ⁻¹' ctFastCell a b) := fun k =>
    (measurable_add_const _) measurableSet_ctFastCell
  rw [iUnion_inter, measure_iUnion]
  · have hk : ∀ k : Fin a → ℤ, volume ((fun z : Phase (a + b) => z + fastShift k) '' E ∩
        ctFastCell a b) =
        volume (E ∩ (fun z : Phase (a + b) => z + fastShift k) ⁻¹' ctFastCell a b) :=
      fun k => by rw [← image_inter_preimage, hvol]
    simp_rw [hk]
    rw [← measure_iUnion]
    · congr 1
      rw [← inter_iUnion]
      refine inter_eq_left.2 fun z _ => mem_iUnion.2 ?_
      obtain ⟨k, hk⟩ := exists_fastShift_mem_fastCell z
      exact ⟨k, hk⟩
    · intro k k' hne
      refine Set.disjoint_left.2 fun z hz hz' => hne (fastShift_unique hz.2 hz'.2)
    · exact fun k => hE.inter (hcell k)
  · intro k k' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne (hdisj k k' x hx.1 hx'.1)
  · exact fun k => (hmeasτ k).inter measurableSet_ctFastCell

end KAM.Planetary

end
