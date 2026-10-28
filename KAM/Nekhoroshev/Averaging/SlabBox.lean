/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Part N12: one box of the slab estimate (`stepN:p12:sl-box`)

For a real function `φ` on a cube `closedBall c r ⊆ ℝᵐ⁺¹` whose derivative in the coordinate `j`
has modulus at least `c₁ > 0` on the cube, the set `{|φ| ≤ v}` in the cube has measure at most
`(2r)ᵐ · 2v / c₁`: every line section along `j` has diameter at most `2v / c₁` (mean value
theorem), and Fubini in the coordinate `j` (`volume_preserving_piFinSuccAbove`) finishes.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace KAM.Nekhoroshev.AvgSlab

variable {m : ℕ}

/-- Line sections of the box have diameter at most `2v / c₁` (mean value theorem). -/
theorem section_dist_le {φ g : (Fin (m + 1) → ℝ) → ℝ} {j : Fin (m + 1)}
    {c : Fin (m + 1) → ℝ} {r c₁ v : ℝ} (hr : 0 ≤ r)
    (hφd : ∀ I ∈ closedBall c r,
      HasDerivAt (fun t => φ (Function.update I j t)) (g I) (I j))
    (hg : ∀ I ∈ closedBall c r, c₁ ≤ |g I|)
    {P : Fin (m + 1) → ℝ} {t₁ t₂ : ℝ} (hP₁ : Function.update P j t₁ ∈ closedBall c r)
    (hP₂ : Function.update P j t₂ ∈ closedBall c r)
    (hv₁ : |φ (Function.update P j t₁)| ≤ v) (hv₂ : |φ (Function.update P j t₂)| ≤ v)
    (hlt : t₁ < t₂) : c₁ * (t₂ - t₁) ≤ 2 * v := by
  have hmem : ∀ t ∈ Icc t₁ t₂, Function.update P j t ∈ closedBall c r := by
    intro t ht
    have h1 := (dist_pi_le_iff hr).1 (mem_closedBall.1 hP₁)
    have h2 := (dist_pi_le_iff hr).1 (mem_closedBall.1 hP₂)
    rw [mem_closedBall, dist_pi_le_iff hr]
    intro l
    by_cases hl : l = j
    · subst hl
      have a1 := h1 l
      have a2 := h2 l
      simp only [Function.update_self, Real.dist_eq, abs_le] at a1 a2 ⊢
      constructor <;> linarith [ht.1, ht.2]
    · have := h1 l
      simpa [Function.update_of_ne hl] using this
  have hder : ∀ t ∈ Icc t₁ t₂,
      HasDerivAt (fun s => φ (Function.update P j s)) (g (Function.update P j t)) t := by
    intro t ht
    have := hφd _ (hmem t ht)
    simpa [Function.update_idem] using this
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun s => φ (Function.update P j s))
    (fun t => g (Function.update P j t)) hlt
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => hder t (Ioo_subset_Icc_self ht))
  have hge := hg _ (hmem ξ (Ioo_subset_Icc_self hξ))
  rw [hξe, abs_div, abs_of_pos (sub_pos.2 hlt), le_div_iff₀ (sub_pos.2 hlt)] at hge
  have : |φ (Function.update P j t₂) - φ (Function.update P j t₁)| ≤ 2 * v := by
    calc _ ≤ |φ (Function.update P j t₂)| + |φ (Function.update P j t₁)| := abs_sub _ _
      _ ≤ 2 * v := by linarith
  linarith

/-- One box of the slab estimate. -/
theorem volume_box_le {φ g : (Fin (m + 1) → ℝ) → ℝ} {j : Fin (m + 1)}
    {c : Fin (m + 1) → ℝ} {r c₁ v : ℝ} (hr : 0 ≤ r) (hc₁ : 0 < c₁)
    (hφc : ContinuousOn φ (closedBall c r))
    (hφd : ∀ I ∈ closedBall c r,
      HasDerivAt (fun t => φ (Function.update I j t)) (g I) (I j))
    (hg : ∀ I ∈ closedBall c r, c₁ ≤ |g I|) :
    volume (closedBall c r ∩ {I | |φ I| ≤ v}) ≤
      ENNReal.ofReal (2 * r) ^ m * ENNReal.ofReal (2 * v / c₁) := by
  set A := closedBall c r ∩ {I | |φ I| ≤ v} with hA
  have hAm : MeasurableSet A := by
    have : IsClosed (closedBall c r ∩ φ ⁻¹' Icc (-v) v) :=
      hφc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Icc
    have h2 : A = closedBall c r ∩ φ ⁻¹' Icc (-v) v := by
      ext I; simp [hA, abs_le]
    rw [h2]; exact this.measurableSet
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j with he
  have hmp : MeasurePreserving e.symm :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j).symm
  have hT : MeasurableSet (e.symm ⁻¹' A) := e.symm.measurable hAm
  have h1 : volume A = volume (e.symm ⁻¹' A) := (hmp.measure_preimage_equiv _).symm
  have hmemA : ∀ x y, x ∈ (fun x : ℝ => (x, y)) ⁻¹' (e.symm ⁻¹' A) ↔
      Fin.insertNth j x y ∈ A := fun x y => Iff.rfl
  set B : Set (Fin m → ℝ) := closedBall (fun l => c (j.succAbove l)) r with hB
  rw [h1, Measure.volume_eq_prod, Measure.prod_apply_symm hT]
  calc ∫⁻ y, volume ((fun x : ℝ => (x, y)) ⁻¹' (e.symm ⁻¹' A))
      ≤ ∫⁻ y, B.indicator (fun _ => ENNReal.ofReal (2 * v / c₁)) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ B
        · rw [Set.indicator_of_mem hy]
          refine (Real.volume_le_diam _).trans ?_
          refine Metric.ediam_le fun x hx x' hx' => ?_
          rw [hmemA] at hx hx'
          have hu : ∀ a t : ℝ, Function.update (Fin.insertNth (α := fun _ => ℝ) j a y) j t =
              Fin.insertNth (α := fun _ => ℝ) j t y := fun a t => by
            rw [Fin.update_insertNth]
          have key : ∀ {a b : ℝ}, Fin.insertNth j a y ∈ A → Fin.insertNth j b y ∈ A →
              a < b → b - a ≤ 2 * v / c₁ := by
            intro a b ha hb hab
            have := section_dist_le (P := Fin.insertNth j a y) (t₁ := a) (t₂ := b) (v := v) hr hφd
              hg
              (by rw [hu]; exact ha.1) (by rw [hu]; exact hb.1)
              (by rw [hu]; exact ha.2) (by rw [hu]; exact hb.2) hab
            rw [le_div_iff₀ hc₁]; linarith
          have hd : dist x x' ≤ 2 * v / c₁ := by
            rw [Real.dist_eq, abs_le]
            rcases lt_trichotomy x x' with hl | he' | hl
            · have := key hx hx' hl
              have h0 : 0 ≤ 2 * v / c₁ := by linarith [sub_pos.2 hl]
              constructor <;> linarith
            · subst he'
              have h0 : 0 ≤ 2 * v / c₁ := by
                have := hx.2
                simp only [mem_ofPred_eq] at this
                exact div_nonneg (by linarith [abs_nonneg (φ (Fin.insertNth j x y))]) hc₁.le
              constructor <;> simp <;> linarith
            · have := key hx' hx hl
              constructor <;> linarith
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal hd
        · rw [Set.indicator_of_notMem hy]
          refine le_of_eq_of_le (measure_mono_null ?_ measure_empty) le_rfl
          intro x hx
          rw [hmemA] at hx
          refine hy ?_
          have := (dist_pi_le_iff hr).1 (mem_closedBall.1 hx.1)
          rw [hB, mem_closedBall, dist_pi_le_iff hr]
          intro l
          simpa using this (j.succAbove l)
    _ = ENNReal.ofReal (2 * v / c₁) * volume B :=
        lintegral_indicator_const measurableSet_closedBall _
    _ = ENNReal.ofReal (2 * r) ^ m * ENNReal.ofReal (2 * v / c₁) := by
        rw [hB, Real.volume_pi_closedBall _ hr, Fintype.card_fin,
          ENNReal.ofReal_pow (by linarith), mul_comm]

end KAM.Nekhoroshev.AvgSlab

end
