/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# P Part 4: Tonelli for short sections (`bpP:p4:ext-tonelli`)

`section_measure_le_of_pairwise_dist` bounds the Lebesgue measure of an arbitrary subset of `ℝ`
of diameter at most `δ`, and `ext_tonelli` is Tonelli on `(Fin m → ℝ) × ℝ`: a measurable set
whose vertical sections all have measure at most `δ` and which lies over `P` has measure at most
`δ * volume P`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-TO.
-/

public section

open Set MeasureTheory

namespace KAM.Planetary

theorem section_measure_le_of_pairwise_dist {E : Set ℝ} {delta : ℝ}
    (hd : 0 ≤ delta)
    (hE : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ delta) :
    volume E ≤ ENNReal.ofReal delta := by
  have _ := hd
  rcases E.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp
  have hbdd : BddBelow E := ⟨x0 - delta, fun y hy => by
    have := hE x0 hx0 y hy
    rw [Real.dist_eq, abs_le] at this
    linarith [this.1]⟩
  have hsub : E ⊆ Icc (sInf E) (sInf E + delta) := by
    intro y hy
    refine ⟨csInf_le hbdd hy, ?_⟩
    have : y - delta ≤ sInf E := le_csInf ⟨x0, hx0⟩ (fun x hx => by
      have := hE y hy x hx
      rw [Real.dist_eq, abs_le] at this
      linarith [this.1])
    linarith
  calc volume E ≤ volume (Icc (sInf E) (sInf E + delta)) := measure_mono hsub
    _ = ENNReal.ofReal delta := by simp

theorem ext_tonelli {m : ℕ} {R : Set ((Fin m → ℝ) × ℝ)} (hR : MeasurableSet R)
    {P : Set (Fin m → ℝ)} (hP : MeasurableSet P) (hsub : R ⊆ P ×ˢ univ)
    {delta : ℝ} (hd : 0 ≤ delta)
    (hsections : ∀ x : Fin m → ℝ, volume {t : ℝ | (x,t) ∈ R} ≤ ENNReal.ofReal delta) :
    volume R ≤ ENNReal.ofReal delta * volume P := by
  have _ := hd
  rw [Measure.volume_eq_prod, Measure.prod_apply hR]
  calc ∫⁻ x, (volume : Measure ℝ) (Prod.mk x ⁻¹' R) ∂(volume : Measure (Fin m → ℝ))
      ≤ ∫⁻ x, P.indicator (fun _ => ENNReal.ofReal delta) x ∂(volume : Measure (Fin m → ℝ)) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ P
        · rw [Set.indicator_of_mem hx]; exact hsections x
        · have : Prod.mk x ⁻¹' R = ∅ := by
            ext t
            simp only [mem_preimage, mem_empty_iff_false, iff_false]
            intro ht
            exact hx (hsub ht).1
          simp [this, hx]
    _ = ENNReal.ofReal delta * volume P := by
        rw [lintegral_indicator hP]
        simp

end KAM.Planetary
