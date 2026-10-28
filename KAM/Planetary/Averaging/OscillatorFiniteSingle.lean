/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.OscillatorFiniteSetup

/-!
# P Part 2: the single doubled-loss step of oscillator averaging (`stepP:p2:oa-first`, Case B)

When `e^{-κ/6} > 2 b y₀` one step with losses `(r/4, rp/4, rq/4, s/3)` already brings the
remainder below `e^{-κ/6} E`. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3,
package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Single

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq sbar s K α E : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : CHam (n + m)}

/-- The single doubled-loss step. -/
theorem oscGood_single (H : OscHyp D r rp rq sbar s K α E h f)
    (hB : 2 * ((1 + (m : ℝ)) * E /
        (2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)))) <
      Real.exp (-(2 * π * K * s) / 6)) :
    OscGood D r rp rq sbar s K α E h f := by
  obtain ⟨hr, hrp, hrq, hs, hK, hα⟩ := H.positive
  have hE := H.E_nonneg
  have hsb := H.sbar_nonneg
  have hbud := H.budget
  have hEP := osc_E_le H
  have hb : (1 : ℝ) ≤ 1 + (m : ℝ) := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hπ := Real.pi_pos
  set κ : ℝ := 2 * π * K * s with hκ
  set q : ℝ := Real.exp (-κ / 6) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hd : 0 < min (r * s) (rp * rq) := lt_min (mul_pos hr hs) (mul_pos hrp hrq)
  have hd0 : 0 < min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) :=
    lt_min (by positivity) (by positivity)
  have hd' : min (r / 4 * (s / 3)) (rp / 4 * (rq / 4)) =
      4 * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1 <;> ring
  have hdd : min (r * s) (rp * rq) / 16 ≤ min (r / 4 * (s / 3)) (rp / 4 * (rq / 4)) := by
    refine le_min ?_ ?_
    · have := min_le_left (r * s) (rp * rq); nlinarith
    · have := min_le_right (r * s) (rp * rq); nlinarith
  have hQ' : 0 < 2 * π * α * min (r / 4 * (s / 3)) (rp / 4 * (rq / 4)) := by
    rw [hd']; positivity
  have hQP : 2 * π * α * min (r * s) (rp * rq) / 16 ≤
      2 * π * α * min (r / 4 * (s / 3)) (rp / 4 * (rq / 4)) := by
    have := mul_le_mul_of_nonneg_left hdd (by positivity : (0 : ℝ) ≤ 2 * π * α)
    linarith
  have hQeq : 2 * π * α * min (r / 4 * (s / 3)) (rp / 4 * (rq / 4)) =
      4 * (2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8))) := by rw [hd']; ring
  have ht1 : (1 + (m : ℝ)) * E / (2 * π * α * min (r / 4 * (s / 3)) (rp / 4 * (rq / 4))) ≤
      1 / 1536 := by
    rw [div_le_div_iff₀ hQ' (by norm_num)]
    have h1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).1 hQP
    have h2 : 0 ≤ (1 + (m : ℝ)) * E := by positivity
    nlinarith
  have ht2 : (1 + (m : ℝ)) * E / (2 * π * α * min (r / 4 * (s / 3)) (rp / 4 * (rq / 4))) ≤
      q / 8 := by
    rw [hQeq, ← div_div]
    have := (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2 hB
    sorry
  sorry

end Single

end KAM.Planetary

end
