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
  have hQ0 : 0 < 2 * π * α * min (r / 8 * (s / 6)) (rp / 8 * (rq / 8)) := by positivity
  have ht2 : (1 + (m : ℝ)) * E / (2 * π * α * min (r / 4 * (s / 3)) (rp / 4 * (rq / 4))) ≤
      q / 8 := by
    rw [hQeq, mul_comm 4, ← div_div]
    linarith
  have hq2 : q ≤ 1 / 2 := by
    have h1 : q ≤ Real.exp (-1) := Real.exp_le_exp.2 (by rw [neg_div]; linarith)
    have : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by have := exp_one_gt_27; linarith)
    linarith
  let c : OSched := ⟨⟨r, sbar + s, fun _ => r / 4, fun _ => s / 3⟩,
    ⟨rp, 0, fun _ => rp / 4, fun _ => 0⟩, ⟨rq, 0, fun _ => rq / 4, fun _ => 0⟩⟩
  let ε : ℕ → ℝ := fun i => if i = 0 then E else q * E
  have hε0 : ε 0 = E := by simp [ε]
  have hε1 : ε 1 = q * E := by simp [ε]
  refine ⟨c, ε, 0, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine oiter_of_hyp H c rfl rfl rfl rfl ε (by rw [hε0]) 0 ?_ ?_ ?_ ?_
    · intro i hi; obtain rfl : i = 0 := by omega
      show 0 < r / 4 ∧ 2 * (r / 4) < r ∧ 0 < rp / 4 ∧ 2 * (rp / 4) < rp ∧ 0 < rq / 4 ∧
        2 * (rq / 4) < rq ∧ 0 < s / 3 ∧ 2 * (s / 3) < sbar + s
      refine ⟨by positivity, by linarith, by positivity, by linarith, by positivity, by linarith,
        by positivity, by linarith⟩
    · intro i hi
      rcases Nat.lt_or_ge i 1 with h0 | h1
      · obtain rfl : i = 0 := by omega
        rw [hε0]; exact hE
      · obtain rfl : i = 1 := by omega
        rw [hε1]; positivity
    · intro i hi; obtain rfl : i = 0 := by omega
      show ε 0 ≤ (2 * π * α) * min (r / 4 * (s / 3)) (rp / 4 * (rq / 4)) / (16 * (1 + (m : ℝ)))
      rw [hε0, le_div_iff₀ (by positivity)]
      have h1 := (div_le_iff₀ hQ').1 ht1
      have : 0 ≤ (1 + (m : ℝ)) * E := by positivity
      nlinarith
    · intro i hi; obtain rfl : i = 0 := by omega
      have e2 : 2 * π * K * (s / 3) = κ / 3 := by rw [hκ]; ring
      have hx : Real.exp (-(κ / 3)) ≤ q / 2 := by
        have : Real.exp (-(κ / 3)) = q * q := by
          rw [hq, ← Real.exp_add]; congr 1; ring
        rw [this]; nlinarith
      have key := osc_step_single (Q := 2 * π * α * min (r / 4 * (s / 3)) (rp / 4 * (rq / 4)))
        (E := E) (b := 1 + (m : ℝ)) (q := q) (x := κ / 3) hQ' hE (by linarith) ht2 ht1 hx
      simpa [c, ε, e2] using key
  · show r / 2 ≤ r - 2 * (r / 4); linarith
  · show rp / 2 ≤ rp - 2 * (rp / 4); linarith
  · show rq / 2 ≤ rq - 2 * (rq / 4); linarith
  · show sbar + s / 6 ≤ sbar + s - 2 * (s / 3); linarith
  · rw [hε1]
  · simp only [Finset.range_zero, Finset.sum_empty]; positivity
  · rw [Finset.sum_range_one]
    show (2 * π * α) * s * (ε 0 / (exp 1 * (2 * π * α) * (s / 3))) ≤ 3 * E
    rw [hε0]
    have : (2 * π * α) * s * (E / (exp 1 * (2 * π * α) * (s / 3))) = 3 * E / exp 1 := by
      field_simp
    rw [this, div_le_iff₀ (by have := exp_one_gt_27; linarith)]
    have := exp_one_gt_27
    nlinarith
  · rw [Finset.sum_range_one]
    show (2 * π * α) * r * (ε 0 / (2 * π * α * (r / 4))) ≤ 9 * E
    rw [hε0]
    have : (2 * π * α) * r * (E / (2 * π * α * (r / 4))) = 4 * E := by field_simp
    rw [this]; linarith
  · rw [Finset.sum_range_one]
    show (2 * π * α) * rq * (ε 0 / (2 * π * α * (rq / 4))) ≤ 9 * E
    rw [hε0]
    have : (2 * π * α) * rq * (E / (2 * π * α * (rq / 4))) = 4 * E := by field_simp
    rw [this]; linarith
  · rw [Finset.sum_range_one]
    show (2 * π * α) * rp * (ε 0 / (2 * π * α * (rp / 4))) ≤ 9 * E
    rw [hε0]
    have : (2 * π * α) * rp * (E / (2 * π * α * (rp / 4))) = 4 * E := by field_simp
    rw [this]; linarith

end Single

end KAM.Planetary

end
