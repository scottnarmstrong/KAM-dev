/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.FiniteNumerics

/-!
# P Part 2: the numerical inequalities of the oscillator finite averaging iteration
(`stepP:p2:oa-first`, `stepP:p2:oa-iter`, `stepP:p2:oa-concl`)

Pure real-number lemmas, with the oscillator factor `b = 1 + m`: the first step (cases A and B),
the inductive step with ratio `1/4`, the stage budget `b δ / Q`, and the bounds of the first
remainder `c₁ = 293 b E² / P`. No operator analysis enters here.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3, package P23-15.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Planetary

theorem exp_one_lt_3 : Real.exp 1 < 3 := by
  have := Real.exp_one_lt_d9
  linarith

/-- `(1 - x)⁻¹ ≤ (1 - c)⁻¹` for `x ≤ c < 1`. -/
theorem inv_one_sub_le' {x c : ℝ} (hx : x ≤ c) (hc : c < 1) : (1 - x)⁻¹ ≤ (1 - c)⁻¹ :=
  inv_anti₀ (by linarith) (by linarith)

/-- First step, case A: the remainder is at most `(32/7) t E` with `t = b E / Q`. -/
theorem osc_step_first {Q E b q κ : ℝ} (hQ : 0 < Q) (hE : 0 ≤ E) (hb : 0 ≤ b) (hκ : 6 ≤ κ)
    (ht : b * E / Q ≤ 1 / (64 * κ)) (hq0 : 0 ≤ q) (hq : q ≤ 2 * (b * E / Q)) :
    (1 - 2 * Real.exp 1 * b * E / Q)⁻¹ * (2 * b / Q * (0 + E) + q) * E ≤
      32 / 7 * (b * E / Q) * E := by
  set t := b * E / Q with htd
  have ht0 : 0 ≤ t := by positivity
  have hκ0 : 0 < κ := by linarith
  have ht384 : t ≤ 1 / 384 := ht.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have h1 : 2 * Real.exp 1 * b * E / Q = 2 * Real.exp 1 * t := by rw [htd]; ring
  have h2 : 2 * b / Q * (0 + E) = 2 * t := by rw [htd]; ring
  rw [h1, h2]
  have he := exp_one_lt_3
  have het : Real.exp 1 * t ≤ 3 * (1 / 384) := mul_le_mul he.le ht384 ht0 (by norm_num)
  have hinv : (1 - 2 * Real.exp 1 * t)⁻¹ ≤ 8 / 7 := by
    have : (7 / 8 : ℝ) ≤ 1 - 2 * Real.exp 1 * t := by linarith
    calc (1 - 2 * Real.exp 1 * t)⁻¹ ≤ (7 / 8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
      _ = 8 / 7 := by norm_num
  have h5 : (1 - 2 * Real.exp 1 * t)⁻¹ * (2 * t + q) ≤ 8 / 7 * (4 * t) :=
    mul_le_mul hinv (by linarith) (by positivity) (by norm_num)
  calc (1 - 2 * Real.exp 1 * t)⁻¹ * (2 * t + q) * E ≤ 8 / 7 * (4 * t) * E :=
        mul_le_mul_of_nonneg_right h5 hE
    _ = 32 / 7 * t * E := by ring

/-- First step, case B (single doubled-loss step): the remainder is at most `q E`. -/
theorem osc_step_single {Q E b q x : ℝ} (hQ : 0 < Q) (hE : 0 ≤ E) (hb : 0 ≤ b)
    (hu : b * E / Q ≤ q / 8) (hu2 : b * E / Q ≤ 1 / 1536) (hx : Real.exp (-x) ≤ q / 2) :
    (1 - 2 * Real.exp 1 * b * E / Q)⁻¹ * (2 * b / Q * (0 + E) + Real.exp (-x)) * E ≤ q * E := by
  set t := b * E / Q with htd
  have ht0 : 0 ≤ t := by positivity
  have h1 : 2 * Real.exp 1 * b * E / Q = 2 * Real.exp 1 * t := by rw [htd]; ring
  have h2 : 2 * b / Q * (0 + E) = 2 * t := by rw [htd]; ring
  rw [h1, h2]
  have he := exp_one_lt_3
  have het : Real.exp 1 * t ≤ 3 * (1 / 1536) := mul_le_mul he.le hu2 ht0 (by norm_num)
  have hinv : (1 - 2 * Real.exp 1 * t)⁻¹ ≤ 32 / 31 := by
    have : (31 / 32 : ℝ) ≤ 1 - 2 * Real.exp 1 * t := by linarith
    calc (1 - 2 * Real.exp 1 * t)⁻¹ ≤ (31 / 32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
      _ = 32 / 31 := by norm_num
  have hq0 : 0 ≤ q := by linarith [ht0, hu]
  have h5 : (1 - 2 * Real.exp 1 * t)⁻¹ * (2 * t + Real.exp (-x)) ≤ 32 / 31 * (3 / 4 * q) :=
    mul_le_mul hinv (by linarith) (by positivity) (by norm_num)
  calc (1 - 2 * Real.exp 1 * t)⁻¹ * (2 * t + Real.exp (-x)) * E ≤ q * E :=
      mul_le_mul_of_nonneg_right (h5.trans (by linarith)) hE

/-- The inductive step: ratio `1/4`. -/
theorem osc_step_big {Q δ b st x : ℝ} (hQ : 0 < Q) (hδ0 : 0 ≤ δ) (hb : 0 ≤ b) (hst0 : 0 ≤ st)
    (hδ : b * δ / Q ≤ 1 / 1024) (hst : b * (st + δ) / Q ≤ 1 / 32)
    (hx : Real.exp (-x) ≤ 1 / 8) :
    (1 - 2 * Real.exp 1 * b * δ / Q)⁻¹ * (2 * b / Q * (st + δ) + Real.exp (-x)) * δ ≤ δ / 4 := by
  set t := b * δ / Q with htd
  have ht0 : 0 ≤ t := by positivity
  have h1 : 2 * Real.exp 1 * b * δ / Q = 2 * Real.exp 1 * t := by rw [htd]; ring
  have h2 : 2 * b / Q * (st + δ) = 2 * (b * (st + δ) / Q) := by ring
  rw [h1, h2]
  have he := exp_one_lt_3
  have het : Real.exp 1 * t ≤ 3 * (1 / 1024) := mul_le_mul he.le hδ ht0 (by norm_num)
  have hinv : (1 - 2 * Real.exp 1 * t)⁻¹ ≤ 128 / 127 := by
    have : (127 / 128 : ℝ) ≤ 1 - 2 * Real.exp 1 * t := by linarith
    calc (1 - 2 * Real.exp 1 * t)⁻¹ ≤ (127 / 128 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
      _ = 128 / 127 := by norm_num
  have h5 : (1 - 2 * Real.exp 1 * t)⁻¹ * (2 * (b * (st + δ) / Q) + Real.exp (-x)) ≤
      128 / 127 * (1 / 16 + 1 / 8) :=
    mul_le_mul hinv (by linarith) (by positivity) (by norm_num)
  calc (1 - 2 * Real.exp 1 * t)⁻¹ * (2 * (b * (st + δ) / Q) + Real.exp (-x)) * δ
      ≤ (1 / 4) * δ := mul_le_mul_of_nonneg_right (h5.trans (by norm_num)) hδ0
    _ = δ / 4 := by ring

/-- The first remainder bound of the multi-step schedule. -/
def firstEps (b E P : ℝ) : ℝ := 293 * b * E ^ 2 / P

theorem firstEps_nonneg {b E P : ℝ} (hb : 0 ≤ b) (hP : 0 ≤ P) : 0 ≤ firstEps b E P := by
  unfold firstEps; positivity

/-- `c₁ ≤ 293 E / (4096 κ)`. -/
theorem firstEps_le {b E P κ : ℝ} (hE : 0 ≤ E) (hP : 0 < P) (hκ : 0 < κ)
    (hEP : 4096 * b * E * κ ≤ P) : firstEps b E P ≤ 293 * E / (4096 * κ) := by
  unfold firstEps
  rw [div_le_div_iff₀ hP (by positivity)]
  have := mul_le_mul_of_nonneg_left hEP (by positivity : 0 ≤ 293 * E)
  nlinarith

/-- The first step, case A, produces at most `c₁`. -/
theorem osc_first_le {Q E b P : ℝ} (hQ : 0 < Q) (hE : 0 ≤ E) (hb : 0 ≤ b) (hP : 0 < P)
    (hQP : P / 64 ≤ Q) : 32 / 7 * (b * E / Q) * E ≤ firstEps b E P := by
  unfold firstEps
  have h1 : b * E / Q ≤ 64 * b * E / P := by
    rw [div_le_div_iff₀ hQ hP]
    have : 0 ≤ b * E := mul_nonneg hb hE
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).1 hQP
    nlinarith
  have h2 : 32 / 7 * (b * E / Q) * E ≤ 32 / 7 * (64 * b * E / P) * E := by gcongr
  have h3 : 32 / 7 * (64 * b * E / P) * E = (2048 / 7 * (b * E ^ 2)) / P := by ring
  rw [h3] at h2
  refine h2.trans ?_
  have : 293 * b * E ^ 2 = 293 * (b * E ^ 2) := by ring
  rw [this]
  exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hb (sq_nonneg E)]) hP.le

/-- The numerical budget of every stage after the first: `b δ / Q ≤ 1/1024`,
`b (st + δ) / Q ≤ 1/32`. -/
theorem multi_stage_num {b E P κ N Q δ st : ℝ} (hb : 1 ≤ b) (hE : 0 ≤ E) (hP : 0 < P)
    (hN : 1 ≤ N) (hNκ : 8 * N < κ) (hEP : 4096 * b * E * κ ≤ P) (hQ : P / (64 * N ^ 2) ≤ Q)
    (hδ : δ ≤ firstEps b E P)
    (hst : st ≤ 3 * E / (4 * N) + 4 * firstEps b E P / 9) :
    b * δ / Q ≤ 1 / 1024 ∧ b * (st + δ) / Q ≤ 1 / 32 := by
  have hb0 : 0 < b := by linarith
  have hN0 : 0 < N := by linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  set Y := b * E * N / P with hY
  have hY0 : 0 ≤ Y := by positivity
  have hY1 : Y ≤ 1 / 32768 := by
    rw [hY, div_le_div_iff₀ hP (by norm_num)]
    have := mul_nonneg hb0.le hE
    nlinarith
  have hY2 : Y ^ 2 ≤ (1 / 32768) ^ 2 := pow_le_pow_left₀ hY0 hY1 2
  have hinvQ : 1 / Q ≤ 64 * N ^ 2 / P := by
    rw [div_le_div_iff₀ hQ0 hP]
    have := (div_le_iff₀ (by positivity)).1 hQ
    nlinarith
  have hc1 : 0 ≤ firstEps b E P := firstEps_nonneg hb0.le hP.le
  have hbc : b * firstEps b E P / Q ≤ 64 * 293 * Y ^ 2 := by
    calc b * firstEps b E P / Q = b * firstEps b E P * (1 / Q) := by ring
      _ ≤ b * firstEps b E P * (64 * N ^ 2 / P) :=
          mul_le_mul_of_nonneg_left hinvQ (by positivity)
      _ = 64 * 293 * Y ^ 2 := by
          rw [hY]; unfold firstEps; field_simp
  have hE' : b * (3 * E / (4 * N)) / Q ≤ 48 * Y := by
    calc b * (3 * E / (4 * N)) / Q = b * (3 * E / (4 * N)) * (1 / Q) := by ring
      _ ≤ b * (3 * E / (4 * N)) * (64 * N ^ 2 / P) :=
          mul_le_mul_of_nonneg_left hinvQ (by positivity)
      _ = 48 * Y := by rw [hY]; field_simp; ring
  have hbδ : b * δ / Q ≤ b * firstEps b E P / Q := by gcongr
  refine ⟨?_, ?_⟩
  · have : 64 * 293 * Y ^ 2 ≤ 64 * 293 * (1 / 32768) ^ 2 := by gcongr
    refine hbδ.trans (hbc.trans (this.trans ?_))
    norm_num
  · have h1 : b * (st + δ) / Q ≤
        b * (3 * E / (4 * N)) / Q + (13 / 9) * (b * firstEps b E P / Q) := by
      have : b * (st + δ) ≤ b * (3 * E / (4 * N)) + (13 / 9) * (b * firstEps b E P) := by
        nlinarith
      calc b * (st + δ) / Q ≤ (b * (3 * E / (4 * N)) + (13 / 9) * (b * firstEps b E P)) / Q :=
            div_le_div_of_nonneg_right this hQ0.le
        _ = _ := by ring
    have h2 : 64 * 293 * Y ^ 2 ≤ 64 * 293 * (1 / 32768) ^ 2 := by gcongr
    refine h1.trans ?_
    have h3 : (13 / 9) * (b * firstEps b E P / Q) ≤ (13 / 9) * (64 * 293 * (1 / 32768) ^ 2) := by
      gcongr
      exact hbc.trans h2
    have : 48 * Y ≤ 48 * (1 / 32768) := by gcongr
    norm_num at h3 this ⊢
    linarith

end KAM.Planetary

end
