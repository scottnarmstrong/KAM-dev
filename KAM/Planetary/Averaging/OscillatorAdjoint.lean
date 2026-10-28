/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Canonical.Adjoint
public import KAM.Planetary.Averaging.OscillatorBracket
public import KAM.Planetary.Averaging.OscillatorSeriesAlgebra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# P Parts 2-3: the oscillator adjoint estimate (`stepP:p2:oi-ratio`)

`oscLieRatio`, `oscTheta`, `osc_ratio_range` and `osc_adjoint_bound`: for `h ≥ 1` the `h`-fold
iterated bracket `ad_φ^h u` is estimated by `h` applications of `osc_bracket`, each with the
losses `(ρ, ρp, ρq, σ)/h` and the generator on its original (outer) domain. At step `i` all four
outer-to-inner ratios are at most `1/(h+1+i)` and the minimum product is `d/h²`, so the step
constant is at most `c_m h² Φ / (d (h+1+i))` with `c_m = 2 (1/e + m)`. The product of the step
constants is `(c_m h² Φ/d)^h h!/(2h)!`, and `(2h)! ≥ (2h/e)^(2h)` gives
`|ad_φ^h u / h!| ≤ q^h A` with `q = e (1 + e m) Φ / (2 d)`. The case `h = 0` is a restriction.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13c.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real Finset

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

def oscLieRatio (m : ℕ) (Φ d : ℝ) : ℝ := exp 1 * (1 + exp 1 * m) * Φ / (2 * d)
def oscTheta (m : ℕ) (Φ d : ℝ) : ℝ := 2 * exp 1 * (1 + (m : ℝ)) * Φ / d

theorem osc_ratio_range (m : ℕ) {Φ d : ℝ} (hd : 0 < d) (hΦ : 0 ≤ Φ)
    (hs : Φ ≤ d / (16 * (1 + (m : ℝ)))) :
    0 ≤ oscLieRatio m Φ d ∧ oscLieRatio m Φ d ≤ oscTheta m Φ d ∧
    oscTheta m Φ d ≤ exp 1 / 8 ∧
    (16 / 9 : ℝ) * oscTheta m Φ d < 1 ∧ Φ / d ≤ 1 / 4 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have he : 0 < exp 1 := exp_pos 1
  have he4 : exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hb : (0 : ℝ) < 1 + m := by positivity
  set x : ℝ := Φ / d with hx
  have hx0 : 0 ≤ x := div_nonneg hΦ hd.le
  have hxb : x * (16 * (1 + (m : ℝ))) ≤ 1 := by
    rw [hx, div_mul_eq_mul_div, div_le_one hd]
    rwa [le_div_iff₀ (by positivity)] at hs
  have hL : oscLieRatio m Φ d = exp 1 * (1 + exp 1 * m) * x / 2 := by
    unfold oscLieRatio; rw [hx]; field_simp
  have hT : oscTheta m Φ d = 2 * exp 1 * (1 + (m : ℝ)) * x := by
    unfold oscTheta; rw [hx]; field_simp
  rw [hL, hT]
  have hem : exp 1 * m ≤ 4 * m := by nlinarith
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · have : exp 1 * (1 + exp 1 * m) / 2 ≤ 2 * exp 1 * (1 + (m : ℝ)) := by nlinarith
    calc exp 1 * (1 + exp 1 * m) * x / 2 = exp 1 * (1 + exp 1 * m) / 2 * x := by ring
      _ ≤ 2 * exp 1 * (1 + (m : ℝ)) * x := mul_le_mul_of_nonneg_right this hx0
  · have h8 : 2 * exp 1 * (1 + (m : ℝ)) * x ≤ exp 1 / 8 := by
      nlinarith [mul_nonneg he.le (sub_nonneg.2 hxb)]
    exact h8
  · have h8 : 2 * exp 1 * (1 + (m : ℝ)) * x ≤ exp 1 / 8 := by
      nlinarith [mul_nonneg he.le (sub_nonneg.2 hxb)]
    nlinarith
  · nlinarith [mul_nonneg hx0 hm]

end KAM.Planetary

end
