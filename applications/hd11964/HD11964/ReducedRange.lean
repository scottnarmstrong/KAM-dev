/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import HD11964.NoCrossing
public import KAM.Application.LambdaDrift.ReducedRange

/-!
# HD 11964: the reduced actions and their range against the heliocentric actions on `R(r)`

Scoping note `docs/tracks/LP/REDUCED-MASS-SCOPE.md` §0 and §4, for HD 11964.

The observable of the reduced-mass bridge is the reduced Delaunay action in the chart,
`G_i(w) = keplerAction (redMass ν μ) (Ψ w) i` (`reducedAction`), which is `Λ^red_i`
(`reducedAction_eq`, from `keplerAction_redMass`).

`reducedAction_sub_mem_region` bounds `G_i - Λ_i` on the fixed set `R(r)` (`HD11964.region rTube`:
actions in `[Λlo - r, Λhi + r]`, chart AMD at most `1/100 + 2r`) analytically, with no cell: the
AMD bounds the eccentricities (`e_c ≤ 93/125`, `e_b ≤ 71/500`) and
`KAM.Application.LambdaDrift.chart_reducedAction_sub_bounds` bounds `G_i - Λ_i` by them. The
rational bounds `loGan`, `hiGan` give the widths `1.4 · 10⁻⁵` (c) and `2.73 · 10⁻⁴` (b); the
note's first-order figure at the nominal `e_b ≈ 0.1` is `1.9 · 10⁻⁴`, and the AMD budget
`1/100 + 2r` allows `e_b` up to `0.142`.

A positive lower bound for `G_i` follows, so `G_i` is continuous on `R(r)`
(`continuousOn_reducedAction`): a positive reduced action forces a negative reduced energy, which
is continuous off collisions.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift

namespace HD11964

theorem mu_nonneg : 0 ≤ mu := by norm_num [mu]

/-- The observable: the reduced Delaunay actions in the chart,
`G_i(w) = keplerAction (redMass ν μ) (Ψ w) i`. -/
def reducedAction (i : Fin 2) (w : Phase (2 + 2)) : ℝ :=
  keplerAction (redMass nu mu) (poincareProd nu 1 w) i

/-- `G_i` is the reduced Delaunay action `Λ^red_i` of the chart image (scoping note §0). -/
theorem reducedAction_eq (i : Fin 2) (w : Phase (2 + 2)) :
    reducedAction i w = reducedDelaunayAction nu mu (poincareProd nu 1 w) i :=
  keplerAction_redMass (nu_pos i) (one_add_mul_pos nu_pos mu_nonneg i) _

/-- Lower ends of the analytic range of `G_i - Λ_i` on `R(r)`. -/
def loGan : Fin 2 → ℚ := ![-1 / 500000, -117 / 1000000]

/-- Upper ends of the analytic range of `G_i - Λ_i` on `R(r)`. -/
def hiGan : Fin 2 → ℚ := ![3 / 250000, 39 / 250000]

theorem lpGamma_le_chartAMD (w : Phase (2 + 2)) (i : Fin 2) : lpGamma w i ≤ chartAMD w := by
  rw [chartAMD_eq_sum_lpGamma]
  exact Finset.single_le_sum (f := lpGamma w) (fun j _ => by unfold lpGamma; positivity)
    (Finset.mem_univ i)

/-- **The range of `G_i - Λ_i` on `R(r)`, analytically:** `loGan_i ≤ G_i - Λ_i ≤ hiGan_i`. -/
theorem reducedAction_sub_mem_region {i : Fin 2} {w : Phase (2 + 2)} (hw : w ∈ region rTube) :
    (loGan i : ℝ) ≤ reducedAction i w - fast w.2 i ∧
      reducedAction i w - fast w.2 i ≤ hiGan i := by
  obtain ⟨hs, hΛ, hA⟩ := hw
  have hdom := chartSafe_subset_dom nu hs
  have hΓ : lpGamma w i ≤ cBar + 2 * rTube := (lpGamma_le_chartAMD w i).trans hA
  unfold reducedAction
  fin_cases i
  · obtain ⟨hlo, hhi⟩ := chart_reducedAction_sub_bounds nu_pos mu_nonneg hdom 0
      (e := 93 / 125) (by norm_num [lamLo, rTube]) (hΛ 0) hΓ
      (by norm_num [lamLo, rTube, cBar]) (by norm_num) (by norm_num [lamLo, rTube, cBar])
      (by norm_num [mu, nu]) (by norm_num [mu, nu])
    refine ⟨le_trans ?_ hlo, hhi.trans ?_⟩
    · exact le_mul_one_div_sqrt_sub_one (by norm_num [lamHi, rTube]) (by norm_num [mu, nu])
        (by norm_num [loGan, lamHi, rTube]) (by norm_num [loGan, lamHi, rTube, mu, nu])
    · exact mul_one_div_sqrt_sub_one_le (by norm_num [lamHi, rTube]) (by norm_num [mu, nu])
        (by norm_num [hiGan, lamHi, rTube]) (by norm_num [hiGan, lamHi, rTube, mu, nu])
  · obtain ⟨hlo, hhi⟩ := chart_reducedAction_sub_bounds nu_pos mu_nonneg hdom 1
      (e := 71 / 500) (by norm_num [lamLo, rTube]) (hΛ 1) hΓ
      (by norm_num [lamLo, rTube, cBar]) (by norm_num) (by norm_num [lamLo, rTube, cBar])
      (by norm_num [mu, nu]) (by norm_num [mu, nu])
    refine ⟨le_trans ?_ hlo, hhi.trans ?_⟩
    · exact le_mul_one_div_sqrt_sub_one (by norm_num [lamHi, rTube]) (by norm_num [mu, nu])
        (by norm_num [loGan, lamHi, rTube]) (by norm_num [loGan, lamHi, rTube, mu, nu])
    · exact mul_one_div_sqrt_sub_one_le (by norm_num [lamHi, rTube]) (by norm_num [mu, nu])
        (by norm_num [hiGan, lamHi, rTube]) (by norm_num [hiGan, lamHi, rTube, mu, nu])

/-- `G_i` is positive on `R(r)`: `G_i ≥ Λ_i + loGan_i ≥ Λlo_i - r + loGan_i > 0`. -/
theorem reducedAction_pos {i : Fin 2} {w : Phase (2 + 2)} (hw : w ∈ region rTube) :
    0 < reducedAction i w := by
  have h1 := (reducedAction_sub_mem_region (i := i) hw).1
  have h2 := (hw.2.1 i).1
  have h3 : (0 : ℝ) < lamLo i - rTube + loGan i := by
    fin_cases i <;> norm_num [lamLo, rTube, loGan]
  linarith

/-- `G_i` is continuous at a chart point of `chartSafe ν` where it is positive: there the reduced
Kepler energy is not zero, and it is continuous off collisions. -/
theorem continuousAt_reducedAction {i : Fin 2} {w : Phase (2 + 2)} (hw : w ∈ chartSafe nu)
    (hpos : 0 < reducedAction i w) : ContinuousAt (reducedAction i) w := by
  have hΨ : ContinuousAt (poincareProd nu 1) w :=
    ((analyticOnNhd_poincareProd nu_pos one_pos) w (chartSafe_subset_dom nu hw)).continuousAt
  have hq : 0 < planeLength (bodyVector (poincareProd nu 1 w).1 i) :=
    ((sec_domain_chart_facts nu_pos (chartSafe_subset_dom nu hw)).1 i).2.1
  have hE : keplerEnergy (redMass nu mu) (poincareProd nu 1 w) i ≠ 0 := by
    intro h0
    have : reducedAction i w = 0 := by
      simp [reducedAction, keplerAction, keplerAxis, h0]
    linarith
  have hEc := continuousAt_keplerEnergy' (redMass nu mu) i hq
  have hA : ContinuousAt (fun z : Phase (2 * 2) => keplerAction (redMass nu mu) z i)
      (poincareProd nu 1 w) := by
    unfold keplerAction keplerAxis
    exact continuousAt_const.mul
      ((continuousAt_const.div (continuousAt_const.mul hEc) (mul_ne_zero two_ne_zero hE)).sqrt)
  exact hA.comp hΨ

/-- `G_i` is continuous on `R(r)`. -/
theorem continuousOn_reducedAction (i : Fin 2) : ContinuousOn (reducedAction i) (region rTube) :=
  fun _ hw => (continuousAt_reducedAction hw.1 (reducedAction_pos hw)).continuousWithinAt

end HD11964

end
