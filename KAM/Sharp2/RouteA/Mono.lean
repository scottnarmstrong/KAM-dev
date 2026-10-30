/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Data
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `routeAOk` is monotone in `X⋆`

(J1)–(J3) hold at every `0 ≤ X ≤ X⋆` when they hold at `X⋆`: a smaller threshold is always
legal. `routeAOk.mono` is what lets the default-data wrappers meet the separate torsion smallness
by shrinking `X⋆` (`g1_v2A_default`), so that this smallness is no longer an outside input.
-/

@[expose] public section

open KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA

theorem xA_mono {a : ℝ} {CE : ℕ → ℝ} (hCE : ∀ s, 0 ≤ CE s) {X Y : ℝ} (h0 : 0 ≤ X) (hXY : X ≤ Y)
    (s : ℕ) : 0 ≤ xA a CE X s ∧ xA a CE X s ≤ xA a CE Y s := by
  induction s with
  | zero => exact ⟨h0, hXY⟩
  | succ s ih =>
    have hc : 0 ≤ (2 : ℝ) ^ (2 * a) * CE s :=
      mul_nonneg (Real.rpow_nonneg zero_le_two _) (hCE s)
    exact ⟨mul_nonneg hc (sq_nonneg _),
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ih.1 ih.2 2) hc⟩

theorem sumA_mono {a lam ρ ρinf γb b : ℝ} {x y c : ℕ → ℝ} (hc : ∀ s, 0 ≤ c s)
    (hd : ∀ s, 0 ≤ deltaSeq lam ρ ρinf s) (hxy : ∀ s, x s ≤ y s) (kp : ℕ) :
    sumA a lam ρ ρinf γb x c b kp ≤ sumA a lam ρ ρinf γb y c b kp := by
  have hw : ∀ t, 0 ≤ γb ^ 2 * deltaSeq lam ρ ρinf t ^ (2 * a - b) := fun t =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hd t) _)
  unfold sumA
  refine add_le_add (Finset.sum_le_sum fun t _ => ?_) ?_
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hxy t) (hc t)) (hw t)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hxy kp) (mul_nonneg two_pos.le (hc kp))) (hw kp)

/-- (J1)–(J3) pass to every smaller threshold. -/
theorem routeAOk.mono {N : NumA} (hN : N.Wf) {σ m₀ : Fin 8 → ℝ} {X Y : ℝ}
    (h : routeAOk N σ m₀ Y) (h0 : 0 ≤ X) (hXY : X ≤ Y) : routeAOk N σ m₀ X := by
  have hCE : ∀ s, 0 ≤ (N.stage s).CE := fun s => (hN.pos s).CE
  have hx : ∀ s, 0 ≤ N.xS X s ∧ N.xS X s ≤ N.xS Y s := xA_mono hCE h0 hXY
  refine ⟨h0, fun s hs => (h.J1 s hs).down (hN.pos s) (hx s).2,
    h.J1t.down (hN.pos _) (hx _).2, ?_, fun i => ?_⟩
  · refine le_trans ?_ h.J2
    exact mul_le_mul_of_nonneg_left (hx _).2
      (mul_nonneg (Real.rpow_nonneg zero_le_two _) (hCE _))
  · refine le_trans (add_le_add le_rfl ?_) (h.J3 i)
    exact sumA_mono (fun s => NumA.rateV_nonneg (hN.pos s) i) (fun s => (hN.δ_pos s).le)
      (fun s => (hx s).2) _

end KAM.Sharp2.RouteA

end
