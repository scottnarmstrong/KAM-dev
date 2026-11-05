/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Abstract pull-back estimates for `y + N y = u` (blueprint-W `bpW:w5:pullback`, steps `p-inv`,
`p-ass`)

For a function `ν` with `ν(x+y) ≤ ν x + ν y`, `ν(-x) = ν x`: if `y + N y = u` and `ν(N y) ≤ q ν(y)`
then
`ν(y) ≤ ν(u)/(1-q)`; and for two solutions with the second operator `q`-contractive for `ν`,
`ν(y₁ - y₂) ≤ (ν(u₁ - u₂) + ν((N₁ - N₂) y₁))/(1-q)`. These are the inverse-free forms of
`‖(Dφ)⁻¹‖ ≤ 2` and `Δ(Dφ)⁻¹ = -(Dφ_ξ)⁻¹ ΔDφ (Dφ_ζ)⁻¹`.
-/

@[expose] public section

namespace KAM.Wave

variable {G : Type*} [AddCommGroup G] {ν : G → ℝ}

theorem seminorm_solve_le (hadd : ∀ x y, ν (x + y) ≤ ν x + ν y) (hneg : ∀ x, ν (-x) = ν x)
    (hnn : ∀ x, 0 ≤ ν x) {N : G → G} {q : ℝ} (hq : q < 1) {y u : G} (hy : y + N y = u)
    (hN : ν (N y) ≤ q * ν y) : ν y ≤ ν u / (1 - q) := by
  have h : y = u + (-(N y)) := by rw [← hy]; abel
  have h1 : ν y ≤ ν u + q * ν y := by
    calc ν y = ν (u + (-(N y))) := by rw [← h]
      _ ≤ ν u + ν (-(N y)) := hadd _ _
      _ = ν u + ν (N y) := by rw [hneg]
      _ ≤ ν u + q * ν y := by linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hnn y]

theorem seminorm_solve_sub_le (hadd : ∀ x y, ν (x + y) ≤ ν x + ν y) (hneg : ∀ x, ν (-x) = ν x)
    (hnn : ∀ x, 0 ≤ ν x) {N₁ N₂ : G →+ G} {q : ℝ} (hq : q < 1) {y₁ y₂ u₁ u₂ : G}
    (hy₁ : y₁ + N₁ y₁ = u₁) (hy₂ : y₂ + N₂ y₂ = u₂) (hN₂ : ∀ d, ν (N₂ d) ≤ q * ν d) :
    ν (y₁ - y₂) ≤ (ν (u₁ - u₂) + ν (N₁ y₁ - N₂ y₁)) / (1 - q) := by
  have e : (y₁ - y₂) + N₂ (y₁ - y₂) = (u₁ - u₂) + (-(N₁ y₁ - N₂ y₁)) := by
    rw [map_sub, ← hy₁, ← hy₂]
    abel
  have hsub : ∀ x y : G, ν (x - y) ≤ ν x + ν y := fun x y => by
    have := hadd x (-y)
    rw [hneg] at this
    simpa [sub_eq_add_neg] using this
  have h1 := seminorm_solve_le hadd hneg hnn hq e (hN₂ (y₁ - y₂))
  have h2 : ν ((u₁ - u₂) + (-(N₁ y₁ - N₂ y₁))) ≤ ν (u₁ - u₂) + ν (N₁ y₁ - N₂ y₁) := by
    refine (hadd _ _).trans ?_
    rw [hneg]
  exact h1.trans (div_le_div_of_nonneg_right h2 (by linarith))

end KAM.Wave
