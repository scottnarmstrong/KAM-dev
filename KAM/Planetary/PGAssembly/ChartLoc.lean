/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ChartMem

/-!
# P Part 5: the location of the torus, elementary lemmas (`bpP:p5:location`)

Scalar and geometric lemmas used by `location`: the oscillator radial margin and the inner core
margin in the fast action.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CH.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Planetary

/-- A displacement of size at most `E` from a point of squared norm `s^2`, `s + E < r`. -/
theorem chart_disc_aux {P Q p q s E r : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hPQ : P^2+Q^2 = s^2)
    (hD : p^2+q^2 ≤ E^2) (hsE : s + E < r) : (P+p)^2+(Q+q)^2 < r^2 := by
  have h1 : (P*p+Q*q)^2 ≤ (s*E)^2 := by
    calc (P*p+Q*q)^2 ≤ (P^2+Q^2)*(p^2+q^2) := by nlinarith [sq_nonneg (P*q-Q*p)]
      _ ≤ s^2*E^2 := by rw [hPQ]; exact mul_le_mul_of_nonneg_left hD (sq_nonneg _)
      _ = (s*E)^2 := by ring
  have h2 : P*p+Q*q ≤ s*E := abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  nlinarith [mul_nonneg hs hE]

/-- The radial margin: `s^2 < r^2 - 3 l`, `E r = l`, `0 < r` give `s + E < r`. -/
theorem chart_radial_margin {s E l r : ℝ} (hE : 0 ≤ E) (hr : 0 < r)
    (hl : E*r = l) (h : s^2 < r^2 - 3*l) : s + E < r := by
  by_contra hc
  rw [not_lt] at hc
  have h3 : 3*E < r := by nlinarith [mul_nonneg hE hr.le, sq_nonneg s]
  have h4 : 0 ≤ r - E := by linarith
  nlinarith [mul_self_le_mul_self h4 (show r - E ≤ s by linarith)]

/-- Points close to the inner core stay in `V`. -/
theorem mem_of_dist_lt_innerCore {n : ℕ} {V : Set (Fin n → ℝ)} {t : ℝ} {y x : Fin n → ℝ}
    (hy : y ∈ V) (hf : ∀ J ∈ frontier V, t ≤ dist y J) (hx : dist x y < t) : x ∈ V := by
  by_contra hxV
  have hpc : IsPreconnected (closedBall y (dist x y)) := (convex_closedBall y _).isPreconnected
  have hno : ∀ J ∈ closedBall y (dist x y), J ∉ frontier V := fun J hJ hJf => by
    have := hf J hJf
    rw [dist_comm] at this
    have h2 : dist J y ≤ dist x y := mem_closedBall.1 hJ
    linarith
  have hcov : closedBall y (dist x y) ⊆ interior V ∪ (closure V)ᶜ := fun J hJ => by
    by_cases hJc : J ∈ closure V
    · left
      by_contra hJi
      exact hno J hJ ⟨hJc, hJi⟩
    · right; exact hJc
  have hyi : y ∈ interior V := by
    by_contra hyi
    exact hno y (mem_closedBall_self dist_nonneg) ⟨subset_closure hy, hyi⟩
  have hsub := hpc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset_closure |>.mono_left le_rfl)
    hcov ⟨y, mem_closedBall_self dist_nonneg, hyi⟩
  exact hxV (interior_subset (hsub (mem_closedBall.2 (by rw [dist_comm]))))

end KAM.Planetary

end
