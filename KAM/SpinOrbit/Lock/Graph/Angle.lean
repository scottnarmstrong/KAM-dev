/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Inverse

/-!
# Inverting a monotone angle (LOCK-GRAPH)

Unfrozen helper code. A continuous real function `A(x, y)` of the two torus angles with
`A(x + 1, y) = A(x, y) + 1`, `A(x, y + 1) = A(x, y)` and `∂_x A ≥ m > 0` (`LockAngle`) has a
continuous inverse `x = lockInv(a, y)` in its first argument (`LockAngle.lockInv_spec`,
`LockAngle.lockInv_apply`, `LockAngle.continuous_lockInv`) with the shift laws
`LockAngle.lockInv_add_one`, `LockAngle.lockInv_add_one_right`, `LockAngle.lockInv_sub_int`. This
is the flow-free part of `SoGraph.Torus` (`Graph/Inverse.lean`), whose structure also carries the
rotational flow equations; the librational graph has a different flow.
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.SpinOrbit.Lock

/-- The data of a monotone angle on the torus. -/
structure LockAngle (A dA : ℝ → ℝ → ℝ) (m : ℝ) : Prop where
  pos : 0 < m
  cont : Continuous fun z : ℝ × ℝ => A z.1 z.2
  per₀ : ∀ x y, A (x + 1) y = A x y + 1
  per₁ : ∀ x y, A x (y + 1) = A x y
  hasDeriv : ∀ x y, HasDerivAt (fun s => A s y) (dA x y) x
  mono : ∀ x y, m ≤ dA x y

variable {A dA : ℝ → ℝ → ℝ} {m : ℝ}

/-- A one-periodic function of the first argument is invariant under integer shifts. -/
theorem sub_int_of_periodic {f : ℝ → ℝ → ℝ} (h : ∀ x y, f (x + 1) y = f x y) (x y : ℝ) (k : ℤ) :
    f (x - k) y = f x y := by
  have hp : Function.Periodic (fun s => f s y) 1 := fun s => h s y
  simpa using hp.sub_int_mul_eq (x := x) k

theorem LockAngle.lockAngle_add_int (T : LockAngle A dA m) (k : ℤ) (x y : ℝ) :
    A (x + k) y = A x y + k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => rw [Int.cast_add, Int.cast_one, ← add_assoc, T.per₀, ih]; ring
  | pred k ih =>
    have := T.per₀ (x + ((-(k : ℤ) - 1 : ℤ) : ℝ)) y
    push_cast at this ⊢
    rw [show x + (-(k : ℝ) - 1) + 1 = x + -(k : ℝ) by ring] at this
    push_cast at ih
    rw [ih] at this
    linarith

theorem LockAngle.lockAngle_exists_inv (T : LockAngle A dA m) (a y : ℝ) : ∃ x, A x y = a := by
  set k : ℤ := ⌊a - A 0 y⌋ with hk
  have h1 : A (0 + k) y ≤ a := by
    rw [T.lockAngle_add_int]; have := Int.floor_le (a - A 0 y); rw [← hk] at this; linarith
  have h2 : a ≤ A (0 + (k + 1 : ℤ)) y := by
    rw [T.lockAngle_add_int]; have := Int.lt_floor_add_one (a - A 0 y); rw [← hk] at this
    push_cast; linarith
  have hle : ((0 : ℝ) + k) ≤ 0 + ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
  have hc : Continuous fun s => A s y := T.cont.comp (continuous_id.prodMk continuous_const)
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hle hc.continuousOn ⟨h1, h2⟩
  exact ⟨x, hx⟩

theorem LockAngle.lockInv_unique (T : LockAngle A dA m) {x x' y : ℝ}
    (h : A x y = A x' y) : x = x' := by
  have := SoGraph.graphAbs_sub_le T.pos T.hasDeriv T.mono x x' y
  rw [h, sub_self, abs_zero] at this
  have h0 : |x' - x| = 0 := le_antisymm (by nlinarith [abs_nonneg (x' - x), T.pos]) (abs_nonneg _)
  linarith [abs_eq_zero.1 h0]

/-- The inverse of `x ↦ A x y`. -/
def LockAngle.lockInv (T : LockAngle A dA m) (a y : ℝ) : ℝ :=
  Classical.choose (T.lockAngle_exists_inv a y)

theorem LockAngle.lockInv_spec (T : LockAngle A dA m) (a y : ℝ) : A (T.lockInv a y) y = a :=
  Classical.choose_spec (T.lockAngle_exists_inv a y)

theorem LockAngle.lockInv_apply (T : LockAngle A dA m) (x y : ℝ) : T.lockInv (A x y) y = x :=
  T.lockInv_unique (T.lockInv_spec _ _)

theorem LockAngle.continuous_lockInv (T : LockAngle A dA m) :
    Continuous fun z : ℝ × ℝ => T.lockInv z.1 z.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a₀, y₀⟩
  set x₀ := T.lockInv a₀ y₀ with hx₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hc : ContinuousAt (fun y => A x₀ y) y₀ :=
    ((T.cont.comp (continuous_const.prodMk continuous_id)) :
      Continuous fun y => A x₀ y).continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc (m * ε / 2) (by have := T.pos; positivity)
  refine ⟨min δ (m * ε / 2), lt_min hδ (by have := T.pos; positivity), ?_⟩
  rintro ⟨a, y⟩ hd
  have hd' : max (dist a a₀) (dist y y₀) < min δ (m * ε / 2) := hd
  have ha2 : dist a a₀ < m * ε / 2 :=
    lt_of_le_of_lt (le_max_left _ _) (hd'.trans_le (min_le_right _ _))
  have hy1 : dist y y₀ < δ :=
    lt_of_le_of_lt (le_max_right _ _) (hd'.trans_le (min_le_left _ _))
  have h1 := hδ' hy1
  have h2 := SoGraph.graphAbs_sub_le T.pos T.hasDeriv T.mono (T.lockInv a y) x₀ y
  rw [T.lockInv_spec a y] at h2
  have h3 : A x₀ y₀ = a₀ := T.lockInv_spec a₀ y₀
  rw [Real.dist_eq, h3] at h1
  rw [Real.dist_eq] at ha2 ⊢
  have h4 : |A x₀ y - a| ≤ |A x₀ y - a₀| + |a₀ - a| := by
    have := abs_add_le (A x₀ y - a₀) (a₀ - a)
    simpa using this
  rw [abs_sub_comm a₀ a] at h4
  have h5 : m * |x₀ - T.lockInv a y| < m * ε := by linarith
  have := lt_of_mul_lt_mul_left h5 T.pos.le
  rwa [abs_sub_comm] at this

theorem LockAngle.lockInv_add_one (T : LockAngle A dA m) (a y : ℝ) :
    T.lockInv (a + 1) y = T.lockInv a y + 1 := by
  refine T.lockInv_unique (y := y) ?_
  rw [T.lockInv_spec, T.per₀, T.lockInv_spec]

theorem LockAngle.lockInv_add_one_right (T : LockAngle A dA m) (a y : ℝ) :
    T.lockInv a (y + 1) = T.lockInv a y := by
  refine T.lockInv_unique (y := y) ?_
  have h := T.lockInv_spec a (y + 1)
  rw [T.per₁] at h
  rw [h, T.lockInv_spec]

theorem LockAngle.lockInv_sub_int (T : LockAngle A dA m) (a y : ℝ) (k : ℤ) :
    T.lockInv (a - k) y = T.lockInv a y - k := by
  refine T.lockInv_unique (y := y) ?_
  rw [T.lockInv_spec, sub_eq_add_neg (T.lockInv a y),
    show -(k : ℝ) = ((-k : ℤ) : ℝ) by push_cast; ring, T.lockAngle_add_int, T.lockInv_spec]
  push_cast
  ring

end KAM.SpinOrbit.Lock

end
