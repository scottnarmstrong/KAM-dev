/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Barrier

/-!
# Graph inversion of an exact torus (track SO, package SO-GRAPHM)

Unfrozen helper code (design §6, proposal §7.2).

An exact invariant torus of the lunar flow, after the clock lemma, is given by real functions of
`(x, y)` (the two angles `θ₀, θ₁`): `Q` (the angle `q`), `Pp` (the momentum `p`); the angle `φ` is
the clock `y + c`. The torus is invariant at the frequency `(ν, 1)`, and `∂_x Q ≥ m > 0`.

* `soGraphInv`: for each `(q, φ)` the unique `x` with `Q x (φ - c) = q`
  (`soGraphInv_spec`, `soGraphInv_unique`); it is continuous (`continuous_soGraphInv`) and
  satisfies `x ↦ q` shift laws (`soGraphInv_add_one`, `soGraphInv_periodic_φ`).
* `soBarrier_of_torus`: the torus is the graph `p = P(q, φ) = Pp (G(q, φ), φ - c)` of a continuous
  doubly periodic function, and it is an invariant barrier (`SoBarrier lo hi`).
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.SpinOrbit

namespace SoGraph

variable {Q : ℝ → ℝ → ℝ} {dQ : ℝ → ℝ → ℝ} {m : ℝ}

/-- Linear growth of `x ↦ Q x y` from the derivative bound. -/
theorem mul_sub_le (hdQ : ∀ x y, HasDerivAt (fun s => Q s y) (dQ x y) x)
    (hmono : ∀ x y, m ≤ dQ x y) {x x' : ℝ} (hx : x ≤ x') (y : ℝ) :
    m * (x' - x) ≤ Q x' y - Q x y := by
  refine mul_sub_le_image_sub_of_le_deriv (f := fun s => Q s y)
    (fun s => (hdQ s y).differentiableAt) (fun s => ?_) hx
  rw [(hdQ s y).deriv]
  exact hmono s y

theorem abs_sub_le (hm : 0 < m) (hdQ : ∀ x y, HasDerivAt (fun s => Q s y) (dQ x y) x)
    (hmono : ∀ x y, m ≤ dQ x y) (x x' y : ℝ) :
    m * |x' - x| ≤ |Q x' y - Q x y| := by
  rcases le_total x x' with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg]
    · exact mul_sub_le hdQ hmono h y
    · have := mul_sub_le hdQ hmono h y
      nlinarith [mul_nonneg hm.le (sub_nonneg.2 h)]
  · rw [abs_sub_comm x' x, abs_sub_comm (Q x' y)]
    rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg]
    · exact mul_sub_le hdQ hmono h y
    · have := mul_sub_le hdQ hmono h y
      nlinarith [mul_nonneg hm.le (sub_nonneg.2 h)]

theorem strictMono (hm : 0 < m) (hdQ : ∀ x y, HasDerivAt (fun s => Q s y) (dQ x y) x)
    (hmono : ∀ x y, m ≤ dQ x y) (y : ℝ) : StrictMono fun s => Q s y := by
  intro a b hab
  have := mul_sub_le hdQ hmono hab.le y
  nlinarith [mul_pos hm (sub_pos.2 hab)]

/-- The data of an exact torus after the clock lemma: real functions `Q` (the angle `q`) and `Pp`
(the momentum `p`) of the two torus angles `(x, y)`, with `φ = y + c`; frequency `(ν, 1)`. -/
structure Torus (Q Pp dQ : ℝ → ℝ → ℝ) (ν c m : ℝ) : Prop where
  pos : 0 < m
  contQ : Continuous fun z : ℝ × ℝ => Q z.1 z.2
  contP : Continuous fun z : ℝ × ℝ => Pp z.1 z.2
  perQ₀ : ∀ x y, Q (x + 1) y = Q x y + 1
  perQ₁ : ∀ x y, Q x (y + 1) = Q x y
  perP₀ : ∀ x y, Pp (x + 1) y = Pp x y
  perP₁ : ∀ x y, Pp x (y + 1) = Pp x y
  derivQ : ∀ x y, HasDerivAt (fun s => Q s y) (dQ x y) x
  mono : ∀ x y, m ≤ dQ x y
  flowQ : ∀ x y, HasDerivAt (fun t => Q (x + t * ν) (y + t)) (Pp x y) 0
  flowP : ∀ x y, HasDerivAt (fun t => Pp (x + t * ν) (y + t)) (-soVq (Q x y) (y + c)) 0

variable {Pp : ℝ → ℝ → ℝ} {ν c : ℝ}

theorem Torus.Q_add_int (T : Torus Q Pp dQ ν c m) (k : ℤ) (x y : ℝ) :
    Q (x + k) y = Q x y + k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => rw [Int.cast_add, Int.cast_one, ← add_assoc, T.perQ₀, ih]; ring
  | pred k ih =>
    have := T.perQ₀ (x + ((-(k : ℤ) - 1 : ℤ) : ℝ)) y
    push_cast at this ⊢
    rw [show x + (-(k : ℝ) - 1) + 1 = x + -(k : ℝ) by ring] at this
    push_cast at ih
    rw [ih] at this
    linarith

theorem Torus.contQ_left (T : Torus Q Pp dQ ν c m) (y : ℝ) : Continuous fun s => Q s y :=
  T.contQ.comp (continuous_id.prodMk continuous_const)

theorem Torus.exists_inv (T : Torus Q Pp dQ ν c m) (q y : ℝ) : ∃ x, Q x y = q := by
  set k : ℤ := ⌊q - Q 0 y⌋ with hk
  have h1 : Q (0 + k) y ≤ q := by
    rw [T.Q_add_int]; have := Int.floor_le (q - Q 0 y); rw [← hk] at this; linarith
  have h2 : q ≤ Q (0 + (k + 1 : ℤ)) y := by
    rw [T.Q_add_int]; have := Int.lt_floor_add_one (q - Q 0 y); rw [← hk] at this
    push_cast; linarith
  have hle : ((0 : ℝ) + k) ≤ 0 + ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hle (T.contQ_left y).continuousOn ⟨h1, h2⟩
  exact ⟨x, hx⟩

theorem Torus.inv_unique (T : Torus Q Pp dQ ν c m) {x x' y : ℝ} (h : Q x y = Q x' y) :
    x = x' := by
  have := abs_sub_le T.pos T.derivQ T.mono x x' y
  rw [h, sub_self, abs_zero] at this
  have h0 : |x' - x| = 0 := le_antisymm (by nlinarith [abs_nonneg (x' - x), T.pos]) (abs_nonneg _)
  linarith [abs_eq_zero.1 h0]

/-- The inverse of `x ↦ Q x (φ - c)`: the torus angle `x` carrying the point `(q, φ)`. -/
def Torus.inv (T : Torus Q Pp dQ ν c m) (q φ : ℝ) : ℝ :=
  Classical.choose (T.exists_inv q (φ - c))

theorem Torus.inv_spec (T : Torus Q Pp dQ ν c m) (q φ : ℝ) : Q (T.inv q φ) (φ - c) = q :=
  Classical.choose_spec (T.exists_inv q (φ - c))

theorem Torus.inv_apply (T : Torus Q Pp dQ ν c m) (x y : ℝ) : T.inv (Q x y) (y + c) = x := by
  refine T.inv_unique (y := y) ?_
  have := T.inv_spec (Q x y) (y + c)
  rwa [add_sub_cancel_right] at this

theorem Torus.continuous_inv (T : Torus Q Pp dQ ν c m) :
    Continuous fun z : ℝ × ℝ => T.inv z.1 z.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨q₀, φ₀⟩
  set x₀ := T.inv q₀ φ₀ with hx₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hc : ContinuousAt (fun φ => Q x₀ (φ - c)) φ₀ :=
    ((T.contQ.comp (continuous_const.prodMk (continuous_id.sub continuous_const)))
      : Continuous fun φ => Q x₀ (φ - c)).continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc (m * ε / 2) (by have := T.pos; positivity)
  refine ⟨min δ (m * ε / 2), lt_min hδ (by have := T.pos; positivity), ?_⟩
  rintro ⟨q, φ⟩ hd
  have hd' : max (dist q q₀) (dist φ φ₀) < min δ (m * ε / 2) := hd
  have hq2 : dist q q₀ < m * ε / 2 :=
    lt_of_le_of_lt (le_max_left _ _) (hd'.trans_le (min_le_right _ _))
  have hφ1 : dist φ φ₀ < δ :=
    lt_of_le_of_lt (le_max_right _ _) (hd'.trans_le (min_le_left _ _))
  have h1 := hδ' hφ1
  have h2 := abs_sub_le T.pos T.derivQ T.mono (T.inv q φ) x₀ (φ - c)
  rw [T.inv_spec q φ] at h2
  have h3 : Q x₀ (φ₀ - c) = q₀ := T.inv_spec q₀ φ₀
  rw [Real.dist_eq, h3] at h1
  rw [Real.dist_eq] at hq2 ⊢
  have h4 : |Q x₀ (φ - c) - q| ≤ |Q x₀ (φ - c) - q₀| + |q₀ - q| := by
    have := abs_add_le (Q x₀ (φ - c) - q₀) (q₀ - q)
    simpa using this
  rw [abs_sub_comm q₀ q] at h4
  have h5 : m * |x₀ - T.inv q φ| < m * ε := by linarith
  have := lt_of_mul_lt_mul_left h5 T.pos.le
  rwa [abs_sub_comm] at this

end SoGraph

end KAM.SpinOrbit

end
