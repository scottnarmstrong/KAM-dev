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

theorem Torus.inv_add_one (T : Torus Q Pp dQ ν c m) (q φ : ℝ) :
    T.inv (q + 1) φ = T.inv q φ + 1 := by
  refine T.inv_unique (y := φ - c) ?_
  rw [T.inv_spec, T.perQ₀, T.inv_spec]

theorem Torus.inv_φ_add_one (T : Torus Q Pp dQ ν c m) (q φ : ℝ) :
    T.inv q (φ + 1) = T.inv q φ := by
  refine T.inv_unique (y := φ - c) ?_
  have h := T.inv_spec q (φ + 1)
  rw [show φ + 1 - c = (φ - c) + 1 by ring, T.perQ₁] at h
  rw [h, T.inv_spec]

/-- The graph function `P(q, φ) = Pp (G(q, φ), φ - c)`. -/
def Torus.graph (T : Torus Q Pp dQ ν c m) (q φ : ℝ) : ℝ := Pp (T.inv q φ) (φ - c)

theorem Torus.continuous_graph (T : Torus Q Pp dQ ν c m) :
    Continuous fun z : ℝ × ℝ => T.graph z.1 z.2 := by
  unfold Torus.graph
  exact T.contP.comp (T.continuous_inv.prodMk (continuous_snd.sub continuous_const))

theorem Torus.graph_apply (T : Torus Q Pp dQ ν c m) (x y : ℝ) :
    T.graph (Q x y) (y + c) = Pp x y := by
  unfold Torus.graph
  rw [T.inv_apply, add_sub_cancel_right]

/-- Derivative along the flow line, at every time (not only at `t = 0`). -/
theorem hasDerivAt_line {f d : ℝ → ℝ → ℝ} (h : ∀ x y, HasDerivAt (fun t => f (x + t * ν) (y + t))
    (d x y) 0) (x y s : ℝ) :
    HasDerivAt (fun t => f (x + t * ν) (y + t)) (d (x + s * ν) (y + s)) s := by
  have h0 := h (x + s * ν) (y + s)
  rw [← sub_self s] at h0
  have := h0.comp_sub_const s s
  convert this using 2 <;> ring_nf

/-- The solution of the physical flow running along the torus through `(x, y)` at time `t₁`. -/
def Torus.orbit (_T : Torus Q Pp dQ ν c m) (x y t₁ t : ℝ) : ℝ × ℝ × ℝ :=
  (Q (x + (t - t₁) * ν) (y + (t - t₁)), Pp (x + (t - t₁) * ν) (y + (t - t₁)),
    y + (t - t₁) + c)

theorem Torus.hasDerivAt_orbit (T : Torus Q Pp dQ ν c m) (x y t₁ t : ℝ) :
    HasDerivAt (T.orbit x y t₁) (soField (T.orbit x y t₁ t)) t := by
  have hs : HasDerivAt (fun t : ℝ => t - t₁) 1 t := (hasDerivAt_id t).sub_const t₁
  have hQ := (hasDerivAt_line T.flowQ x y (t - t₁)).comp t hs
  have hP := (hasDerivAt_line T.flowP x y (t - t₁)).comp t hs
  have hφ : HasDerivAt (fun t : ℝ => y + (t - t₁) + c) 1 t := by
    simpa using (hs.const_add y).add_const c
  rw [soField_eq]
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · exact hQ.congr_deriv (mul_one _)
  · exact hP.congr_deriv (mul_one _)
  · exact hφ

theorem Torus.orbit_mem (T : Torus Q Pp dQ ν c m) (x y t₁ t : ℝ) :
    (T.orbit x y t₁ t).2.1 = T.graph (T.orbit x y t₁ t).1 (T.orbit x y t₁ t).2.2 := by
  simp only [Torus.orbit]
  rw [T.graph_apply]

theorem Torus.invariant (T : Torus Q Pp dQ ν c m) :
    KAM.ODE.IsInvariantSet soField Set.univ {x | x.2.1 = T.graph x.1 x.2.2} := by
  intro J y hJ hy t₁ ht₁ hS t ht
  have hS' : (y t₁).2.1 = T.graph (y t₁).1 (y t₁).2.2 := hS
  set X := T.inv (y t₁).1 (y t₁).2.2 with hX
  set Y := (y t₁).2.2 - c with hY
  have hQ : Q X Y = (y t₁).1 := T.inv_spec _ _
  have hP : Pp X Y = (y t₁).2.1 := by rw [hS']; rfl
  have h0 : T.orbit X Y t₁ t₁ = y t₁ := by
    simp only [Torus.orbit, sub_self, zero_mul, add_zero]
    refine Prod.ext hQ (Prod.ext hP ?_)
    simp [hY]
  have hw : KAM.ODE.IsSolutionIn soField Set.univ J (T.orbit X Y t₁) :=
    fun s _ => ⟨Set.mem_univ _, T.hasDerivAt_orbit X Y t₁ s⟩
  have := KAM.ODE.gen_uniqueness isOpen_univ soField_contDiff.contDiffOn hJ ht₁ hy hw h0.symm ht
  rw [this]
  exact T.orbit_mem X Y t₁ t

end SoGraph

/-- **Graph inversion of an exact torus** (proposal §7.2, owner ruling O4: continuous graphs).
Let `(Q, Pp)` be the angle `q` and the momentum `p` of an exact torus on the reals, as functions of
the torus angles `(x, y)`, where the clock lemma gave `φ = y + c` and the frequency `(ν, 1)`:
both are continuous, `Q - x` and `Pp` are doubly 1-periodic, `∂_x Q ≥ m > 0`, and
`d/dt Q = Pp`, `d/dt Pp = -∂_q V(Q, y + c)` along `t ↦ (x + tν, y + t)`. Then the torus is the
graph `p = P(q, φ)` of a continuous doubly periodic function, with values in `[lo, hi]` whenever
`Pp` is, and it is an invariant barrier. -/
theorem soBarrier_of_torus {Q Pp dQ : ℝ → ℝ → ℝ} {ν c m lo hi : ℝ} (hm : 0 < m)
    (hQc : Continuous fun z : ℝ × ℝ => Q z.1 z.2) (hPc : Continuous fun z : ℝ × ℝ => Pp z.1 z.2)
    (hQ₀ : ∀ x y, Q (x + 1) y = Q x y + 1) (hQ₁ : ∀ x y, Q x (y + 1) = Q x y)
    (hP₀ : ∀ x y, Pp (x + 1) y = Pp x y) (hP₁ : ∀ x y, Pp x (y + 1) = Pp x y)
    (hdQ : ∀ x y, HasDerivAt (fun s => Q s y) (dQ x y) x) (hmono : ∀ x y, m ≤ dQ x y)
    (hflowQ : ∀ x y, HasDerivAt (fun t => Q (x + t * ν) (y + t)) (Pp x y) 0)
    (hflowP : ∀ x y,
      HasDerivAt (fun t => Pp (x + t * ν) (y + t)) (-soVq (Q x y) (y + c)) 0)
    (hlo : ∀ x y, lo ≤ Pp x y) (hhi : ∀ x y, Pp x y ≤ hi) :
    Nonempty (SoBarrier lo hi) := by
  have T : SoGraph.Torus Q Pp dQ ν c m :=
    ⟨hm, hQc, hPc, hQ₀, hQ₁, hP₀, hP₁, hdQ, hmono, hflowQ, hflowP⟩
  refine ⟨⟨T.graph, T.continuous_graph, fun q φ => ?_, fun q φ => ?_, T.invariant,
    fun q φ => hlo _ _, fun q φ => hhi _ _⟩⟩
  · unfold SoGraph.Torus.graph
    rw [T.inv_add_one, hP₀]
  · unfold SoGraph.Torus.graph
    rw [T.inv_φ_add_one, show φ + 1 - c = (φ - c) + 1 by ring, hP₁]

end KAM.SpinOrbit

end
