/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Clock
public import KAM.SpinOrbit.Barrier
public import KAM.SpinOrbit.Hamiltonian

/-!
# Graph inversion of an exact torus (track SO, package SO-GRAPHM)

Unfrozen helper code (design §6, proposal §7.2).

An exact invariant torus of the lunar flow, after the clock lemma, is given by real functions of
`(x, y)` (the two angles `θ₀, θ₁`): `Q` (the angle `q`), `Pp` (the momentum `p`); the angle `φ` is
the clock `y + c`. The torus is invariant at the frequency `(ν, 1)`, and `∂_x Q ≥ m > 0`.

* `Torus.soGraphInv`: for each `(q, φ)` the unique `x` with `Q x (φ - c) = q`
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

theorem graphAbs_sub_le (hm : 0 < m) (hdQ : ∀ x y, HasDerivAt (fun s => Q s y) (dQ x y) x)
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

theorem soStrictMono (hm : 0 < m) (hdQ : ∀ x y, HasDerivAt (fun s => Q s y) (dQ x y) x)
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

theorem Torus.soGraphInv_exists (T : Torus Q Pp dQ ν c m) (q y : ℝ) : ∃ x, Q x y = q := by
  set k : ℤ := ⌊q - Q 0 y⌋ with hk
  have h1 : Q (0 + k) y ≤ q := by
    rw [T.Q_add_int]; have := Int.floor_le (q - Q 0 y); rw [← hk] at this; linarith
  have h2 : q ≤ Q (0 + (k + 1 : ℤ)) y := by
    rw [T.Q_add_int]; have := Int.lt_floor_add_one (q - Q 0 y); rw [← hk] at this
    push_cast; linarith
  have hle : ((0 : ℝ) + k) ≤ 0 + ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hle (T.contQ_left y).continuousOn ⟨h1, h2⟩
  exact ⟨x, hx⟩

theorem Torus.soGraphInv_unique (T : Torus Q Pp dQ ν c m) {x x' y : ℝ} (h : Q x y = Q x' y) :
    x = x' := by
  have := graphAbs_sub_le T.pos T.derivQ T.mono x x' y
  rw [h, sub_self, abs_zero] at this
  have h0 : |x' - x| = 0 := le_antisymm (by nlinarith [abs_nonneg (x' - x), T.pos]) (abs_nonneg _)
  linarith [abs_eq_zero.1 h0]

/-- The inverse of `x ↦ Q x (φ - c)`: the torus angle `x` carrying the point `(q, φ)`. -/
def Torus.soGraphInv (T : Torus Q Pp dQ ν c m) (q φ : ℝ) : ℝ :=
  Classical.choose (T.soGraphInv_exists q (φ - c))

theorem Torus.soGraphInv_spec (T : Torus Q Pp dQ ν c m) (q φ : ℝ) :
    Q (T.soGraphInv q φ) (φ - c) = q :=
  Classical.choose_spec (T.soGraphInv_exists q (φ - c))

theorem Torus.soGraphInv_apply (T : Torus Q Pp dQ ν c m) (x y : ℝ) :
    T.soGraphInv (Q x y) (y + c) = x := by
  refine T.soGraphInv_unique (y := y) ?_
  have := T.soGraphInv_spec (Q x y) (y + c)
  rwa [add_sub_cancel_right] at this

theorem Torus.continuous_soGraphInv (T : Torus Q Pp dQ ν c m) :
    Continuous fun z : ℝ × ℝ => T.soGraphInv z.1 z.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨q₀, φ₀⟩
  set x₀ := T.soGraphInv q₀ φ₀ with hx₀
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
  have h2 := graphAbs_sub_le T.pos T.derivQ T.mono (T.soGraphInv q φ) x₀ (φ - c)
  rw [T.soGraphInv_spec q φ] at h2
  have h3 : Q x₀ (φ₀ - c) = q₀ := T.soGraphInv_spec q₀ φ₀
  rw [Real.dist_eq, h3] at h1
  rw [Real.dist_eq] at hq2 ⊢
  have h4 : |Q x₀ (φ - c) - q| ≤ |Q x₀ (φ - c) - q₀| + |q₀ - q| := by
    have := abs_add_le (Q x₀ (φ - c) - q₀) (q₀ - q)
    simpa using this
  rw [abs_sub_comm q₀ q] at h4
  have h5 : m * |x₀ - T.soGraphInv q φ| < m * ε := by linarith
  have := lt_of_mul_lt_mul_left h5 T.pos.le
  rwa [abs_sub_comm] at this

theorem Torus.soGraphInv_add_one (T : Torus Q Pp dQ ν c m) (q φ : ℝ) :
    T.soGraphInv (q + 1) φ = T.soGraphInv q φ + 1 := by
  refine T.soGraphInv_unique (y := φ - c) ?_
  rw [T.soGraphInv_spec, T.perQ₀, T.soGraphInv_spec]

theorem Torus.soGraphInv_periodic_φ (T : Torus Q Pp dQ ν c m) (q φ : ℝ) :
    T.soGraphInv q (φ + 1) = T.soGraphInv q φ := by
  refine T.soGraphInv_unique (y := φ - c) ?_
  have h := T.soGraphInv_spec q (φ + 1)
  rw [show φ + 1 - c = (φ - c) + 1 by ring, T.perQ₁] at h
  rw [h, T.soGraphInv_spec]

/-- The graph function `P(q, φ) = Pp (G(q, φ), φ - c)`. -/
def Torus.soGraphFun (T : Torus Q Pp dQ ν c m) (q φ : ℝ) : ℝ := Pp (T.soGraphInv q φ) (φ - c)

theorem Torus.continuous_soGraphFun (T : Torus Q Pp dQ ν c m) :
    Continuous fun z : ℝ × ℝ => T.soGraphFun z.1 z.2 := by
  unfold Torus.soGraphFun
  exact T.contP.comp (T.continuous_soGraphInv.prodMk (continuous_snd.sub continuous_const))

theorem Torus.soGraphFun_apply (T : Torus Q Pp dQ ν c m) (x y : ℝ) :
    T.soGraphFun (Q x y) (y + c) = Pp x y := by
  unfold Torus.soGraphFun
  rw [T.soGraphInv_apply, add_sub_cancel_right]

/-- Derivative along the flow line, at every time (not only at `t = 0`). -/
theorem graphHasDerivAt_line {f d : ℝ → ℝ → ℝ}
    (h : ∀ x y, HasDerivAt (fun t => f (x + t * ν) (y + t)) (d x y) 0) (x y s : ℝ) :
    HasDerivAt (fun t => f (x + t * ν) (y + t)) (d (x + s * ν) (y + s)) s := by
  have h0 := h (x + s * ν) (y + s)
  rw [← sub_self s] at h0
  have := h0.comp_sub_const s s
  convert this using 2; ring_nf

/-- The solution of the physical flow running along the torus through `(x, y)` at time `t₁`. -/
def Torus.soOrbit (_T : Torus Q Pp dQ ν c m) (x y t₁ t : ℝ) : ℝ × ℝ × ℝ :=
  (Q (x + (t - t₁) * ν) (y + (t - t₁)), Pp (x + (t - t₁) * ν) (y + (t - t₁)),
    y + (t - t₁) + c)

theorem Torus.hasDerivAt_soOrbit (T : Torus Q Pp dQ ν c m) (x y t₁ t : ℝ) :
    HasDerivAt (T.soOrbit x y t₁) (soField (T.soOrbit x y t₁ t)) t := by
  have hs : HasDerivAt (fun t : ℝ => t - t₁) 1 t := (hasDerivAt_id t).sub_const t₁
  have hQ := (graphHasDerivAt_line T.flowQ x y (t - t₁)).comp t hs
  have hP := (graphHasDerivAt_line T.flowP x y (t - t₁)).comp t hs
  have hφ : HasDerivAt (fun t : ℝ => y + (t - t₁) + c) 1 t := by
    simpa using (hs.const_add y).add_const c
  rw [soField_eq]
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · exact hQ.congr_deriv (mul_one _)
  · exact hP.congr_deriv (mul_one _)
  · exact hφ

theorem Torus.soOrbit_mem (T : Torus Q Pp dQ ν c m) (x y t₁ t : ℝ) :
    (T.soOrbit x y t₁ t).2.1 = T.soGraphFun (T.soOrbit x y t₁ t).1 (T.soOrbit x y t₁ t).2.2 := by
  simp only [Torus.soOrbit]
  rw [T.soGraphFun_apply]

theorem Torus.soGraph_invariant (T : Torus Q Pp dQ ν c m) :
    KAM.ODE.IsInvariantSet soField Set.univ {x | x.2.1 = T.soGraphFun x.1 x.2.2} := by
  intro J y hJ hy t₁ ht₁ hS t ht
  have hS' : (y t₁).2.1 = T.soGraphFun (y t₁).1 (y t₁).2.2 := hS
  set X := T.soGraphInv (y t₁).1 (y t₁).2.2 with hX
  set Y := (y t₁).2.2 - c with hY
  have hQ : Q X Y = (y t₁).1 := T.soGraphInv_spec _ _
  have hP : Pp X Y = (y t₁).2.1 := by rw [hS']; rfl
  have h0 : T.soOrbit X Y t₁ t₁ = y t₁ := by
    simp only [Torus.soOrbit, sub_self, zero_mul, add_zero]
    refine Prod.ext hQ (Prod.ext hP ?_)
    simp [hY]
  have hw : KAM.ODE.IsSolutionIn soField Set.univ J (T.soOrbit X Y t₁) :=
    fun s _ => ⟨Set.mem_univ _, T.hasDerivAt_soOrbit X Y t₁ s⟩
  have := KAM.ODE.gen_uniqueness isOpen_univ soField_contDiff.contDiffOn hJ ht₁ hy hw h0.symm ht
  rw [this]
  exact T.soOrbit_mem X Y t₁ t

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
  refine ⟨⟨T.soGraphFun, T.continuous_soGraphFun, fun q φ => ?_, fun q φ => ?_, T.soGraph_invariant,
    fun q φ => hlo _ _, fun q φ => hhi _ _⟩⟩
  · unfold SoGraph.Torus.soGraphFun
    rw [T.soGraphInv_add_one, hP₀]
  · unfold SoGraph.Torus.soGraphFun
    rw [T.soGraphInv_periodic_φ, show φ + 1 - c = (φ - c) + 1 by ring, hP₁]

/-! ### From the complex torus `K∞` to the real data -/

namespace SoGraph

open KAM KAM.Certificate

variable {Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}

/-- The real torus angle `(x, y)` as a point of `ℂ²`. -/
def realPt (x y : ℝ) : Fin 2 → ℂ := fun i => ((![x, y] i : ℝ) : ℂ)

/-- The angle `q` of the real torus at `(x, y)`. -/
def realQ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (x y : ℝ) : ℝ :=
  ((Kinf (realPt x y)).1 0).re

/-- The momentum `p` of the real torus at `(x, y)`. -/
def realP (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (x y : ℝ) : ℝ :=
  ((Kinf (realPt x y)).2 0).re

theorem realPt_mem {ρ : ℝ} (hρ : 0 < ρ) (x y : ℝ) : realPt x y ∈ complexStrip 2 ρ :=
  ofReal_mem_complexStrip hρ ![x, y]

theorem real_comp (hreal : IsRealOnReals Kinf) (θ : Fin 2 → ℝ) :
    ∃ z : (Fin 2 → ℝ) × (Fin 2 → ℝ), Kinf (fun i => (θ i : ℂ)) =
      (fun i => (z.1 i : ℂ), fun i => (z.2 i : ℂ)) := hreal θ

theorem realQ_eq (hreal : IsRealOnReals Kinf) (x y : ℝ) :
    (Kinf (realPt x y)).1 0 = ((realQ Kinf x y : ℝ) : ℂ) := by
  obtain ⟨z, hz⟩ := hreal ![x, y]
  have : Kinf (realPt x y) = _ := hz
  simp [realQ, this]

theorem realP_eq (hreal : IsRealOnReals Kinf) (x y : ℝ) :
    (Kinf (realPt x y)).2 0 = ((realP Kinf x y : ℝ) : ℂ) := by
  obtain ⟨z, hz⟩ := hreal ![x, y]
  have : Kinf (realPt x y) = _ := hz
  simp [realP, this]

/-- Derivative of `K∞` along a real line, at every time. -/
theorem graphHasDerivAt_lineK {ρ : ℝ} (hholo : DifferentiableOn ℂ Kinf (complexStrip 2 ρ))
    (hρ : 0 < ρ) (θ v : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Kinf (fun i => ((θ i + s * v i : ℝ) : ℂ)))
      (fderiv ℂ Kinf (fun i => ((θ i + t * v i : ℝ) : ℂ)) (fun i => (v i : ℂ))) t := by
  have hℓ : HasDerivAt (fun s : ℝ => fun i => ((θ i + s * v i : ℝ) : ℂ))
      (fun i => (v i : ℂ)) t := by
    refine hasDerivAt_pi.2 fun i => ?_
    have := (((hasDerivAt_id t).mul_const (v i)).const_add (θ i)).ofReal_comp
    simpa using this
  have hmem : (fun i => ((θ i + t * v i : ℝ) : ℂ)) ∈ complexStrip 2 ρ := by
    intro i; simpa using hρ
  have hK : DifferentiableAt ℂ Kinf (fun i => ((θ i + t * v i : ℝ) : ℂ)) :=
    hholo.differentiableAt ((isOpen_complexStrip 2 ρ).mem_nhds hmem)
  exact (hK.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hℓ

theorem realPt_line (x y ν s : ℝ) :
    (fun i => ((![x, y] i + s * ![ν, 1] i : ℝ) : ℂ)) = realPt (x + s * ν) (y + s) := by
  funext i; fin_cases i <;> simp [realPt]

theorem realPt_zero_line (y s : ℝ) :
    (fun i => ((![0, y] i + s * ![1, 0] i : ℝ) : ℂ)) = realPt s y := by
  funext i; fin_cases i <;> simp [realPt]

/-- The real part of a component of a `ℂ²`-valued derivative. -/
theorem hasDerivAt_re_comp {f : ℝ → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {D : (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {t : ℝ} (h : HasDerivAt f D t) :
    HasDerivAt (fun s => ((f s).1 0).re) (D.1 0).re t := by
  have h1 : HasDerivAt (fun s => (f s).1 0) (D.1 0) t := hasDerivAt_pi.1 h.fst 0
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1

theorem hasDerivAt_re_comp₂ {f : ℝ → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {D : (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {t : ℝ} (h : HasDerivAt f D t) :
    HasDerivAt (fun s => ((f s).2 0).re) (D.2 0).re t := by
  have h1 : HasDerivAt (fun s => (f s).2 0) (D.2 0) t := hasDerivAt_pi.1 h.snd 0
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1

end SoGraph

open KAM KAM.Certificate SoGraph in
/-- **The exact torus is an invariant barrier graph.** Let `K∞` be the exact torus of the
isoenergetic theorem for `soHC` (holomorphic on the strip `T_ρ`, primary, real on the reals,
invariant at `s∞ ω*`, with `s∞ ω*` Diophantine). If `∂_{θ₀} q ≥ m > 0` on the real torus
(`fderiv` of `K∞` applied to the first real direction `realPt 1 0`) and the momentum on the real
torus lies in `[lo, hi]`, then the clock lemma gives `φ = θ₁ + c` and `s∞ ω*₁ = 1`, and the real
torus is the graph `p = P(q, φ)` of a continuous periodic function: an invariant barrier. -/
theorem soBarrier_of_exact_torus {Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {ρ sinf γ τ m lo hi : ℝ} {ωstar : Fin 2 → ℝ} (hρ : 0 < ρ)
    (hholo : DifferentiableOn ℂ Kinf (complexStrip 2 ρ)) (hprim : IsPrimaryOnStrip Kinf ρ)
    (hreal : IsRealOnReals Kinf)
    (hinv : ∀ θ ∈ complexStrip 2 ρ, invarianceError soHC Kinf (sinf • ωstar) θ = 0)
    (hγ : 0 < γ) (hdio : IsDiophantine γ τ (sinf • ωstar)) (hm : 0 < m)
    (hmono : ∀ x y : ℝ, m ≤ ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re)
    (hlo : ∀ x y : ℝ, lo ≤ ((Kinf (realPt x y)).2 0).re)
    (hhi : ∀ x y : ℝ, ((Kinf (realPt x y)).2 0).re ≤ hi) :
    Nonempty (SoBarrier lo hi) := by
  have hH1 : ∀ z ∈ (Set.univ : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))),
      fderiv ℂ soHC z (phaseBasis (.inr (1 : Fin 2))) = 1 := by
    intro z _
    rw [phaseBasis_inr, fderiv_soHC_apply]
    simp
  obtain ⟨hone, c, hc⟩ := clock_frequency (D := Set.univ) (H := soHC) (j := 1) hρ hH1
    (fun _ _ => Set.mem_univ _) hholo hprim hreal hinv hγ hdio
  set ν : ℝ := sinf * ωstar 0 with hν
  have hω : sinf • ωstar = ![ν, 1] := by
    funext i; fin_cases i <;> simp [hν, hone]
  have hcl : ∀ x y : ℝ, (Kinf (realPt x y)).1 1 = ((y + c : ℝ) : ℂ) := fun x y => by
    have h : (Kinf (realPt x y)).1 1 = ((![x, y] 1 + c : ℝ) : ℂ) := hc ![x, y]
    simpa using h
  -- the flow equation at every real point
  have hflow : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => Kinf (realPt (x + s * ν) (y + s)))
      (soExtFieldC (Kinf (realPt x y))) 0 := by
    intro x y
    have h := graphHasDerivAt_lineK hholo hρ ![x, y] ![ν, 1] 0
    have e := hinv (realPt x y) (realPt_mem hρ x y)
    rw [invarianceError, hω, hamiltonianVectorFieldℂ_soHC, sub_eq_zero] at e
    have e2 : (fun i => ((![x, y] i + (0 : ℝ) * ![ν, 1] i : ℝ) : ℂ)) = realPt x y := by
      funext i; fin_cases i <;> simp [realPt]
    rw [e2, ← e] at h
    simpa only [realPt_line] using h
  have hper : ∀ (x y : ℝ) (k : Fin 2 → ℤ),
      Kinf (realPt x y + fun i => ((k i : ℤ) : ℂ)) =
        Kinf (realPt x y) + (fun i => ((k i : ℤ) : ℂ), 0) :=
    fun x y k => hprim _ (realPt_mem hρ x y) k
  have hPeq : ∀ x y, (Kinf (realPt x y)).2 0 = ((realP Kinf x y : ℝ) : ℂ) := realP_eq hreal
  refine soBarrier_of_torus (Q := realQ Kinf) (Pp := realP Kinf)
    (dQ := fun x y => ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re) (ν := ν) (c := c)
    (m := m) hm ?_ ?_ ?_ ?_ ?_ ?_ ?_ hmono ?_ ?_ hlo hhi
  · have hcp : Continuous fun z : ℝ × ℝ => realPt z.1 z.2 :=
      continuous_pi fun i => by fin_cases i <;> simp [realPt] <;> fun_prop
    have hcK : Continuous fun z : ℝ × ℝ => Kinf (realPt z.1 z.2) :=
      hholo.continuousOn.comp_continuous hcp fun z => realPt_mem hρ _ _
    exact Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_fst.comp hcK))
  · have hcp : Continuous fun z : ℝ × ℝ => realPt z.1 z.2 :=
      continuous_pi fun i => by fin_cases i <;> simp [realPt] <;> fun_prop
    have hcK : Continuous fun z : ℝ × ℝ => Kinf (realPt z.1 z.2) :=
      hholo.continuousOn.comp_continuous hcp fun z => realPt_mem hρ _ _
    exact Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_snd.comp hcK))
  · intro x y
    have h := hper x y ![1, 0]
    have e : realPt x y + (fun i => ((![1, 0] i : ℤ) : ℂ)) = realPt (x + 1) y := by
      funext i; fin_cases i <;> simp [realPt]
    rw [e] at h
    simpa [realQ] using congrArg (fun u => (u.1 0).re) h
  · intro x y
    have h := hper x y ![0, 1]
    have e : realPt x y + (fun i => ((![0, 1] i : ℤ) : ℂ)) = realPt x (y + 1) := by
      funext i; fin_cases i <;> simp [realPt]
    rw [e] at h
    simpa [realQ] using congrArg (fun u => (u.1 0).re) h
  · intro x y
    have h := hper x y ![1, 0]
    have e : realPt x y + (fun i => ((![1, 0] i : ℤ) : ℂ)) = realPt (x + 1) y := by
      funext i; fin_cases i <;> simp [realPt]
    rw [e] at h
    simpa [realP] using congrArg (fun u => (u.2 0).re) h
  · intro x y
    have h := hper x y ![0, 1]
    have e : realPt x y + (fun i => ((![0, 1] i : ℤ) : ℂ)) = realPt x (y + 1) := by
      funext i; fin_cases i <;> simp [realPt]
    rw [e] at h
    simpa [realP] using congrArg (fun u => (u.2 0).re) h
  · intro x y
    have h := graphHasDerivAt_lineK hholo hρ ![0, y] ![1, 0] x
    simp only [realPt_zero_line] at h
    exact hasDerivAt_re_comp h
  · intro x y
    have h := hasDerivAt_re_comp (hflow x y)
    have hv : ((soExtFieldC (Kinf (realPt x y))).1 0).re = realP Kinf x y := by
      simp [soExtFieldC, hPeq]
    rw [hv] at h
    exact h
  · intro x y
    have h := hasDerivAt_re_comp₂ (hflow x y)
    have hv : ((soExtFieldC (Kinf (realPt x y))).2 0).re = -soVq (realQ Kinf x y) (y + c) := by
      simp only [soExtFieldC, Matrix.cons_val_zero, realQ_eq hreal, hcl, soVqC_ofReal]
      simp
    rw [hv] at h
    exact h

end KAM.SpinOrbit

end
