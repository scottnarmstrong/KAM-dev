/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Real tori that are graphs over the angles

Pure geometry, no certificate data (improvement #7, the graph/embedding adapter).

* `DerivNearId f L`: `f : ℝⁿ → ℝⁿ` is differentiable with `‖Df(x) - 1‖ ≤ L` everywhere, for the
  operator norm of the max norm, i.e. the maximal row sum `max_i Σ_j |∂_j f_i(x) - δ_ij|`.
  For `L < 1`, `f` is bi-Lipschitz (`DerivNearId.lower`, `DerivNearId.upper`) and bijective (the
  inverse is the fixed point of a contraction), hence a homeomorphism of `ℝⁿ`
  (`DerivNearId.toHomeomorph`); every `Df(x)` is invertible (`DerivNearId.fderivEquiv`), so an
  analytic `f` has an analytic inverse (`DerivNearId.analyticOnNhd_invFun`).
* A real torus `k : ℝⁿ → ℝⁿ × ℝⁿ` with `k(θ + m) = k(θ) + (m, 0)` has the angle map
  `torusAngle k = (k ·).1` and the graph function `torusGraph k = (k ∘ A⁻¹ ·).2`
  (`A⁻¹ = Function.invFun (torusAngle k)`).
* `isAngleGraph_of_derivNearId`: if `k` is analytic and `torusAngle k` is `DerivNearId` with
  `L < 1`, then `IsAngleGraph k L`: `k(θ) = (A θ, G (A θ))`, the image of `k` is exactly the
  graph of the analytic `ℤⁿ`-periodic `G`, `A` is a bijection commuting with `ℤⁿ` (so `A` induces a
  homeomorphism of `𝕋ⁿ` and `k` an injective map of `𝕋ⁿ`), `k` is an immersion, and the
  quantitative bounds `(1 - L) ‖θ - θ'‖ ≤ ‖A θ - A θ'‖`, `(1 - L) ‖v‖ ≤ ‖Dk(θ) v‖`.
-/

@[expose] public noncomputable section

open Set Function

namespace KAM.Application

variable {n : ℕ}

/-- `f : ℝⁿ → ℝⁿ` is differentiable and `‖Df(x) - 1‖ ≤ L` at every `x` (operator norm of the max
norm: the maximal row sum `max_i Σ_j |∂_j f_i(x) - δ_ij|`). For an angle map `θ ↦ θ + u(θ)` this
is `‖Du‖ ≤ L`. -/
def DerivNearId (f : (Fin n → ℝ) → (Fin n → ℝ)) (L : ℝ) : Prop :=
  ∀ x, DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ L

namespace DerivNearId

variable {f : (Fin n → ℝ) → (Fin n → ℝ)} {L : ℝ}

theorem differentiable (h : DerivNearId f L) : Differentiable ℝ f := fun x => (h x).1

theorem continuous (h : DerivNearId f L) : Continuous f := h.differentiable.continuous

theorem nonneg (h : DerivNearId f L) : 0 ≤ L := (norm_nonneg _).trans (h 0).2

/-- The displacement `f - id` is `L`-Lipschitz (mean value inequality on `ℝⁿ`). -/
theorem sub_le (h : DerivNearId f L) (x y : Fin n → ℝ) :
    ‖(f x - x) - (f y - y)‖ ≤ L * ‖x - y‖ := by
  have hd : ∀ z ∈ (univ : Set (Fin n → ℝ)), DifferentiableAt ℝ (f - id) z :=
    fun z _ => (h z).1.sub differentiableAt_id
  have hb : ∀ z ∈ (univ : Set (Fin n → ℝ)), ‖fderiv ℝ (f - id) z‖ ≤ L := by
    intro z _
    rw [fderiv_sub (h z).1 differentiableAt_id, fderiv_id]
    exact (h z).2
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le hd hb (mem_univ y) (mem_univ x)

/-- The lower Lipschitz bound `(1 - L) ‖x - y‖ ≤ ‖f x - f y‖`. -/
theorem lower (h : DerivNearId f L) (x y : Fin n → ℝ) :
    (1 - L) * ‖x - y‖ ≤ ‖f x - f y‖ := by
  have e : x - y = (f x - f y) - ((f x - x) - (f y - y)) := by abel
  have h1 := norm_sub_le (f x - f y) ((f x - x) - (f y - y))
  rw [← e] at h1
  have h2 := h.sub_le x y
  linarith

/-- The upper Lipschitz bound `‖f x - f y‖ ≤ (1 + L) ‖x - y‖`. -/
theorem upper (h : DerivNearId f L) (x y : Fin n → ℝ) :
    ‖f x - f y‖ ≤ (1 + L) * ‖x - y‖ := by
  have e : f x - f y = (x - y) + ((f x - x) - (f y - y)) := by abel
  have h1 := norm_add_le (x - y) ((f x - x) - (f y - y))
  rw [← e] at h1
  have h2 := h.sub_le x y
  linarith

theorem injective (h : DerivNearId f L) (hL : L < 1) : Injective f := by
  intro x y hxy
  have h1 := h.lower x y
  rw [hxy, sub_self, norm_zero] at h1
  have h0 : ‖x - y‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < (1 - L) * ‖x - y‖ := mul_pos (by linarith) hc
    linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- Surjectivity: the preimage of `y` is the fixed point of the contraction `x ↦ x + (y - f x)`. -/
theorem surjective (h : DerivNearId f L) (hL : L < 1) : Surjective f := by
  intro y
  set K : NNReal := ⟨L, h.nonneg⟩
  have hK : ContractingWith K (fun x => x + (y - f x)) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; exact hL, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have e : a + (y - f a) - (b + (y - f b)) = -((f a - a) - (f b - b)) := by abel
    rw [e, norm_neg]
    exact h.sub_le a b
  refine ⟨ContractingWith.fixedPoint _ hK, ?_⟩
  have hx : _ + (y - f _) = _ :=
    ContractingWith.fixedPoint_isFixedPt (f := fun x => x + (y - f x)) hK
  have := congrArg (fun z => z - ContractingWith.fixedPoint _ hK) hx
  simp only [add_sub_cancel_left, sub_self] at this
  exact (sub_eq_zero.1 this).symm

theorem bijective (h : DerivNearId f L) (hL : L < 1) : Bijective f :=
  ⟨h.injective hL, h.surjective hL⟩

/-- `f` as a homeomorphism of `ℝⁿ`; the inverse is `(1 - L)⁻¹`-Lipschitz. -/
def toHomeomorph (h : DerivNearId f L) (hL : L < 1) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toEquiv := Equiv.ofBijective f (h.bijective hL)
  continuous_toFun := h.continuous
  continuous_invFun := by
    have hpos : 0 < 1 - L := by linarith
    refine (LipschitzWith.of_dist_le_mul (K := ⟨(1 - L)⁻¹, (inv_pos.2 hpos).le⟩)
      fun a b => ?_).continuous
    set e := Equiv.ofBijective f (h.bijective hL)
    have h1 := h.lower (e.symm a) (e.symm b)
    have ha : f (e.symm a) = a := e.apply_symm_apply a
    have hb : f (e.symm b) = b := e.apply_symm_apply b
    rw [ha, hb] at h1
    rw [dist_eq_norm, dist_eq_norm]
    show ‖e.symm a - e.symm b‖ ≤ (1 - L)⁻¹ * ‖a - b‖
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact h1

@[simp] theorem toHomeomorph_apply (h : DerivNearId f L) (hL : L < 1) (x : Fin n → ℝ) :
    h.toHomeomorph hL x = f x := rfl

/-- `Function.invFun f` is the inverse of the homeomorphism. -/
theorem invFun_eq (h : DerivNearId f L) (hL : L < 1) :
    invFun f = (h.toHomeomorph hL).symm := by
  funext y
  apply h.injective hL
  rw [Function.invFun_eq (h.surjective hL y)]
  exact ((h.toHomeomorph hL).apply_symm_apply y).symm

theorem apply_invFun (h : DerivNearId f L) (hL : L < 1) (y : Fin n → ℝ) : f (invFun f y) = y :=
  Function.invFun_eq (h.surjective hL y)

theorem invFun_apply (h : DerivNearId f L) (hL : L < 1) (x : Fin n → ℝ) : invFun f (f x) = x :=
  leftInverse_invFun (h.injective hL) x

/-- `Df(x)` is bounded below: `(1 - L) ‖v‖ ≤ ‖Df(x) v‖`. -/
theorem fderiv_lower (h : DerivNearId f L) (x v : Fin n → ℝ) :
    (1 - L) * ‖v‖ ≤ ‖fderiv ℝ f x v‖ := by
  have h1 : ‖(fderiv ℝ f x - ContinuousLinearMap.id ℝ (Fin n → ℝ)) v‖ ≤ L * ‖v‖ :=
    ((fderiv ℝ f x - ContinuousLinearMap.id ℝ (Fin n → ℝ)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h x).2 (norm_nonneg v))
  have e : v = fderiv ℝ f x v - (fderiv ℝ f x - ContinuousLinearMap.id ℝ (Fin n → ℝ)) v := by
    simp
  have h2 := norm_sub_le (fderiv ℝ f x v)
    ((fderiv ℝ f x - ContinuousLinearMap.id ℝ (Fin n → ℝ)) v)
  rw [← e] at h2
  linarith

theorem fderiv_injective (h : DerivNearId f L) (hL : L < 1) (x : Fin n → ℝ) :
    Injective (fderiv ℝ f x) := by
  intro u v huv
  have h1 := h.fderiv_lower x (u - v)
  rw [map_sub, huv, sub_self, norm_zero] at h1
  have h0 : ‖u - v‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < (1 - L) * ‖u - v‖ := mul_pos (by linarith) hc
    linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

theorem fderiv_bijective (h : DerivNearId f L) (hL : L < 1) (x : Fin n → ℝ) :
    Bijective (fderiv ℝ f x) := by
  have hi : Injective (fderiv ℝ f x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := h.fderiv_injective hL x
  exact ⟨hi, LinearMap.injective_iff_surjective.1 hi⟩

/-- `Df(x)` as a continuous linear equivalence. -/
def fderivEquiv (h : DerivNearId f L) (hL : L < 1) (x : Fin n → ℝ) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (LinearEquiv.ofBijective (fderiv ℝ f x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (h.fderiv_bijective hL x)).toContinuousLinearEquiv

theorem coe_fderivEquiv (h : DerivNearId f L) (hL : L < 1) (x : Fin n → ℝ) :
    (h.fderivEquiv hL x : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ f x := by
  ext w : 1
  rfl

/-- An analytic `f` has an analytic inverse (inverse function theorem, Mathlib's
`Homeomorph.contDiff_symm` at order `ω`). -/
theorem analyticOnNhd_invFun (h : DerivNearId f L) (hL : L < 1)
    (hf : AnalyticOnNhd ℝ f univ) : AnalyticOnNhd ℝ (invFun f) univ := by
  rw [h.invFun_eq hL]
  have hc : ContDiff ℝ (⊤ : WithTop ℕ∞) (h.toHomeomorph hL : (Fin n → ℝ) → (Fin n → ℝ)) :=
    contDiff_omega_iff_analyticOnNhd.2 hf
  have hd : ∀ a, HasFDerivAt (h.toHomeomorph hL : (Fin n → ℝ) → (Fin n → ℝ))
      (h.fderivEquiv hL a : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) a := fun a => by
    rw [coe_fderivEquiv]
    exact (h a).1.hasFDerivAt
  exact contDiff_omega_iff_analyticOnNhd.1 (Homeomorph.contDiff_symm _ hd hc)

end DerivNearId

/-! ### Real tori -/

/-- The angle component `θ ↦ (k θ).1` of a real torus `k : ℝⁿ → ℝⁿ × ℝⁿ`. -/
def torusAngle (k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun θ => (k θ).1

/-- The graph function of a real torus over the angles: the action component at the inverse of the
angle map, `G = (k ∘ A⁻¹)₂` with `A⁻¹ = Function.invFun (torusAngle k)`. -/
def torusGraph (k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun φ => (k (invFun (torusAngle k) φ)).2

/-- **The real torus `k` is an analytic graph over the angles** (with derivative constant `L`).
With `A = torusAngle k` and `G = torusGraph k`: `A` is a bijection of `ℝⁿ` with
`‖DA - 1‖ ≤ L < 1`, commuting with `ℤⁿ`, with analytic inverse; `k(θ) = (A θ, G (A θ))`; the image
of `k` is the graph `{z | z.2 = G z.1}` of the analytic `ℤⁿ`-periodic `G`; `k` is injective modulo
`ℤⁿ` (so it embeds `𝕋ⁿ`); `k` is an immersion; and the bi-Lipschitz bounds hold. -/
structure IsAngleGraph (k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (L : ℝ) : Prop where
  lt_one : L < 1
  nearId : DerivNearId (torusAngle k) L
  bijective : Bijective (torusAngle k)
  angle_add_int : ∀ θ (m : Fin n → ℤ),
    torusAngle k (θ + fun i => (m i : ℝ)) = torusAngle k θ + fun i => (m i : ℝ)
  eq_graph : ∀ θ, k θ = (torusAngle k θ, torusGraph k (torusAngle k θ))
  range_eq : range k = {z | z.2 = torusGraph k z.1}
  graph_add_int : ∀ φ (m : Fin n → ℤ), torusGraph k (φ + fun i => (m i : ℝ)) = torusGraph k φ
  analytic_graph : AnalyticOnNhd ℝ (torusGraph k) univ
  analytic_angleInv : AnalyticOnNhd ℝ (invFun (torusAngle k)) univ
  injective_mod : ∀ θ θ' (m : Fin n → ℤ),
    torusAngle k θ' = torusAngle k θ + (fun i => (m i : ℝ)) → θ' = θ + fun i => (m i : ℝ)
  immersion : ∀ θ, Injective (fderiv ℝ k θ)
  angle_lower : ∀ θ θ', (1 - L) * ‖θ - θ'‖ ≤ ‖torusAngle k θ - torusAngle k θ'‖
  fderiv_lower : ∀ θ v, (1 - L) * ‖v‖ ≤ ‖fderiv ℝ k θ v‖

section Graph

variable {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {L : ℝ}

theorem analyticOnNhd_torusAngle (hk : AnalyticOnNhd ℝ k univ) :
    AnalyticOnNhd ℝ (torusAngle k) univ := fun θ _ =>
  (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).analyticAt _ |>.comp (hk θ (mem_univ θ))

theorem fderiv_torusAngle {θ : Fin n → ℝ} (hk : DifferentiableAt ℝ k θ) :
    fderiv ℝ (torusAngle k) θ = (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).comp
      (fderiv ℝ k θ) :=
  ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt.comp θ hk.hasFDerivAt).fderiv

theorem torusAngle_add_int
    (hper : ∀ θ (m : Fin n → ℤ), k (θ + fun i => (m i : ℝ)) = k θ + (fun i => (m i : ℝ), 0))
    (θ : Fin n → ℝ) (m : Fin n → ℤ) :
    torusAngle k (θ + fun i => (m i : ℝ)) = torusAngle k θ + fun i => (m i : ℝ) := by
  simp [torusAngle, hper θ m]

theorem torusGraph_torusAngle (hA : DerivNearId (torusAngle k) L) (hL : L < 1) (θ : Fin n → ℝ) :
    torusGraph k (torusAngle k θ) = (k θ).2 := by
  simp only [torusGraph, hA.invFun_apply hL]

/-- **The graph adapter** (pure form): an analytic real torus with `k(θ + m) = k(θ) + (m, 0)` whose
angle map is within `L < 1` of the identity in derivative is an analytic graph over the angles. -/
theorem isAngleGraph_of_derivNearId (hk : AnalyticOnNhd ℝ k univ)
    (hper : ∀ θ (m : Fin n → ℤ), k (θ + fun i => (m i : ℝ)) = k θ + (fun i => (m i : ℝ), 0))
    (hA : DerivNearId (torusAngle k) L) (hL : L < 1) : IsAngleGraph k L := by
  have hdk : ∀ θ, DifferentiableAt ℝ k θ := fun θ => (hk θ (mem_univ θ)).differentiableAt
  have hinv := hA.analyticOnNhd_invFun hL (analyticOnNhd_torusAngle hk)
  have hG : ∀ θ, torusGraph k (torusAngle k θ) = (k θ).2 := torusGraph_torusAngle hA hL
  refine ⟨hL, hA, hA.bijective hL, torusAngle_add_int hper, fun θ => ?_, ?_, fun φ m => ?_, ?_,
    hinv, fun θ θ' m h => ?_, fun θ => ?_, hA.lower, fun θ v => ?_⟩
  · rw [hG θ]; rfl
  · ext z
    simp only [mem_range, mem_ofPred_eq]
    constructor
    · rintro ⟨θ, rfl⟩
      exact (hG θ).symm
    · intro hz
      refine ⟨invFun (torusAngle k) z.1, Prod.ext (hA.apply_invFun hL z.1) ?_⟩
      exact hz.symm
  · obtain ⟨θ, rfl⟩ := hA.surjective hL φ
    rw [← torusAngle_add_int hper, hG, hG, hper θ m]
    simp
  · intro φ _
    exact ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).analyticAt _).comp
      ((hk _ (mem_univ _)).comp (hinv φ (mem_univ φ)))
  · apply hA.injective hL
    rw [h, torusAngle_add_int hper]
  · intro u v huv
    apply hA.fderiv_injective hL θ
    rw [fderiv_torusAngle (hdk θ)]
    simp [huv]
  · have h1 := hA.fderiv_lower θ v
    rw [fderiv_torusAngle (hdk θ)] at h1
    exact h1.trans (norm_fst_le _)

end Graph

end KAM.Application
