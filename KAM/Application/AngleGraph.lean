/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Graph
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Analytic graphs over the angles (no near-identity constant)

Pure geometry, no certificate data. `IsAngleGraph k L` (`Graph.lean`) records the graph property
of a real torus together with the near-identity bound `‖DA - 1‖ ≤ L < 1` that proves it. Other
criteria (the clock-triangular one of `ClockGraph.lean`) prove the same qualitative property with
other estimates, so the property itself is isolated here:

* `IsAnalyticAngleGraph k`: `k : ℝⁿ → ℝⁿ × ℝⁿ` is analytic; `A = torusAngle k` is a bijection of
  `ℝⁿ` commuting with `ℤⁿ`, with analytic inverse and invertible derivative everywhere;
  `k(θ) = (A θ, G (A θ))` and `range k = {z | z.2 = G z.1}` for the analytic `ℤⁿ`-periodic
  `G = torusGraph k`; `k` is injective modulo `ℤⁿ` (it embeds `𝕋ⁿ`) and an immersion.
* `isAnalyticAngleGraph_of_bijective`: an analytic `k` with `k(θ + m) = k(θ) + (m, 0)` whose
  angle map is bijective with injective derivative everywhere is an analytic angle graph. The
  inverse is continuous by the inverse function theorem (`A` is an open map,
  `isOpenMap_of_hasStrictFDerivAt_equiv`) and analytic by `Homeomorph.contDiff_symm` at order
  `ω`. (Bijectivity is the global input; Hadamard's theorem would give it from the derivative
  alone, but it is not in Mathlib.)
* `IsAngleGraph.isAnalyticAngleGraph`: the near-identity graph adapter lands in this notion.
-/

@[expose] public noncomputable section

open Set Function

namespace KAM.Application

variable {n : ℕ}

/-- **`k` is an analytic graph over the angles** (qualitative form). With `A = torusAngle k` and
`G = torusGraph k`: `k` is analytic; `A` is a bijection of `ℝⁿ` commuting with `ℤⁿ`, with analytic
inverse and invertible derivative everywhere; `k(θ) = (A θ, G (A θ))`; the image of `k` is the
graph `{z | z.2 = G z.1}` of the analytic `ℤⁿ`-periodic `G`; `k` is injective modulo `ℤⁿ` (so it
embeds `𝕋ⁿ`) and an immersion. -/
structure IsAnalyticAngleGraph (k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) : Prop where
  analytic : AnalyticOnNhd ℝ k univ
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
  fderiv_injective : ∀ θ, Injective (fderiv ℝ (torusAngle k) θ)
  immersion : ∀ θ, Injective (fderiv ℝ k θ)

section Constructor

variable {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}

/-- An injective endomorphism of `ℝⁿ` as a continuous linear equivalence. -/
def clmEquivOfInjective (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hL : Injective L) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (LinearEquiv.ofBijective (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    ⟨hL, LinearMap.injective_iff_surjective.1 hL⟩).toContinuousLinearEquiv

theorem coe_clmEquivOfInjective (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hL : Injective L) :
    (clmEquivOfInjective L hL : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = L := by
  ext w : 1
  rfl

/-- A bijective analytic map of `ℝⁿ` with injective derivative everywhere is a homeomorphism (it
is an open map by the inverse function theorem). -/
def homeomorphOfAnalytic (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : AnalyticOnNhd ℝ f univ)
    (hb : Bijective f) (hD : ∀ x, Injective (fderiv ℝ f x)) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen
    (continuous_iff_continuousAt.2 fun x => (hf x (mem_univ x)).continuousAt)
    (isOpenMap_of_hasStrictFDerivAt_equiv (f' := fun x => clmEquivOfInjective _ (hD x))
      fun x => by
        rw [coe_clmEquivOfInjective]
        exact (hf x (mem_univ x)).hasStrictFDerivAt)

theorem homeomorphOfAnalytic_apply (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : AnalyticOnNhd ℝ f univ) (hb : Bijective f) (hD : ∀ x, Injective (fderiv ℝ f x))
    (x : Fin n → ℝ) : homeomorphOfAnalytic f hf hb hD x = f x := rfl

/-- The inverse of a bijective analytic map with injective derivative is analytic. -/
theorem analyticOnNhd_invFun_of_bijective {f : (Fin n → ℝ) → (Fin n → ℝ)}
    (hf : AnalyticOnNhd ℝ f univ) (hb : Bijective f) (hD : ∀ x, Injective (fderiv ℝ f x)) :
    AnalyticOnNhd ℝ (invFun f) univ := by
  set e := homeomorphOfAnalytic f hf hb hD
  have hinv : invFun f = e.symm := by
    funext y
    apply hb.1
    rw [Function.invFun_eq (hb.2 y)]
    exact (e.apply_symm_apply y).symm
  rw [hinv]
  have hc : ContDiff ℝ (⊤ : WithTop ℕ∞) (e : (Fin n → ℝ) → (Fin n → ℝ)) :=
    contDiff_omega_iff_analyticOnNhd.2 hf
  have hd : ∀ a, HasFDerivAt (e : (Fin n → ℝ) → (Fin n → ℝ))
      (clmEquivOfInjective _ (hD a) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) a := fun a => by
    rw [coe_clmEquivOfInjective]
    exact (hf a (mem_univ a)).differentiableAt.hasFDerivAt
  exact contDiff_omega_iff_analyticOnNhd.1 (Homeomorph.contDiff_symm _ hd hc)

/-- **The general graph constructor**: an analytic real torus with `k(θ + m) = k(θ) + (m, 0)`
whose angle map is bijective with injective derivative everywhere is an analytic graph over the
angles. -/
theorem isAnalyticAngleGraph_of_bijective (hk : AnalyticOnNhd ℝ k univ)
    (hper : ∀ θ (m : Fin n → ℤ), k (θ + fun i => (m i : ℝ)) = k θ + (fun i => (m i : ℝ), 0))
    (hb : Bijective (torusAngle k)) (hD : ∀ θ, Injective (fderiv ℝ (torusAngle k) θ)) :
    IsAnalyticAngleGraph k := by
  have hA := analyticOnNhd_torusAngle hk
  have hinv := analyticOnNhd_invFun_of_bijective hA hb hD
  have hG : ∀ θ, torusGraph k (torusAngle k θ) = (k θ).2 := fun θ => by
    simp only [torusGraph, leftInverse_invFun hb.1 θ]
  have hAinv : ∀ φ, torusAngle k (invFun (torusAngle k) φ) = φ := fun φ =>
    Function.invFun_eq (hb.2 φ)
  refine ⟨hk, hb, torusAngle_add_int hper, fun θ => ?_, ?_, fun φ m => ?_, ?_, hinv,
    fun θ θ' m h => ?_, hD, fun θ => ?_⟩
  · rw [hG θ]; rfl
  · ext z
    simp only [mem_range, mem_ofPred_eq]
    constructor
    · rintro ⟨θ, rfl⟩
      exact (hG θ).symm
    · intro hz
      exact ⟨invFun (torusAngle k) z.1, Prod.ext (hAinv z.1) hz.symm⟩
  · obtain ⟨θ, rfl⟩ := hb.2 φ
    rw [← torusAngle_add_int hper, hG, hG, hper θ m]
    simp
  · intro θ _
    have h1 : AnalyticAt ℝ (fun φ => k (invFun (torusAngle k) φ)) θ :=
      (hk _ (mem_univ _)).comp (hinv θ (mem_univ θ))
    exact (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).analyticAt _ |>.comp h1
  · apply hb.1
    rw [h, torusAngle_add_int hper]
  · intro u v huv
    apply hD θ
    have hdk : DifferentiableAt ℝ k θ := (hk θ (mem_univ θ)).differentiableAt
    rw [fderiv_torusAngle hdk]
    simp only [ContinuousLinearMap.comp_apply, huv]

end Constructor

namespace IsAnalyticAngleGraph

variable {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} (h : IsAnalyticAngleGraph k)
include h

/-- The angle map as a homeomorphism of `ℝⁿ`. -/
def angleHomeomorph : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  homeomorphOfAnalytic (torusAngle k) (analyticOnNhd_torusAngle h.analytic) h.bijective
    h.fderiv_injective

theorem angleHomeomorph_apply (θ : Fin n → ℝ) : h.angleHomeomorph θ = torusAngle k θ := rfl

theorem apply_invFun (φ : Fin n → ℝ) : torusAngle k (invFun (torusAngle k) φ) = φ :=
  Function.invFun_eq (h.bijective.2 φ)

theorem invFun_apply (θ : Fin n → ℝ) : invFun (torusAngle k) (torusAngle k θ) = θ :=
  leftInverse_invFun h.bijective.1 θ

theorem continuous : Continuous k :=
  continuous_iff_continuousAt.2 fun θ => (h.analytic θ (mem_univ θ)).continuousAt

theorem continuous_angleInv : Continuous (invFun (torusAngle k)) :=
  continuous_iff_continuousAt.2 fun φ => (h.analytic_angleInv φ (mem_univ φ)).continuousAt

theorem continuous_graph : Continuous (torusGraph k) :=
  continuous_iff_continuousAt.2 fun φ => (h.analytic_graph φ (mem_univ φ)).continuousAt

theorem mem_range_iff (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    z ∈ range k ↔ z.2 = torusGraph k z.1 := by
  rw [h.range_eq]; rfl

/-- The torus point over the angle `φ`: `k (A⁻¹ φ) = (φ, G φ)`. -/
theorem k_invFun (φ : Fin n → ℝ) : k (invFun (torusAngle k) φ) = (φ, torusGraph k φ) := by
  rw [h.eq_graph, h.apply_invFun]

end IsAnalyticAngleGraph

/-- **The near-identity graph adapter lands in `IsAnalyticAngleGraph`**: `IsAngleGraph k L`
(`L < 1`) of an analytic `k` is an analytic angle graph. -/
theorem IsAngleGraph.isAnalyticAngleGraph {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {L : ℝ}
    (h : IsAngleGraph k L) (hk : AnalyticOnNhd ℝ k univ) : IsAnalyticAngleGraph k :=
  ⟨hk, h.bijective, h.angle_add_int, h.eq_graph, h.range_eq, h.graph_add_int, h.analytic_graph,
    h.analytic_angleInv, h.injective_mod, h.nearId.fderiv_injective h.lt_one, h.immersion⟩

end KAM.Application
