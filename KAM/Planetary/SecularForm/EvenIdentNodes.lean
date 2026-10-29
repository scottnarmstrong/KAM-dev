/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Symmetry
public import KAM.Planetary.SecularForm.Quadratic
public import KAM.Planetary.SecularForm.Quadratic.Jet
public import KAM.Planetary.SecularForm.Quadratic.Calculus
public import KAM.Planetary.SecularForm.Quadratic.Coeff
public import KAM.Planetary.SecularForm.ModelTransfer
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.PGAssembly.JetsPolar

/-!
# Secular form: literal exports of the evenness nodes of Part 8

Graph-gap package GAP-P8c (append-only).  Literal conclusions of `stepP:p8:ev-tay`,
`stepP:p8:ev-quad` and the bundle `bpP:p8:evenness`, built from the landed `evenness`,
`evenness_taylor`, `quadratic_form` and `same_jets`.

* `iteratedFDeriv_invariant_of_equiv`: a function invariant near `0` under a continuous linear
  equivalence has an invariant jet at `0`.
* `slowRotCLE`, `slowReflCLE`: the rotation of the planar vectors `(ξᵢ, ηᵢ)` and the reflection
  `η ↦ -η`, generating the diagonal `O(2)`.
* `p8_ev_tay`: odd jets vanish, the origin is critical, all jets are `O(2)`-invariant, and the jets
  are real analytic in `Λ`.
* `p8_ev_quad`: the `ξη`-block of the Hessian vanishes and the `ηη`-block equals the `ξξ`-block.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

section EquivariantJet

/-- A function that is invariant near `0` under a continuous linear equivalence has an invariant
jet at `0`: `Dᵏf(0) ∘ (L, …, L) = Dᵏf(0)`. -/
theorem iteratedFDeriv_invariant_of_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] E) {f : E → F}
    (h : f =ᶠ[𝓝 0] fun u => f (L u)) (k : ℕ) :
    (iteratedFDeriv ℝ k f 0).compContinuousLinearMap (fun _ => (L : E →L[ℝ] E)) =
      iteratedFDeriv ℝ k f 0 := by
  have e1 : iteratedFDeriv ℝ k f 0 = iteratedFDeriv ℝ k (fun u => f (L u)) 0 :=
    (h.iteratedFDeriv ℝ k).eq_of_nhds
  have e2 : iteratedFDeriv ℝ k (fun u => f (L u)) 0 =
      (iteratedFDeriv ℝ k f (L 0)).compContinuousLinearMap fun _ => (L : E →L[ℝ] E) := by
    have := L.iteratedFDerivWithin_comp_right f (uniqueDiffOn_univ) (mem_univ (L 0)) k
    simp only [preimage_univ, iteratedFDerivWithin_univ] at this
    exact this
  rw [map_zero] at e2
  exact (e1.trans e2).symm

/-- Second-order form of `iteratedFDeriv_invariant_of_equiv`. -/
theorem fderiv_fderiv_invariant_of_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) {f : E → ℝ} (h : f =ᶠ[𝓝 0] fun u => f (L u)) (u v : E) :
    fderiv ℝ (fderiv ℝ f) 0 (L u) (L v) = fderiv ℝ (fderiv ℝ f) 0 u v := by
  have := congrArg (fun M => M ![u, v]) (iteratedFDeriv_invariant_of_equiv L h 2)
  simpa [iteratedFDeriv_two_apply] using this

end EquivariantJet

namespace SecularForm
variable {n : ℕ}

/-- The rotation by `θ` of every planar vector `(ξᵢ, ηᵢ)`, as a continuous linear map. -/
def slowRotCLM (θ : ℝ) : (Vec n × Vec n) →L[ℝ] (Vec n × Vec n) :=
  ((Real.cos θ • ContinuousLinearMap.fst ℝ (Vec n) (Vec n) -
      Real.sin θ • ContinuousLinearMap.snd ℝ (Vec n) (Vec n)).prod
    (Real.sin θ • ContinuousLinearMap.fst ℝ (Vec n) (Vec n) +
      Real.cos θ • ContinuousLinearMap.snd ℝ (Vec n) (Vec n)))

theorem slowRotCLM_apply (θ : ℝ) (u : Vec n × Vec n) :
    slowRotCLM θ u = (Real.cos θ • u.1 - Real.sin θ • u.2, Real.sin θ • u.1 + Real.cos θ • u.2) :=
  rfl

/-- The rotation of the planar vectors `(ξᵢ, ηᵢ)` by `θ` as a continuous linear equivalence. -/
def slowRotCLE (θ : ℝ) : (Vec n × Vec n) ≃L[ℝ] (Vec n × Vec n) :=
  ContinuousLinearEquiv.equivOfInverse (slowRotCLM θ) (slowRotCLM (-θ))
    (fun u => Prod.ext (funext fun i => by
        simp only [slowRotCLM_apply, Real.cos_neg, Real.sin_neg, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, neg_mul]
        linear_combination (u.1 i) * Real.cos_sq_add_sin_sq θ)
      (funext fun i => by
        simp only [slowRotCLM_apply, Real.cos_neg, Real.sin_neg, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, neg_mul]
        linear_combination (u.2 i) * Real.cos_sq_add_sin_sq θ))
    (fun u => Prod.ext (funext fun i => by
        simp only [slowRotCLM_apply, Real.cos_neg, Real.sin_neg, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, neg_mul]
        linear_combination (u.1 i) * Real.cos_sq_add_sin_sq θ)
      (funext fun i => by
        simp only [slowRotCLM_apply, Real.cos_neg, Real.sin_neg, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, neg_mul]
        linear_combination (u.2 i) * Real.cos_sq_add_sin_sq θ))

theorem slowRotCLE_apply (θ : ℝ) (u : Vec n × Vec n) : slowRotCLE θ u = slowRotCLM θ u := rfl

/-- The reflection `η ↦ -η` of the planar vectors. -/
def slowReflCLE : (Vec n × Vec n) ≃L[ℝ] (Vec n × Vec n) :=
  (ContinuousLinearEquiv.refl ℝ (Vec n)).prodCongr (ContinuousLinearEquiv.neg ℝ)

theorem slowReflCLE_apply (u : Vec n × Vec n) : slowReflCLE u = (u.1, -u.2) := rfl

/-- Near `0`, the slow point over a fixed action vector of the action domain is in the chart. -/
theorem eventually_mem_slowDom_zero (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) :
    ∀ᶠ u : Vec n × Vec n in 𝓝 0, ((u.1, I, u.2) : Slow n) ∈ slowDom D := by
  obtain ⟨a, ha, rfl⟩ := hI
  have hpos : ∀ i, 0 < action D a i := fun i => by
    have := ha.1 i
    have := D.hm i; have := D.hG; have := D.hm0
    unfold action; positivity
  have hev : ∀ᶠ u : Vec n × Vec n in 𝓝 0,
      ∀ i, 0 < action D a i ∧ (u.1 i ^ 2 + u.2 i ^ 2) / 2 < action D a i := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous fun u : Vec n × Vec n => (u.1 i ^ 2 + u.2 i ^ 2) / 2 := by fun_prop
    have h0 : (fun u : Vec n × Vec n => (u.1 i ^ 2 + u.2 i ^ 2) / 2) 0 < action D a i := by
      simpa using hpos i
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h0] with u hu
    exact ⟨hpos i, hu⟩
  filter_upwards [hev] with u hu
  exact (mem_slowDom_iff D _).2 hu

/-- The secular function is invariant near `0` under the rotation of the planar vectors. -/
theorem slowSecular_eventually_rotate (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D)
    (b : Bool) (θ : ℝ) :
    slowSecular D b I =ᶠ[𝓝 0] fun u => slowSecular D b I (slowRotCLE θ u) := by
  filter_upwards [eventually_mem_slowDom_zero D hI] with u hu
  have h := (evenness D hu b θ).2.2.2
  unfold slowSecular
  rw [slowRotCLE_apply, slowRotCLM_apply]
  convert h.symm using 2
  simp only [rotateSlow, rot]
  refine Prod.ext (funext fun i => ?_) (Prod.ext rfl (funext fun i => ?_)) <;>
    simp [sub_eq_add_neg]

/-- The secular function is invariant near `0` under the reflection `η ↦ -η`. -/
theorem slowSecular_eventually_reflect (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D)
    (b : Bool) :
    slowSecular D b I =ᶠ[𝓝 0] fun u => slowSecular D b I (slowReflCLE u) := by
  filter_upwards [eventually_mem_slowDom_zero D hI] with u hu
  have h := (evenness D hu b 0).2.1
  unfold slowSecular
  rw [slowReflCLE_apply]
  exact h.symm

end SecularForm

end KAM.Planetary

end
