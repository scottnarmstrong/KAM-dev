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
public import KAM.Planetary.SecularForm.Laplace
public import KAM.Planetary.SecularForm.LaplaceIdentities

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

/-- The embedding `(Λ, (ξ, η)) ↦ (ξ, Λ, η)` as a continuous linear map. -/
def slowEmbCLM (n : ℕ) : (Vec n × (Vec n × Vec n)) →L[ℝ] Slow n :=
  ((ContinuousLinearMap.fst ℝ (Vec n) (Vec n)).comp (ContinuousLinearMap.snd ℝ (Vec n)
      (Vec n × Vec n))).prod
    ((ContinuousLinearMap.fst ℝ (Vec n) (Vec n × Vec n)).prod
      ((ContinuousLinearMap.snd ℝ (Vec n) (Vec n)).comp
        (ContinuousLinearMap.snd ℝ (Vec n) (Vec n × Vec n))))

theorem slowEmbCLM_apply (I : Vec n) (u : Vec n × Vec n) :
    slowEmbCLM n (I, u) = (u.1, I, u.2) := rfl

/-- The slow `k`-jet of the secular function at `0` is real analytic in the actions. -/
theorem analyticAt_slowSecular_jet (D : Data n) {I0 : Vec n} (hI0 : I0 ∈ actionDomain D)
    (b : Bool) (k : ℕ) :
    AnalyticAt ℝ (fun I => iteratedFDeriv ℝ k (slowSecular D b I) 0) I0 := by
  obtain ⟨a, ha, rfl⟩ := hI0
  obtain ⟨r, hr0, -, -, hall⟩ := perturbation_analytic D ha
  have hA : AnalyticOnNhd ℝ (secular D b) (realDisc D a r) := (hall b).2.2.2.2.1
  set emb := slowEmbCLM n with hemb
  set N : Set (Vec n × (Vec n × Vec n)) := emb ⁻¹' realDisc D a r with hNdef
  have hN : IsOpen N := (isOpen_realDisc D a hr0).preimage emb.continuous
  set G : Vec n × (Vec n × Vec n) → ℝ := fun p => secular D b (emb p) with hG
  have hGA : AnalyticOnNhd ℝ G N := fun x hx => (hA _ hx).comp (emb.analyticAt x)
  have h0 : ((action D a, (0 : Vec n × Vec n)) : Vec n × (Vec n × Vec n)) ∈ N := by
    show emb (action D a, 0) ∈ realDisc D a r
    intro i
    simp [hemb, slowEmbCLM, inclusion, hr0]
  let inr : (Vec n × Vec n) →L[ℝ] Vec n × (Vec n × Vec n) :=
    ContinuousLinearMap.inr ℝ (Vec n) (Vec n × Vec n)
  have hEq : ∀ I : Vec n, (I, (0 : Vec n × Vec n)) ∈ N →
      iteratedFDeriv ℝ k (slowSecular D b I) 0 =
        (iteratedFDeriv ℝ k G (I, 0)).compContinuousLinearMap fun _ => inr := by
    intro I hI
    set c : Vec n × (Vec n × Vec n) := (I, 0) with hc
    have hcomp : slowSecular D b I = (fun z => G (z + c)) ∘ inr := by
      funext w; simp [inr, hc, hG, hemb, slowSecular, slowEmbCLM_apply]
    have hadd : Continuous fun z : Vec n × (Vec n × Vec n) => z + c :=
      continuous_id.add continuous_const
    have hU : IsOpen ((fun z : Vec n × (Vec n × Vec n) => z + c) ⁻¹' N) := hN.preimage hadd
    have hcd : ContDiffOn ℝ k (fun z => G (z + c))
        ((fun z : Vec n × (Vec n × Vec n) => z + c) ⁻¹' N) :=
      (hGA.contDiffOn hN.uniqueDiffOn).comp (contDiff_id.add contDiff_const).contDiffOn
        fun z hz => hz
    have key := iteratedFDeriv_comp_clm_of_isOpen hU hcd inr (x := 0)
      (by simpa [inr, hc] using hI) (le_refl k)
    rw [hcomp, key, iteratedFDeriv_comp_add_right]
    simp [inr, hc]
  have hV : IsOpen {I : Vec n | (I, (0 : Vec n × Vec n)) ∈ N} :=
    hN.preimage (continuous_id.prodMk continuous_const)
  have hmap : AnalyticAt ℝ (fun I : Vec n => (I, (0 : Vec n × Vec n))) (action D a) :=
    analyticAt_id.prod analyticAt_const
  have hJ : AnalyticAt ℝ (fun I : Vec n => iteratedFDeriv ℝ k G (I, 0)) (action D a) :=
    AnalyticAt.comp_of_eq ((hGA.iteratedFDeriv_of_isOpen hN k) _ h0) hmap rfl
  let T := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := ℝ)
    (fun _ : Fin k => inr)
  have hT : AnalyticAt ℝ (fun I : Vec n => T (iteratedFDeriv ℝ k G (I, 0))) (action D a) :=
    (T.analyticAt _).comp hJ
  refine hT.congr ?_
  filter_upwards [hV.mem_nhds h0] with I hI
  exact (hEq I hI).symm

theorem analyticOnNhd_slowSecular_jet (D : Data n) (b : Bool) (k : ℕ) :
    AnalyticOnNhd ℝ (fun I => iteratedFDeriv ℝ k (slowSecular D b I) 0) (actionDomain D) :=
  fun _ hI => analyticAt_slowSecular_jet D hI b k

/-- `stepP:p8:ev-tay`: the odd jets of the secular function at `0` vanish (in particular the
origin is critical), and every jet, hence the degree-`2d` Taylor part, is invariant under the
diagonal `O(2)` acting on the planar vectors `(ξᵢ, ηᵢ)` (rotations and the reflection). -/
theorem p8_ev_tay (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) (b : Bool) :
    (∀ k : ℕ, iteratedFDeriv ℝ (2 * k + 1) (slowSecular D b I) 0 = 0) ∧
    fderiv ℝ (slowSecular D b I) 0 = 0 ∧
    (∀ (k : ℕ) (θ : ℝ) (u : Vec n × Vec n),
      iteratedFDeriv ℝ k (slowSecular D b I) 0 (fun _ => slowRotCLE θ u) =
        iteratedFDeriv ℝ k (slowSecular D b I) 0 (fun _ => u)) ∧
    (∀ (k : ℕ) (u : Vec n × Vec n),
      iteratedFDeriv ℝ k (slowSecular D b I) 0 (fun _ => (u.1, -u.2)) =
        iteratedFDeriv ℝ k (slowSecular D b I) 0 (fun _ => u)) := by
  refine ⟨fun k => evenness_taylor D hI b k, ?_, fun k θ u => ?_, fun k u => ?_⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    have h := evenness_taylor D hI b 0
    have := congrArg (fun M => M (fun _ => v)) h
    simpa [iteratedFDeriv_one_apply] using this
  · have := congrArg (fun M => M (fun _ => u))
      (iteratedFDeriv_invariant_of_equiv (slowRotCLE θ) (slowSecular_eventually_rotate D hI b θ) k)
    simpa using this
  · have := congrArg (fun M => M (fun _ => u))
      (iteratedFDeriv_invariant_of_equiv slowReflCLE (slowSecular_eventually_reflect D hI b) k)
    simpa [slowReflCLE_apply] using this

/-- `stepP:p8:ev-quad`: in the Hessian of the secular function at `0`, the `ξη`-block vanishes
(evenness in `η` alone) and the `ηη`-block equals the `ξξ`-block (the quarter turn
`(ξ, η) ↦ (-η, ξ)`).  Full-`n` statement, for both models. -/
theorem p8_ev_quad (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) (b : Bool) :
    (∀ ξ η : Vec n, fderiv ℝ (fderiv ℝ (slowSecular D b I)) 0 (ξ, 0) (0, η) = 0) ∧
    (∀ η η' : Vec n, fderiv ℝ (fderiv ℝ (slowSecular D b I)) 0 (0, η) (0, η') =
      fderiv ℝ (fderiv ℝ (slowSecular D b I)) 0 (η, 0) (η', 0)) := by
  set H := fderiv ℝ (fderiv ℝ (slowSecular D b I)) 0 with hH
  constructor
  · intro ξ η
    have h := fderiv_fderiv_invariant_of_equiv slowReflCLE (slowSecular_eventually_reflect D hI b)
      (ξ, 0) (0, η)
    simp only [slowReflCLE_apply, neg_zero] at h
    have h2 : H (ξ, 0) (0, -η) = -H (ξ, 0) (0, η) := by
      have : ((0 : Vec n), -η) = -((0 : Vec n), η) := by simp
      rw [this, map_neg]
    rw [h2] at h
    linarith
  · intro η η'
    have h := fderiv_fderiv_invariant_of_equiv (slowRotCLE (π / 2))
      (slowSecular_eventually_rotate D hI b (π / 2)) (0, η) (0, η')
    have e : ∀ w : Vec n, slowRotCLE (π / 2) (0, w) = -(w, 0) := fun w => by
      rw [slowRotCLE_apply, slowRotCLM_apply]
      simp
    simp only [e, map_neg, neg_apply, neg_neg] at h
    exact h.symm

/-- The fixed-model secular function is analytic in the slow variables at `0`. -/
theorem analyticAt_slowSecular_fix (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    AnalyticAt ℝ (slowSecular D false (action D a)) 0 := by
  obtain ⟨r, hr0, -, -, hall⟩ := perturbation_analytic D ha
  have hx : ((0 : Vec n), action D a, (0 : Vec n)) ∈ realDisc D a r := by
    refine fun i => ⟨?_, ?_, ?_⟩ <;> simp [inclusion, hr0]
  have hA := (hall false).2.2.2.2.1 _ hx
  have hemb : AnalyticAt ℝ (fun u : Vec n × Vec n => slowEmbCLM n (action D a, u)) 0 :=
    (slowEmbCLM n).analyticAt _ |>.comp (analyticAt_const.prod analyticAt_id)
  exact hA.comp_of_eq hemb rfl

/-- The quadratic part of the fixed-model secular function: `ξᵀ A ξ + ηᵀ A η`. -/
theorem slowSecular_fix_second_jet (D : Data n) {a : Vec n} (ha : a ∈ axes n)
    (u : Vec n × Vec n) :
    iteratedFDeriv ℝ 2 (slowSecular D false (action D a)) 0 (fun _ => u) / 2 =
      quad (coeffs D a) u.1 + quad (coeffs D a) u.2 := by
  set f := slowSecular D false (action D a) with hf
  have hfa : AnalyticAt ℝ f 0 := analyticAt_slowSecular_fix D ha
  have h1 : iteratedFDeriv ℝ 2 f 0 (fun _ => u) = iteratedDeriv 2 (fun s : ℝ => f (s • u)) 0 := by
    rw [iteratedDeriv_two_ray hfa.contDiffAt, iteratedFDeriv_two_apply]
  set Q := quad (coeffs D a) u.1 + quad (coeffs D a) u.2 with hQ
  have hray : (fun s : ℝ => f (s • u)) = fun s =>
      rayRemainder D a u.1 u.2 s + (constantTerm D a + Q * s ^ 2) := by
    funext s
    simp only [hf, slowSecular, rayRemainder, raySlow, Prod.smul_fst, Prod.smul_snd, hQ]
    ring
  have hRa := analyticAt_rayRemainder D ha u.1 u.2
  have hpa : AnalyticAt ℝ (fun s : ℝ => constantTerm D a + Q * s ^ 2) 0 := by fun_prop
  rw [h1, hray, iteratedDeriv_fun_add hRa.contDiffAt hpa.contDiffAt,
    iteratedDeriv_two_rayRemainder D ha u.1 u.2, iteratedDeriv_two_quadratic]
  ring

/-- Real-symmetry of the secular matrix. -/
theorem coeffs_transpose (D : Data n) (a : Vec n) : (coeffs D a).transpose = coeffs D a := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (coeffs_hermitian D a).eq

/-- The quadratic part of the secular function, both models: `ξᵀ A ξ + ηᵀ A η` with
`A = coeffs D (axis D Λ)`. -/
theorem slowSecular_second_jet (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) (b : Bool)
    (u : Vec n × Vec n) :
    iteratedFDeriv ℝ 2 (slowSecular D b I) 0 (fun _ => u) / 2 =
      quad (coeffs D (axis D I)) u.1 + quad (coeffs D (axis D I)) u.2 := by
  obtain ⟨a, ha, rfl⟩ := hI
  rw [axis_action D ha]
  cases b
  · exact slowSecular_fix_second_jet D ha u
  · rw [same_jets D ⟨a, ha, rfl⟩ 2 (by norm_num)]
    exact slowSecular_fix_second_jet D ha u

/-- `bpP:p8:evenness`, literal and for both models: the four invariances of `S` on the chart
domain; the Taylor expansion at `(ξ, η) = 0` has only even total degree, the origin is critical,
every jet (so the degree-`2d` part) is `O(2)`-invariant, the jets are real analytic in `Λ`, and the
degree-two part is `ξᵀ A(Λ) ξ + ηᵀ A(Λ) η` with `A = Aᵀ` real analytic in `Λ`. -/
theorem p8_evenness_full (D : Data n) (b : Bool) :
    (∀ x ∈ slowDom D, ∀ θ : ℝ,
      secular D b (-x.1, x.2.1, -x.2.2) = secular D b x ∧
      secular D b (x.1, x.2.1, -x.2.2) = secular D b x ∧
      secular D b (-x.1, x.2.1, x.2.2) = secular D b x ∧
      secular D b (rotateSlow θ x) = secular D b x) ∧
    (∀ I ∈ actionDomain D,
      (∀ k : ℕ, iteratedFDeriv ℝ (2 * k + 1) (slowSecular D b I) 0 = 0) ∧
      fderiv ℝ (slowSecular D b I) 0 = 0 ∧
      (∀ (k : ℕ) (θ : ℝ) (u : Vec n × Vec n),
        iteratedFDeriv ℝ k (slowSecular D b I) 0 (fun _ => slowRotCLE θ u) =
          iteratedFDeriv ℝ k (slowSecular D b I) 0 (fun _ => u)) ∧
      (∀ (k : ℕ) (u : Vec n × Vec n),
        iteratedFDeriv ℝ k (slowSecular D b I) 0 (fun _ => (u.1, -u.2)) =
          iteratedFDeriv ℝ k (slowSecular D b I) 0 (fun _ => u)) ∧
      (∀ u : Vec n × Vec n, iteratedFDeriv ℝ 2 (slowSecular D b I) 0 (fun _ => u) / 2 =
        quad (coeffs D (axis D I)) u.1 + quad (coeffs D (axis D I)) u.2) ∧
      (coeffs D (axis D I)).transpose = coeffs D (axis D I)) ∧
    (∀ k : ℕ, AnalyticOnNhd ℝ (fun I => iteratedFDeriv ℝ k (slowSecular D b I) 0)
      (actionDomain D)) ∧
    AnalyticOnNhd ℝ (fun I => coeffs D (axis D I)) (actionDomain D) := by
  refine ⟨fun x hx θ => evenness D hx b θ, fun I hI => ?_,
    fun k => analyticOnNhd_slowSecular_jet D b k, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := p8_ev_tay D hI b
    exact ⟨h1, h2, h3, h4, slowSecular_second_jet D hI b, coeffs_transpose D _⟩
  · rintro I ⟨a, ha, rfl⟩
    have hA := coeffs_analytic D (axis D (action D a)) (by rw [axis_action D ha]; exact ha)
    exact hA.comp_of_eq (analyticAt_axis D _) rfl

/-! ### Laplace coefficients: parity and analyticity at `α = 0` -/

/-- Parity of the Laplace coefficients: `b_s^{(k)}(-α) = (-1)^k b_s^{(k)}(α)`. -/
theorem laplace_def_neg_arg (s : ℝ) (k : ℕ) (α : ℝ) :
    laplace_def s k (-α) = (-1) ^ k * laplace_def s k α := by
  unfold laplace_def
  set g : ℝ → ℝ := fun t => Real.cos (((k : ℤ) : ℝ) * t) *
    (1 + α ^ 2 - 2 * α * Real.cos t) ^ (-s) with hg
  have hper : Function.Periodic g (2 * π) := fun t => by
    simp only [hg, Int.cast_natCast]
    rw [show (k : ℝ) * (t + 2 * π) = k * t + k * (2 * π) by ring, Real.cos_add_nat_mul_two_pi,
      Real.cos_add_two_pi]
  have hk : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; simp
  have h1 : ∀ t : ℝ, Real.cos (((k : ℤ) : ℝ) * t) *
      (1 + (-α) ^ 2 - 2 * (-α) * Real.cos t) ^ (-s) = (-1) ^ k * g (t + π) := fun t => by
    simp only [hg, Int.cast_natCast]
    rw [show (k : ℝ) * (t + π) = k * t + k * π by ring, Real.cos_add, Real.cos_nat_mul_pi,
      Real.sin_nat_mul_pi, Real.cos_add_pi]
    have : 1 + α ^ 2 - 2 * α * -Real.cos t = 1 + (-α) ^ 2 - 2 * (-α) * Real.cos t := by ring
    rw [this]
    linear_combination (-(Real.cos (k * t) * (1 + (-α) ^ 2 - 2 * (-α) * Real.cos t) ^ (-s))) * hk
  have h2 : (∫ t in (0 : ℝ)..2 * π, Real.cos (((k : ℤ) : ℝ) * t) *
      (1 + (-α) ^ 2 - 2 * (-α) * Real.cos t) ^ (-s)) = (-1) ^ k * ∫ t in (0 : ℝ)..2 * π, g t := by
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right g π]
    congr 1
    have := hper.intervalIntegral_add_eq π 0
    simpa [add_comm] using this
  rw [h2]; ring

theorem laplaceC_neg (s : ℝ) (k : ℕ) (z : ℂ) : laplaceC s k (-z) = (-1) ^ k * laplaceC s k z := by
  unfold laplaceC
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [neg_pow, show 2 * q + k = k + 2 * q by ring, pow_add, pow_mul]
  simp only [neg_one_sq, one_pow, mul_one]
  ring_nf

theorem laplace_def_eq_re {s : ℝ} (hs : 0 < s) (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1) :
    laplace_def s k α = (laplaceC s k (α : ℂ)).re := by
  rcases le_or_gt 0 α with h0 | h0
  · rw [laplaceC_ofReal hs k h0 hα.2, Complex.ofReal_re]
  · have h1 := laplace_def_neg_arg s k (-α)
    rw [neg_neg] at h1
    have h2 := laplaceC_ofReal hs k (neg_nonneg.2 h0.le) (by linarith [hα.1])
    have hc : laplaceC s k (α : ℂ) = (-1) ^ k * laplaceC s k ((-α : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg, laplaceC_neg, ← mul_assoc, ← mul_pow]; simp
    rw [h1, hc, h2]
    have : ((-1 : ℂ) ^ k * (laplace_def s k (-α) : ℂ)) =
        (((-1 : ℝ) ^ k * laplace_def s k (-α) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]

theorem analyticAt_laplace_def_zero {s : ℝ} (hs : 0 < s) (k : ℕ) :
    AnalyticAt ℝ (laplace_def s k) 0 := by
  have hC : AnalyticOnNhd ℂ (laplaceC s k) (Metric.ball 0 1) :=
    (differentiableOn_laplaceC hs k).analyticOnNhd Metric.isOpen_ball
  have a1 : AnalyticAt ℝ (laplaceC s k) ((0 : ℝ) : ℂ) :=
    (hC _ (by simp)).restrictScalars
  have a2 : AnalyticAt ℝ (fun x : ℝ => (x : ℂ)) 0 := Complex.ofRealCLM.analyticAt 0
  have h1 : AnalyticAt ℝ (fun x : ℝ => Complex.re (laplaceC s k (x : ℂ))) 0 :=
    Complex.reCLM.analyticAt _ |>.comp (a1.comp a2)
  refine h1.congr ?_
  filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
    with x hx
  exact (laplace_def_eq_re hs k hx).symm

theorem analyticAt_iteratedDeriv_two {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (iteratedDeriv 2 f) x := by
  have : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [this]
  exact hf.deriv.deriv

/-- A function continuous at `0` and vanishing on `(0, 1)` vanishes at `0`. -/
theorem eq_zero_of_continuousAt_of_zero_Ioo {F : ℝ → ℝ} (hF : ContinuousAt F 0)
    (h : ∀ α ∈ Ioo (0 : ℝ) 1, F α = 0) : F 0 = 0 := by
  have h1 : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := hF.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto F (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with α hα
      exact (h α hα).symm)
  exact tendsto_nhds_unique h1 h2

/-- `bpP:p8:identities`, (I1), literally on `[0, 1)`: `α β'' + 2 β' = b_{3/2}^{(1)}`
with `β = b_{1/2}^{(0)}`. -/
theorem p8_identity_one {α : ℝ} (hα : α ∈ Ico (0 : ℝ) 1) :
    α * iteratedDeriv 2 (laplace_def (1/2) 0) α + 2 * deriv (laplace_def (1/2) 0) α =
      laplace_def (3/2) 1 α := by
  set F : ℝ → ℝ := fun α => α * iteratedDeriv 2 (laplace_def (1/2) 0) α +
    2 * deriv (laplace_def (1/2) 0) α - laplace_def (3/2) 1 α with hF
  have hpos : ∀ α ∈ Ioo (0 : ℝ) 1, F α = 0 := by
    intro α hα
    have h := (identities hα.1 hα.2).1
    have hne : α ≠ 0 := hα.1.ne'
    have : α * F α = 0 := by simp only [hF]; linear_combination h
    exact (mul_eq_zero.1 this).resolve_left hne
  have hcont : ContinuousAt F 0 := by
    have hb := analyticAt_laplace_def_zero (s := 1/2) (by norm_num) 0
    have hb3 := analyticAt_laplace_def_zero (s := 3/2) (by norm_num) 1
    have : AnalyticAt ℝ F 0 := by
      simp only [hF]
      exact ((analyticAt_id.mul (analyticAt_iteratedDeriv_two hb)).add
        (analyticAt_const.mul hb.deriv)).sub hb3
    exact this.continuousAt
  rcases hα.1.eq_or_lt with h0 | h0
  · subst h0
    have := eq_zero_of_continuousAt_of_zero_Ioo hcont hpos
    simpa [hF, sub_eq_zero] using this
  · exact sub_eq_zero.1 (hpos α ⟨h0, hα.2⟩)

/-- `bpP:p8:identities`, (I2), literally on `[0, 1)`: `α² b'' + 2 α b' - 2 b = α b_{3/2}^{(2)}`
with `b = b_{1/2}^{(1)}`. -/
theorem p8_identity_two {α : ℝ} (hα : α ∈ Ico (0 : ℝ) 1) :
    α ^ 2 * iteratedDeriv 2 (laplace_def (1/2) 1) α + 2 * α * deriv (laplace_def (1/2) 1) α -
      2 * laplace_def (1/2) 1 α = α * laplace_def (3/2) 2 α := by
  set F : ℝ → ℝ := fun α => α ^ 2 * iteratedDeriv 2 (laplace_def (1/2) 1) α +
    2 * α * deriv (laplace_def (1/2) 1) α - 2 * laplace_def (1/2) 1 α -
      α * laplace_def (3/2) 2 α with hF
  have hpos : ∀ α ∈ Ioo (0 : ℝ) 1, F α = 0 := by
    intro α hα
    have h := (identities hα.1 hα.2).2
    simp only [hF]; linear_combination 2 * h
  have hcont : ContinuousAt F 0 := by
    have hb := analyticAt_laplace_def_zero (s := 1/2) (by norm_num) 1
    have hb3 := analyticAt_laplace_def_zero (s := 3/2) (by norm_num) 2
    have : AnalyticAt ℝ F 0 := by
      simp only [hF]
      exact ((((analyticAt_id.pow 2).mul (analyticAt_iteratedDeriv_two hb)).add
        ((analyticAt_const.mul analyticAt_id).mul hb.deriv)).sub
        (analyticAt_const.mul hb)).sub (analyticAt_id.mul hb3)
    exact this.continuousAt
  have := eq_zero_of_continuousAt_of_zero_Ioo hcont hpos
  rcases hα.1.eq_or_lt with h0 | h0
  · subst h0
    simpa [hF, sub_eq_zero] using this
  · exact sub_eq_zero.1 (hpos α ⟨h0, hα.2⟩)

/-- `bpP:p8:identities`: both identities for every `α ∈ [0, 1)`. -/
theorem p8_identities_full {α : ℝ} (hα : α ∈ Ico (0 : ℝ) 1) :
    α * iteratedDeriv 2 (laplace_def (1/2) 0) α + 2 * deriv (laplace_def (1/2) 0) α =
      laplace_def (3/2) 1 α ∧
    α ^ 2 * iteratedDeriv 2 (laplace_def (1/2) 1) α + 2 * α * deriv (laplace_def (1/2) 1) α -
      2 * laplace_def (1/2) 1 α = α * laplace_def (3/2) 2 α :=
  ⟨p8_identity_one hα, p8_identity_two hα⟩

/-- `stepP:p8:id-1`: the coefficient of `α^(2q+1)` in `α β'' + 2 β'` is
`(2q+2)(2q+3) ((1/2)_{q+1}/(q+1)!)²`, and it equals the coefficient of `α^(2q+1)` in
`b_{3/2}^{(1)}`, `(3/2)_{q+1} (3/2)_q / ((q+1)! q!)`. -/
theorem p8_id1 (q : ℕ) :
    pcoef (1/2) (q + 1) ^ 2 * (((2 * (q + 1) : ℕ) : ℝ) * (((2 * (q + 1) : ℕ) : ℝ) + 1)) =
      poch (3/2) (q + 1) * poch (3/2) q / (((q + 1).factorial : ℝ) * q.factorial) ∧
    laplaceTerm (3/2) 1 q = fun α =>
      (poch (3/2) (q + 1) * poch (3/2) q / (((q + 1).factorial : ℝ) * q.factorial)) *
        α ^ (2 * q + 1) := by
  refine ⟨?_, ?_⟩
  · have h := coef1 q
    have e : halfCoef 0 (q + 1) = pcoef (1/2) (q + 1) ^ 2 := by simp [halfCoef, sq]
    rw [e] at h
    rw [← h]; ring
  · funext α; rw [laplaceTerm_eq_coef_mul]

/-- `stepP:p8:id-2`: with `c_q = halfCoef 1 q` the coefficient of `α^(2q+1)` in `b_{1/2}^{(1)}`,
the coefficient of `α^(2q+1)` in `α² b'' + 2 α b' - 2 b` is `0` for `q = 0` and
`2q(2q+3) c_q` for `q ≥ 1`; it equals the coefficient of `α^(2q+1)` in `α b_{3/2}^{(2)}`, namely
`(3/2)_{q+1} (3/2)_{q-1} / ((q+1)! (q-1)!)` (written with `q = r + 1`); for `q = 0` the right side
has no `α^1` term. -/
theorem p8_id2 (r : ℕ) :
    halfCoef 1 0 * (((2 * 0 : ℕ) : ℝ) * ((2 * 0 + 3 : ℕ) : ℝ)) = 0 ∧
    halfCoef 1 (r + 1) * (((2 * (r + 1) : ℕ) : ℝ) * ((2 * (r + 1) + 3 : ℕ) : ℝ)) =
      poch (3/2) (r + 2) * poch (3/2) r / (((r + 2).factorial : ℝ) * r.factorial) ∧
    laplaceTerm (3/2) 2 r = fun α =>
      (poch (3/2) (r + 2) * poch (3/2) r / (((r + 2).factorial : ℝ) * r.factorial)) *
        α ^ (2 * r + 2) := by
  refine ⟨by simp, ?_, ?_⟩
  · have h := coef2 r
    push_cast at h ⊢
    linear_combination 2 * h
  · funext α; rw [laplaceTerm_eq_coef_mul]

end SecularForm

end KAM.Planetary

end
