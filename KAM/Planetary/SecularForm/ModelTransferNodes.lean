/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.ModelTransfer
public import KAM.Planetary.SecularForm.AnalyticNodes
public import KAM.Planetary.SecularForm.ProductInterface
public import KAM.Planetary.SecularForm.Quadratic
public import KAM.Planetary.SecularForm.Quartic

/-!
# Secular form: literal exports for the model-identification nodes

Blueprint P, Part 8, graph-gap package GAP-P8a (identification half). Unsigned exports stating the
literal conclusions of `stepP:p8:id-diff`, `stepP:p8:id-avg`, `stepP:p8:id-int` and of the theorem
`bpP:p8:identification` (`identification_full`), built from the landed `identification`,
`lemma64`, `perturbation_analytic_full` and the product-chart facts.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

/-- `stepP:p8:id-diff`: `f̂_mov - f̂_fix = |∑ p⁽ⁱ⁾|²/(2 m₀)`, a polynomial in the continuous
`p⁽ⁱ⁾(λᵢ)`, hence continuous. -/
theorem identification_diff (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) :
    (∀ t : Vec n, perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1) =
      (2 * D.m0)⁻¹ * planeSq (∑ i, momentum D x t i)) ∧
    (∀ i, Continuous (pmom D x i) ∧ ∀ t : Vec n, momentum D x t i = pmom D x i (t i)) ∧
    Continuous (fun t : Vec n => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1)) :=
  ⟨fun t => perturbation_diff D x t,
    fun i => ⟨continuous_pmom hx i, fun t => momentum_eq_pmom D x t i⟩,
    (identification D hx).1⟩

private theorem delta_forms (D : Data n) {I : Vec n} (hI : ∀ i, 0 < I i) :
    modelDelta D I = (D.G * D.m0) * D.G / 2 * ∑ i, D.m i ^ 4 / I i ^ 2 ∧
    modelDelta D I = D.G / 2 * ∑ i, D.m i ^ 2 / axis D I i := by
  have hm0 := D.hm0.ne'
  have hG := D.hG.ne'
  have hm := fun i => (D.hm i).ne'
  have hI' := fun i => (hI i).ne'
  unfold modelDelta
  constructor
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hm i; have := hI' i
    field_simp
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hm i; have := hI' i
    simp only [axis]
    field_simp

/-- `stepP:p8:id-avg`: `(2π)⁻ⁿ ∫ (f̂_mov - f̂_fix) dλ = δ(Λ)`, in the two forms
`(κG/2) ∑ mᵢ⁴/Λᵢ²` and `(G/2) ∑ mᵢ²/aᵢ`. -/
theorem identification_avg (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) :
    (2 * π) ^ (-(n : ℤ)) * ∫ t in cell n, (perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1)) = modelDelta D x.2.1 ∧
    modelDelta D x.2.1 = (D.G * D.m0) * D.G / 2 * ∑ i, D.m i ^ 4 / x.2.1 i ^ 2 ∧
    modelDelta D x.2.1 = D.G / 2 * ∑ i, D.m i ^ 2 / axis D x.2.1 i := by
  have hI : ∀ i, 0 < x.2.1 i := fun i => by
    have := (blk_mem hx i 0).1
    simpa [blk] using this
  obtain ⟨h1, h2⟩ := delta_forms D hI
  exact ⟨(identification D hx).2.1, h1, h2⟩

/-- A radius `ρ* < ρ₀/2` on whose real polydisc both perturbations are integrable over the cell
(the real-analytic radius of `perturbation_analytic` shrunk to that of
`perturbation_analytic_full`). -/
private theorem radius_integrable (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a / 2 ∧ ∀ b : Bool,
      (∀ x ∈ realDisc D a r,
        IntegrableOn (fun t => perturbation D b (assemble x.2.1 t x.2.2 x.1)) (cell n)) ∧
      AnalyticOnNhd ℝ (secular D b) (realDisc D a r) := by
  obtain ⟨r1, hr1, hrho1, -, h1⟩ := perturbation_analytic D ha
  obtain ⟨r2, hr2, hrh2, -⟩ := perturbation_analytic_full D ha
  refine ⟨min r1 r2, lt_min hr1 hr2, (min_le_right _ _).trans_lt hrh2,
    fun b => ⟨fun x hx => ?_, ?_⟩⟩
  · exact (h1 b).2.2.2.2.2.2 x (realDisc_mono D a (min_le_left _ _) hx)
  · exact (h1 b).2.2.2.2.1.mono (realDisc_mono D a (min_le_left _ _))

/-- `stepP:p8:id-int`: integrability of `f̂_fix` is that of `f̂_mov` and the averages subtract; on
the real polydisc both are integrable. -/
theorem identification_int (D : Data n) :
    (∀ x ∈ slowDom D,
      (IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) ↔
        IntegrableOn (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1)) (cell n)) ∧
      (IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) →
        avg (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
          perturbation D false (assemble x.2.1 t x.2.2 x.1)) =
        avg (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1)) -
          avg (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)))) ∧
    ∀ {a : Vec n}, a ∈ axes n → ∃ r : ℝ, 0 < r ∧ r < rho D a / 2 ∧
      ∀ x ∈ realDisc D a r,
        IntegrableOn (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1)) (cell n) ∧
        IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) := by
  refine ⟨fun x hx => ⟨((identification D hx).2.2.1).symm, fun hF => ?_⟩, fun {a} ha => ?_⟩
  · have hM := ((identification D hx).2.2.1).2 hF
    unfold avg
    rw [integral_sub hM hF, smul_sub]
  · obtain ⟨r, hr0, hrh, h⟩ := radius_integrable D ha
    exact ⟨r, hr0, hrh, fun x hx => ⟨((h true).1 x hx), ((h false).1 x hx)⟩⟩

private theorem avg_const_real (c : ℝ) : avg (fun _ : Vec n => c) = c := by
  have h1 : avg (fun _ : Vec n => (1 : ℝ)) = 1 := by
    have := avg_prod (n := n) (fun _ _ => (1 : ℝ))
    simp only [mean_one, Finset.prod_const_one] at this
    exact this
  have h2 := avg_const_mul c (fun _ : Vec n => (1 : ℝ))
  simp only [mul_one] at h2
  rw [h2, h1, mul_one]

private theorem avg_const_add_mul {f : Vec n → ℝ} (hf : IntegrableOn f (cell n)) (c μ : ℝ) :
    avg (fun t => c + μ * f t) = c + μ * avg f := by
  have hf' : IntegrableOn (fun t => μ * f t) (cell n) := hf.const_mul μ
  have : (fun t => c + μ * f t) = fun t => μ * f t + c := funext fun t => add_comm _ _
  rw [this, avg_add hf' continuous_const, avg_const_mul, avg_const_real, add_comm]

private theorem hProd_assemble_eq (D : Data n) (I t p q : Vec n) :
    hProd (D.G * D.m0) D.m (assemble I t p q) = keplerActionHam D I := by
  simp [keplerActionHam, hProd, fast, assemble]

/-- Averaged Hamiltonians of the two models (`⟨H^Ψ⟩ = h + μ S` at an integrable point). -/
private theorem avg_hamiltonians (D : Data n) {x : Slow n} (hx : x ∈ slowDom D)
    (hF : IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n))
    (hM : IntegrableOn (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1)) (cell n))
    (μ : ℝ) :
    avg (fun t : Vec n => movingHamiltonian D.G D.m0 D.m μ
        (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1))) =
      keplerActionHam D x.2.1 + μ * secular D true x ∧
    avg (fun t : Vec n => fixedHamiltonian D.G D.m0 D.m μ
        (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1))) =
      keplerActionHam D x.2.1 + μ * secular D false x := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  constructor
  · have : (fun t : Vec n => movingHamiltonian D.G D.m0 D.m μ
        (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1))) =
        fun t => keplerActionHam D x.2.1 +
          μ * perturbation D true (assemble x.2.1 t x.2.2 x.1) := funext fun t => by
      rw [movingHamiltonian_poincareProd D.hm hκ (assemble_mem hx t), hProd_assemble_eq]
      rfl
    rw [this, avg_const_add_mul hM, secular_eq_avg]
  · have : (fun t : Vec n => fixedHamiltonian D.G D.m0 D.m μ
        (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1))) =
        fun t => keplerActionHam D x.2.1 +
          μ * perturbation D false (assemble x.2.1 t x.2.2 x.1) := funext fun t => by
      rw [fixedHamiltonian_poincareProd D.hm hκ (assemble_mem hx t), hProd_assemble_eq]
      rfl
    rw [this, avg_const_add_mul hF, secular_eq_avg]

/-- `bpP:p8:identification`: the difference `f̂_mov - f̂_fix = |∑ p⁽ⁱ⁾|²/(2 m₀)` is continuous with
average `δ(Λ)`; integrability of
`f̂_fix` and `f̂_mov` is equivalent and then `S_mov = S_fix + δ`; on the real polydisc this holds
unconditionally, with `⟨H_mov^Ψ⟩ = h + μ S_mov = h + μ S_fix + μ δ` and
`⟨H_fix^Ψ⟩ = h + ε S_fix`. -/
theorem identification_full (D : Data n) :
    (∀ x ∈ slowDom D,
      Continuous (fun t : Vec n => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
        perturbation D false (assemble x.2.1 t x.2.2 x.1)) ∧
      avg (fun t : Vec n => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
        perturbation D false (assemble x.2.1 t x.2.2 x.1)) = modelDelta D x.2.1 ∧
      (IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) ↔
        IntegrableOn (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1)) (cell n)) ∧
      (IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) →
        secular D true x = secular D false x + modelDelta D x.2.1) ∧
      ∀ t : Vec n, perturbation D true (assemble x.2.1 t x.2.2 x.1) -
        perturbation D false (assemble x.2.1 t x.2.2 x.1) =
        (2 * D.m0)⁻¹ * planeSq (∑ i, momentum D x t i)) ∧
    ∀ {a : Vec n}, a ∈ axes n → ∃ r : ℝ, 0 < r ∧ r < rho D a / 2 ∧ ∀ x ∈ realDisc D a r,
      secular D true x = secular D false x + modelDelta D x.2.1 ∧
      (∀ μ : ℝ, avg (fun t : Vec n => movingHamiltonian D.G D.m0 D.m μ
          (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1))) =
        keplerActionHam D x.2.1 + μ * secular D true x ∧
        keplerActionHam D x.2.1 + μ * secular D true x =
          keplerActionHam D x.2.1 + μ * secular D false x + μ * modelDelta D x.2.1) ∧
      ∀ ε : ℝ, avg (fun t : Vec n => fixedHamiltonian D.G D.m0 D.m ε
          (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1))) =
        keplerActionHam D x.2.1 + ε * secular D false x := by
  refine ⟨fun x hx => ⟨(identification D hx).1, (identification D hx).2.1,
    (identification D hx).2.2.1.symm, (identification D hx).2.2.2,
    fun t => perturbation_diff D x t⟩, fun {a} ha => ?_⟩
  obtain ⟨r, hr0, hrh, h⟩ := radius_integrable D ha
  have hrho : r < rho D a := by have := rho_pos D ha; linarith
  refine ⟨r, hr0, hrh, fun x hx => ?_⟩
  have hxd := realDisc_subset_slowDom D ha hrho hx
  have hid := (identification D hxd).2.2.2 ((h false).1 x hx)
  have hH := avg_hamiltonians D hxd ((h false).1 x hx) ((h true).1 x hx)
  refine ⟨hid, fun μ => ⟨(hH μ).1, ?_⟩, fun ε => (hH ε).2⟩
  rw [hid]
  ring

/-! ### Same jets, same quadratic form, same equations, transfer -/

private theorem differentiableAt_modelDelta (D : Data n) {I : Vec n} (hI : ∀ i, I i ≠ 0) :
    DifferentiableAt ℝ (modelDelta D) I := by
  unfold modelDelta
  refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun i _ => ?_) _
  have h : DifferentiableAt ℝ (fun I : Vec n => I i) I :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt
  have h2 : DifferentiableAt ℝ (fun I : Vec n => I i ^ 2) I := h.pow 2
  fun_prop (disch := exact pow_ne_zero 2 (hI i))

private theorem pos_of_realDisc (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hrho : r < rho D a) {x : Slow n} (hx : x ∈ realDisc D a r) (i : Fin n) : 0 < x.2.1 i := by
  have := (mem_slowDom_iff' D x).1 (realDisc_subset_slowDom D ha hrho hx) i
  exact this.1

/-- The first-order data of the identification at a point of the real polydisc. -/
private theorem first_order_at (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ} (hr : 0 < r)
    (hrho : r < rho D a)
    (hint : ∀ x ∈ realDisc D a r,
      IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n))
    (hAn : AnalyticOnNhd ℝ (secular D false) (realDisc D a r)) {x : Slow n}
    (hx : x ∈ realDisc D a r) :
    fderiv ℝ (slowSecular D true x.2.1) (x.1, x.2.2) =
      fderiv ℝ (slowSecular D false x.2.1) (x.1, x.2.2) ∧
    fderiv ℝ (fun I => secular D true (x.1, I, x.2.2)) x.2.1 =
      fderiv ℝ (fun I => secular D false (x.1, I, x.2.2)) x.2.1 +
        fderiv ℝ (modelDelta D) x.2.1 := by
  have hid : ∀ y ∈ realDisc D a r,
      secular D true y = secular D false y + modelDelta D y.2.1 := fun y hy =>
    (identification D (realDisc_subset_slowDom D ha hrho hy)).2.2.2 (hint y hy)
  constructor
  · let emb : Vec n × Vec n → Slow n := fun u => (u.1, x.2.1, u.2)
    have hopen : IsOpen (emb ⁻¹' realDisc D a r) :=
      (isOpen_realDisc D a hr).preimage (by fun_prop)
    have hev : slowSecular D true x.2.1 =ᶠ[𝓝 (x.1, x.2.2)]
        fun u => slowSecular D false x.2.1 u + modelDelta D x.2.1 := by
      filter_upwards [hopen.mem_nhds (show (x.1, x.2.2) ∈ emb ⁻¹' realDisc D a r from hx)]
        with u hu
      exact hid _ hu
    rw [hev.fderiv_eq, fderiv_add_const]
  · let emb : Vec n → Slow n := fun I => (x.1, I, x.2.2)
    have hopen : IsOpen (emb ⁻¹' realDisc D a r) :=
      (isOpen_realDisc D a hr).preimage (by fun_prop)
    have hev : (fun I => secular D true (x.1, I, x.2.2)) =ᶠ[𝓝 x.2.1]
        fun I => secular D false (x.1, I, x.2.2) + modelDelta D I := by
      filter_upwards [hopen.mem_nhds (show x.2.1 ∈ emb ⁻¹' realDisc D a r from hx)] with I hI
      exact hid _ hI
    have hS : DifferentiableAt ℝ (fun I => secular D false (x.1, I, x.2.2)) x.2.1 :=
      DifferentiableAt.comp (g := secular D false) (f := fun I : Vec n => (x.1, I, x.2.2))
        x.2.1 (hAn x hx).differentiableAt (by fun_prop)
    have hδ := differentiableAt_modelDelta D (fun i => (pos_of_realDisc D ha hrho hx i).ne')
    rw [hev.fderiv_eq]
    exact fderiv_fun_add hS hδ

/-! ### The secular Hamilton equations of the averaged Hamiltonians -/

/-- The slow coordinates `(ξ, Λ, η) = (q, I, p)` of a phase point. -/
private def phaseSlow (n : ℕ) : Phase (n + n) →L[ℝ] Slow n :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.pi fun k => (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (n + n) => ℝ) (Fin.natAdd n k)).comp
        (ContinuousLinearMap.fst ℝ (Fin (n + n) → ℝ) (Fin (n + n) → ℝ)))
    (ContinuousLinearMap.prod
      (ContinuousLinearMap.pi fun k => (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (n + n) => ℝ) (Fin.castAdd n k)).comp
          (ContinuousLinearMap.snd ℝ (Fin (n + n) → ℝ) (Fin (n + n) → ℝ)))
      (ContinuousLinearMap.pi fun k => (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (n + n) => ℝ) (Fin.natAdd n k)).comp
          (ContinuousLinearMap.snd ℝ (Fin (n + n) → ℝ) (Fin (n + n) → ℝ))))

private theorem phaseSlow_apply (w : Phase (n + n)) : phaseSlow n w =
    (fun k => w.1 (Fin.natAdd n k), fun k => w.2 (Fin.castAdd n k),
      fun k => w.2 (Fin.natAdd n k)) := rfl

private theorem phaseSlow_assemble (I φ p q : Vec n) :
    phaseSlow n (assemble I φ p q) = (q, I, p) := by
  rw [phaseSlow_apply]
  simp [assemble]

private theorem phaseSlow_natAdd_fst (i : Fin n) :
    phaseSlow n (Pi.single (Fin.natAdd n i) 1, 0) = (Pi.single i 1, 0, 0) := by
  rw [phaseSlow_apply]
  refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) <;>
    simp [Pi.single_apply, Fin.ext_iff] <;> omega

private theorem phaseSlow_natAdd_snd (i : Fin n) :
    phaseSlow n (0, Pi.single (Fin.natAdd n i) 1) = (0, 0, Pi.single i 1) := by
  rw [phaseSlow_apply]
  refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) <;>
    simp [Pi.single_apply, Fin.ext_iff] <;> omega

private theorem phaseSlow_castAdd_fst (i : Fin n) :
    phaseSlow n (Pi.single (Fin.castAdd n i) 1, 0) = 0 := by
  rw [phaseSlow_apply]
  refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) <;>
    simp [Pi.single_apply, Fin.ext_iff] <;> omega

private theorem phaseSlow_castAdd_snd (i : Fin n) :
    phaseSlow n (0, Pi.single (Fin.castAdd n i) 1) = (0, Pi.single i 1, 0) := by
  rw [phaseSlow_apply]
  refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) <;>
    simp [Pi.single_apply, Fin.ext_iff] <;> omega

private theorem differentiableAt_keplerActionHam (D : Data n) {I : Vec n}
    (hI : ∀ i, I i ≠ 0) : DifferentiableAt ℝ (keplerActionHam D) I := by
  have h : keplerActionHam D = fun I : Vec n =>
      -∑ i, (D.G * D.m0) ^ 2 * D.m i ^ 3 / (2 * I i ^ 2) := funext fun I => by
    simp [keplerActionHam, hProd, fast, assemble]
  rw [h]
  refine DifferentiableAt.neg (DifferentiableAt.fun_sum fun i _ => ?_)
  have hp : DifferentiableAt ℝ (fun I : Vec n => I i) I :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt
  fun_prop (disch := exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (hI i)))

/-- `bpP:p8:same-jets` (b), literally: for `μ = ε` the Hamilton equations of the averaged
Hamiltonians `⟨H_mov^Ψ⟩`, `⟨H_fix^Ψ⟩` (frozen `hamiltonianVectorField`, at any `λ`) give
`ξ̇ = μ ∂_η S`, `η̇ = -μ ∂_ξ S`, identically in the two models, `Λ̇ = 0`, and the frequencies
`λ̇` differ by `μ ∂_Λ δ`. -/
private theorem dynamics_at (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ} (hr : 0 < r)
    (hrho : r < rho D a)
    (hint : ∀ x ∈ realDisc D a r,
      IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n))
    (hAn : AnalyticOnNhd ℝ (secular D false) (realDisc D a r)) :
    ∀ (μ : ℝ) (Hm Hf : Phase (n + n) → ℝ),
      Hm = (fun z => avg (fun t : Vec n => movingHamiltonian D.G D.m0 D.m μ
        (poincareProd D.m (D.G * D.m0) (assemble (fun k => z.2 (Fin.castAdd n k)) t
          (fun k => z.2 (Fin.natAdd n k)) (fun k => z.1 (Fin.natAdd n k)))))) →
      Hf = (fun z => avg (fun t : Vec n => fixedHamiltonian D.G D.m0 D.m μ
        (poincareProd D.m (D.G * D.m0) (assemble (fun k => z.2 (Fin.castAdd n k)) t
          (fun k => z.2 (Fin.natAdd n k)) (fun k => z.1 (Fin.natAdd n k)))))) →
      ∀ x ∈ realDisc D a r, ∀ (φ : Vec n) (i : Fin n) (z : Phase (n + n)),
        z = assemble x.2.1 φ x.2.2 x.1 →
        (hamiltonianVectorField Hm z).1 (Fin.natAdd n i) =
          μ * fderiv ℝ (secular D true) x (0, 0, Pi.single i 1) ∧
        (hamiltonianVectorField Hm z).2 (Fin.natAdd n i) =
          -(μ * fderiv ℝ (secular D true) x (Pi.single i 1, 0, 0)) ∧
        (hamiltonianVectorField Hm z).2 (Fin.castAdd n i) = 0 ∧
        (hamiltonianVectorField Hf z).1 (Fin.natAdd n i) =
          μ * fderiv ℝ (secular D false) x (0, 0, Pi.single i 1) ∧
        (hamiltonianVectorField Hf z).2 (Fin.natAdd n i) =
          -(μ * fderiv ℝ (secular D false) x (Pi.single i 1, 0, 0)) ∧
        (hamiltonianVectorField Hf z).2 (Fin.castAdd n i) = 0 ∧
        (hamiltonianVectorField Hm z).1 (Fin.natAdd n i) =
          (hamiltonianVectorField Hf z).1 (Fin.natAdd n i) ∧
        (hamiltonianVectorField Hm z).2 (Fin.natAdd n i) =
          (hamiltonianVectorField Hf z).2 (Fin.natAdd n i) ∧
        (hamiltonianVectorField Hm z).1 (Fin.castAdd n i) =
          (hamiltonianVectorField Hf z).1 (Fin.castAdd n i) +
            μ * fderiv ℝ (modelDelta D) x.2.1 (Pi.single i 1) := by
  intro μ Hm Hf hHm hHf x hx φ i z hz
  have hxd := realDisc_subset_slowDom D ha hrho hx
  have hπz : phaseSlow n z = x := by rw [hz, phaseSlow_assemble]
  have hopen := (isOpen_realDisc D a hr).mem_nhds hx
  have hSf : HasFDerivAt (secular D false) (fderiv ℝ (secular D false) x) x :=
    (hAn x hx).differentiableAt.hasFDerivAt
  have hδ : HasFDerivAt (modelDelta D) (fderiv ℝ (modelDelta D) x.2.1) x.2.1 :=
    (differentiableAt_modelDelta D fun k => (pos_of_realDisc D ha hrho hx k).ne').hasFDerivAt
  have hh : HasFDerivAt (keplerActionHam D) (fderiv ℝ (keplerActionHam D) x.2.1) x.2.1 :=
    (differentiableAt_keplerActionHam D fun k => (pos_of_realDisc D ha hrho hx k).ne').hasFDerivAt
  set ΛL : Slow n →L[ℝ] Vec n := (ContinuousLinearMap.fst ℝ (Vec n) (Vec n)).comp
    (ContinuousLinearMap.snd ℝ (Vec n) (Vec n × Vec n)) with hΛL
  have hΛ : HasFDerivAt (fun y : Slow n => y.2.1) ΛL x := ΛL.hasFDerivAt
  have hδΛ := hδ.comp x hΛ
  have hhΛ := hh.comp x hΛ
  have hev : secular D true =ᶠ[𝓝 x] fun y => secular D false y + modelDelta D y.2.1 := by
    filter_upwards [hopen] with y hy
    exact (identification D (realDisc_subset_slowDom D ha hrho hy)).2.2.2 (hint y hy)
  have hSm : HasFDerivAt (secular D true)
      (fderiv ℝ (secular D false) x + (fderiv ℝ (modelDelta D) x.2.1).comp ΛL) x :=
    (hSf.add hδΛ).congr_of_eventuallyEq hev
  have hav : ∀ y ∈ realDisc D a r,
      avg (fun t : Vec n => movingHamiltonian D.G D.m0 D.m μ
        (poincareProd D.m (D.G * D.m0) (assemble y.2.1 t y.2.2 y.1))) =
        keplerActionHam D y.2.1 + μ * secular D true y ∧
      avg (fun t : Vec n => fixedHamiltonian D.G D.m0 D.m μ
        (poincareProd D.m (D.G * D.m0) (assemble y.2.1 t y.2.2 y.1))) =
        keplerActionHam D y.2.1 + μ * secular D false y := fun y hy =>
    avg_hamiltonians D (realDisc_subset_slowDom D ha hrho hy) (hint y hy)
      ((identification D (realDisc_subset_slowDom D ha hrho hy)).2.2.1.2 (hint y hy)) μ
  have hcont : Tendsto (phaseSlow n) (𝓝 z) (𝓝 x) := by
    have h : Tendsto (phaseSlow n) (𝓝 z) (𝓝 (phaseSlow n z)) :=
      (phaseSlow n).continuous.continuousAt
    rwa [hπz] at h
  have hK : ∀ (S : Slow n → ℝ) (S' : Slow n →L[ℝ] ℝ), HasFDerivAt S S' x →
      HasFDerivAt (fun y => keplerActionHam D y.2.1 + μ * S y)
        ((fderiv ℝ (keplerActionHam D) x.2.1).comp ΛL + μ • S') x :=
    fun S S' hS => hhΛ.add (hS.const_mul μ)
  have hK' : ∀ (S : Slow n → ℝ) (S' : Slow n →L[ℝ] ℝ), HasFDerivAt S S' x →
      HasFDerivAt (fun y => keplerActionHam D y.2.1 + μ * S y)
        ((fderiv ℝ (keplerActionHam D) x.2.1).comp ΛL + μ • S') (phaseSlow n z) :=
    fun S S' hS => by rw [hπz]; exact hK S S' hS
  have hfm : ∀ v, fderiv ℝ Hm z v = fderiv ℝ (keplerActionHam D) x.2.1 (ΛL (phaseSlow n v)) +
      μ * fderiv ℝ (secular D true) x (phaseSlow n v) := by
    intro v
    have h1 := (hK' _ _ hSm).comp z (phaseSlow n).hasFDerivAt
    have h2 := h1.congr_of_eventuallyEq (f₁ := Hm) (by
      filter_upwards [hcont.eventually hopen] with z' hz'
      rw [hHm]
      exact (hav _ hz').1)
    rw [h2.fderiv, hSm.fderiv]
    simp [hΛL]
    ring
  have hff : ∀ v, fderiv ℝ Hf z v = fderiv ℝ (keplerActionHam D) x.2.1 (ΛL (phaseSlow n v)) +
      μ * fderiv ℝ (secular D false) x (phaseSlow n v) := by
    intro v
    have h1 := (hK' _ _ hSf).comp z (phaseSlow n).hasFDerivAt
    have h2 := h1.congr_of_eventuallyEq (f₁ := Hf) (by
      filter_upwards [hcont.eventually hopen] with z' hz'
      rw [hHf]
      exact (hav _ hz').2)
    rw [h2.fderiv]
    simp [hΛL]
  have hsm : ∀ w : Slow n, fderiv ℝ (secular D true) x w =
      fderiv ℝ (secular D false) x w + fderiv ℝ (modelDelta D) x.2.1 w.2.1 := fun w => by
    rw [hSm.fderiv]
    simp [hΛL]
  simp only [hamiltonianVectorField, hfm, hff, phaseSlow_natAdd_fst, phaseSlow_natAdd_snd,
    phaseSlow_castAdd_fst, phaseSlow_castAdd_snd, hsm]
  simp [hΛL]
  ring

/-- `bpP:p8:same-jets` (parent of `#jets` and `#transfer`), at one common radius `ρ*`:
all-order jet equality, (a) quadratic form with the same `Q_h`, (b) equations, (c) transfer of
`HasSecularBirkhoffForm` (both directions, `P₀ ↦ P₀ - δ`) when the points `(Λ, η, ξ)`,
`Λ ∈ V`, `p_j² + q_j² < r₀²` lie in the real polydisc, and `S_mov ∘ χ - S_fix ∘ χ = δ(Λ)` for
every slow change `χ` that keeps `Λ` and takes values in the real polydisc. -/
theorem same_jets_full (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r C : ℝ, 0 < r ∧ r < rho D a / 2 ∧ 0 < C ∧
    AnalyticOnNhd ℝ (fun x : Slow n => secular D true x - constantTerm D (axis D x.2.1) -
      modelDelta D x.2.1 - quad (coeffs D (axis D x.2.1)) x.1 -
      quad (coeffs D (axis D x.2.1)) x.2.2) (realDisc D a r) ∧
    (∀ x ∈ realDisc D a r,
      (∀ k : ℕ, 0 < k → ∀ l : ℕ,
        iteratedFDeriv ℝ l (fun I => iteratedFDeriv ℝ k (slowSecular D true I) (x.1, x.2.2))
          x.2.1 =
        iteratedFDeriv ℝ l (fun I => iteratedFDeriv ℝ k (slowSecular D false I) (x.1, x.2.2))
          x.2.1) ∧
      |secular D true x - constantTerm D (axis D x.2.1) - modelDelta D x.2.1 -
        quad (coeffs D (axis D x.2.1)) x.1 - quad (coeffs D (axis D x.2.1)) x.2.2| ≤
        C * ‖(x.1, x.2.2)‖ ^ 4 ∧
      fderiv ℝ (slowSecular D true x.2.1) (x.1, x.2.2) =
        fderiv ℝ (slowSecular D false x.2.1) (x.1, x.2.2) ∧
      fderiv ℝ (fun I => secular D true (x.1, I, x.2.2)) x.2.1 =
        fderiv ℝ (fun I => secular D false (x.1, I, x.2.2)) x.2.1 +
          fderiv ℝ (modelDelta D) x.2.1) ∧
    (∀ {V : Set (Vec n)} {r0 μ0 : ℝ} {P0 : ℝ → Vec n → ℝ} {Ω : ℝ → Vec n → Vec n}
      {β : ℝ → Vec n → Mat n},
      (∀ I ∈ V, ∀ p q : Vec n, (∀ j, p j ^ 2 + q j ^ 2 < r0 ^ 2) → (q, I, p) ∈ realDisc D a r) →
      (HasSecularBirkhoffForm (fun _ => perturbation D true) V r0 μ0 P0 Ω β ↔
        HasSecularBirkhoffForm (fun _ => perturbation D false) V r0 μ0
          (fun μ I => P0 μ I - modelDelta D I) Ω β)) ∧
    (∀ {U : Set (Slow n)} {χ : Slow n → Slow n}, (∀ y ∈ U, (χ y).2.1 = y.2.1) →
      (∀ y ∈ U, χ y ∈ realDisc D a r) →
      ∀ y ∈ U, secular D true (χ y) - secular D false (χ y) = modelDelta D y.2.1) ∧
    ∀ (μ : ℝ) (Hm Hf : Phase (n + n) → ℝ),
    Hm = (fun z => avg (fun t : Vec n => movingHamiltonian D.G D.m0 D.m μ
      (poincareProd D.m (D.G * D.m0) (assemble (fun k => z.2 (Fin.castAdd n k)) t
        (fun k => z.2 (Fin.natAdd n k)) (fun k => z.1 (Fin.natAdd n k)))))) →
    Hf = (fun z => avg (fun t : Vec n => fixedHamiltonian D.G D.m0 D.m μ
      (poincareProd D.m (D.G * D.m0) (assemble (fun k => z.2 (Fin.castAdd n k)) t
        (fun k => z.2 (Fin.natAdd n k)) (fun k => z.1 (Fin.natAdd n k)))))) →
    ∀ x ∈ realDisc D a r, ∀ (φ : Vec n) (i : Fin n) (z : Phase (n + n)),
      z = assemble x.2.1 φ x.2.2 x.1 →
      (hamiltonianVectorField Hm z).1 (Fin.natAdd n i) =
        μ * fderiv ℝ (secular D true) x (0, 0, Pi.single i 1) ∧
      (hamiltonianVectorField Hm z).2 (Fin.natAdd n i) =
        -(μ * fderiv ℝ (secular D true) x (Pi.single i 1, 0, 0)) ∧
      (hamiltonianVectorField Hm z).2 (Fin.castAdd n i) = 0 ∧
      (hamiltonianVectorField Hf z).1 (Fin.natAdd n i) =
        μ * fderiv ℝ (secular D false) x (0, 0, Pi.single i 1) ∧
      (hamiltonianVectorField Hf z).2 (Fin.natAdd n i) =
        -(μ * fderiv ℝ (secular D false) x (Pi.single i 1, 0, 0)) ∧
      (hamiltonianVectorField Hf z).2 (Fin.castAdd n i) = 0 ∧
      (hamiltonianVectorField Hm z).1 (Fin.natAdd n i) =
        (hamiltonianVectorField Hf z).1 (Fin.natAdd n i) ∧
      (hamiltonianVectorField Hm z).2 (Fin.natAdd n i) =
        (hamiltonianVectorField Hf z).2 (Fin.natAdd n i) ∧
      (hamiltonianVectorField Hm z).1 (Fin.castAdd n i) =
        (hamiltonianVectorField Hf z).1 (Fin.castAdd n i) +
          μ * fderiv ℝ (modelDelta D) x.2.1 (Pi.single i 1) := by
  obtain ⟨r1, hr1, hrh1, h1⟩ := radius_integrable D ha
  obtain ⟨r2, C, hr2, hr2rho, hC, hAn2, hB2⟩ := quadratic_form D ha
  have hρ := rho_pos D ha
  have hrho1 : r1 < rho D a := by linarith
  set r := min r1 r2 with hrdef
  have hr : 0 < r := lt_min hr1 hr2
  have hrr1 : r ≤ r1 := min_le_left _ _
  have hrr2 : r ≤ r2 := min_le_right _ _
  have hrho : r < rho D a := lt_of_le_of_lt hrr1 hrho1
  have hint : ∀ x ∈ realDisc D a r,
      IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) :=
    fun x hx => ((h1 false).1 x (realDisc_mono D a hrr1 hx))
  have hAn : AnalyticOnNhd ℝ (secular D false) (realDisc D a r) :=
    (h1 false).2.mono (realDisc_mono D a hrr1)
  have hid : ∀ y ∈ realDisc D a r,
      secular D true y = secular D false y + modelDelta D y.2.1 := fun y hy =>
    (identification D (realDisc_subset_slowDom D ha hrho hy)).2.2.2 (hint y hy)
  have heq : ∀ y ∈ realDisc D a r, secular D false y - constantTerm D (axis D y.2.1) -
      quad (coeffs D (axis D y.2.1)) y.1 - quad (coeffs D (axis D y.2.1)) y.2.2 =
      secular D true y - constantTerm D (axis D y.2.1) - modelDelta D y.2.1 -
        quad (coeffs D (axis D y.2.1)) y.1 - quad (coeffs D (axis D y.2.1)) y.2.2 := by
    intro y hy
    rw [hid y hy]; ring
  refine ⟨r, C, hr, (min_le_left _ _).trans_lt hrh1, hC, ?_, fun x hx => ?_, ?_⟩
  · exact (hAn2.mono (realDisc_mono D a hrr2)).congr (isOpen_realDisc D a hr) heq
  · have hx2 : x ∈ realDisc D a r2 := realDisc_mono D a hrr2 hx
    refine ⟨fun k hk l => ?_, ?_, first_order_at D ha hr hrho hint hAn hx⟩
    · let emb : Vec n → Slow n := fun I => (x.1, I, x.2.2)
      have hopen : IsOpen (emb ⁻¹' realDisc D a r) :=
        (isOpen_realDisc D a hr).preimage (by fun_prop)
      have hev : (fun I => iteratedFDeriv ℝ k (slowSecular D true I) (x.1, x.2.2)) =ᶠ[𝓝 x.2.1]
          fun I => iteratedFDeriv ℝ k (slowSecular D false I) (x.1, x.2.2) := by
        filter_upwards [hopen.mem_nhds (show x.2.1 ∈ emb ⁻¹' realDisc D a r from hx)] with I hI
        exact jets_core D ha hrho hint hr (x := emb I) hI hk
      rw [(hev.iteratedFDeriv ℝ l).self_of_nhds]
    · rw [← heq x hx]
      exact (hB2 x hx2)
  · refine ⟨fun {V r0 μ0 P0 Ω β} hV => ?_, fun {U χ} hΛ hχ y hy => ?_,
      dynamics_at D ha hr hrho hint hAn⟩
    · exact same_jets_transfer D fun I hI p q hpq =>
        realDisc_subset_slowDom D ha hrho (hV I hI p q hpq)
    · have hid' := (identification D (realDisc_subset_slowDom D ha hrho (hχ y hy))).2.2.2
        (hint _ (hχ y hy))
      rw [hid', hΛ y hy]
      ring

/-- `bpP:p8:same-jets#jets`: all `(ξ,η)`-jets of positive order of `S_mov` and `S_fix` agree (with
all `Λ`-derivatives); (a) `S_mov = C₀ + δ + ξᵀ Q_h ξ + ηᵀ Q_h η + O(|(ξ,η)|⁴)` with the same `Q_h`
(hence the same `σ_j`, `Ω_j`); (b) the `(ξ,η)`-gradients agree, so for `μ = ε` the secular
equations coincide, and the `Λ`-gradients differ by that of `δ`. -/
theorem same_jets_jets (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r C : ℝ, 0 < r ∧ r < rho D a / 2 ∧ 0 < C ∧
    AnalyticOnNhd ℝ (fun x : Slow n => secular D true x - constantTerm D (axis D x.2.1) -
      modelDelta D x.2.1 - quad (coeffs D (axis D x.2.1)) x.1 -
      quad (coeffs D (axis D x.2.1)) x.2.2) (realDisc D a r) ∧
    (∀ x ∈ realDisc D a r,
      (∀ k : ℕ, 0 < k → ∀ l : ℕ,
        iteratedFDeriv ℝ l (fun I => iteratedFDeriv ℝ k (slowSecular D true I) (x.1, x.2.2))
          x.2.1 =
        iteratedFDeriv ℝ l (fun I => iteratedFDeriv ℝ k (slowSecular D false I) (x.1, x.2.2))
          x.2.1) ∧
      |secular D true x - constantTerm D (axis D x.2.1) - modelDelta D x.2.1 -
        quad (coeffs D (axis D x.2.1)) x.1 - quad (coeffs D (axis D x.2.1)) x.2.2| ≤
        C * ‖(x.1, x.2.2)‖ ^ 4 ∧
      fderiv ℝ (slowSecular D true x.2.1) (x.1, x.2.2) =
        fderiv ℝ (slowSecular D false x.2.1) (x.1, x.2.2) ∧
      fderiv ℝ (fun I => secular D true (x.1, I, x.2.2)) x.2.1 =
        fderiv ℝ (fun I => secular D false (x.1, I, x.2.2)) x.2.1 +
          fderiv ℝ (modelDelta D) x.2.1) ∧
    ∀ (μ : ℝ) (Hm Hf : Phase (n + n) → ℝ),
    Hm = (fun z => avg (fun t : Vec n => movingHamiltonian D.G D.m0 D.m μ
      (poincareProd D.m (D.G * D.m0) (assemble (fun k => z.2 (Fin.castAdd n k)) t
        (fun k => z.2 (Fin.natAdd n k)) (fun k => z.1 (Fin.natAdd n k)))))) →
    Hf = (fun z => avg (fun t : Vec n => fixedHamiltonian D.G D.m0 D.m μ
      (poincareProd D.m (D.G * D.m0) (assemble (fun k => z.2 (Fin.castAdd n k)) t
        (fun k => z.2 (Fin.natAdd n k)) (fun k => z.1 (Fin.natAdd n k)))))) →
    ∀ x ∈ realDisc D a r, ∀ (φ : Vec n) (i : Fin n) (z : Phase (n + n)),
      z = assemble x.2.1 φ x.2.2 x.1 →
      (hamiltonianVectorField Hm z).1 (Fin.natAdd n i) =
        μ * fderiv ℝ (secular D true) x (0, 0, Pi.single i 1) ∧
      (hamiltonianVectorField Hm z).2 (Fin.natAdd n i) =
        -(μ * fderiv ℝ (secular D true) x (Pi.single i 1, 0, 0)) ∧
      (hamiltonianVectorField Hm z).2 (Fin.castAdd n i) = 0 ∧
      (hamiltonianVectorField Hf z).1 (Fin.natAdd n i) =
        μ * fderiv ℝ (secular D false) x (0, 0, Pi.single i 1) ∧
      (hamiltonianVectorField Hf z).2 (Fin.natAdd n i) =
        -(μ * fderiv ℝ (secular D false) x (Pi.single i 1, 0, 0)) ∧
      (hamiltonianVectorField Hf z).2 (Fin.castAdd n i) = 0 ∧
      (hamiltonianVectorField Hm z).1 (Fin.natAdd n i) =
        (hamiltonianVectorField Hf z).1 (Fin.natAdd n i) ∧
      (hamiltonianVectorField Hm z).2 (Fin.natAdd n i) =
        (hamiltonianVectorField Hf z).2 (Fin.natAdd n i) ∧
      (hamiltonianVectorField Hm z).1 (Fin.castAdd n i) =
        (hamiltonianVectorField Hf z).1 (Fin.castAdd n i) +
          μ * fderiv ℝ (modelDelta D) x.2.1 (Pi.single i 1) := by
  obtain ⟨r, C, hr, hrh, hC, hA, hJ, -, -, hD⟩ := same_jets_full D ha
  exact ⟨r, C, hr, hrh, hC, hA, hJ, hD⟩

/-- `bpP:p8:same-jets#transfer` (c): `HasBirkhoff` transfers in both directions with
`P₀ ↦ P₀ - δ` when the points `(Λ, η, ξ)`, `Λ ∈ V`, `p_j² + q_j² < r₀²` lie in the real polydisc
(unchanged `Ω`, `β`), and `S_mov ∘ χ - S_fix ∘ χ = δ(Λ)` for every slow change `χ` that keeps `Λ`
and takes values in the real polydisc. -/
theorem same_jets_transfer_full (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a / 2 ∧
    (∀ {V : Set (Vec n)} {r0 μ0 : ℝ} {P0 : ℝ → Vec n → ℝ} {Ω : ℝ → Vec n → Vec n}
      {β : ℝ → Vec n → Mat n},
      (∀ I ∈ V, ∀ p q : Vec n, (∀ j, p j ^ 2 + q j ^ 2 < r0 ^ 2) → (q, I, p) ∈ realDisc D a r) →
      (HasSecularBirkhoffForm (fun _ => perturbation D true) V r0 μ0 P0 Ω β ↔
        HasSecularBirkhoffForm (fun _ => perturbation D false) V r0 μ0
          (fun μ I => P0 μ I - modelDelta D I) Ω β)) ∧
    ∀ {U : Set (Slow n)} {χ : Slow n → Slow n}, (∀ y ∈ U, (χ y).2.1 = y.2.1) →
      (∀ y ∈ U, χ y ∈ realDisc D a r) →
      ∀ y ∈ U, secular D true (χ y) - secular D false (χ y) = modelDelta D y.2.1 := by
  obtain ⟨r, C, hr, hrh, -, -, -, hT, hT', -⟩ := same_jets_full D ha
  exact ⟨r, hr, hrh, hT, hT'⟩

/-! ### The quartic jet -/

/-- `stepP:p8:q4-c`: the diagonal quartic coefficients are `G mᵢ mⱼ r₁ᵉˣ / (2 Λ²)` (the source
statement is the case `G = m₀ = 1`), with `r₁ᵉˣ = radialR1`. -/
theorem quartic_c_node (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) {i j : Fin n}
    (hij : i < j) :
    quarticCoeff D i j (I i, I j) 0 =
      D.G * D.m i * D.m j * radialR1 (axis D I i) (axis D I j) / (2 * I i ^ 2) ∧
    quarticCoeff D i j (I i, I j) 1 =
      D.G * D.m i * D.m j * radialR1 (axis D I j) (axis D I i) / (2 * I j ^ 2) := by
  obtain ⟨a, ha, rfl⟩ := hI
  have h0 := quarticCoeff_zero D i j (action_pos D ha i) (action_pos D ha j)
    (action_axes_lt D ha hij)
  have h1 := quarticCoeff_one D i j (action_pos D ha i) (action_pos D ha j)
    (action_axes_lt D ha hij)
  refine ⟨?_, ?_⟩
  · rw [h0]; unfold radialR1 axis; ring
  · rw [h1]; unfold radialR1 axis; ring

/-- The separated domain contains the product of the small balls `|v| < min(1/4, (1-α)/(1+α))`. -/
private theorem mem_separatedDomain_of_small {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {vi vj : Fin 2 → ℝ} (hi : planeLength vi < min (1 / 4) ((1 - α) / (1 + α)))
    (hj : planeLength vj < min (1 / 4) ((1 - α) / (1 + α))) :
    (α, vi, vj) ∈ separatedDomain := by
  have hi1 := hi.trans_le (min_le_left _ _)
  have hj1 := hj.trans_le (min_le_left _ _)
  have hi2 := hi.trans_le (min_le_right _ _)
  have hj2 := hj.trans_le (min_le_right _ _)
  have hs : (1 + α) * ((1 - α) / (1 + α)) = 1 - α := by field_simp
  have hli : 0 ≤ planeLength vi := Real.sqrt_nonneg _
  refine ⟨hα0, hα1, hi1, hj1, ?_⟩
  nlinarith

/-- The Taylor coefficients of `𝒲(α; ·)` at `v = 0`, of every order, are real analytic in `α` on the
whole interval `(0, 1)`. -/
private theorem taylor_analytic_alpha (k : ℕ) :
    AnalyticOnNhd ℝ (fun α : ℝ => iteratedFDeriv ℝ k
      (fun v : (Fin 2 → ℝ) × (Fin 2 → ℝ) => dimensionlessPair (α, v.1, v.2)) 0) (Ioo 0 1) := by
  set F : ℝ × PairW → ℝ := fun p => dimensionlessPair (p.1, p.2.1, p.2.2) with hF
  set W : Set (ℝ × PairW) := {p | (p.1, p.2.1, p.2.2) ∈ separatedDomain} with hW
  have hWo : IsOpen W := qsc_isOpen_separatedDomain.preimage (by fun_prop)
  have hFa : AnalyticOnNhd ℝ F W := fun p hp =>
    (quartic_scaling _ hp).comp_of_eq (analyticAt_fst.prod
      ((analyticAt_fst.comp analyticAt_snd).prod (analyticAt_snd.comp analyticAt_snd))) rfl
  have hmem : ∀ α ∈ Ioo (0 : ℝ) 1, (α, (0 : PairW)) ∈ W := fun α hα => by
    refine ⟨hα.1, hα.2, ?_, ?_, ?_⟩ <;> simp [planeLength, planeSq]
    linarith [hα.1, hα.2]
  set ι := ContinuousLinearMap.inr ℝ ℝ PairW with hι
  have hslice : ∀ α ∈ Ioo (0 : ℝ) 1, iteratedFDeriv ℝ k (fun v : PairW => F (α, v)) 0 =
      (iteratedFDeriv ℝ k F (α, 0)).compContinuousLinearMap fun _ => ι := by
    intro α hα
    set a : ℝ × PairW := (α, 0) with ha
    set S : Set (ℝ × PairW) := (fun z => a + z) ⁻¹' W with hS
    have hSo : IsOpen S := hWo.preimage (continuous_const.add continuous_id)
    have hFa' : ContDiffOn ℝ k (fun z => F (a + z)) S :=
      (hFa.contDiffOn_of_completeSpace.mono (fun z hz => hz) : ContDiffOn ℝ k F W).comp
        (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
    have hy : ι 0 ∈ S := by simpa [hS, ha, hι] using hmem α hα
    have h1 := ι.iteratedFDerivWithin_comp_right (f := fun z => F (a + z)) hFa'
      hSo.uniqueDiffOn ((hSo.preimage ι.continuous).uniqueDiffOn) hy (i := k)
      (by exact_mod_cast le_rfl)
    rw [iteratedFDerivWithin_of_isOpen _ hSo hy,
      iteratedFDerivWithin_of_isOpen _ (hSo.preimage ι.continuous) (by exact hy)] at h1
    have hfun : (fun v : PairW => F (α, v)) = (fun z => F (a + z)) ∘ ι := by
      funext y'; simp [ha, hι, hF]
    rw [hfun, h1, iteratedFDeriv_comp_add_left]
    simp [ha, hι]
  have hA : AnalyticOnNhd ℝ (fun α : ℝ => iteratedFDeriv ℝ k F (α, 0)) (Ioo 0 1) := by
    refine (hFa.iteratedFDeriv_of_isOpen hWo k).comp
      (analyticOnNhd_id.prod analyticOnNhd_const) (fun α hα => hmem α hα)
  have hL := (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ι) : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × PairW) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => PairW) ℝ).comp_analyticOnNhd hA
  exact hL.congr (isOpen_Ioo) (fun α hα => (hslice α hα).symm)

/-- `bpP:p8:quartic`: the six invariant coefficients (analytic in the two actions) give the
degree-four jet of `S_fix` and of `S_mov`; the diagonal coefficients are the explicit
`radialR1` values; the pair average is `-G mᵢ mⱼ a_j⁻¹ 𝒲(α; vᵢ, vⱼ)` with `𝒲 = dimensionlessPair`
real analytic on the separated domain, which contains the sufficient subdomain; and the exact
passage to `u` is the stated expansion. -/
theorem quartic_full (D : Data n) (_hn : 2 ≤ n) :
    (∃ c : Fin n → Fin n → (ℝ × ℝ) → Fin 6 → ℝ,
      (∀ i j, i < j → AnalyticOnNhd ℝ (c i j)
        {IJ | 0 < IJ.1 ∧ 0 < IJ.2 ∧ IJ.1 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) <
          IJ.2 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))}) ∧
      (∀ I ∈ actionDomain D, ∀ u : Vec n × Vec n,
        iteratedFDeriv ℝ 4 (slowSecular D false I) 0 (fun _ => u) / 24 =
          ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
            ∑ k, c i j (I i, I j) k * quarticMonomials ![u.1 i, u.2 i] ![u.1 j, u.2 j] k ∧
        iteratedFDeriv ℝ 4 (slowSecular D true I) 0 (fun _ => u) / 24 =
          ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
            ∑ k, c i j (I i, I j) k * quarticMonomials ![u.1 i, u.2 i] ![u.1 j, u.2 j] k) ∧
      (∀ I ∈ actionDomain D, ∀ i j, i < j →
        c i j (I i, I j) 0 =
          D.G * D.m i * D.m j * radialR1 (axis D I i) (axis D I j) / (2 * I i ^ 2) ∧
        c i j (I i, I j) 1 =
          D.G * D.m i * D.m j * radialR1 (axis D I j) (axis D I i) / (2 * I j ^ 2)) ∧
      ∀ i j, i < j → ∀ {I0 J0 : ℝ}, 0 < I0 → 0 < J0 →
        I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) →
        ∃ (A A' B : ℝ) (cW : Fin 6 → ℝ),
          (fun v : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
            dimensionlessPair (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) /
              (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))), v.1, v.2) -
            dimensionlessPair (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) /
              (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))), 0, 0) -
            (A * planeSq v.1 + A' * planeSq v.2 + B * planeDot v.1 v.2) -
            ∑ k, cW k * quarticMonomials v.1 v.2 k) =O[𝓝 0] (fun v => ‖v‖ ^ 5) ∧
          ∀ w : (Fin 2 → ℝ) × (Fin 2 → ℝ),
            ∑ k, c i j (I0, J0) k * quarticMonomials w.1 w.2 k =
              -D.G * D.m i * D.m j / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) *
                (∑ k, cW k * quarticMonomials ((√I0)⁻¹ • w.1) ((√J0)⁻¹ • w.2) k -
                  (A / 4 * planeSq w.1 ^ 2 / I0 ^ 2 + A' / 4 * planeSq w.2 ^ 2 / J0 ^ 2 +
                    B / 8 * (planeDot w.1 w.2 / (√I0 * √J0)) *
                      (planeSq w.1 / I0 + planeSq w.2 / J0))) ) ∧
    AnalyticOnNhd ℝ dimensionlessPair separatedDomain ∧
    (∀ {i j : Fin n}, i < j → ∀ {L1 L2 : ℝ}, 0 < L1 → 0 < L2 → ∀ u v : Fin 2 → ℝ,
      (![0, u 0], ![L1, u 1]) ∈ poincareDom → (![0, v 0], ![L2, v 1]) ∈ poincareDom →
      (L1 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (L2 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))),
        poincareV (![0, u 0], ![L1, u 1]), poincareV (![0, v 0], ![L2, v 1])) ∈
        separatedDomain →
      pairSlowSecular D i j L1 L2 (u, v) =
        -D.G * D.m i * D.m j / (L2 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) *
          dimensionlessPair (L1 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) /
            (L2 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))),
            poincareV (![0, u 0], ![L1, u 1]), poincareV (![0, v 0], ![L2, v 1]))) ∧
    (∀ {α : ℝ} {vi vj : Fin 2 → ℝ}, 0 < α → α < 1 →
      planeLength vi < min (1 / 4) ((1 - α) / (1 + α)) →
      planeLength vj < min (1 / 4) ((1 - α) / (1 + α)) → (α, vi, vj) ∈ separatedDomain) ∧
    ∀ k : ℕ, AnalyticOnNhd ℝ (fun α : ℝ => iteratedFDeriv ℝ k
      (fun v : (Fin 2 → ℝ) × (Fin 2 → ℝ) => dimensionlessPair (α, v.1, v.2)) 0) (Ioo 0 1) := by
  refine ⟨⟨fun i j IJ => quarticCoeff D i j IJ, fun i j _ IJ hIJ =>
    analyticAt_quarticCoeff D i j hIJ.1 hIJ.2.1 hIJ.2.2, fun I hI u => ⟨?_, ?_⟩,
    fun I hI i j hij => quartic_c_node D hI hij,
    fun i j hij {I0 J0} hI hJ hab => quartic_pair_chart_conversion hij hI hJ hab⟩,
    quartic_scaling,
    fun {i j} hij {L1 L2} hI hJ u v hu hv hSep =>
      quartic_pair_scaling D hij hI hJ u v hu hv hSep,
    fun {α vi vj} h0 h1 hi hj => mem_separatedDomain_of_small h0 h1 hi hj,
    taylor_analytic_alpha⟩
  · exact quartic_jet D hI u
  · rw [same_jets D hI 4 (by norm_num)]
    exact quartic_jet D hI u

end SecularForm
end KAM.Planetary
end
