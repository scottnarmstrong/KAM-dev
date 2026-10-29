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
    ∃ r : ℝ, 0 < r ∧ r < rho D a / 2 ∧ ∀ b : Bool, ∀ x ∈ realDisc D a r,
      IntegrableOn (fun t => perturbation D b (assemble x.2.1 t x.2.2 x.1)) (cell n) := by
  obtain ⟨r1, hr1, hrho1, -, h1⟩ := perturbation_analytic D ha
  obtain ⟨r2, hr2, hrh2, -⟩ := perturbation_analytic_full D ha
  refine ⟨min r1 r2, lt_min hr1 hr2, (min_le_right _ _).trans_lt hrh2, fun b x hx => ?_⟩
  exact (h1 b).2.2.2.2.2.2 x (realDisc_mono D a (min_le_left _ _) hx)

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
    exact ⟨r, hr0, hrh, fun x hx => ⟨h true x hx, h false x hx⟩⟩

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

/-- `bpP:p8:identification`: the difference is continuous with average `δ(Λ)`; integrability of
`f̂_fix` and `f̂_mov` is equivalent and then `S_mov = S_fix + δ`; on the real polydisc this holds
unconditionally, with `⟨H_mov^Ψ⟩ = h + μ S_mov = h + μ S_fix + μ δ` and `⟨H_fix^Ψ⟩ = h + ε S_fix`. -/
theorem identification_full (D : Data n) :
    (∀ x ∈ slowDom D,
      Continuous (fun t : Vec n => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
        perturbation D false (assemble x.2.1 t x.2.2 x.1)) ∧
      avg (fun t : Vec n => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
        perturbation D false (assemble x.2.1 t x.2.2 x.1)) = modelDelta D x.2.1 ∧
      (IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) ↔
        IntegrableOn (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1)) (cell n)) ∧
      (IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) →
        secular D true x = secular D false x + modelDelta D x.2.1)) ∧
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
    (identification D hx).2.2.1.symm, (identification D hx).2.2.2⟩, fun {a} ha => ?_⟩
  obtain ⟨r, hr0, hrh, h⟩ := radius_integrable D ha
  have hrho : r < rho D a := by have := rho_pos D ha; linarith
  refine ⟨r, hr0, hrh, fun x hx => ?_⟩
  have hxd := realDisc_subset_slowDom D ha hrho hx
  have hid := (identification D hxd).2.2.2 (h false x hx)
  have hH := avg_hamiltonians D hxd (h false x hx) (h true x hx)
  refine ⟨hid, fun μ => ⟨(hH μ).1, ?_⟩, fun ε => (hH ε).2⟩
  rw [hid]
  ring

end SecularForm
end KAM.Planetary
end
