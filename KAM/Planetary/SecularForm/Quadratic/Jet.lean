/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.PairHessian
public import KAM.Planetary.SecularForm.Quadratic.Algebra
public import KAM.Planetary.SecularForm.Quadratic.Coeff

/-!
# Quadratic part: the jet of the secular function along rays

Blueprint P, Part 8, `stepP:p8:qf-pair` and `stepP:p8:qf-assembly` (package S8-Q). Along the ray
`s ↦ (s ξ, Λ, s η)` at `Λ = action D a`, the function
`ψ(s) = S(sξ, Λ, sη) - C₀(a) - s² (ξᵀ Q ξ + ηᵀ Q η)` is analytic and its derivatives of order `≤ 3`
at `s = 0` vanish: the value and the second derivative come from the pair decomposition
(`secular_eq_sum_pair`, `pair_value_zero`, `pair_second_derivative`, `quad_pair_sum`), the odd ones
from `evenness`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

/-- The ray in the slow variables. -/
def raySlow (D : Data n) (a : Vec n) (ξ η : Vec n) (s : ℝ) : Slow n :=
  (s • ξ, action D a, s • η)

/-- The remainder along the ray. -/
def rayRemainder (D : Data n) (a : Vec n) (ξ η : Vec n) (s : ℝ) : ℝ :=
  secular D false (raySlow D a ξ η s) - constantTerm D a -
    s ^ 2 * (quad (coeffs D a) ξ + quad (coeffs D a) η)

theorem analyticAt_raySlow (D : Data n) (a ξ η : Vec n) (s : ℝ) :
    AnalyticAt ℝ (raySlow D a ξ η) s := by
  unfold raySlow
  exact (analyticAt_id.smul analyticAt_const).prod
    (analyticAt_const.prod (analyticAt_id.smul analyticAt_const))

theorem continuous_raySlow (D : Data n) (a ξ η : Vec n) : Continuous (raySlow D a ξ η) := by
  unfold raySlow
  fun_prop

/-- The pair vector of the pair `(i, j)` along the ray. -/
def rayPair (ξ η : Vec n) (i j : Fin n) : Vec 2 × Vec 2 := (![ξ i, η i], ![ξ j, η j])

theorem raySlow_zero_mem (D : Data n) (a ξ η : Vec n) {r : ℝ} (hr : 0 < r) :
    raySlow D a ξ η 0 ∈ realDisc D a r := by
  intro i
  simp [raySlow, inclusion, hr]

/-- The pair decomposition along the ray, near `s = 0`. -/
theorem secular_ray_eq (D : Data n) {a : Vec n} (ha : a ∈ axes n) (ξ η : Vec n) :
    ∀ᶠ s in 𝓝 (0 : ℝ), secular D false (raySlow D a ξ η s) =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        pairSlowSecular D i j (action D a i) (action D a j) (s • rayPair ξ η i j) := by
  obtain ⟨r, hr0, hrho, hsepC, -⟩ := perturbation_analytic D ha
  have hopen := isOpen_realDisc D a hr0
  have hW : ∀ᶠ s in 𝓝 (0 : ℝ), raySlow D a ξ η s ∈ realDisc D a r :=
    ((continuous_raySlow D a ξ η).continuousAt).preimage_mem_nhds
      (hopen.mem_nhds (raySlow_zero_mem D a ξ η hr0))
  filter_upwards [hW] with s hs
  have hx := mem_slowDom_of_realDisc D ha hrho hs
  have hsep := pairSeparated_of_realDisc D ha hrho hsepC hs
  rw [secular_eq_sum_pair D hx hsep]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hij := (Finset.mem_filter.1 hj).2
  rw [secular_pair_eq D hx (hsep i j hij)]
  simp only [raySlow, rayPair, Prod.smul_mk]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp

theorem rayRemainder_zero (D : Data n) {a : Vec n} (ha : a ∈ axes n) (ξ η : Vec n) :
    rayRemainder D a ξ η 0 = 0 := by
  have h0 := (secular_ray_eq D ha ξ η).self_of_nhds
  unfold rayRemainder
  rw [h0]
  simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    sub_zero]
  rw [constantTerm, ← Finset.sum_neg_distrib, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact pair_value_zero D ha (Finset.mem_filter.1 hj).2

theorem analyticAt_rayRemainder (D : Data n) {a : Vec n} (ha : a ∈ axes n) (ξ η : Vec n) :
    AnalyticAt ℝ (rayRemainder D a ξ η) 0 := by
  obtain ⟨r, hr0, -, -, hall⟩ := perturbation_analytic D ha
  have hA := (hall false).2.2.2.2.1 _ (raySlow_zero_mem D a ξ η hr0)
  have h1 : AnalyticAt ℝ (fun s : ℝ => secular D false (raySlow D a ξ η s)) 0 :=
    hA.comp (analyticAt_raySlow D a ξ η 0)
  unfold rayRemainder
  exact (h1.sub analyticAt_const).sub (analyticAt_id.pow 2 |>.mul analyticAt_const)

theorem rayRemainder_even (D : Data n) {a : Vec n} (ha : a ∈ axes n) (ξ η : Vec n) :
    rayRemainder D a ξ η =ᶠ[𝓝 0] fun s => rayRemainder D a ξ η (-s) := by
  obtain ⟨r, hr0, hrho, -, -⟩ := perturbation_analytic D ha
  have hW : ∀ᶠ s in 𝓝 (0 : ℝ), raySlow D a ξ η s ∈ realDisc D a r :=
    ((continuous_raySlow D a ξ η).continuousAt).preimage_mem_nhds
      ((isOpen_realDisc D a hr0).mem_nhds (raySlow_zero_mem D a ξ η hr0))
  filter_upwards [hW] with s hs
  have hx := mem_slowDom_of_realDisc D ha hrho hs
  have h := (evenness D hx false 0).1
  have e : raySlow D a ξ η (-s) = (-(raySlow D a ξ η s).1, (raySlow D a ξ η s).2.1,
      -(raySlow D a ξ η s).2.2) := by
    simp [raySlow]
  unfold rayRemainder
  rw [e, h]
  ring

theorem iteratedDeriv_rayRemainder_odd (D : Data n) {a : Vec n} (ha : a ∈ axes n) (ξ η : Vec n)
    {m : ℕ} (hm : Odd m) : iteratedDeriv m (rayRemainder D a ξ η) 0 = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_odd_eq_zero (rayRemainder_even D ha ξ η) hm]
  rfl

theorem iteratedDeriv_two_rayRemainder (D : Data n) {a : Vec n} (ha : a ∈ axes n)
    (ξ η : Vec n) : iteratedDeriv 2 (rayRemainder D a ξ η) 0 = 0 := by
  set Q := quad (coeffs D a) ξ + quad (coeffs D a) η with hQ
  set φ : Fin n → Fin n → ℝ → ℝ := fun i j s =>
    pairSlowSecular D i j (action D a i) (action D a j) (s • rayPair ξ η i j) with hφ
  have hφa : ∀ i j, i < j → AnalyticAt ℝ (φ i j) 0 := fun i j hij =>
    (analyticAt_pairSlowSecular D ha hij).comp_of_eq
      (analyticAt_id.smul analyticAt_const) (by simp)
  have hev : rayRemainder D a ξ η =ᶠ[𝓝 0] fun s : ℝ =>
      (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), φ i j s) - (constantTerm D a + Q * s ^ 2) := by
    filter_upwards [secular_ray_eq D ha ξ η] with s hs
    unfold rayRemainder
    rw [hs]; ring
  have hcd : ∀ i : Fin n, ContDiffAt ℝ 2 (fun s => ∑ j ∈ Finset.univ.filter (i < ·), φ i j s) 0 :=
    fun i => ContDiffAt.sum fun j hj => (hφa i j (Finset.mem_filter.1 hj).2).contDiffAt
  have hcdF : ContDiffAt ℝ 2 (fun s => ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), φ i j s) 0 :=
    ContDiffAt.sum fun i _ => hcd i
  have hpoly : ContDiffAt ℝ 2 (fun s : ℝ => constantTerm D a + Q * s ^ 2) 0 := by
    have : AnalyticAt ℝ (fun s : ℝ => constantTerm D a + Q * s ^ 2) 0 := by fun_prop
    exact this.contDiffAt
  rw [hev.iteratedDeriv_eq 2, iteratedDeriv_fun_sub hcdF hpoly,
    iteratedDeriv_fun_sum (fun i _ => hcd i), iteratedDeriv_two_quadratic]
  have hin : ∀ i : Fin n, iteratedDeriv 2 (fun s => ∑ j ∈ Finset.univ.filter (i < ·), φ i j s) 0 =
      ∑ j ∈ Finset.univ.filter (i < ·), iteratedDeriv 2 (φ i j) 0 := fun i =>
    iteratedDeriv_fun_sum fun j hj => (hφa i j (Finset.mem_filter.1 hj).2).contDiffAt
  simp only [hin]
  have hpair : ∀ i j, i < j → iteratedDeriv 2 (φ i j) 0 =
      2 * ((-pairA D a i j / action D a i) * (ξ i ^ 2 + η i ^ 2) +
        (-pairA D a i j / action D a j) * (ξ j ^ 2 + η j ^ 2) +
        2 * coeffs D a i j * (ξ i * ξ j + η i * η j)) := fun i j hij => by
    rw [hφ]
    simp only
    rw [pair_second_derivative D ha hij (rayPair ξ η i j)]
    simp only [rayPair, planeSq, planeDot, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hsum : ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), iteratedDeriv 2 (φ i j) 0 = 2 * Q := by
    rw [hQ, quad_pair_sum D ha ξ η, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => hpair i j (Finset.mem_filter.1 hj).2
  rw [hsum]; ring

theorem iteratedDeriv_rayRemainder (D : Data n) {a : Vec n} (ha : a ∈ axes n) (ξ η : Vec n)
    {k : ℕ} (hk : k ≤ 3) : iteratedDeriv k (rayRemainder D a ξ η) 0 = 0 := by
  interval_cases k
  · simpa using rayRemainder_zero D ha ξ η
  · exact iteratedDeriv_rayRemainder_odd D ha ξ η (by decide)
  · exact iteratedDeriv_two_rayRemainder D ha ξ η
  · exact iteratedDeriv_rayRemainder_odd D ha ξ η (by decide)

end SecularForm
end KAM.Planetary
end
