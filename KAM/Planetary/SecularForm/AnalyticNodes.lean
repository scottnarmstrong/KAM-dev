/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Analytic
public import KAM.Planetary.SecularForm.ParameterIntegral

/-!
# Secular form: literal exports for the analyticity nodes

Blueprint P, Part 8, graph-gap package GAP-P8b. Unsigned exports stating the literal conclusions of
the proof steps `stepP:p8:pa-unif`, `stepP:p8:pa-hol`, `stepP:p8:pa-avg` and of the proposition
`bpP:p8:perturbation-analytic` (bundle `perturbation_analytic_full`), built from the landed
`AnalyticGeometry`, `AnalyticRegularity`, `AnalyticReal`, `Analytic` and `ParameterIntegral`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

/-- At a real point the assembled phase lies in the domain of the product chart. -/
private theorem assemble_mem_dom (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) :
    assemble x.2.1 t x.2.2 x.1 ∈ poincareProdDom n := by
  intro i
  have hΛ := action_pos D ha i
  have h := (poincare_holomorphic (m := D.m i) (κ := D.G * D.m0) (Λo := action D a i)
    (D.hm i) (mul_pos D.hG D.hm0) hΛ).2.2.2.2
  have hb : blockC t (inclusion x) i = phaseToC (planetBlock (assemble x.2.1 t x.2.2 x.1) i) := by
    rw [planetBlock_assemble_slow]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
      simp [blockC, inclusion, phaseToC]
  have hmem := blockC_mem_nbhd D ha hr (t := t) hx i
  rw [hb] at hmem
  exact (h _ hmem).1

private theorem gap_pos {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j) :
    0 < (a j - a i) ^ 2 / 2 := by
  have : a i < a j := ha.2 hij
  have : 0 < a j - a i := by linarith
  positivity

/-- Under the separation bound, real points of the polydisc are collision free. -/
private theorem mem_collisionFree (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) :
    poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1) ∈ collisionFreeDomain n := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hw := assemble_mem_dom D ha hr hx t
  have hreg := poincareProd_mem_regionProd D.hm hκ hw
  set z := poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1) with hz
  have hsq : ∀ i j, i < j → 0 < planeSq (bodyVector z.1 i - bodyVector z.1 j) := by
    intro i j hij
    have h := hsep t (inclusion x) hx i j hij
    rw [separationC_inclusion D ha hr hx, Complex.ofReal_re] at h
    exact lt_of_lt_of_le (gap_pos ha hij) h
  refine ⟨fun i => (hreg i).1, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact Real.sqrt_pos.2 (hsq i j h)
  · have := hsq j i h
    have e : planeSq (bodyVector z.1 i - bodyVector z.1 j) =
        planeSq (bodyVector z.1 j - bodyVector z.1 i) := by
      unfold planeSq
      exact Finset.sum_congr rfl fun k _ => by simp only [Pi.sub_apply]; ring
    exact Real.sqrt_pos.2 (e ▸ this)

/-- `stepP:p8:pa-unif`: one radius `ρ* < ρ₀/2` with `Re s_ij ≥ (a_j - a_i)²/2` for all angles; at
real points `s_ij = |q_i - q_j|²`, `|q_i - q_j| ≥ (a_j - a_i)/√2`, and the position is collision
free for every angle. -/
theorem perturbation_unif (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a / 2 ∧
      (∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
        ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re) ∧
      ∀ x ∈ realDisc D a r, ∀ t : Vec n,
        (∀ i j, separationC D t (inclusion x) i j =
          ((planeSq (bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
            bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j) : ℝ) :
            ℂ)) ∧
        (∀ i j, i < j → (a j - a i) / √2 ≤
          planeLength (bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
            bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j)) ∧
        poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1) ∈ collisionFreeDomain n := by
  obtain ⟨r0, hr0, hrho0, hsep0⟩ := exists_radius D ha
  have hρ := rho_pos D ha
  set r := min r0 (rho D a / 4) with hrdef
  have hr : 0 < r := lt_min hr0 (by positivity)
  have hrhalf : r < rho D a / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hrr : r < rho D a := by linarith
  have hsub : polydisc D a r ⊆ polydisc D a r0 := by
    rw [polydisc_eq_ball D a hr, polydisc_eq_ball D a hr0]
    exact Metric.ball_subset_ball (min_le_left _ _)
  have hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re :=
    fun t x hx i j hij => hsep0 t x (hsub hx) i j hij
  refine ⟨r, hr, hrhalf, hsep, fun x hx t => ⟨fun i j => ?_, fun i j hij => ?_, ?_⟩⟩
  · exact separationC_inclusion D ha hrr hx t i j
  · have h := hsep t (inclusion x) hx i j hij
    rw [separationC_inclusion D ha hrr hx, Complex.ofReal_re] at h
    have h2 : ((a j - a i) / √2) ^ 2 ≤ planeSq (bodyVector
        (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
        bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j) := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      exact h
    have h3 : 0 ≤ (a j - a i) / √2 := by
      have : a i < a j := ha.2 hij
      have : 0 < a j - a i := by linarith
      positivity
    exact Real.le_sqrt_of_sq_le h2
  · exact mem_collisionFree D ha hrr hsep hx t

/-- `bpP:p8:perturbation-analytic` (b), periodicity: `f̂` is `2π`-periodic in each angle. -/
theorem perturbationC_periodic (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) (b : Bool) {x : CSlow n} (hx : x ∈ polydisc D a r) (t : Vec n)
    (i : Fin n) :
    perturbationC D b (Function.update t i (t i + 2 * π)) x = perturbationC D b t x := by
  have hp : ∀ k, planetC D (Function.update t i (t i + 2 * π)) x k = planetC D t x k := by
    intro k
    by_cases hk : k = i
    · subst hk
      have := planetC_periodic D ha hr hx k (t k)
      simpa [planetC, Function.update_self] using this
    · simp [planetC, Function.update_of_ne hk]
  unfold perturbationC separationC
  simp only [hp]

end SecularForm
end KAM.Planetary
end
