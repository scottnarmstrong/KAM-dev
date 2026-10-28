/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.Marginal
public import KAM.Planetary.SecularForm.Symmetry
public import KAM.Planetary.SecularForm.Momentum

/-!
# Quadratic part: the secular function is the sum of the pair averages

Blueprint P, Part 8, `stepP:p8:qf-pair` (package S8-Q). The perturbation `-Σ_{i<j} G mᵢ mⱼ/|qᵢ-qⱼ|`
is a sum of pair terms each depending on two angles only; away from collisions the cell average of
each is its two-planet secular function (`pairData`, `pairSlow`), by `avg_pair_marginal`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

/-- The two-planet data of the pair `(i, j)`. -/
def pairData (D : Data n) (i j : Fin n) : Data 2 where
  G := D.G
  m0 := D.m0
  m := ![D.m i, D.m j]
  hG := D.hG
  hm0 := D.hm0
  hm := fun k => by fin_cases k <;> simp [D.hm]
  hn := by norm_num

/-- The slow point of the pair `(i, j)`. -/
def pairSlow (x : Slow n) (i j : Fin n) : Slow 2 :=
  (![x.1 i, x.1 j], ![x.2.1 i, x.2.1 j], ![x.2.2 i, x.2.2 j])

/-- The position of planet `i` at the slow point `x` and mean longitude `s`. -/
def pairPos (D : Data n) (x : Slow n) (i : Fin n) (s : ℝ) : Fin 2 → ℝ :=
  (poincare (D.m i) (D.G * D.m0) (![s, x.1 i], ![x.2.1 i, x.2.2 i])).1

/-- The pair term `-G mᵢ mⱼ/|qᵢ - qⱼ|` as a function of the two mean longitudes. -/
def pairTerm (D : Data n) (x : Slow n) (i j : Fin n) (s : Vec 2) : ℝ :=
  -D.G * D.m i * D.m j / planeLength (pairPos D x i (s 0) - pairPos D x j (s 1))

/-- The planets `i < j` never collide, for independent mean longitudes. -/
def PairSeparated (D : Data n) (x : Slow n) : Prop :=
  ∀ i j : Fin n, i < j → ∀ s s' : ℝ, pairPos D x i s ≠ pairPos D x j s'

private theorem continuous_planeLength_q : Continuous planeLength := by
  unfold planeLength planeSq
  fun_prop

theorem perturbation_false_eq (D : Data n) (x : Slow n) (t : Vec n) :
    perturbation D false (assemble x.2.1 t x.2.2 x.1) =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), pairTerm D x i j ![t i, t j] := by
  simp only [perturbation, Bool.false_eq_true, ite_false, fFix, pairPotential,
    poincareProd_assemble, bodyVector_ofPlanets_fst, pairTerm, pairPos, Matrix.cons_val_zero,
    Matrix.cons_val_one, ← Finset.sum_neg_distrib]
  simp [neg_mul, neg_div]

theorem perturbation_pair_eq (D : Data n) (x : Slow n) (i j : Fin n) (t : Vec 2) :
    perturbation (pairData D i j) false
      (assemble (pairSlow x i j).2.1 t (pairSlow x i j).2.2 (pairSlow x i j).1) =
      pairTerm D x i j t := by
  rw [perturbation_false_eq]
  have ht : t = ![t 0, t 1] := by ext k; fin_cases k <;> rfl
  rw [ht]
  simp [Finset.sum_filter, Fin.sum_univ_two, pairTerm, pairPos, pairData, pairSlow]

theorem secular_eq_avg (D : Data n) (b : Bool) (x : Slow n) :
    secular D b x = avg (fun t : Vec n => perturbation D b (assemble x.2.1 t x.2.2 x.1)) := rfl

theorem avg_finset_sum {ι : Type*} (s : Finset ι) {f : ι → Vec n → ℝ}
    (hf : ∀ c ∈ s, ContinuousOn (f c) (cell n)) :
    avg (fun t => ∑ c ∈ s, f c t) = ∑ c ∈ s, avg (f c) := by
  unfold avg
  rw [integral_finsetSum _ fun c hc => (hf c hc).integrableOn_compact isCompact_cell,
    Finset.smul_sum]

theorem continuous_pairPos (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) (k : Fin n) :
    Continuous (pairPos D x k) := by
  have := (analyticOnNhd_poincare (D.hm k) (mul_pos D.hG D.hm0)).continuousOn
  have h2 : Continuous fun s : ℝ => ((![s, x.1 k], ![x.2.1 k, x.2.2 k]) : Phase 2) := by
    refine Continuous.prodMk ?_ continuous_const
    rw [continuous_pi_iff]
    intro c; fin_cases c <;> simp <;> fun_prop
  exact continuous_fst.comp (this.comp_continuous h2 (fun s => blk_mem hx k s))

theorem continuous_pairTerm (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) {i j : Fin n}
    (hsep : ∀ s s' : ℝ, pairPos D x i s ≠ pairPos D x j s') : Continuous (pairTerm D x i j) := by
  unfold pairTerm
  refine continuous_const.div (continuous_planeLength_q.comp ?_) fun s => ?_
  · exact ((continuous_pairPos D hx i).comp (continuous_apply 0)).sub
      ((continuous_pairPos D hx j).comp (continuous_apply 1))
  · exact (planeLength_pos_iff.2 (sub_ne_zero.2 (hsep _ _))).ne'

theorem secular_eq_sum_pair (D : Data n) {x : Slow n} (hx : x ∈ slowDom D)
    (hsep : PairSeparated D x) :
    secular D false x = ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
      secular (pairData D i j) false (pairSlow x i j) := by
  have hterm : ∀ i j : Fin n, i < j → Continuous fun t : Vec n => pairTerm D x i j ![t i, t j] :=
    fun i j hij => (continuous_pairTerm D hx (hsep i j hij)).comp
      (by rw [continuous_pi_iff]; intro c; fin_cases c <;> simp <;> fun_prop)
  rw [secular_eq_avg]
  simp only [perturbation_false_eq]
  rw [avg_finset_sum _ (fun i _ => (continuousOn_finsetSum _ fun j hj =>
    (hterm i j (Finset.mem_filter.1 hj).2).continuousOn))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [avg_finset_sum _ (fun j hj => (hterm i j (Finset.mem_filter.1 hj).2).continuousOn)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij := (Finset.mem_filter.1 hj).2
  rw [avg_pair_marginal hij.ne ((continuous_pairTerm D hx (hsep i j hij)).continuousOn),
    secular_eq_avg]
  simp only [perturbation_pair_eq]

end SecularForm
end KAM.Planetary
end
