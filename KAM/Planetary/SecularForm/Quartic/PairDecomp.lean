/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.PairAverage
public import KAM.Planetary.SecularForm.Analytic
public import KAM.Planetary.SecularForm.AnalyticReal
public import KAM.Planetary.SecularForm.Momentum
public import KAM.Planetary.SecularForm.ParameterIntegral
public import KAM.Planetary.SecularForm.ModelTransfer

/-!
# Secular form: pair decomposition of the fixed-model secular function

Blueprint P, Part 8, `stepP:p8:q4-str` (the pair decomposition, as in `stepP:p8:qf-pair`):
on the real polydisc of `perturbation_analytic` the fixed-model secular function is the sum over
pairs `i < j` of the literal pair averages `pairSlowSecular`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

private theorem continuous_planeLength_quartic : Continuous planeLength :=
  Real.continuous_sqrt.comp (by unfold planeSq; fun_prop)

theorem continuous_ppos {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    Continuous (ppos D x i) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_ppos hx i s).continuousAt

/-- On the real polydisc the two planets of a pair never collide: the squared distance is
bounded below by a positive constant. -/
theorem planeSq_ppos_sub_pos (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hrho : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    {x : Slow n} (hx : x ∈ realDisc D a r) {i j : Fin n} (hij : i < j) (s t' : ℝ) :
    0 < planeSq (ppos D x i s - ppos D x j t') := by
  set T : Vec n := Function.update (Function.update (0 : Vec n) i s) j t' with hT
  have hTj : T j = t' := by simp [hT]
  have hTi : T i = s := by simp [hT, hij.ne]
  have h := hsep T (inclusion x) hx i j hij
  rw [separationC_inclusion D ha hrho hx T i j, Complex.ofReal_re] at h
  have e : bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 T x.2.2 x.1)).1 i -
      bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 T x.2.2 x.1)).1 j =
      ppos D x i s - ppos D x j t' := by
    have h1 := position_eq_block D x T i
    have h2 := position_eq_block D x T j
    rw [hTi] at h1; rw [hTj] at h2
    exact congrArg₂ (· - ·) h1 h2
  rw [e] at h
  have : 0 < (a j - a i) ^ 2 / 2 := by
    have := ha.2 hij
    have : 0 < a j - a i := sub_pos.2 this
    positivity
  linarith

theorem perturbation_false_pairs (D : Data n) (x : Slow n) (t : Vec n) :
    perturbation D false (assemble x.2.1 t x.2.2 x.1) =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        -D.G * D.m i * D.m j / planeLength (ppos D x i (t i) - ppos D x j (t j)) := by
  unfold perturbation fFix pairPotential
  simp only [Bool.false_eq_true, ite_false, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 := position_eq_block D x t i
  have h2 := position_eq_block D x t j
  change -(D.G * D.m i * D.m j / planeLength (position D x t i - position D x t j)) = _
  rw [h1, h2]
  change -(D.G * D.m i * D.m j / planeLength (ppos D x i (t i) - ppos D x j (t j))) = _
  ring

theorem q4_avg_finset_sum {ι : Type*} (s : Finset ι) {f : ι → Vec n → ℝ}
    (hf : ∀ c ∈ s, IntegrableOn (f c) (cell n)) :
    avg (fun t => ∑ c ∈ s, f c t) = ∑ c ∈ s, avg (f c) := by
  unfold avg
  rw [integral_finsetSum _ hf, Finset.smul_sum]

theorem secular_eq_avg (D : Data n) (b : Bool) (x : Slow n) :
    secular D b x = avg (fun t : Vec n => perturbation D b (assemble x.2.1 t x.2.2 x.1)) := rfl

/-- The pair kernel: the inverse separation of planets `i`, `j` at their own angles. -/
def pairKernel (D : Data n) (x : Slow n) (i j : Fin n) (s t : ℝ) : ℝ :=
  -D.G * D.m i * D.m j / planeLength (ppos D x i s - ppos D x j t)

theorem continuous_pairKernel_comp (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hrho : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    {x : Slow n} (hx : x ∈ realDisc D a r) {i j : Fin n} (hij : i < j)
    {α : Type*} [TopologicalSpace α] {f g : α → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : α => pairKernel D x i j (f p) (g p)) := by
  have hxs : x ∈ slowDom D := realDisc_subset_slowDom D ha hrho hx
  refine continuous_const.div (continuous_planeLength_quartic.comp
    (((continuous_ppos hxs i).comp hf).sub ((continuous_ppos hxs j).comp hg))) fun p => ?_
  have := planeSq_ppos_sub_pos D ha hrho hsep hx hij (f p) (g p)
  intro h0
  have h0' := (planeLength_eq_zero_iff.1 h0)
  rw [h0'] at this
  simp [planeSq] at this

theorem integrableOn_pairKernel (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hrho : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    {x : Slow n} (hx : x ∈ realDisc D a r) {i j : Fin n} (hij : i < j) :
    IntegrableOn (fun t : Vec n => pairKernel D x i j (t i) (t j)) (cell n) := by
  have hc := continuous_pairKernel_comp D ha hrho hsep hx hij
    (f := fun t : Vec n => t i) (g := fun t : Vec n => t j) (continuous_apply i)
    (continuous_apply j)
  exact hc.continuousOn.integrableOn_compact (isCompact_cell (n := n))

theorem pairKernel_avg (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hrho : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    {x : Slow n} (hx : x ∈ realDisc D a r) {i j : Fin n} (hij : i < j) :
    avg (fun t : Vec n => pairKernel D x i j (t i) (t j)) =
      pairSlowSecular D i j (x.2.1 i) (x.2.1 j) (![x.1 i, x.2.2 i], ![x.1 j, x.2.2 j]) := by
  have hc := continuous_pairKernel_comp D ha hrho hsep hx hij
    (f := fun p : ℝ × ℝ => p.1) (g := fun p : ℝ × ℝ => p.2) continuous_fst continuous_snd
  rw [avg_pair hij.ne (g := pairKernel D x i j) hc.continuousOn]
  simp only [pairSlowSecular, pairKernel, ppos, blk, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Pair decomposition: `stepP:p8:qf-pair`. -/
theorem secular_false_eq_pairs (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hrho : r < rho D a)
    (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)
    {x : Slow n} (hx : x ∈ realDisc D a r) :
    secular D false x = ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
      pairSlowSecular D i j (x.2.1 i) (x.2.1 j) (![x.1 i, x.2.2 i], ![x.1 j, x.2.2 j]) := by
  rw [secular_eq_avg]
  have e : (fun t : Vec n => perturbation D false (assemble x.2.1 t x.2.2 x.1)) =
      fun t => ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), pairKernel D x i j (t i) (t j) :=
    funext fun t => perturbation_false_pairs D x t
  rw [e]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin n)), IntegrableOn (fun t : Vec n =>
      ∑ j ∈ Finset.univ.filter (i < ·), pairKernel D x i j (t i) (t j)) (cell n) := fun i _ =>
    integrable_finsetSum _ fun j hj =>
      integrableOn_pairKernel D ha hrho hsep hx (Finset.mem_filter.1 hj).2
  rw [q4_avg_finset_sum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [q4_avg_finset_sum _ fun j hj =>
    integrableOn_pairKernel D ha hrho hsep hx (Finset.mem_filter.1 hj).2]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact pairKernel_avg D ha hrho hsep hx (Finset.mem_filter.1 hj).2

end SecularForm
end KAM.Planetary
end
