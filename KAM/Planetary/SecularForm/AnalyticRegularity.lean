/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.AnalyticGeometry

/-!
# Secular form: holomorphy and continuity of the complexified perturbation

Blueprint P, Part 8, Proposition `bpP:p8:perturbation-analytic` (steps `pa-circ`, `pa-unif`,
`pa-hol`, `pa-avg`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

def perturbationC (D : Data n) (moving : Bool) (t : Vec n) (x : CSlow n) : ℂ :=
  -(D.G : ℂ) * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    (D.m i : ℂ) * D.m j * separationC D t x i j ^ (-1/2 : ℂ) +
  if moving then (∑ c : Fin 2, (∑ i, (planetC D t x i).2 c)^2) / (2 * D.m0) else 0
def secularC (D : Data n) (moving : Bool) (x : CSlow n) : ℂ :=
  (2 * π) ^ (-(n : ℤ)) • ∫ t in cell n, perturbationC D moving t x

section Regularity
variable (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ} (hr : r < rho D a)

theorem differentiable_blockC (t : Vec n) (i : Fin n) :
    Differentiable ℂ (fun x : CSlow n => blockC t x i) := by
  refine Differentiable.prodMk (differentiable_pi.2 fun k => ?_)
    (differentiable_pi.2 fun k => ?_) <;> fin_cases k <;> simp <;> fun_prop

include ha hr in
theorem differentiableOn_planetC (_hr0 : 0 < r) (t : Vec n) (i : Fin n) :
    DifferentiableOn ℂ (fun x => planetC D t x i) (polydisc D a r) := by
  have hΛ := action_pos D ha i
  have h := (poincare_holomorphic (m := D.m i) (κ := D.G * D.m0) (Λo := action D a i)
    (D.hm i) (mul_pos D.hG D.hm0) hΛ).2.2.1
  exact h.comp (differentiable_blockC t i).differentiableOn fun x hx =>
    blockC_mem_nbhd D ha hr hx i

include ha hr in
theorem differentiableOn_planetC_fst (hr0 : 0 < r) (t : Vec n) (i : Fin n) (c : Fin 2) :
    DifferentiableOn ℂ (fun x => (planetC D t x i).1 c) (polydisc D a r) :=
  (show Differentiable ℂ (fun v : (Fin 2 → ℂ) × (Fin 2 → ℂ) => v.1 c)
    by fun_prop).comp_differentiableOn
    (differentiableOn_planetC D ha hr hr0 t i)

include ha hr in
theorem differentiableOn_planetC_snd (hr0 : 0 < r) (t : Vec n) (i : Fin n) (c : Fin 2) :
    DifferentiableOn ℂ (fun x => (planetC D t x i).2 c) (polydisc D a r) :=
  (show Differentiable ℂ (fun v : (Fin 2 → ℂ) × (Fin 2 → ℂ) => v.2 c)
    by fun_prop).comp_differentiableOn
    (differentiableOn_planetC D ha hr hr0 t i)

include ha hr in
theorem continuousOn_planetC_fst (i : Fin n) (c : Fin 2) :
    ContinuousOn (fun z : Vec n × CSlow n => (planetC D z.1 z.2 i).1 c)
      (univ ×ˢ polydisc D a r) :=
  (continuous_apply c).comp_continuousOn
    (continuous_fst.comp_continuousOn (continuousOn_planetC D ha hr i))

include ha hr in
theorem continuousOn_planetC_snd (i : Fin n) (c : Fin 2) :
    ContinuousOn (fun z : Vec n × CSlow n => (planetC D z.1 z.2 i).2 c)
      (univ ×ˢ polydisc D a r) :=
  (continuous_apply c).comp_continuousOn
    (continuous_snd.comp_continuousOn (continuousOn_planetC D ha hr i))

include ha hr in
theorem differentiableOn_separationC (hr0 : 0 < r) (t : Vec n) (i j : Fin n) :
    DifferentiableOn ℂ (fun x => separationC D t x i j) (polydisc D a r) := by
  unfold separationC
  refine DifferentiableOn.fun_sum fun c _ => ?_
  exact ((differentiableOn_planetC_fst D ha hr hr0 t i c).sub
    (differentiableOn_planetC_fst D ha hr hr0 t j c)).pow 2

include ha hr in
theorem continuousOn_separationC (i j : Fin n) :
    ContinuousOn (fun z : Vec n × CSlow n => separationC D z.1 z.2 i j)
      (univ ×ˢ polydisc D a r) := by
  unfold separationC
  refine continuousOn_finsetSum _ fun c _ => ?_
  exact ((continuousOn_planetC_fst D ha hr i c).sub (continuousOn_planetC_fst D ha hr j c)).pow 2

variable (hsep : ∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
  ((a j - a i) ^ 2 / 2) ≤ (separationC D t x i j).re)

include ha hsep in
theorem separationC_slit {t : Vec n} {x : CSlow n} (hx : x ∈ polydisc D a r) {i j : Fin n}
    (hij : i < j) : separationC D t x i j ∈ Complex.slitPlane := by
  have h := hsep t x hx i j hij
  have : a i < a j := ha.2 hij
  have : 0 < (a j - a i) ^ 2 / 2 := by
    have : 0 < a j - a i := by linarith
    positivity
  exact Complex.mem_slitPlane_iff.2 (Or.inl (by linarith))

include ha hr hsep in
theorem differentiableOn_perturbationC (hr0 : 0 < r) (b : Bool) (t : Vec n) :
    DifferentiableOn ℂ (perturbationC D b t) (polydisc D a r) := by
  unfold perturbationC
  refine DifferentiableOn.add (DifferentiableOn.const_mul ?_ _) ?_
  · refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.1 hj).2
    refine DifferentiableOn.const_mul ?_ _
    exact (differentiableOn_separationC D ha hr hr0 t i j).cpow_const
      fun x hx => separationC_slit D ha hsep hx hij
  · cases b
    · simp
    · simp only [ite_true]
      have hs : DifferentiableOn ℂ (fun x => ∑ c : Fin 2, (∑ i, (planetC D t x i).2 c) ^ 2)
          (polydisc D a r) :=
        DifferentiableOn.fun_sum fun c _ => (DifferentiableOn.fun_sum fun i _ =>
          differentiableOn_planetC_snd D ha hr hr0 t i c).pow 2
      exact (hs.mul_const ((2 * (D.m0 : ℂ))⁻¹)).congr fun x _ => div_eq_mul_inv _ _

include ha hr hsep in
theorem continuousOn_perturbationC (b : Bool) :
    ContinuousOn (fun z : Vec n × CSlow n => perturbationC D b z.1 z.2)
      (univ ×ˢ polydisc D a r) := by
  unfold perturbationC
  refine ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_) ?_
  · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.1 hj).2
    refine ContinuousOn.mul continuousOn_const ?_
    exact (continuousOn_separationC D ha hr i j).cpow_const
      fun z hz => separationC_slit D ha hsep hz.2 hij
  · cases b
    · simpa using continuousOn_const (c := (0 : ℂ))
    · simp only [ite_true]
      refine ContinuousOn.div_const (continuousOn_finsetSum _ fun c _ => ?_) _
      exact (continuousOn_finsetSum _ fun i _ => continuousOn_planetC_snd D ha hr i c).pow 2

end Regularity

end SecularForm
end KAM.Planetary
end
