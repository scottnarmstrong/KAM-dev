/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.ParameterIntegral
public import KAM.Planetary.Poincare.Holomorphic
public import KAM.Planetary.Poincare.Symplectic

/-!
# Secular form: the polydisc inside the chart neighbourhood, and the circular separation

Blueprint P, Part 8, Proposition `bpP:p8:perturbation-analytic`, steps `pa-circ` and `pa-unif`
(geometry only): the polydisc of radius `r < rho` is a ball around the circular point, lies in the
product of the chart neighbourhoods `poincareNbhd`, the complexified planet coordinates are
jointly continuous and `2π`-periodic in the angles, and the squared separation at the circular
point is `≥ (a_j - a_i)²`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

/-- The circular point `(ξ, Λ, η) = (0, Λ*, 0)` of the slow carrier. -/
def center (D : Data n) (a : Vec n) : CSlow n := inclusion (0, action D a, 0)

theorem polydisc_eq_ball (D : Data n) (a : Vec n) {r : ℝ} (hr : 0 < r) :
    polydisc D a r = Metric.ball (center D a) r := by
  ext x
  simp only [polydisc, center, inclusion, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm,
    Prod.norm_def, Prod.fst_sub, Prod.snd_sub, max_lt_iff, pi_norm_lt_iff hr]
  simp only [Pi.sub_apply, Pi.zero_apply, Complex.ofReal_zero, sub_zero, forall_and]

theorem action_pos (D : Data n) {a : Vec n} (ha : a ∈ axes n) (i : Fin n) : 0 < action D a i := by
  have := D.hG; have := D.hm0; have := D.hm i; have := ha.1 i
  unfold action; positivity

theorem rho_pos (D : Data n) {a : Vec n} (ha : a ∈ axes n) : 0 < rho D a := by
  have : Nonempty (Fin n) := ⟨⟨0, D.hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => min (action D a i / 2)
    (√(action D a i) / 16))
  have h := action_pos D ha i
  unfold rho; rw [← hi]
  exact lt_min (by positivity) (by positivity)

theorem rho_le_half (D : Data n) (a : Vec n) (i : Fin n) : rho D a ≤ action D a i / 2 :=
  (ciInf_le (Set.finite_range _).bddBelow i).trans (min_le_left _ _)

theorem rho_le_sqrt (D : Data n) (a : Vec n) (i : Fin n) : rho D a ≤ √(action D a i) / 16 :=
  (ciInf_le (Set.finite_range _).bddBelow i).trans (min_le_right _ _)

def planetC (D : Data n) (t : Vec n) (x : CSlow n) (i : Fin n) :=
  poincareC (D.m i) (D.G * D.m0) (![t i, x.1 i], ![x.2.1 i,x.2.2 i])
def separationC (D : Data n) (t : Vec n) (x : CSlow n) (i j : Fin n) : ℂ :=
  ∑ c : Fin 2, ((planetC D t x i).1 c - (planetC D t x j).1 c)^2

/-- The `i`-th planet's complex chart coordinates `((λ, ξ), (Λ, η))`. -/
def blockC (t : Vec n) (x : CSlow n) (i : Fin n) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![(t i : ℂ), x.1 i], ![x.2.1 i, x.2.2 i])

theorem planetC_eq (D : Data n) (t : Vec n) (x : CSlow n) (i : Fin n) :
    planetC D t x i = poincareC (D.m i) (D.G * D.m0) (blockC t x i) := rfl

theorem blockC_mem_nbhd (D : Data n) {a : Vec n} (_ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) {t : Vec n} {x : CSlow n} (hx : x ∈ polydisc D a r) (i : Fin n) :
    blockC t x i ∈ poincareNbhd (action D a i) := by
  have h1 := rho_le_half D a i
  have h2 := rho_le_sqrt D a i
  have h := hx i
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [blockC]
  · simp only [blockC]; show ‖x.2.1 i - _‖ < _; linarith [h.2.1]
  · simp only [blockC]; show ‖x.1 i‖ < _; linarith [h.1]
  · simp only [blockC]; show ‖x.2.2 i‖ < _; linarith [h.2.2]

theorem continuous_blockC (i : Fin n) :
    Continuous (fun z : Vec n × CSlow n => blockC z.1 z.2 i) := by
  refine Continuous.prodMk (continuous_pi fun k => ?_) (continuous_pi fun k => ?_) <;>
    fin_cases k <;> simp <;> fun_prop

theorem continuousOn_planetC (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hr : r < rho D a) (i : Fin n) :
    ContinuousOn (fun z : Vec n × CSlow n => planetC D z.1 z.2 i)
      (univ ×ˢ polydisc D a r) := by
  have hΛ := action_pos D ha i
  have h := (poincare_holomorphic (m := D.m i) (κ := D.G * D.m0) (Λo := action D a i)
    (D.hm i) (mul_pos D.hG D.hm0) hΛ).2.2.1
  exact h.continuousOn.comp (continuous_blockC i).continuousOn fun z hz =>
    blockC_mem_nbhd D ha hr hz.2 i

end SecularForm
end KAM.Planetary
end
