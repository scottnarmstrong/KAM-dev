/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Continuation
public import KAM.Nekhoroshev.Averaging.FlowChain
public import KAM.Planetary.WeakMeasure.Basic

/-!
# Global real flows of bounded `C¹` fields (P11A-C7)

`rl-global` and `rl-deriv` suppliers of `bpP:p11a:real-lipschitz`: a bounded `C¹` field on
`Fin n → ℝ` has a complete flow (`p11_bounded_global_flow`, by the maximal solution and the
compact-confinement continuation criterion), and for a bounded `C²` field with bounded derivative
the flow `p11RealFlow` is differentiable in the initial data and its derivative solves the actual
variational equation (`p11_global_variational`, by chaining the local `C¹` dependence of
`KAM.Nekhoroshev.FlowChain`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
open KAM.ODE (IsSolutionIn IsMaximalSolution eIoo)
namespace KAM.Planetary

variable {n : ℕ} {v : P11Vec n → P11Vec n}

private theorem p11_norm_sub_le_of_sol {M : ℝ} (hb : ∀ x, ‖v x‖ ≤ M) {u : ℝ → P11Vec n}
    {a b : ℝ} (hu : ∀ t ∈ uIcc a b, HasDerivAt u (v (u t)) t) :
    ‖u b - u a‖ ≤ M * ‖b - a‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := u) (f' := fun t => v (u t))
    (s := uIcc a b) (fun t ht => (hu t ht).hasDerivWithinAt) (fun _ _ => hb _)
    (convex_uIcc a b) left_mem_uIcc right_mem_uIcc

/-- The forward end of the maximal interval of a bounded `C¹` field is infinite. -/
private theorem p11_maximal_top (hv : ContDiff ℝ 1 v) {M : ℝ} (hb : ∀ x, ‖v x‖ ≤ M)
    {x : P11Vec n} {Tm Tp : EReal} {z : ℝ → P11Vec n}
    (hz : IsMaximalSolution v univ x Tm Tp z) : Tp = ⊤ := by
  by_contra hne
  obtain ⟨T, hT⟩ : ∃ T : ℝ, Tp = (T : EReal) :=
    ⟨Tp.toReal, (EReal.coe_toReal hne (ne_bot_of_gt hz.pos_lt)).symm⟩
  have hT0 : 0 < T := by
    have := hz.pos_lt
    rw [hT] at this
    exact_mod_cast this
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0)
  refine hne ((KAM.ODE.gen_continuation_compact isOpen_univ hv.contDiffOn hz
    (K := closedBall x (M * T)) (isCompact_closedBall _ _) (subset_univ _)).1
    ⟨0, le_rfl, hz.pos_lt, fun t ht0 htT => ?_⟩)
  have htT' : t < T := by
    rw [hT] at htT
    exact_mod_cast htT
  have hsub : ∀ s ∈ uIcc 0 t, HasDerivAt z (v (z s)) s := fun s hs => by
    rw [uIcc_of_le ht0] at hs
    exact (hz.isSolution s ⟨lt_of_lt_of_le hz.neg_lt (by exact_mod_cast hs.1), by
      rw [hT]; exact_mod_cast lt_of_le_of_lt hs.2 htT'⟩).2
  have h := p11_norm_sub_le_of_sol hb hsub
  rw [hz.init, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht0] at h
  rw [mem_closedBall, dist_eq_norm]
  exact h.trans (mul_le_mul_of_nonneg_left htT'.le hM)

/-- The maximal solution of a bounded `C¹` field is global. -/
private theorem p11_maximal_global (hv : ContDiff ℝ 1 v) {M : ℝ} (hb : ∀ x, ‖v x‖ ≤ M)
    {x : P11Vec n} {Tm Tp : EReal} {z : ℝ → P11Vec n}
    (hz : IsMaximalSolution v univ x Tm Tp z) : Tm = ⊥ ∧ Tp = ⊤ := by
  refine ⟨?_, p11_maximal_top hv hb hz⟩
  have := p11_maximal_top (v := fun x => -v x) hv.neg (M := M) (fun y => by simpa using hb y) hz.neg
  simpa using this

private theorem p11_eq_global_flow (hv : ContDiff ℝ 1 v) {x : P11Vec n} {u w : ℝ → P11Vec n}
    (hu0 : u 0 = x) (hw0 : w 0 = x) (hu : ∀ t, HasDerivAt u (v (u t)) t)
    (hw : ∀ t, HasDerivAt w (v (w t)) t) (t : ℝ) : u t = w t :=
  KAM.ODE.gen_uniqueness isOpen_univ hv.contDiffOn ordConnected_univ (mem_univ 0)
    (fun t _ => ⟨mem_univ _, hu t⟩) (fun t _ => ⟨mem_univ _, hw t⟩) (by rw [hu0, hw0])
    (mem_univ t)

/-- rl-global supplier: complete nonlinear flow of a bounded C1 field. -/
theorem p11_bounded_global_flow {n : ℕ} {v : P11Vec n → P11Vec n}
    (hv : ContDiff ℝ 1 v) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖v x‖ ≤ M)
    (x : P11Vec n) :
    ∃ u : ℝ → P11Vec n, u 0=x ∧ ∀ t, HasDerivAt u (v (u t)) t := by
  have _ := hM
  obtain ⟨Tm, Tp, z, hz⟩ := (KAM.ODE.gen_maximal isOpen_univ hv.contDiffOn (mem_univ x)).1
  obtain ⟨hTm, hTp⟩ := p11_maximal_global hv hb hz
  refine ⟨z, hz.init, fun t => (hz.isSolution t ?_).2⟩
  rw [hTm, hTp, KAM.ODE.eIoo_bot_top]
  exact mem_univ t

open Classical in
def p11RealFlow {n : ℕ} (v : P11Vec n → P11Vec n) (t : ℝ) (x : P11Vec n) : P11Vec n :=
  if h : ∃ u : ℝ → P11Vec n, u 0=x ∧ ∀ t, HasDerivAt u (v (u t)) t
    then h.choose t else x

/-- The flow `p11RealFlow` is the global solution through each initial point. -/
theorem p11RealFlow_spec (hv : ContDiff ℝ 1 v) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖v x‖ ≤ M)
    (x : P11Vec n) :
    p11RealFlow v 0 x = x ∧
      ∀ t, HasDerivAt (fun s => p11RealFlow v s x) (v (p11RealFlow v t x)) t := by
  have h := p11_bounded_global_flow hv hM hb x
  have e : (fun s => p11RealFlow v s x) = h.choose := funext fun s => by
    simp [p11RealFlow, h]
  have e' : ∀ t, p11RealFlow v t x = h.choose t := congrFun e
  simp only [e']
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

/-- A global solution is the flow. -/
theorem p11RealFlow_eq (hv : ContDiff ℝ 1 v) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖v x‖ ≤ M)
    {x : P11Vec n} {u : ℝ → P11Vec n} (hu0 : u 0 = x) (hu : ∀ t, HasDerivAt u (v (u t)) t)
    (t : ℝ) : u t = p11RealFlow v t x :=
  p11_eq_global_flow hv hu0 (p11RealFlow_spec hv hM hb x).1 hu
    (p11RealFlow_spec hv hM hb x).2 t

/-- rl-deriv supplier: differentiability in initial data and its actual variational equation. -/
theorem p11_global_variational {n : ℕ} {v : P11Vec n → P11Vec n}
    (hv : ContDiff ℝ 2 v) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ x, ‖v x‖ ≤ M) (hD : ∀ x, ‖fderiv ℝ v x‖ ≤ L) :
    (∀ t, Differentiable ℝ (p11RealFlow v t)) ∧
    (∀ x t, HasDerivAt (fun s => fderiv ℝ (p11RealFlow v s) x)
      ((fderiv ℝ v (p11RealFlow v t x)).comp (fderiv ℝ (p11RealFlow v t) x)) t) ∧
    ∀ x, fderiv ℝ (p11RealFlow v 0) x=ContinuousLinearMap.id ℝ _ := by
  have _ := hL
  have _ := hD
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hF : ContDiffOn ℝ 1 v univ := hv1.contDiffOn
  have hmax : ∀ x ∈ (univ : Set (P11Vec n)), IsMaximalSolution v univ x
      ((fun _ => ⊥ : P11Vec n → EReal) x) ((fun _ => ⊤ : P11Vec n → EReal) x)
      ((fun x s => p11RealFlow v s x : P11Vec n → ℝ → P11Vec n) x) := fun x _ => by
    obtain ⟨h0, hd⟩ := p11RealFlow_spec hv1 hM hb x
    refine ⟨EReal.bot_lt_coe 0, EReal.coe_lt_top 0, h0, fun t _ => ⟨mem_univ _, hd t⟩, ?_⟩
    intro J y hJ hJ0 hy0 hy
    refine ⟨by simp [KAM.ODE.eIoo_bot_top], fun t ht => ?_⟩
    exact KAM.ODE.gen_uniqueness isOpen_univ hF hJ hJ0 hy
      (fun t _ => ⟨mem_univ _, hd t⟩) (by rw [hy0, h0]) ht
  have hreg : ∀ (x : P11Vec n) (t : ℝ), ∃ (J : Set ℝ) (U : Set (P11Vec n)), IsOpen J ∧ IsOpen U ∧
      t ∈ J ∧ x ∈ U ∧ KAM.Nekhoroshev.FlowChain.RegOn v univ (fun _ => ⊥) (fun _ => ⊤)
        (fun x s => p11RealFlow v s x) J U := fun x t =>
    KAM.Nekhoroshev.FlowChain.reg_all isOpen_univ hF hmax (mem_univ x)
      (by simp [KAM.ODE.eIoo_bot_top])
  refine ⟨fun t x => ?_, fun x t => ?_, fun x => ?_⟩
  · obtain ⟨J, U, -, -, htJ, hxU, hR⟩ := hreg x t
    exact (hR.2.2.2.2 x hxU t htJ).1.differentiableAt
  · obtain ⟨J, U, -, -, htJ, hxU, hR⟩ := hreg x t
    exact (hR.2.2.2.2 x hxU t htJ).2
  · have : p11RealFlow v 0 = id := funext fun y => (p11RealFlow_spec hv1 hM hb y).1
    rw [this, fderiv_id]

end KAM.Planetary

end
