/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Lift.Iterate

/-!
# Planar quartic torsion: angle translations, inverse and chart on the whole tube (package T11)

Blueprint P, Part 11b (`bpP:p11b:lm-prop`).  `p11c_liftFlow` commutes with every translation of the
angles (`p11cL_liftFlow_translate`, immediate from the definition), which transports the chart
property from the zero-angle slab `p11cL_nbhd` to the tube `p11c_tube O' r`
(`p11cL_chart_tube`).  The lift of `-chi` is a left inverse of the lift of `chi` on the tube
(`p11cL_left_inverse`): the action is constant, the slow part is inverted by the last clause of
the signed theorem `flow`, and the angle integral is odd under time reversal.  This gives
injectivity (`p11cL_injOn`).
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

variable {O O' : Set (Fin 2 → ℝ)}

theorem p11cL_act_shift (w : Phase (2 + 2)) (c : Fin 2 → ℝ) :
    p11cL_act (w + (Fin.append c (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) = p11cL_act w := by
  funext i; simp [p11cL_act]

theorem p11cL_ang_shift (w : Phase (2 + 2)) (c : Fin 2 → ℝ) :
    p11cL_ang (w + (Fin.append c (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) = p11cL_ang w + c := by
  funext i; simp [p11cL_ang, Fin.append_left]

theorem p11cL_slow_shift (w : Phase (2 + 2)) (c : Fin 2 → ℝ) :
    p11cL_slow (w + (Fin.append c (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) = p11cL_slow w := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [p11cL_slow, Fin.append_right]

/-- Translation covariance in the angles (from the definition). -/
theorem p11cL_liftFlow_translate (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (w : Phase (2 + 2))
    (c : Fin 2 → ℝ) :
    p11c_liftFlow chi (w + (Fin.append c (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) =
      p11c_liftFlow chi w + (Fin.append c (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ)) := by
  rw [p11cL_liftFlow_eq, p11cL_liftFlow_eq, p11cL_act_shift, p11cL_ang_shift, p11cL_slow_shift]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> refine Fin.addCases ?_ ?_ j <;>
    intro i <;> simp [assemble, Fin.append_left, Fin.append_right, add_assoc] <;> ring

/-- The chart property on the zero-angle slab extends to the whole tube. -/
theorem p11cL_chart_tube (hO : IsOpen O) (hO' : IsOpen O') (hK : IsCompact (closure O'))
    (hKO : closure O' ⊆ O) (chi : QuarticFamily O) {r : ℝ} (hr : 0 < r)
    (hfs : p11cL_FlowSpec chi.eval (closure O') (2 * r)) :
    IsChart 1 (p11c_liftFlow chi.eval) (p11c_tube O' r) := by
  have hc := p11cL_chart_local hO hO' hK hKO chi hr hfs
  have hshift : ∀ w ∈ p11c_tube O' r,
      p11c_liftFlow chi.eval =
        (fun w' => p11c_liftFlow chi.eval (w' - (Fin.append (p11cL_ang w) (0 : Fin 2 → ℝ),
          (0 : Fin (2 + 2) → ℝ))) + (Fin.append (p11cL_ang w) (0 : Fin 2 → ℝ),
          (0 : Fin (2 + 2) → ℝ))) ∧
      w - (Fin.append (p11cL_ang w) (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ)) ∈
        p11cL_nbhd O' r := by
    intro w hw
    refine ⟨funext fun w' => ?_, ?_⟩
    · rw [← p11cL_liftFlow_translate, sub_add_cancel]
    · have h1 : w - (Fin.append (p11cL_ang w) (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ)) =
          w + (Fin.append (-p11cL_ang w) (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ)) := by
        refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
          refine Fin.addCases ?_ ?_ j <;> intro i <;> simp [sub_eq_add_neg]
      rw [h1]
      refine ⟨?_, ?_, ?_⟩
      · rw [p11cL_act_shift]; exact hw.1
      · rw [p11cL_slow_shift]; exact hw.2
      · rw [p11cL_ang_shift]; simp
  refine ⟨fun w hw => ?_, fun w hw u v => ?_⟩
  · obtain ⟨hf, hw0⟩ := hshift w hw
    have h := hc.1 _ hw0
    have h2 : AnalyticAt ℝ (fun w' : Phase (2 + 2) => w' - (Fin.append (p11cL_ang w)
        (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) w :=
      analyticAt_id.sub analyticAt_const
    rw [hf]
    exact (h.comp_of_eq h2 rfl).add analyticAt_const
  · obtain ⟨hf, hw0⟩ := hshift w hw
    have hd : DifferentiableAt ℝ (p11c_liftFlow chi.eval) (w - (Fin.append (p11cL_ang w)
        (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) := (hc.1 _ hw0).differentiableAt
    have h1 : HasFDerivAt (fun w' : Phase (2 + 2) => w' - (Fin.append (p11cL_ang w)
        (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) (ContinuousLinearMap.id ℝ _) w :=
      (hasFDerivAt_id w).sub_const _
    have h2 := (hd.hasFDerivAt.comp w h1).add_const (Fin.append (p11cL_ang w) (0 : Fin 2 → ℝ),
      (0 : Fin (2 + 2) → ℝ))
    have e : fderiv ℝ (fun w' : Phase (2 + 2) => p11c_liftFlow chi.eval (w' - (Fin.append
        (p11cL_ang w) (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) + (Fin.append (p11cL_ang w)
        (0 : Fin 2 → ℝ), (0 : Fin (2 + 2) → ℝ))) w =
        (fderiv ℝ (p11c_liftFlow chi.eval) (w - (Fin.append (p11cL_ang w) (0 : Fin 2 → ℝ),
          (0 : Fin (2 + 2) → ℝ)))).comp (ContinuousLinearMap.id ℝ _) := h2.fderiv
    rw [hf, e]
    have := hc.2 _ hw0 u v
    simpa using this

end KAM.Planetary

end
