/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Fast
public import KAM.Planetary.Preparation.HoloAssembly

/-!
# Signed `avg_fast` and `p11FastData` (P11A-P5W, `bpP:p11:avg-fast`)

Short wrappers of the core `avg_fast_of_spec` at `C = p11SecularData D`, whose
`P11SecularSpec` comes from `holo_chart`. The reality premise `P11SecularHReal` of the core is
discharged by `p11SecularHReal_of_spec` from the h-realness clause of the specification.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- The h-realness clause of the secular specification gives `P11SecularHReal`. -/
theorem p11SecularHReal_of_spec {n : ℕ} {D : P11Physical n} {C : P11SecularData n}
    (hC : P11SecularSpec D C) : P11SecularHReal C := by
  intro J hJ
  refine (hC.2.1 J ?_).2
  rw [mem_ball_iff_norm, ← map_sub, KAM.norm_realInclusion] at hJ
  exact hJ

theorem avg_fast {n : ℕ} (D : P11Physical n) :
    let C := p11SecularData D
    ∃ eps1 : ℝ, 0 < eps1 ∧ eps1 < 1 ∧ ∀ eps, 0 < eps → eps ≤ eps1 →
      2^12*(1+n)*p11K1 C eps*eps*C.MF*C.sigma ≤ p11Alpha1 C eps*p11d1 C eps ∧
      ∃ A, P11FastSpec C eps A :=
  avg_fast_of_spec (holo_chart D).choose_spec.1
    (p11SecularHReal_of_spec (holo_chart D).choose_spec.1)

open Classical in
def p11FastData {n : ℕ} (D : P11Physical n) (eps : ℝ) : P11FastData n :=
  if h : ∃ A, P11FastSpec (p11SecularData D) eps A then h.choose else default

end KAM.Planetary

end
