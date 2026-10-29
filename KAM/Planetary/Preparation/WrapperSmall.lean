/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedBasic
public import KAM.Planetary.Preparation.WrapperDatum

/-!
# Smallness of `ε` for the wrapper (P11A-P10, `stepP:p11:wr-nu`, first part)

`p11_wr_small`: the signed fast and slow specifications and the elementary smallness conditions
(`hεM`, `hpe`, `hsm`) hold for all small `ε`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace KAM.Planetary

section Small

variable {n : ℕ}

theorem p11_wr_small (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ eps3 : ℝ, 0 < eps3 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps3 →
      P11FastSpec (p11SecularData D) eps (p11FastData D eps) ∧
      P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps) ∧
      eps*(p11SecularData D).MF ≤ Real.exp (-1) ∧
      Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps ∧
      256*eps < (p11SecularData D).rz^2 := by
  have hC : P11SecularSpec D (p11SecularData D) := (holo_chart D).choose_spec.1
  obtain ⟨-, -, -, -, -, -, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨eps1, h1pos, -, hfast⟩ := avg_fast D
  obtain ⟨h2pos, -, -, hslow⟩ := (avg_slow D hnu).choose_spec.choose_spec
  have hc2 : p11SlowConstant D nu = (avg_slow D hnu).choose_spec.choose := by
    unfold p11SlowConstant; rw [dif_pos hnu]
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (slow_pe_eventually hC hnu)
  have hM0 : 0 < (p11SecularData D).MF := by linarith
  refine ⟨min (u/2) (min eps1 (min (avg_slow D hnu).choose
    (min (Real.exp (-1)/(p11SecularData D).MF) ((p11SecularData D).rz^2/257)))),
    lt_min (by simpa using hu) (lt_min h1pos (lt_min h2pos (lt_min (by positivity)
      (by positivity)))), fun eps heps hle => ?_⟩
  have hle1 := hle.trans (min_le_left _ _)
  have hle2 := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle3 := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hle4 := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hle5 := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hεM : eps*(p11SecularData D).MF ≤ Real.exp (-1) := (le_div_iff₀ hM0).1 hle4
  have hsm' : 256*eps < (p11SecularData D).rz^2 := by
    have : 0 < (p11SecularData D).rz^2 := by positivity
    linarith
  have hpe := hsub ⟨heps, by linarith⟩ heps hεM
  refine ⟨?_, ?_, hεM, hpe, hsm'⟩
  · have h := (hfast eps heps hle2).2
    unfold p11FastData
    rw [dif_pos h]
    exact h.choose_spec
  · have h : ∃ A, P11SlowSpec D nu eps (p11SlowConstant D nu) A := by
      rw [hc2]; exact hslow eps heps hle3
    unfold p11SlowData
    rw [dif_pos h]
    exact h.choose_spec

end Small

end KAM.Planetary

end
