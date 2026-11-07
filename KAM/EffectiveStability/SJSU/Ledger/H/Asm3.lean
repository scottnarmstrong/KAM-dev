/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.H.Checks0
public import KAM.EffectiveStability.SJSU.Ledger.H.Asm2

/-!
# Ledger blocks (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem vb_18_9 : sjsuHD.vBlock 18 9 (sjsuUp 18 9) (sjsuVp 18 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_9_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_18_9_0]


end KAM.EffectiveStability.SJSU

end
