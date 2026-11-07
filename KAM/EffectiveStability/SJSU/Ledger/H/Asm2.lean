/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.H.Checks0
public import KAM.EffectiveStability.SJSU.Ledger.H.Asm1

/-!
# Ledger blocks (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem vb_11_4 : sjsuHD.vBlock 11 4 (sjsuUp 11 4) (sjsuVp 11 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_4_0, vu_11_4_1, vu_11_4_2, vu_11_4_3, vu_11_4_4, vu_11_4_5, vu_11_4_6, vu_11_4_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_11_4_0, vv_11_4_1, vv_11_4_2, vv_11_4_3, vv_11_4_4, vv_11_4_5]

theorem vb_11_5 : sjsuHD.vBlock 11 5 (sjsuUp 11 5) (sjsuVp 11 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_5_0, vu_11_5_1, vu_11_5_2, vu_11_5_3, vu_11_5_4, vu_11_5_5, vu_11_5_6, vu_11_5_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_11_5_0, vv_11_5_1, vv_11_5_2, vv_11_5_3, vv_11_5_4]

theorem vb_11_6 : sjsuHD.vBlock 11 6 (sjsuUp 11 6) (sjsuVp 11 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_6_0, vu_11_6_1, vu_11_6_2, vu_11_6_3, vu_11_6_4, vu_11_6_5, vu_11_6_6, vu_11_6_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_11_6_0, vv_11_6_1, vv_11_6_2, vv_11_6_3]

theorem vb_11_7 : sjsuHD.vBlock 11 7 (sjsuUp 11 7) (sjsuVp 11 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_7_0, vu_11_7_1, vu_11_7_2, vu_11_7_3, vu_11_7_4, vu_11_7_5, vu_11_7_6, vu_11_7_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_11_7_0, vv_11_7_1, vv_11_7_2]

theorem vb_11_8 : sjsuHD.vBlock 11 8 (sjsuUp 11 8) (sjsuVp 11 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_8_0, vu_11_8_1, vu_11_8_2, vu_11_8_3, vu_11_8_4, vu_11_8_5, vu_11_8_6, vu_11_8_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_11_8_0, vv_11_8_1]

theorem vb_11_9 : sjsuHD.vBlock 11 9 (sjsuUp 11 9) (sjsuVp 11 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_9_0, vu_11_9_1, vu_11_9_2, vu_11_9_3, vu_11_9_4, vu_11_9_5, vu_11_9_6, vu_11_9_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_11_9_0]

theorem vb_12_0 : sjsuHD.vBlock 12 0 (sjsuUp 12 0) (sjsuVp 12 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_0_0, vu_12_0_1, vu_12_0_2, vu_12_0_3, vu_12_0_4, vu_12_0_5, vu_12_0_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_12_0_0, vv_12_0_1, vv_12_0_2, vv_12_0_3, vv_12_0_4, vv_12_0_5, vv_12_0_6, vv_12_0_7,
      vv_12_0_8, vv_12_0_9]

theorem vb_12_1 : sjsuHD.vBlock 12 1 (sjsuUp 12 1) (sjsuVp 12 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_1_0, vu_12_1_1, vu_12_1_2, vu_12_1_3, vu_12_1_4, vu_12_1_5, vu_12_1_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_12_1_0, vv_12_1_1, vv_12_1_2, vv_12_1_3, vv_12_1_4, vv_12_1_5, vv_12_1_6, vv_12_1_7,
      vv_12_1_8]

theorem vb_12_2 : sjsuHD.vBlock 12 2 (sjsuUp 12 2) (sjsuVp 12 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_2_0, vu_12_2_1, vu_12_2_2, vu_12_2_3, vu_12_2_4, vu_12_2_5, vu_12_2_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_12_2_0, vv_12_2_1, vv_12_2_2, vv_12_2_3, vv_12_2_4, vv_12_2_5, vv_12_2_6, vv_12_2_7]

theorem vb_12_3 : sjsuHD.vBlock 12 3 (sjsuUp 12 3) (sjsuVp 12 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_3_0, vu_12_3_1, vu_12_3_2, vu_12_3_3, vu_12_3_4, vu_12_3_5, vu_12_3_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_12_3_0, vv_12_3_1, vv_12_3_2, vv_12_3_3, vv_12_3_4, vv_12_3_5, vv_12_3_6]

theorem vb_12_4 : sjsuHD.vBlock 12 4 (sjsuUp 12 4) (sjsuVp 12 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_4_0, vu_12_4_1, vu_12_4_2, vu_12_4_3, vu_12_4_4, vu_12_4_5, vu_12_4_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_12_4_0, vv_12_4_1, vv_12_4_2, vv_12_4_3, vv_12_4_4, vv_12_4_5]

theorem vb_12_5 : sjsuHD.vBlock 12 5 (sjsuUp 12 5) (sjsuVp 12 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_5_0, vu_12_5_1, vu_12_5_2, vu_12_5_3, vu_12_5_4, vu_12_5_5, vu_12_5_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_12_5_0, vv_12_5_1, vv_12_5_2, vv_12_5_3, vv_12_5_4]

theorem vb_12_6 : sjsuHD.vBlock 12 6 (sjsuUp 12 6) (sjsuVp 12 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_6_0, vu_12_6_1, vu_12_6_2, vu_12_6_3, vu_12_6_4, vu_12_6_5, vu_12_6_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_12_6_0, vv_12_6_1, vv_12_6_2, vv_12_6_3]

theorem vb_12_7 : sjsuHD.vBlock 12 7 (sjsuUp 12 7) (sjsuVp 12 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_7_0, vu_12_7_1, vu_12_7_2, vu_12_7_3, vu_12_7_4, vu_12_7_5, vu_12_7_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_12_7_0, vv_12_7_1, vv_12_7_2]

theorem vb_12_8 : sjsuHD.vBlock 12 8 (sjsuUp 12 8) (sjsuVp 12 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_8_0, vu_12_8_1, vu_12_8_2, vu_12_8_3, vu_12_8_4, vu_12_8_5, vu_12_8_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_12_8_0, vv_12_8_1]

theorem vb_12_9 : sjsuHD.vBlock 12 9 (sjsuUp 12 9) (sjsuVp 12 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 12 = [0, 1, 2, 3, 4, 5, 6] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_12_9_0, vu_12_9_1, vu_12_9_2, vu_12_9_3, vu_12_9_4, vu_12_9_5, vu_12_9_6]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_12_9_0]

theorem vb_13_0 : sjsuHD.vBlock 13 0 (sjsuUp 13 0) (sjsuVp 13 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_0_0, vu_13_0_1, vu_13_0_2, vu_13_0_3, vu_13_0_4, vu_13_0_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_13_0_0, vv_13_0_1, vv_13_0_2, vv_13_0_3, vv_13_0_4, vv_13_0_5, vv_13_0_6, vv_13_0_7,
      vv_13_0_8, vv_13_0_9]

theorem vb_13_1 : sjsuHD.vBlock 13 1 (sjsuUp 13 1) (sjsuVp 13 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_1_0, vu_13_1_1, vu_13_1_2, vu_13_1_3, vu_13_1_4, vu_13_1_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_13_1_0, vv_13_1_1, vv_13_1_2, vv_13_1_3, vv_13_1_4, vv_13_1_5, vv_13_1_6, vv_13_1_7,
      vv_13_1_8]

theorem vb_13_2 : sjsuHD.vBlock 13 2 (sjsuUp 13 2) (sjsuVp 13 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_2_0, vu_13_2_1, vu_13_2_2, vu_13_2_3, vu_13_2_4, vu_13_2_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_13_2_0, vv_13_2_1, vv_13_2_2, vv_13_2_3, vv_13_2_4, vv_13_2_5, vv_13_2_6, vv_13_2_7]

theorem vb_13_3 : sjsuHD.vBlock 13 3 (sjsuUp 13 3) (sjsuVp 13 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_3_0, vu_13_3_1, vu_13_3_2, vu_13_3_3, vu_13_3_4, vu_13_3_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_13_3_0, vv_13_3_1, vv_13_3_2, vv_13_3_3, vv_13_3_4, vv_13_3_5, vv_13_3_6]

theorem vb_13_4 : sjsuHD.vBlock 13 4 (sjsuUp 13 4) (sjsuVp 13 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_4_0, vu_13_4_1, vu_13_4_2, vu_13_4_3, vu_13_4_4, vu_13_4_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_13_4_0, vv_13_4_1, vv_13_4_2, vv_13_4_3, vv_13_4_4, vv_13_4_5]

theorem vb_13_5 : sjsuHD.vBlock 13 5 (sjsuUp 13 5) (sjsuVp 13 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_5_0, vu_13_5_1, vu_13_5_2, vu_13_5_3, vu_13_5_4, vu_13_5_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_13_5_0, vv_13_5_1, vv_13_5_2, vv_13_5_3, vv_13_5_4]

theorem vb_13_6 : sjsuHD.vBlock 13 6 (sjsuUp 13 6) (sjsuVp 13 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_6_0, vu_13_6_1, vu_13_6_2, vu_13_6_3, vu_13_6_4, vu_13_6_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_13_6_0, vv_13_6_1, vv_13_6_2, vv_13_6_3]

theorem vb_13_7 : sjsuHD.vBlock 13 7 (sjsuUp 13 7) (sjsuVp 13 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_7_0, vu_13_7_1, vu_13_7_2, vu_13_7_3, vu_13_7_4, vu_13_7_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_13_7_0, vv_13_7_1, vv_13_7_2]

theorem vb_13_8 : sjsuHD.vBlock 13 8 (sjsuUp 13 8) (sjsuVp 13 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_8_0, vu_13_8_1, vu_13_8_2, vu_13_8_3, vu_13_8_4, vu_13_8_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_13_8_0, vv_13_8_1]

theorem vb_13_9 : sjsuHD.vBlock 13 9 (sjsuUp 13 9) (sjsuVp 13 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 13 = [0, 1, 2, 3, 4, 5] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_13_9_0, vu_13_9_1, vu_13_9_2, vu_13_9_3, vu_13_9_4, vu_13_9_5]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_13_9_0]

theorem vb_14_0 : sjsuHD.vBlock 14 0 (sjsuUp 14 0) (sjsuVp 14 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_0_0, vu_14_0_1, vu_14_0_2, vu_14_0_3, vu_14_0_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_14_0_0, vv_14_0_1, vv_14_0_2, vv_14_0_3, vv_14_0_4, vv_14_0_5, vv_14_0_6, vv_14_0_7,
      vv_14_0_8, vv_14_0_9]

theorem vb_14_1 : sjsuHD.vBlock 14 1 (sjsuUp 14 1) (sjsuVp 14 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_1_0, vu_14_1_1, vu_14_1_2, vu_14_1_3, vu_14_1_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_14_1_0, vv_14_1_1, vv_14_1_2, vv_14_1_3, vv_14_1_4, vv_14_1_5, vv_14_1_6, vv_14_1_7,
      vv_14_1_8]

theorem vb_14_2 : sjsuHD.vBlock 14 2 (sjsuUp 14 2) (sjsuVp 14 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_2_0, vu_14_2_1, vu_14_2_2, vu_14_2_3, vu_14_2_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_14_2_0, vv_14_2_1, vv_14_2_2, vv_14_2_3, vv_14_2_4, vv_14_2_5, vv_14_2_6, vv_14_2_7]

theorem vb_14_3 : sjsuHD.vBlock 14 3 (sjsuUp 14 3) (sjsuVp 14 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_3_0, vu_14_3_1, vu_14_3_2, vu_14_3_3, vu_14_3_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_14_3_0, vv_14_3_1, vv_14_3_2, vv_14_3_3, vv_14_3_4, vv_14_3_5, vv_14_3_6]

theorem vb_14_4 : sjsuHD.vBlock 14 4 (sjsuUp 14 4) (sjsuVp 14 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_4_0, vu_14_4_1, vu_14_4_2, vu_14_4_3, vu_14_4_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_14_4_0, vv_14_4_1, vv_14_4_2, vv_14_4_3, vv_14_4_4, vv_14_4_5]

theorem vb_14_5 : sjsuHD.vBlock 14 5 (sjsuUp 14 5) (sjsuVp 14 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_5_0, vu_14_5_1, vu_14_5_2, vu_14_5_3, vu_14_5_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_14_5_0, vv_14_5_1, vv_14_5_2, vv_14_5_3, vv_14_5_4]

theorem vb_14_6 : sjsuHD.vBlock 14 6 (sjsuUp 14 6) (sjsuVp 14 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_6_0, vu_14_6_1, vu_14_6_2, vu_14_6_3, vu_14_6_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_14_6_0, vv_14_6_1, vv_14_6_2, vv_14_6_3]

theorem vb_14_7 : sjsuHD.vBlock 14 7 (sjsuUp 14 7) (sjsuVp 14 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_7_0, vu_14_7_1, vu_14_7_2, vu_14_7_3, vu_14_7_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_14_7_0, vv_14_7_1, vv_14_7_2]

theorem vb_14_8 : sjsuHD.vBlock 14 8 (sjsuUp 14 8) (sjsuVp 14 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_8_0, vu_14_8_1, vu_14_8_2, vu_14_8_3, vu_14_8_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_14_8_0, vv_14_8_1]

theorem vb_14_9 : sjsuHD.vBlock 14 9 (sjsuUp 14 9) (sjsuVp 14 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 14 = [0, 1, 2, 3, 4] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl
    exacts [vu_14_9_0, vu_14_9_1, vu_14_9_2, vu_14_9_3, vu_14_9_4]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_14_9_0]

theorem vb_15_0 : sjsuHD.vBlock 15 0 (sjsuUp 15 0) (sjsuVp 15 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_0_0, vu_15_0_1, vu_15_0_2, vu_15_0_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_15_0_0, vv_15_0_1, vv_15_0_2, vv_15_0_3, vv_15_0_4, vv_15_0_5, vv_15_0_6, vv_15_0_7,
      vv_15_0_8, vv_15_0_9]

theorem vb_15_1 : sjsuHD.vBlock 15 1 (sjsuUp 15 1) (sjsuVp 15 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_1_0, vu_15_1_1, vu_15_1_2, vu_15_1_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_15_1_0, vv_15_1_1, vv_15_1_2, vv_15_1_3, vv_15_1_4, vv_15_1_5, vv_15_1_6, vv_15_1_7,
      vv_15_1_8]

theorem vb_15_2 : sjsuHD.vBlock 15 2 (sjsuUp 15 2) (sjsuVp 15 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_2_0, vu_15_2_1, vu_15_2_2, vu_15_2_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_15_2_0, vv_15_2_1, vv_15_2_2, vv_15_2_3, vv_15_2_4, vv_15_2_5, vv_15_2_6, vv_15_2_7]

theorem vb_15_3 : sjsuHD.vBlock 15 3 (sjsuUp 15 3) (sjsuVp 15 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_3_0, vu_15_3_1, vu_15_3_2, vu_15_3_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_15_3_0, vv_15_3_1, vv_15_3_2, vv_15_3_3, vv_15_3_4, vv_15_3_5, vv_15_3_6]

theorem vb_15_4 : sjsuHD.vBlock 15 4 (sjsuUp 15 4) (sjsuVp 15 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_4_0, vu_15_4_1, vu_15_4_2, vu_15_4_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_15_4_0, vv_15_4_1, vv_15_4_2, vv_15_4_3, vv_15_4_4, vv_15_4_5]

theorem vb_15_5 : sjsuHD.vBlock 15 5 (sjsuUp 15 5) (sjsuVp 15 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_5_0, vu_15_5_1, vu_15_5_2, vu_15_5_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_15_5_0, vv_15_5_1, vv_15_5_2, vv_15_5_3, vv_15_5_4]

theorem vb_15_6 : sjsuHD.vBlock 15 6 (sjsuUp 15 6) (sjsuVp 15 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_6_0, vu_15_6_1, vu_15_6_2, vu_15_6_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_15_6_0, vv_15_6_1, vv_15_6_2, vv_15_6_3]

theorem vb_15_7 : sjsuHD.vBlock 15 7 (sjsuUp 15 7) (sjsuVp 15 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_7_0, vu_15_7_1, vu_15_7_2, vu_15_7_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_15_7_0, vv_15_7_1, vv_15_7_2]

theorem vb_15_8 : sjsuHD.vBlock 15 8 (sjsuUp 15 8) (sjsuVp 15 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_8_0, vu_15_8_1, vu_15_8_2, vu_15_8_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_15_8_0, vv_15_8_1]

theorem vb_15_9 : sjsuHD.vBlock 15 9 (sjsuUp 15 9) (sjsuVp 15 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 15 = [0, 1, 2, 3] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl
    exacts [vu_15_9_0, vu_15_9_1, vu_15_9_2, vu_15_9_3]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_15_9_0]

theorem vb_16_0 : sjsuHD.vBlock 16 0 (sjsuUp 16 0) (sjsuVp 16 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_0_0, vu_16_0_1, vu_16_0_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_16_0_0, vv_16_0_1, vv_16_0_2, vv_16_0_3, vv_16_0_4, vv_16_0_5, vv_16_0_6, vv_16_0_7,
      vv_16_0_8, vv_16_0_9]

theorem vb_16_1 : sjsuHD.vBlock 16 1 (sjsuUp 16 1) (sjsuVp 16 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_1_0, vu_16_1_1, vu_16_1_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_16_1_0, vv_16_1_1, vv_16_1_2, vv_16_1_3, vv_16_1_4, vv_16_1_5, vv_16_1_6, vv_16_1_7,
      vv_16_1_8]

theorem vb_16_2 : sjsuHD.vBlock 16 2 (sjsuUp 16 2) (sjsuVp 16 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_2_0, vu_16_2_1, vu_16_2_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_16_2_0, vv_16_2_1, vv_16_2_2, vv_16_2_3, vv_16_2_4, vv_16_2_5, vv_16_2_6, vv_16_2_7]

theorem vb_16_3 : sjsuHD.vBlock 16 3 (sjsuUp 16 3) (sjsuVp 16 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_3_0, vu_16_3_1, vu_16_3_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_16_3_0, vv_16_3_1, vv_16_3_2, vv_16_3_3, vv_16_3_4, vv_16_3_5, vv_16_3_6]

theorem vb_16_4 : sjsuHD.vBlock 16 4 (sjsuUp 16 4) (sjsuVp 16 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_4_0, vu_16_4_1, vu_16_4_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_16_4_0, vv_16_4_1, vv_16_4_2, vv_16_4_3, vv_16_4_4, vv_16_4_5]

theorem vb_16_5 : sjsuHD.vBlock 16 5 (sjsuUp 16 5) (sjsuVp 16 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_5_0, vu_16_5_1, vu_16_5_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_16_5_0, vv_16_5_1, vv_16_5_2, vv_16_5_3, vv_16_5_4]

theorem vb_16_6 : sjsuHD.vBlock 16 6 (sjsuUp 16 6) (sjsuVp 16 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_6_0, vu_16_6_1, vu_16_6_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_16_6_0, vv_16_6_1, vv_16_6_2, vv_16_6_3]

theorem vb_16_7 : sjsuHD.vBlock 16 7 (sjsuUp 16 7) (sjsuVp 16 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_7_0, vu_16_7_1, vu_16_7_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_16_7_0, vv_16_7_1, vv_16_7_2]

theorem vb_16_8 : sjsuHD.vBlock 16 8 (sjsuUp 16 8) (sjsuVp 16 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_8_0, vu_16_8_1, vu_16_8_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_16_8_0, vv_16_8_1]

theorem vb_16_9 : sjsuHD.vBlock 16 9 (sjsuUp 16 9) (sjsuVp 16 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 16 = [0, 1, 2] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl
    exacts [vu_16_9_0, vu_16_9_1, vu_16_9_2]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_16_9_0]

theorem vb_17_0 : sjsuHD.vBlock 17 0 (sjsuUp 17 0) (sjsuVp 17 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_0_0, vu_17_0_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_17_0_0, vv_17_0_1, vv_17_0_2, vv_17_0_3, vv_17_0_4, vv_17_0_5, vv_17_0_6, vv_17_0_7,
      vv_17_0_8, vv_17_0_9]

theorem vb_17_1 : sjsuHD.vBlock 17 1 (sjsuUp 17 1) (sjsuVp 17 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_1_0, vu_17_1_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_17_1_0, vv_17_1_1, vv_17_1_2, vv_17_1_3, vv_17_1_4, vv_17_1_5, vv_17_1_6, vv_17_1_7,
      vv_17_1_8]

theorem vb_17_2 : sjsuHD.vBlock 17 2 (sjsuUp 17 2) (sjsuVp 17 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_2_0, vu_17_2_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_17_2_0, vv_17_2_1, vv_17_2_2, vv_17_2_3, vv_17_2_4, vv_17_2_5, vv_17_2_6, vv_17_2_7]

theorem vb_17_3 : sjsuHD.vBlock 17 3 (sjsuUp 17 3) (sjsuVp 17 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_3_0, vu_17_3_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_17_3_0, vv_17_3_1, vv_17_3_2, vv_17_3_3, vv_17_3_4, vv_17_3_5, vv_17_3_6]

theorem vb_17_4 : sjsuHD.vBlock 17 4 (sjsuUp 17 4) (sjsuVp 17 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_4_0, vu_17_4_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_17_4_0, vv_17_4_1, vv_17_4_2, vv_17_4_3, vv_17_4_4, vv_17_4_5]

theorem vb_17_5 : sjsuHD.vBlock 17 5 (sjsuUp 17 5) (sjsuVp 17 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_5_0, vu_17_5_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_17_5_0, vv_17_5_1, vv_17_5_2, vv_17_5_3, vv_17_5_4]

theorem vb_17_6 : sjsuHD.vBlock 17 6 (sjsuUp 17 6) (sjsuVp 17 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_6_0, vu_17_6_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_17_6_0, vv_17_6_1, vv_17_6_2, vv_17_6_3]

theorem vb_17_7 : sjsuHD.vBlock 17 7 (sjsuUp 17 7) (sjsuVp 17 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_7_0, vu_17_7_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_17_7_0, vv_17_7_1, vv_17_7_2]

theorem vb_17_8 : sjsuHD.vBlock 17 8 (sjsuUp 17 8) (sjsuVp 17 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_8_0, vu_17_8_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_17_8_0, vv_17_8_1]

theorem vb_17_9 : sjsuHD.vBlock 17 9 (sjsuUp 17 9) (sjsuVp 17 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 17 = [0, 1] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl
    exacts [vu_17_9_0, vu_17_9_1]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_17_9_0]

theorem vb_18_0 : sjsuHD.vBlock 18 0 (sjsuUp 18 0) (sjsuVp 18 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_0_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_18_0_0, vv_18_0_1, vv_18_0_2, vv_18_0_3, vv_18_0_4, vv_18_0_5, vv_18_0_6, vv_18_0_7,
      vv_18_0_8, vv_18_0_9]

theorem vb_18_1 : sjsuHD.vBlock 18 1 (sjsuUp 18 1) (sjsuVp 18 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_1_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_18_1_0, vv_18_1_1, vv_18_1_2, vv_18_1_3, vv_18_1_4, vv_18_1_5, vv_18_1_6, vv_18_1_7,
      vv_18_1_8]

theorem vb_18_2 : sjsuHD.vBlock 18 2 (sjsuUp 18 2) (sjsuVp 18 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_2_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_18_2_0, vv_18_2_1, vv_18_2_2, vv_18_2_3, vv_18_2_4, vv_18_2_5, vv_18_2_6, vv_18_2_7]

theorem vb_18_3 : sjsuHD.vBlock 18 3 (sjsuUp 18 3) (sjsuVp 18 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_3_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_18_3_0, vv_18_3_1, vv_18_3_2, vv_18_3_3, vv_18_3_4, vv_18_3_5, vv_18_3_6]

theorem vb_18_4 : sjsuHD.vBlock 18 4 (sjsuUp 18 4) (sjsuVp 18 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_4_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_18_4_0, vv_18_4_1, vv_18_4_2, vv_18_4_3, vv_18_4_4, vv_18_4_5]

theorem vb_18_5 : sjsuHD.vBlock 18 5 (sjsuUp 18 5) (sjsuVp 18 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_5_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_18_5_0, vv_18_5_1, vv_18_5_2, vv_18_5_3, vv_18_5_4]

theorem vb_18_6 : sjsuHD.vBlock 18 6 (sjsuUp 18 6) (sjsuVp 18 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_6_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_18_6_0, vv_18_6_1, vv_18_6_2, vv_18_6_3]

theorem vb_18_7 : sjsuHD.vBlock 18 7 (sjsuUp 18 7) (sjsuVp 18 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_7_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_18_7_0, vv_18_7_1, vv_18_7_2]

theorem vb_18_8 : sjsuHD.vBlock 18 8 (sjsuUp 18 8) (sjsuVp 18 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 18 = [0] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl
    exacts [vu_18_8_0]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_18_8_0, vv_18_8_1]


end KAM.EffectiveStability.SJSU

end
