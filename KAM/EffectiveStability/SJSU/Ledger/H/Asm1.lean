/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.H.Checks0
public import KAM.EffectiveStability.SJSU.Ledger.H.Asm0

/-!
# Ledger blocks (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem vb_4_6 : sjsuHD.vBlock 4 6 (sjsuUp 4 6) (sjsuVp 4 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_6_0, vu_4_6_1, vu_4_6_2, vu_4_6_3, vu_4_6_4, vu_4_6_5, vu_4_6_6, vu_4_6_7, vu_4_6_8
      , vu_4_6_9, vu_4_6_10, vu_4_6_11, vu_4_6_12, vu_4_6_13, vu_4_6_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_4_6_0, vv_4_6_1, vv_4_6_2, vv_4_6_3]

theorem vb_4_7 : sjsuHD.vBlock 4 7 (sjsuUp 4 7) (sjsuVp 4 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_7_0, vu_4_7_1, vu_4_7_2, vu_4_7_3, vu_4_7_4, vu_4_7_5, vu_4_7_6, vu_4_7_7, vu_4_7_8
      , vu_4_7_9, vu_4_7_10, vu_4_7_11, vu_4_7_12, vu_4_7_13, vu_4_7_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_4_7_0, vv_4_7_1, vv_4_7_2]

theorem vb_4_8 : sjsuHD.vBlock 4 8 (sjsuUp 4 8) (sjsuVp 4 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_8_0, vu_4_8_1, vu_4_8_2, vu_4_8_3, vu_4_8_4, vu_4_8_5, vu_4_8_6, vu_4_8_7, vu_4_8_8
      , vu_4_8_9, vu_4_8_10, vu_4_8_11, vu_4_8_12, vu_4_8_13, vu_4_8_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_4_8_0, vv_4_8_1]

theorem vb_4_9 : sjsuHD.vBlock 4 9 (sjsuUp 4 9) (sjsuVp 4 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_9_0, vu_4_9_1, vu_4_9_2, vu_4_9_3, vu_4_9_4, vu_4_9_5, vu_4_9_6, vu_4_9_7, vu_4_9_8
      , vu_4_9_9, vu_4_9_10, vu_4_9_11, vu_4_9_12, vu_4_9_13, vu_4_9_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_4_9_0]

theorem vb_5_0 : sjsuHD.vBlock 5 0 (sjsuUp 5 0) (sjsuVp 5 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_0_0, vu_5_0_1, vu_5_0_2, vu_5_0_3, vu_5_0_4, vu_5_0_5, vu_5_0_6, vu_5_0_7, vu_5_0_8
      , vu_5_0_9, vu_5_0_10, vu_5_0_11, vu_5_0_12, vu_5_0_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_5_0_0, vv_5_0_1, vv_5_0_2, vv_5_0_3, vv_5_0_4, vv_5_0_5, vv_5_0_6, vv_5_0_7, vv_5_0_8
      , vv_5_0_9]

theorem vb_5_1 : sjsuHD.vBlock 5 1 (sjsuUp 5 1) (sjsuVp 5 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_1_0, vu_5_1_1, vu_5_1_2, vu_5_1_3, vu_5_1_4, vu_5_1_5, vu_5_1_6, vu_5_1_7, vu_5_1_8
      , vu_5_1_9, vu_5_1_10, vu_5_1_11, vu_5_1_12, vu_5_1_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_5_1_0, vv_5_1_1, vv_5_1_2, vv_5_1_3, vv_5_1_4, vv_5_1_5, vv_5_1_6, vv_5_1_7, vv_5_1_8
      ]

theorem vb_5_2 : sjsuHD.vBlock 5 2 (sjsuUp 5 2) (sjsuVp 5 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_2_0, vu_5_2_1, vu_5_2_2, vu_5_2_3, vu_5_2_4, vu_5_2_5, vu_5_2_6, vu_5_2_7, vu_5_2_8
      , vu_5_2_9, vu_5_2_10, vu_5_2_11, vu_5_2_12, vu_5_2_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_5_2_0, vv_5_2_1, vv_5_2_2, vv_5_2_3, vv_5_2_4, vv_5_2_5, vv_5_2_6, vv_5_2_7]

theorem vb_5_3 : sjsuHD.vBlock 5 3 (sjsuUp 5 3) (sjsuVp 5 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_3_0, vu_5_3_1, vu_5_3_2, vu_5_3_3, vu_5_3_4, vu_5_3_5, vu_5_3_6, vu_5_3_7, vu_5_3_8
      , vu_5_3_9, vu_5_3_10, vu_5_3_11, vu_5_3_12, vu_5_3_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_5_3_0, vv_5_3_1, vv_5_3_2, vv_5_3_3, vv_5_3_4, vv_5_3_5, vv_5_3_6]

theorem vb_5_4 : sjsuHD.vBlock 5 4 (sjsuUp 5 4) (sjsuVp 5 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_4_0, vu_5_4_1, vu_5_4_2, vu_5_4_3, vu_5_4_4, vu_5_4_5, vu_5_4_6, vu_5_4_7, vu_5_4_8
      , vu_5_4_9, vu_5_4_10, vu_5_4_11, vu_5_4_12, vu_5_4_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_5_4_0, vv_5_4_1, vv_5_4_2, vv_5_4_3, vv_5_4_4, vv_5_4_5]

theorem vb_5_5 : sjsuHD.vBlock 5 5 (sjsuUp 5 5) (sjsuVp 5 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_5_0, vu_5_5_1, vu_5_5_2, vu_5_5_3, vu_5_5_4, vu_5_5_5, vu_5_5_6, vu_5_5_7, vu_5_5_8
      , vu_5_5_9, vu_5_5_10, vu_5_5_11, vu_5_5_12, vu_5_5_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_5_5_0, vv_5_5_1, vv_5_5_2, vv_5_5_3, vv_5_5_4]

theorem vb_5_6 : sjsuHD.vBlock 5 6 (sjsuUp 5 6) (sjsuVp 5 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_6_0, vu_5_6_1, vu_5_6_2, vu_5_6_3, vu_5_6_4, vu_5_6_5, vu_5_6_6, vu_5_6_7, vu_5_6_8
      , vu_5_6_9, vu_5_6_10, vu_5_6_11, vu_5_6_12, vu_5_6_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_5_6_0, vv_5_6_1, vv_5_6_2, vv_5_6_3]

theorem vb_5_7 : sjsuHD.vBlock 5 7 (sjsuUp 5 7) (sjsuVp 5 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_7_0, vu_5_7_1, vu_5_7_2, vu_5_7_3, vu_5_7_4, vu_5_7_5, vu_5_7_6, vu_5_7_7, vu_5_7_8
      , vu_5_7_9, vu_5_7_10, vu_5_7_11, vu_5_7_12, vu_5_7_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_5_7_0, vv_5_7_1, vv_5_7_2]

theorem vb_5_8 : sjsuHD.vBlock 5 8 (sjsuUp 5 8) (sjsuVp 5 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_8_0, vu_5_8_1, vu_5_8_2, vu_5_8_3, vu_5_8_4, vu_5_8_5, vu_5_8_6, vu_5_8_7, vu_5_8_8
      , vu_5_8_9, vu_5_8_10, vu_5_8_11, vu_5_8_12, vu_5_8_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_5_8_0, vv_5_8_1]

theorem vb_5_9 : sjsuHD.vBlock 5 9 (sjsuUp 5 9) (sjsuVp 5 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 5 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    exacts [vu_5_9_0, vu_5_9_1, vu_5_9_2, vu_5_9_3, vu_5_9_4, vu_5_9_5, vu_5_9_6, vu_5_9_7, vu_5_9_8
      , vu_5_9_9, vu_5_9_10, vu_5_9_11, vu_5_9_12, vu_5_9_13]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_5_9_0]

theorem vb_6_0 : sjsuHD.vBlock 6 0 (sjsuUp 6 0) (sjsuVp 6 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_0_0, vu_6_0_1, vu_6_0_2, vu_6_0_3, vu_6_0_4, vu_6_0_5, vu_6_0_6, vu_6_0_7, vu_6_0_8
      , vu_6_0_9, vu_6_0_10, vu_6_0_11, vu_6_0_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_6_0_0, vv_6_0_1, vv_6_0_2, vv_6_0_3, vv_6_0_4, vv_6_0_5, vv_6_0_6, vv_6_0_7, vv_6_0_8
      , vv_6_0_9]

theorem vb_6_1 : sjsuHD.vBlock 6 1 (sjsuUp 6 1) (sjsuVp 6 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_1_0, vu_6_1_1, vu_6_1_2, vu_6_1_3, vu_6_1_4, vu_6_1_5, vu_6_1_6, vu_6_1_7, vu_6_1_8
      , vu_6_1_9, vu_6_1_10, vu_6_1_11, vu_6_1_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_6_1_0, vv_6_1_1, vv_6_1_2, vv_6_1_3, vv_6_1_4, vv_6_1_5, vv_6_1_6, vv_6_1_7, vv_6_1_8
      ]

theorem vb_6_2 : sjsuHD.vBlock 6 2 (sjsuUp 6 2) (sjsuVp 6 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_2_0, vu_6_2_1, vu_6_2_2, vu_6_2_3, vu_6_2_4, vu_6_2_5, vu_6_2_6, vu_6_2_7, vu_6_2_8
      , vu_6_2_9, vu_6_2_10, vu_6_2_11, vu_6_2_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_6_2_0, vv_6_2_1, vv_6_2_2, vv_6_2_3, vv_6_2_4, vv_6_2_5, vv_6_2_6, vv_6_2_7]

theorem vb_6_3 : sjsuHD.vBlock 6 3 (sjsuUp 6 3) (sjsuVp 6 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_3_0, vu_6_3_1, vu_6_3_2, vu_6_3_3, vu_6_3_4, vu_6_3_5, vu_6_3_6, vu_6_3_7, vu_6_3_8
      , vu_6_3_9, vu_6_3_10, vu_6_3_11, vu_6_3_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_6_3_0, vv_6_3_1, vv_6_3_2, vv_6_3_3, vv_6_3_4, vv_6_3_5, vv_6_3_6]

theorem vb_6_4 : sjsuHD.vBlock 6 4 (sjsuUp 6 4) (sjsuVp 6 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_4_0, vu_6_4_1, vu_6_4_2, vu_6_4_3, vu_6_4_4, vu_6_4_5, vu_6_4_6, vu_6_4_7, vu_6_4_8
      , vu_6_4_9, vu_6_4_10, vu_6_4_11, vu_6_4_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_6_4_0, vv_6_4_1, vv_6_4_2, vv_6_4_3, vv_6_4_4, vv_6_4_5]

theorem vb_6_5 : sjsuHD.vBlock 6 5 (sjsuUp 6 5) (sjsuVp 6 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_5_0, vu_6_5_1, vu_6_5_2, vu_6_5_3, vu_6_5_4, vu_6_5_5, vu_6_5_6, vu_6_5_7, vu_6_5_8
      , vu_6_5_9, vu_6_5_10, vu_6_5_11, vu_6_5_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_6_5_0, vv_6_5_1, vv_6_5_2, vv_6_5_3, vv_6_5_4]

theorem vb_6_6 : sjsuHD.vBlock 6 6 (sjsuUp 6 6) (sjsuVp 6 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_6_0, vu_6_6_1, vu_6_6_2, vu_6_6_3, vu_6_6_4, vu_6_6_5, vu_6_6_6, vu_6_6_7, vu_6_6_8
      , vu_6_6_9, vu_6_6_10, vu_6_6_11, vu_6_6_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_6_6_0, vv_6_6_1, vv_6_6_2, vv_6_6_3]

theorem vb_6_7 : sjsuHD.vBlock 6 7 (sjsuUp 6 7) (sjsuVp 6 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_7_0, vu_6_7_1, vu_6_7_2, vu_6_7_3, vu_6_7_4, vu_6_7_5, vu_6_7_6, vu_6_7_7, vu_6_7_8
      , vu_6_7_9, vu_6_7_10, vu_6_7_11, vu_6_7_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_6_7_0, vv_6_7_1, vv_6_7_2]

theorem vb_6_8 : sjsuHD.vBlock 6 8 (sjsuUp 6 8) (sjsuVp 6 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_8_0, vu_6_8_1, vu_6_8_2, vu_6_8_3, vu_6_8_4, vu_6_8_5, vu_6_8_6, vu_6_8_7, vu_6_8_8
      , vu_6_8_9, vu_6_8_10, vu_6_8_11, vu_6_8_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_6_8_0, vv_6_8_1]

theorem vb_6_9 : sjsuHD.vBlock 6 9 (sjsuUp 6 9) (sjsuVp 6 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 6 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_6_9_0, vu_6_9_1, vu_6_9_2, vu_6_9_3, vu_6_9_4, vu_6_9_5, vu_6_9_6, vu_6_9_7, vu_6_9_8
      , vu_6_9_9, vu_6_9_10, vu_6_9_11, vu_6_9_12]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_6_9_0]

theorem vb_7_0 : sjsuHD.vBlock 7 0 (sjsuUp 7 0) (sjsuVp 7 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_0_0, vu_7_0_1, vu_7_0_2, vu_7_0_3, vu_7_0_4, vu_7_0_5, vu_7_0_6, vu_7_0_7, vu_7_0_8
      , vu_7_0_9, vu_7_0_10, vu_7_0_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_7_0_0, vv_7_0_1, vv_7_0_2, vv_7_0_3, vv_7_0_4, vv_7_0_5, vv_7_0_6, vv_7_0_7, vv_7_0_8
      , vv_7_0_9]

theorem vb_7_1 : sjsuHD.vBlock 7 1 (sjsuUp 7 1) (sjsuVp 7 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_1_0, vu_7_1_1, vu_7_1_2, vu_7_1_3, vu_7_1_4, vu_7_1_5, vu_7_1_6, vu_7_1_7, vu_7_1_8
      , vu_7_1_9, vu_7_1_10, vu_7_1_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_7_1_0, vv_7_1_1, vv_7_1_2, vv_7_1_3, vv_7_1_4, vv_7_1_5, vv_7_1_6, vv_7_1_7, vv_7_1_8
      ]

theorem vb_7_2 : sjsuHD.vBlock 7 2 (sjsuUp 7 2) (sjsuVp 7 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_2_0, vu_7_2_1, vu_7_2_2, vu_7_2_3, vu_7_2_4, vu_7_2_5, vu_7_2_6, vu_7_2_7, vu_7_2_8
      , vu_7_2_9, vu_7_2_10, vu_7_2_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_7_2_0, vv_7_2_1, vv_7_2_2, vv_7_2_3, vv_7_2_4, vv_7_2_5, vv_7_2_6, vv_7_2_7]

theorem vb_7_3 : sjsuHD.vBlock 7 3 (sjsuUp 7 3) (sjsuVp 7 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_3_0, vu_7_3_1, vu_7_3_2, vu_7_3_3, vu_7_3_4, vu_7_3_5, vu_7_3_6, vu_7_3_7, vu_7_3_8
      , vu_7_3_9, vu_7_3_10, vu_7_3_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_7_3_0, vv_7_3_1, vv_7_3_2, vv_7_3_3, vv_7_3_4, vv_7_3_5, vv_7_3_6]

theorem vb_7_4 : sjsuHD.vBlock 7 4 (sjsuUp 7 4) (sjsuVp 7 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_4_0, vu_7_4_1, vu_7_4_2, vu_7_4_3, vu_7_4_4, vu_7_4_5, vu_7_4_6, vu_7_4_7, vu_7_4_8
      , vu_7_4_9, vu_7_4_10, vu_7_4_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_7_4_0, vv_7_4_1, vv_7_4_2, vv_7_4_3, vv_7_4_4, vv_7_4_5]

theorem vb_7_5 : sjsuHD.vBlock 7 5 (sjsuUp 7 5) (sjsuVp 7 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_5_0, vu_7_5_1, vu_7_5_2, vu_7_5_3, vu_7_5_4, vu_7_5_5, vu_7_5_6, vu_7_5_7, vu_7_5_8
      , vu_7_5_9, vu_7_5_10, vu_7_5_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_7_5_0, vv_7_5_1, vv_7_5_2, vv_7_5_3, vv_7_5_4]

theorem vb_7_6 : sjsuHD.vBlock 7 6 (sjsuUp 7 6) (sjsuVp 7 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_6_0, vu_7_6_1, vu_7_6_2, vu_7_6_3, vu_7_6_4, vu_7_6_5, vu_7_6_6, vu_7_6_7, vu_7_6_8
      , vu_7_6_9, vu_7_6_10, vu_7_6_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_7_6_0, vv_7_6_1, vv_7_6_2, vv_7_6_3]

theorem vb_7_7 : sjsuHD.vBlock 7 7 (sjsuUp 7 7) (sjsuVp 7 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_7_0, vu_7_7_1, vu_7_7_2, vu_7_7_3, vu_7_7_4, vu_7_7_5, vu_7_7_6, vu_7_7_7, vu_7_7_8
      , vu_7_7_9, vu_7_7_10, vu_7_7_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_7_7_0, vv_7_7_1, vv_7_7_2]

theorem vb_7_8 : sjsuHD.vBlock 7 8 (sjsuUp 7 8) (sjsuVp 7 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_8_0, vu_7_8_1, vu_7_8_2, vu_7_8_3, vu_7_8_4, vu_7_8_5, vu_7_8_6, vu_7_8_7, vu_7_8_8
      , vu_7_8_9, vu_7_8_10, vu_7_8_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_7_8_0, vv_7_8_1]

theorem vb_7_9 : sjsuHD.vBlock 7 9 (sjsuUp 7 9) (sjsuVp 7 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 7 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_7_9_0, vu_7_9_1, vu_7_9_2, vu_7_9_3, vu_7_9_4, vu_7_9_5, vu_7_9_6, vu_7_9_7, vu_7_9_8
      , vu_7_9_9, vu_7_9_10, vu_7_9_11]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_7_9_0]

theorem vb_8_0 : sjsuHD.vBlock 8 0 (sjsuUp 8 0) (sjsuVp 8 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_0_0, vu_8_0_1, vu_8_0_2, vu_8_0_3, vu_8_0_4, vu_8_0_5, vu_8_0_6, vu_8_0_7, vu_8_0_8
      , vu_8_0_9, vu_8_0_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_8_0_0, vv_8_0_1, vv_8_0_2, vv_8_0_3, vv_8_0_4, vv_8_0_5, vv_8_0_6, vv_8_0_7, vv_8_0_8
      , vv_8_0_9]

theorem vb_8_1 : sjsuHD.vBlock 8 1 (sjsuUp 8 1) (sjsuVp 8 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_1_0, vu_8_1_1, vu_8_1_2, vu_8_1_3, vu_8_1_4, vu_8_1_5, vu_8_1_6, vu_8_1_7, vu_8_1_8
      , vu_8_1_9, vu_8_1_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_8_1_0, vv_8_1_1, vv_8_1_2, vv_8_1_3, vv_8_1_4, vv_8_1_5, vv_8_1_6, vv_8_1_7, vv_8_1_8
      ]

theorem vb_8_2 : sjsuHD.vBlock 8 2 (sjsuUp 8 2) (sjsuVp 8 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_2_0, vu_8_2_1, vu_8_2_2, vu_8_2_3, vu_8_2_4, vu_8_2_5, vu_8_2_6, vu_8_2_7, vu_8_2_8
      , vu_8_2_9, vu_8_2_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_8_2_0, vv_8_2_1, vv_8_2_2, vv_8_2_3, vv_8_2_4, vv_8_2_5, vv_8_2_6, vv_8_2_7]

theorem vb_8_3 : sjsuHD.vBlock 8 3 (sjsuUp 8 3) (sjsuVp 8 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_3_0, vu_8_3_1, vu_8_3_2, vu_8_3_3, vu_8_3_4, vu_8_3_5, vu_8_3_6, vu_8_3_7, vu_8_3_8
      , vu_8_3_9, vu_8_3_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_8_3_0, vv_8_3_1, vv_8_3_2, vv_8_3_3, vv_8_3_4, vv_8_3_5, vv_8_3_6]

theorem vb_8_4 : sjsuHD.vBlock 8 4 (sjsuUp 8 4) (sjsuVp 8 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_4_0, vu_8_4_1, vu_8_4_2, vu_8_4_3, vu_8_4_4, vu_8_4_5, vu_8_4_6, vu_8_4_7, vu_8_4_8
      , vu_8_4_9, vu_8_4_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_8_4_0, vv_8_4_1, vv_8_4_2, vv_8_4_3, vv_8_4_4, vv_8_4_5]

theorem vb_8_5 : sjsuHD.vBlock 8 5 (sjsuUp 8 5) (sjsuVp 8 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_5_0, vu_8_5_1, vu_8_5_2, vu_8_5_3, vu_8_5_4, vu_8_5_5, vu_8_5_6, vu_8_5_7, vu_8_5_8
      , vu_8_5_9, vu_8_5_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_8_5_0, vv_8_5_1, vv_8_5_2, vv_8_5_3, vv_8_5_4]

theorem vb_8_6 : sjsuHD.vBlock 8 6 (sjsuUp 8 6) (sjsuVp 8 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_6_0, vu_8_6_1, vu_8_6_2, vu_8_6_3, vu_8_6_4, vu_8_6_5, vu_8_6_6, vu_8_6_7, vu_8_6_8
      , vu_8_6_9, vu_8_6_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_8_6_0, vv_8_6_1, vv_8_6_2, vv_8_6_3]

theorem vb_8_7 : sjsuHD.vBlock 8 7 (sjsuUp 8 7) (sjsuVp 8 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_7_0, vu_8_7_1, vu_8_7_2, vu_8_7_3, vu_8_7_4, vu_8_7_5, vu_8_7_6, vu_8_7_7, vu_8_7_8
      , vu_8_7_9, vu_8_7_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_8_7_0, vv_8_7_1, vv_8_7_2]

theorem vb_8_8 : sjsuHD.vBlock 8 8 (sjsuUp 8 8) (sjsuVp 8 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_8_0, vu_8_8_1, vu_8_8_2, vu_8_8_3, vu_8_8_4, vu_8_8_5, vu_8_8_6, vu_8_8_7, vu_8_8_8
      , vu_8_8_9, vu_8_8_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_8_8_0, vv_8_8_1]

theorem vb_8_9 : sjsuHD.vBlock 8 9 (sjsuUp 8 9) (sjsuVp 8 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 8 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_8_9_0, vu_8_9_1, vu_8_9_2, vu_8_9_3, vu_8_9_4, vu_8_9_5, vu_8_9_6, vu_8_9_7, vu_8_9_8
      , vu_8_9_9, vu_8_9_10]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_8_9_0]

theorem vb_9_0 : sjsuHD.vBlock 9 0 (sjsuUp 9 0) (sjsuVp 9 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_0_0, vu_9_0_1, vu_9_0_2, vu_9_0_3, vu_9_0_4, vu_9_0_5, vu_9_0_6, vu_9_0_7, vu_9_0_8
      , vu_9_0_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_9_0_0, vv_9_0_1, vv_9_0_2, vv_9_0_3, vv_9_0_4, vv_9_0_5, vv_9_0_6, vv_9_0_7, vv_9_0_8
      , vv_9_0_9]

theorem vb_9_1 : sjsuHD.vBlock 9 1 (sjsuUp 9 1) (sjsuVp 9 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_1_0, vu_9_1_1, vu_9_1_2, vu_9_1_3, vu_9_1_4, vu_9_1_5, vu_9_1_6, vu_9_1_7, vu_9_1_8
      , vu_9_1_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_9_1_0, vv_9_1_1, vv_9_1_2, vv_9_1_3, vv_9_1_4, vv_9_1_5, vv_9_1_6, vv_9_1_7, vv_9_1_8
      ]

theorem vb_9_2 : sjsuHD.vBlock 9 2 (sjsuUp 9 2) (sjsuVp 9 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_2_0, vu_9_2_1, vu_9_2_2, vu_9_2_3, vu_9_2_4, vu_9_2_5, vu_9_2_6, vu_9_2_7, vu_9_2_8
      , vu_9_2_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_9_2_0, vv_9_2_1, vv_9_2_2, vv_9_2_3, vv_9_2_4, vv_9_2_5, vv_9_2_6, vv_9_2_7]

theorem vb_9_3 : sjsuHD.vBlock 9 3 (sjsuUp 9 3) (sjsuVp 9 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_3_0, vu_9_3_1, vu_9_3_2, vu_9_3_3, vu_9_3_4, vu_9_3_5, vu_9_3_6, vu_9_3_7, vu_9_3_8
      , vu_9_3_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_9_3_0, vv_9_3_1, vv_9_3_2, vv_9_3_3, vv_9_3_4, vv_9_3_5, vv_9_3_6]

theorem vb_9_4 : sjsuHD.vBlock 9 4 (sjsuUp 9 4) (sjsuVp 9 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_4_0, vu_9_4_1, vu_9_4_2, vu_9_4_3, vu_9_4_4, vu_9_4_5, vu_9_4_6, vu_9_4_7, vu_9_4_8
      , vu_9_4_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_9_4_0, vv_9_4_1, vv_9_4_2, vv_9_4_3, vv_9_4_4, vv_9_4_5]

theorem vb_9_5 : sjsuHD.vBlock 9 5 (sjsuUp 9 5) (sjsuVp 9 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_5_0, vu_9_5_1, vu_9_5_2, vu_9_5_3, vu_9_5_4, vu_9_5_5, vu_9_5_6, vu_9_5_7, vu_9_5_8
      , vu_9_5_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_9_5_0, vv_9_5_1, vv_9_5_2, vv_9_5_3, vv_9_5_4]

theorem vb_9_6 : sjsuHD.vBlock 9 6 (sjsuUp 9 6) (sjsuVp 9 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_6_0, vu_9_6_1, vu_9_6_2, vu_9_6_3, vu_9_6_4, vu_9_6_5, vu_9_6_6, vu_9_6_7, vu_9_6_8
      , vu_9_6_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_9_6_0, vv_9_6_1, vv_9_6_2, vv_9_6_3]

theorem vb_9_7 : sjsuHD.vBlock 9 7 (sjsuUp 9 7) (sjsuVp 9 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_7_0, vu_9_7_1, vu_9_7_2, vu_9_7_3, vu_9_7_4, vu_9_7_5, vu_9_7_6, vu_9_7_7, vu_9_7_8
      , vu_9_7_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_9_7_0, vv_9_7_1, vv_9_7_2]

theorem vb_9_8 : sjsuHD.vBlock 9 8 (sjsuUp 9 8) (sjsuVp 9 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_8_0, vu_9_8_1, vu_9_8_2, vu_9_8_3, vu_9_8_4, vu_9_8_5, vu_9_8_6, vu_9_8_7, vu_9_8_8
      , vu_9_8_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_9_8_0, vv_9_8_1]

theorem vb_9_9 : sjsuHD.vBlock 9 9 (sjsuUp 9 9) (sjsuVp 9 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_9_9_0, vu_9_9_1, vu_9_9_2, vu_9_9_3, vu_9_9_4, vu_9_9_5, vu_9_9_6, vu_9_9_7, vu_9_9_8
      , vu_9_9_9]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_9_9_0]

theorem vb_10_0 : sjsuHD.vBlock 10 0 (sjsuUp 10 0) (sjsuVp 10 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_0_0, vu_10_0_1, vu_10_0_2, vu_10_0_3, vu_10_0_4, vu_10_0_5, vu_10_0_6, vu_10_0_7,
      vu_10_0_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_10_0_0, vv_10_0_1, vv_10_0_2, vv_10_0_3, vv_10_0_4, vv_10_0_5, vv_10_0_6, vv_10_0_7,
      vv_10_0_8, vv_10_0_9]

theorem vb_10_1 : sjsuHD.vBlock 10 1 (sjsuUp 10 1) (sjsuVp 10 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_1_0, vu_10_1_1, vu_10_1_2, vu_10_1_3, vu_10_1_4, vu_10_1_5, vu_10_1_6, vu_10_1_7,
      vu_10_1_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_10_1_0, vv_10_1_1, vv_10_1_2, vv_10_1_3, vv_10_1_4, vv_10_1_5, vv_10_1_6, vv_10_1_7,
      vv_10_1_8]

theorem vb_10_2 : sjsuHD.vBlock 10 2 (sjsuUp 10 2) (sjsuVp 10 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_2_0, vu_10_2_1, vu_10_2_2, vu_10_2_3, vu_10_2_4, vu_10_2_5, vu_10_2_6, vu_10_2_7,
      vu_10_2_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_10_2_0, vv_10_2_1, vv_10_2_2, vv_10_2_3, vv_10_2_4, vv_10_2_5, vv_10_2_6, vv_10_2_7]

theorem vb_10_3 : sjsuHD.vBlock 10 3 (sjsuUp 10 3) (sjsuVp 10 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_3_0, vu_10_3_1, vu_10_3_2, vu_10_3_3, vu_10_3_4, vu_10_3_5, vu_10_3_6, vu_10_3_7,
      vu_10_3_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_10_3_0, vv_10_3_1, vv_10_3_2, vv_10_3_3, vv_10_3_4, vv_10_3_5, vv_10_3_6]

theorem vb_10_4 : sjsuHD.vBlock 10 4 (sjsuUp 10 4) (sjsuVp 10 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_4_0, vu_10_4_1, vu_10_4_2, vu_10_4_3, vu_10_4_4, vu_10_4_5, vu_10_4_6, vu_10_4_7,
      vu_10_4_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_10_4_0, vv_10_4_1, vv_10_4_2, vv_10_4_3, vv_10_4_4, vv_10_4_5]

theorem vb_10_5 : sjsuHD.vBlock 10 5 (sjsuUp 10 5) (sjsuVp 10 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_5_0, vu_10_5_1, vu_10_5_2, vu_10_5_3, vu_10_5_4, vu_10_5_5, vu_10_5_6, vu_10_5_7,
      vu_10_5_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_10_5_0, vv_10_5_1, vv_10_5_2, vv_10_5_3, vv_10_5_4]

theorem vb_10_6 : sjsuHD.vBlock 10 6 (sjsuUp 10 6) (sjsuVp 10 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_6_0, vu_10_6_1, vu_10_6_2, vu_10_6_3, vu_10_6_4, vu_10_6_5, vu_10_6_6, vu_10_6_7,
      vu_10_6_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_10_6_0, vv_10_6_1, vv_10_6_2, vv_10_6_3]

theorem vb_10_7 : sjsuHD.vBlock 10 7 (sjsuUp 10 7) (sjsuVp 10 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_7_0, vu_10_7_1, vu_10_7_2, vu_10_7_3, vu_10_7_4, vu_10_7_5, vu_10_7_6, vu_10_7_7,
      vu_10_7_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_10_7_0, vv_10_7_1, vv_10_7_2]

theorem vb_10_8 : sjsuHD.vBlock 10 8 (sjsuUp 10 8) (sjsuVp 10 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_8_0, vu_10_8_1, vu_10_8_2, vu_10_8_3, vu_10_8_4, vu_10_8_5, vu_10_8_6, vu_10_8_7,
      vu_10_8_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_10_8_0, vv_10_8_1]

theorem vb_10_9 : sjsuHD.vBlock 10 9 (sjsuUp 10 9) (sjsuVp 10 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_10_9_0, vu_10_9_1, vu_10_9_2, vu_10_9_3, vu_10_9_4, vu_10_9_5, vu_10_9_6, vu_10_9_7,
      vu_10_9_8]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_10_9_0]

theorem vb_11_0 : sjsuHD.vBlock 11 0 (sjsuUp 11 0) (sjsuVp 11 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_0_0, vu_11_0_1, vu_11_0_2, vu_11_0_3, vu_11_0_4, vu_11_0_5, vu_11_0_6, vu_11_0_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_11_0_0, vv_11_0_1, vv_11_0_2, vv_11_0_3, vv_11_0_4, vv_11_0_5, vv_11_0_6, vv_11_0_7,
      vv_11_0_8, vv_11_0_9]

theorem vb_11_1 : sjsuHD.vBlock 11 1 (sjsuUp 11 1) (sjsuVp 11 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_1_0, vu_11_1_1, vu_11_1_2, vu_11_1_3, vu_11_1_4, vu_11_1_5, vu_11_1_6, vu_11_1_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_11_1_0, vv_11_1_1, vv_11_1_2, vv_11_1_3, vv_11_1_4, vv_11_1_5, vv_11_1_6, vv_11_1_7,
      vv_11_1_8]

theorem vb_11_2 : sjsuHD.vBlock 11 2 (sjsuUp 11 2) (sjsuVp 11 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_2_0, vu_11_2_1, vu_11_2_2, vu_11_2_3, vu_11_2_4, vu_11_2_5, vu_11_2_6, vu_11_2_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_11_2_0, vv_11_2_1, vv_11_2_2, vv_11_2_3, vv_11_2_4, vv_11_2_5, vv_11_2_6, vv_11_2_7]

theorem vb_11_3 : sjsuHD.vBlock 11 3 (sjsuUp 11 3) (sjsuVp 11 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 11 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_11_3_0, vu_11_3_1, vu_11_3_2, vu_11_3_3, vu_11_3_4, vu_11_3_5, vu_11_3_6, vu_11_3_7]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_11_3_0, vv_11_3_1, vv_11_3_2, vv_11_3_3, vv_11_3_4, vv_11_3_5, vv_11_3_6]


end KAM.EffectiveStability.SJSU

end
