/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.Br.Ps0

/-!
# Kept coefficients (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem brq_0_0_0_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 0)) (brGc 0 (0, 0, 0)) (sjsuG 0 (0, 0, 0)) (0, 0, 0) := by
  have hn : brN 0 (0, 0, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_0_0

theorem brq_0_0_0_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 1)) (brGc 0 (0, 0, 1)) (sjsuG 0 (0, 0, 1)) (0, 0, 1) := by
  have hn : brN 0 (0, 0, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_1_0

theorem brq_0_0_0_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 2)) (brGc 0 (0, 0, 2)) (sjsuG 0 (0, 0, 2)) (0, 0, 2) := by
  have hn : brN 0 (0, 0, 2) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_2_0

theorem brq_0_0_0_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 3)) (brGc 0 (0, 0, 3)) (sjsuG 0 (0, 0, 3)) (0, 0, 3) := by
  have hn : brN 0 (0, 0, 3) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_3_0

theorem brq_0_0_0_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 4)) (brGc 0 (0, 0, 4)) (sjsuG 0 (0, 0, 4)) (0, 0, 4) := by
  have hn : brN 0 (0, 0, 4) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_4_0

theorem brq_0_0_0_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 5)) (brGc 0 (0, 0, 5)) (sjsuG 0 (0, 0, 5)) (0, 0, 5) := by
  have hn : brN 0 (0, 0, 5) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_5_0

theorem brq_0_0_0_6 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 6)) (brGc 0 (0, 0, 6)) (sjsuG 0 (0, 0, 6)) (0, 0, 6) := by
  have hn : brN 0 (0, 0, 6) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_6_0

theorem brq_0_0_0_7 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 7)) (brGc 0 (0, 0, 7)) (sjsuG 0 (0, 0, 7)) (0, 0, 7) := by
  have hn : brN 0 (0, 0, 7) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_7_0

theorem brq_0_0_0_8 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 0, 8)) (brGc 0 (0, 0, 8)) (sjsuG 0 (0, 0, 8)) (0, 0, 8) := by
  have hn : brN 0 (0, 0, 8) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_0_8_0

theorem brq_0_0_1_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 1, 0)) (brGc 0 (0, 1, 0)) (sjsuG 0 (0, 1, 0)) (0, 1, 0) := by
  have hn : brN 0 (0, 1, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_1_0_0

theorem brq_0_0_1_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 1, 1)) (brGc 0 (0, 1, 1)) (sjsuG 0 (0, 1, 1)) (0, 1, 1) := by
  have hn : brN 0 (0, 1, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_1_1_0

theorem brq_0_0_1_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 1, 2)) (brGc 0 (0, 1, 2)) (sjsuG 0 (0, 1, 2)) (0, 1, 2) := by
  have hn : brN 0 (0, 1, 2) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_1_2_0

theorem brq_0_0_1_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 1, 3)) (brGc 0 (0, 1, 3)) (sjsuG 0 (0, 1, 3)) (0, 1, 3) := by
  have hn : brN 0 (0, 1, 3) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_1_3_0

theorem brq_0_0_1_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 1, 4)) (brGc 0 (0, 1, 4)) (sjsuG 0 (0, 1, 4)) (0, 1, 4) := by
  have hn : brN 0 (0, 1, 4) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_1_4_0

theorem brq_0_0_1_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 1, 5)) (brGc 0 (0, 1, 5)) (sjsuG 0 (0, 1, 5)) (0, 1, 5) := by
  have hn : brN 0 (0, 1, 5) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_1_5_0

theorem brq_0_0_1_6 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 1, 6)) (brGc 0 (0, 1, 6)) (sjsuG 0 (0, 1, 6)) (0, 1, 6) := by
  have hn : brN 0 (0, 1, 6) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_1_6_0
  · exact brp_0_0_1_6_1

theorem brq_0_0_1_7 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 1, 7)) (brGc 0 (0, 1, 7)) (sjsuG 0 (0, 1, 7)) (0, 1, 7) := by
  have hn : brN 0 (0, 1, 7) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_1_7_0
  · exact brp_0_0_1_7_1

theorem brq_0_0_2_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 2, 0)) (brGc 0 (0, 2, 0)) (sjsuG 0 (0, 2, 0)) (0, 2, 0) := by
  have hn : brN 0 (0, 2, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_2_0_0

theorem brq_0_0_2_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 2, 1)) (brGc 0 (0, 2, 1)) (sjsuG 0 (0, 2, 1)) (0, 2, 1) := by
  have hn : brN 0 (0, 2, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_2_1_0

theorem brq_0_0_2_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 2, 2)) (brGc 0 (0, 2, 2)) (sjsuG 0 (0, 2, 2)) (0, 2, 2) := by
  have hn : brN 0 (0, 2, 2) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_2_2_0

theorem brq_0_0_2_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 2, 3)) (brGc 0 (0, 2, 3)) (sjsuG 0 (0, 2, 3)) (0, 2, 3) := by
  have hn : brN 0 (0, 2, 3) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_2_3_0

theorem brq_0_0_2_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 2, 4)) (brGc 0 (0, 2, 4)) (sjsuG 0 (0, 2, 4)) (0, 2, 4) := by
  have hn : brN 0 (0, 2, 4) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_2_4_0
  · exact brp_0_0_2_4_1

theorem brq_0_0_2_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 2, 5)) (brGc 0 (0, 2, 5)) (sjsuG 0 (0, 2, 5)) (0, 2, 5) := by
  have hn : brN 0 (0, 2, 5) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_2_5_0
  · exact brp_0_0_2_5_1

theorem brq_0_0_2_6 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 2, 6)) (brGc 0 (0, 2, 6)) (sjsuG 0 (0, 2, 6)) (0, 2, 6) := by
  have hn : brN 0 (0, 2, 6) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_2_6_0
  · exact brp_0_0_2_6_1

theorem brq_0_0_3_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 3, 0)) (brGc 0 (0, 3, 0)) (sjsuG 0 (0, 3, 0)) (0, 3, 0) := by
  have hn : brN 0 (0, 3, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_3_0_0

theorem brq_0_0_3_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 3, 1)) (brGc 0 (0, 3, 1)) (sjsuG 0 (0, 3, 1)) (0, 3, 1) := by
  have hn : brN 0 (0, 3, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_3_1_0

theorem brq_0_0_3_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 3, 2)) (brGc 0 (0, 3, 2)) (sjsuG 0 (0, 3, 2)) (0, 3, 2) := by
  have hn : brN 0 (0, 3, 2) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_3_2_0

theorem brq_0_0_3_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 3, 3)) (brGc 0 (0, 3, 3)) (sjsuG 0 (0, 3, 3)) (0, 3, 3) := by
  have hn : brN 0 (0, 3, 3) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_3_3_0
  · exact brp_0_0_3_3_1

theorem brq_0_0_3_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 3, 4)) (brGc 0 (0, 3, 4)) (sjsuG 0 (0, 3, 4)) (0, 3, 4) := by
  have hn : brN 0 (0, 3, 4) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_3_4_0
  · exact brp_0_0_3_4_1

theorem brq_0_0_3_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 3, 5)) (brGc 0 (0, 3, 5)) (sjsuG 0 (0, 3, 5)) (0, 3, 5) := by
  have hn : brN 0 (0, 3, 5) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_3_5_0
  · exact brp_0_0_3_5_1

theorem brq_0_0_4_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 4, 0)) (brGc 0 (0, 4, 0)) (sjsuG 0 (0, 4, 0)) (0, 4, 0) := by
  have hn : brN 0 (0, 4, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_4_0_0

theorem brq_0_0_4_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 4, 1)) (brGc 0 (0, 4, 1)) (sjsuG 0 (0, 4, 1)) (0, 4, 1) := by
  have hn : brN 0 (0, 4, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_4_1_0

theorem brq_0_0_4_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 4, 2)) (brGc 0 (0, 4, 2)) (sjsuG 0 (0, 4, 2)) (0, 4, 2) := by
  have hn : brN 0 (0, 4, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_4_2_0
  · exact brp_0_0_4_2_1

theorem brq_0_0_4_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 4, 3)) (brGc 0 (0, 4, 3)) (sjsuG 0 (0, 4, 3)) (0, 4, 3) := by
  have hn : brN 0 (0, 4, 3) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_4_3_0
  · exact brp_0_0_4_3_1

theorem brq_0_0_4_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 4, 4)) (brGc 0 (0, 4, 4)) (sjsuG 0 (0, 4, 4)) (0, 4, 4) := by
  have hn : brN 0 (0, 4, 4) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_4_4_0
  · exact brp_0_0_4_4_1

theorem brq_0_0_5_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 5, 0)) (brGc 0 (0, 5, 0)) (sjsuG 0 (0, 5, 0)) (0, 5, 0) := by
  have hn : brN 0 (0, 5, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_5_0_0

theorem brq_0_0_5_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 5, 1)) (brGc 0 (0, 5, 1)) (sjsuG 0 (0, 5, 1)) (0, 5, 1) := by
  have hn : brN 0 (0, 5, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_5_1_0

theorem brq_0_0_5_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 5, 2)) (brGc 0 (0, 5, 2)) (sjsuG 0 (0, 5, 2)) (0, 5, 2) := by
  have hn : brN 0 (0, 5, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_5_2_0
  · exact brp_0_0_5_2_1

theorem brq_0_0_5_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 5, 3)) (brGc 0 (0, 5, 3)) (sjsuG 0 (0, 5, 3)) (0, 5, 3) := by
  have hn : brN 0 (0, 5, 3) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_5_3_0
  · exact brp_0_0_5_3_1

theorem brq_0_0_6_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 6, 0)) (brGc 0 (0, 6, 0)) (sjsuG 0 (0, 6, 0)) (0, 6, 0) := by
  have hn : brN 0 (0, 6, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_6_0_0

theorem brq_0_0_6_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 6, 1)) (brGc 0 (0, 6, 1)) (sjsuG 0 (0, 6, 1)) (0, 6, 1) := by
  have hn : brN 0 (0, 6, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_6_1_0

theorem brq_0_0_6_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 6, 2)) (brGc 0 (0, 6, 2)) (sjsuG 0 (0, 6, 2)) (0, 6, 2) := by
  have hn : brN 0 (0, 6, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_6_2_0
  · exact brp_0_0_6_2_1

theorem brq_0_0_7_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 7, 0)) (brGc 0 (0, 7, 0)) (sjsuG 0 (0, 7, 0)) (0, 7, 0) := by
  have hn : brN 0 (0, 7, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_7_0_0

theorem brq_0_0_7_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 7, 1)) (brGc 0 (0, 7, 1)) (sjsuG 0 (0, 7, 1)) (0, 7, 1) := by
  have hn : brN 0 (0, 7, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_7_1_0

theorem brq_0_0_8_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (0, 8, 0)) (brGc 0 (0, 8, 0)) (sjsuG 0 (0, 8, 0)) (0, 8, 0) := by
  have hn : brN 0 (0, 8, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_0_8_0_0

theorem brq_0_1_0_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 0, 0)) (brGc 0 (1, 0, 0)) (sjsuG 0 (1, 0, 0)) (1, 0, 0) := by
  have hn : brN 0 (1, 0, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_0_0_0

theorem brq_0_1_0_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 0, 1)) (brGc 0 (1, 0, 1)) (sjsuG 0 (1, 0, 1)) (1, 0, 1) := by
  have hn : brN 0 (1, 0, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_0_1_0

theorem brq_0_1_0_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 0, 2)) (brGc 0 (1, 0, 2)) (sjsuG 0 (1, 0, 2)) (1, 0, 2) := by
  have hn : brN 0 (1, 0, 2) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_0_2_0

theorem brq_0_1_0_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 0, 3)) (brGc 0 (1, 0, 3)) (sjsuG 0 (1, 0, 3)) (1, 0, 3) := by
  have hn : brN 0 (1, 0, 3) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_0_3_0

theorem brq_0_1_0_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 0, 4)) (brGc 0 (1, 0, 4)) (sjsuG 0 (1, 0, 4)) (1, 0, 4) := by
  have hn : brN 0 (1, 0, 4) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_0_4_0

theorem brq_0_1_0_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 0, 5)) (brGc 0 (1, 0, 5)) (sjsuG 0 (1, 0, 5)) (1, 0, 5) := by
  have hn : brN 0 (1, 0, 5) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_0_5_0

theorem brq_0_1_0_6 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 0, 6)) (brGc 0 (1, 0, 6)) (sjsuG 0 (1, 0, 6)) (1, 0, 6) := by
  have hn : brN 0 (1, 0, 6) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_0_6_0
  · exact brp_0_1_0_6_1

theorem brq_0_1_0_7 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 0, 7)) (brGc 0 (1, 0, 7)) (sjsuG 0 (1, 0, 7)) (1, 0, 7) := by
  have hn : brN 0 (1, 0, 7) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_0_7_0
  · exact brp_0_1_0_7_1

theorem brq_0_1_1_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 1, 0)) (brGc 0 (1, 1, 0)) (sjsuG 0 (1, 1, 0)) (1, 1, 0) := by
  have hn : brN 0 (1, 1, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_1_0_0

theorem brq_0_1_1_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 1, 1)) (brGc 0 (1, 1, 1)) (sjsuG 0 (1, 1, 1)) (1, 1, 1) := by
  have hn : brN 0 (1, 1, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_1_1_0

theorem brq_0_1_1_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 1, 2)) (brGc 0 (1, 1, 2)) (sjsuG 0 (1, 1, 2)) (1, 1, 2) := by
  have hn : brN 0 (1, 1, 2) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_1_2_0

theorem brq_0_1_1_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 1, 3)) (brGc 0 (1, 1, 3)) (sjsuG 0 (1, 1, 3)) (1, 1, 3) := by
  have hn : brN 0 (1, 1, 3) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_1_3_0
  · exact brp_0_1_1_3_1

theorem brq_0_1_1_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 1, 4)) (brGc 0 (1, 1, 4)) (sjsuG 0 (1, 1, 4)) (1, 1, 4) := by
  have hn : brN 0 (1, 1, 4) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_1_4_0
  · exact brp_0_1_1_4_1

theorem brq_0_1_1_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 1, 5)) (brGc 0 (1, 1, 5)) (sjsuG 0 (1, 1, 5)) (1, 1, 5) := by
  have hn : brN 0 (1, 1, 5) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_1_5_0
  · exact brp_0_1_1_5_1

theorem brq_0_1_1_6 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 1, 6)) (brGc 0 (1, 1, 6)) (sjsuG 0 (1, 1, 6)) (1, 1, 6) := by
  have hn : brN 0 (1, 1, 6) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_1_6_0
  · exact brp_0_1_1_6_1
  · exact brp_0_1_1_6_2

theorem brq_0_1_2_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 2, 0)) (brGc 0 (1, 2, 0)) (sjsuG 0 (1, 2, 0)) (1, 2, 0) := by
  have hn : brN 0 (1, 2, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_2_0_0

theorem brq_0_1_2_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 2, 1)) (brGc 0 (1, 2, 1)) (sjsuG 0 (1, 2, 1)) (1, 2, 1) := by
  have hn : brN 0 (1, 2, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_2_1_0

theorem brq_0_1_2_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 2, 2)) (brGc 0 (1, 2, 2)) (sjsuG 0 (1, 2, 2)) (1, 2, 2) := by
  have hn : brN 0 (1, 2, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_2_2_0
  · exact brp_0_1_2_2_1

theorem brq_0_1_2_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 2, 3)) (brGc 0 (1, 2, 3)) (sjsuG 0 (1, 2, 3)) (1, 2, 3) := by
  have hn : brN 0 (1, 2, 3) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_2_3_0
  · exact brp_0_1_2_3_1

theorem brq_0_1_2_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 2, 4)) (brGc 0 (1, 2, 4)) (sjsuG 0 (1, 2, 4)) (1, 2, 4) := by
  have hn : brN 0 (1, 2, 4) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_2_4_0
  · exact brp_0_1_2_4_1
  · exact brp_0_1_2_4_2

theorem brq_0_1_2_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 2, 5)) (brGc 0 (1, 2, 5)) (sjsuG 0 (1, 2, 5)) (1, 2, 5) := by
  have hn : brN 0 (1, 2, 5) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_2_5_0
  · exact brp_0_1_2_5_1
  · exact brp_0_1_2_5_2

theorem brq_0_1_3_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 3, 0)) (brGc 0 (1, 3, 0)) (sjsuG 0 (1, 3, 0)) (1, 3, 0) := by
  have hn : brN 0 (1, 3, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_3_0_0

theorem brq_0_1_3_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 3, 1)) (brGc 0 (1, 3, 1)) (sjsuG 0 (1, 3, 1)) (1, 3, 1) := by
  have hn : brN 0 (1, 3, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_3_1_0
  · exact brp_0_1_3_1_1

theorem brq_0_1_3_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 3, 2)) (brGc 0 (1, 3, 2)) (sjsuG 0 (1, 3, 2)) (1, 3, 2) := by
  have hn : brN 0 (1, 3, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_3_2_0
  · exact brp_0_1_3_2_1

theorem brq_0_1_3_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 3, 3)) (brGc 0 (1, 3, 3)) (sjsuG 0 (1, 3, 3)) (1, 3, 3) := by
  have hn : brN 0 (1, 3, 3) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_3_3_0
  · exact brp_0_1_3_3_1
  · exact brp_0_1_3_3_2

theorem brq_0_1_3_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 3, 4)) (brGc 0 (1, 3, 4)) (sjsuG 0 (1, 3, 4)) (1, 3, 4) := by
  have hn : brN 0 (1, 3, 4) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_3_4_0
  · exact brp_0_1_3_4_1
  · exact brp_0_1_3_4_2

theorem brq_0_1_4_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 4, 0)) (brGc 0 (1, 4, 0)) (sjsuG 0 (1, 4, 0)) (1, 4, 0) := by
  have hn : brN 0 (1, 4, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_4_0_0

theorem brq_0_1_4_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 4, 1)) (brGc 0 (1, 4, 1)) (sjsuG 0 (1, 4, 1)) (1, 4, 1) := by
  have hn : brN 0 (1, 4, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_4_1_0
  · exact brp_0_1_4_1_1

theorem brq_0_1_4_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 4, 2)) (brGc 0 (1, 4, 2)) (sjsuG 0 (1, 4, 2)) (1, 4, 2) := by
  have hn : brN 0 (1, 4, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_4_2_0
  · exact brp_0_1_4_2_1

theorem brq_0_1_4_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 4, 3)) (brGc 0 (1, 4, 3)) (sjsuG 0 (1, 4, 3)) (1, 4, 3) := by
  have hn : brN 0 (1, 4, 3) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_4_3_0
  · exact brp_0_1_4_3_1
  · exact brp_0_1_4_3_2

theorem brq_0_1_5_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 5, 0)) (brGc 0 (1, 5, 0)) (sjsuG 0 (1, 5, 0)) (1, 5, 0) := by
  have hn : brN 0 (1, 5, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_5_0_0

theorem brq_0_1_5_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 5, 1)) (brGc 0 (1, 5, 1)) (sjsuG 0 (1, 5, 1)) (1, 5, 1) := by
  have hn : brN 0 (1, 5, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_5_1_0
  · exact brp_0_1_5_1_1

theorem brq_0_1_5_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 5, 2)) (brGc 0 (1, 5, 2)) (sjsuG 0 (1, 5, 2)) (1, 5, 2) := by
  have hn : brN 0 (1, 5, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_5_2_0
  · exact brp_0_1_5_2_1

theorem brq_0_1_6_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 6, 0)) (brGc 0 (1, 6, 0)) (sjsuG 0 (1, 6, 0)) (1, 6, 0) := by
  have hn : brN 0 (1, 6, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_6_0_0

theorem brq_0_1_6_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 6, 1)) (brGc 0 (1, 6, 1)) (sjsuG 0 (1, 6, 1)) (1, 6, 1) := by
  have hn : brN 0 (1, 6, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_6_1_0
  · exact brp_0_1_6_1_1

theorem brq_0_1_7_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (1, 7, 0)) (brGc 0 (1, 7, 0)) (sjsuG 0 (1, 7, 0)) (1, 7, 0) := by
  have hn : brN 0 (1, 7, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_1_7_0_0

theorem brq_0_2_0_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 0, 0)) (brGc 0 (2, 0, 0)) (sjsuG 0 (2, 0, 0)) (2, 0, 0) := by
  have hn : brN 0 (2, 0, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_0_0_0

theorem brq_0_2_0_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 0, 1)) (brGc 0 (2, 0, 1)) (sjsuG 0 (2, 0, 1)) (2, 0, 1) := by
  have hn : brN 0 (2, 0, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_0_1_0

theorem brq_0_2_0_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 0, 2)) (brGc 0 (2, 0, 2)) (sjsuG 0 (2, 0, 2)) (2, 0, 2) := by
  have hn : brN 0 (2, 0, 2) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_0_2_0

theorem brq_0_2_0_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 0, 3)) (brGc 0 (2, 0, 3)) (sjsuG 0 (2, 0, 3)) (2, 0, 3) := by
  have hn : brN 0 (2, 0, 3) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_0_3_0

theorem brq_0_2_0_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 0, 4)) (brGc 0 (2, 0, 4)) (sjsuG 0 (2, 0, 4)) (2, 0, 4) := by
  have hn : brN 0 (2, 0, 4) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_0_4_0
  · exact brp_0_2_0_4_1

theorem brq_0_2_0_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 0, 5)) (brGc 0 (2, 0, 5)) (sjsuG 0 (2, 0, 5)) (2, 0, 5) := by
  have hn : brN 0 (2, 0, 5) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_0_5_0
  · exact brp_0_2_0_5_1

theorem brq_0_2_0_6 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 0, 6)) (brGc 0 (2, 0, 6)) (sjsuG 0 (2, 0, 6)) (2, 0, 6) := by
  have hn : brN 0 (2, 0, 6) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_0_6_0
  · exact brp_0_2_0_6_1

theorem brq_0_2_1_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 1, 0)) (brGc 0 (2, 1, 0)) (sjsuG 0 (2, 1, 0)) (2, 1, 0) := by
  have hn : brN 0 (2, 1, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_1_0_0

theorem brq_0_2_1_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 1, 1)) (brGc 0 (2, 1, 1)) (sjsuG 0 (2, 1, 1)) (2, 1, 1) := by
  have hn : brN 0 (2, 1, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_1_1_0

theorem brq_0_2_1_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 1, 2)) (brGc 0 (2, 1, 2)) (sjsuG 0 (2, 1, 2)) (2, 1, 2) := by
  have hn : brN 0 (2, 1, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_1_2_0
  · exact brp_0_2_1_2_1

theorem brq_0_2_1_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 1, 3)) (brGc 0 (2, 1, 3)) (sjsuG 0 (2, 1, 3)) (2, 1, 3) := by
  have hn : brN 0 (2, 1, 3) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_1_3_0
  · exact brp_0_2_1_3_1

theorem brq_0_2_1_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 1, 4)) (brGc 0 (2, 1, 4)) (sjsuG 0 (2, 1, 4)) (2, 1, 4) := by
  have hn : brN 0 (2, 1, 4) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_1_4_0
  · exact brp_0_2_1_4_1
  · exact brp_0_2_1_4_2

theorem brq_0_2_1_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 1, 5)) (brGc 0 (2, 1, 5)) (sjsuG 0 (2, 1, 5)) (2, 1, 5) := by
  have hn : brN 0 (2, 1, 5) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_1_5_0
  · exact brp_0_2_1_5_1
  · exact brp_0_2_1_5_2

theorem brq_0_2_2_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 2, 0)) (brGc 0 (2, 2, 0)) (sjsuG 0 (2, 2, 0)) (2, 2, 0) := by
  have hn : brN 0 (2, 2, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_2_0_0

theorem brq_0_2_2_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 2, 1)) (brGc 0 (2, 2, 1)) (sjsuG 0 (2, 2, 1)) (2, 2, 1) := by
  have hn : brN 0 (2, 2, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_2_1_0
  · exact brp_0_2_2_1_1

theorem brq_0_2_2_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 2, 2)) (brGc 0 (2, 2, 2)) (sjsuG 0 (2, 2, 2)) (2, 2, 2) := by
  have hn : brN 0 (2, 2, 2) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_2_2_0
  · exact brp_0_2_2_2_1
  · exact brp_0_2_2_2_2

theorem brq_0_2_2_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 2, 3)) (brGc 0 (2, 2, 3)) (sjsuG 0 (2, 2, 3)) (2, 2, 3) := by
  have hn : brN 0 (2, 2, 3) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_2_3_0
  · exact brp_0_2_2_3_1
  · exact brp_0_2_2_3_2

theorem brq_0_2_2_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 2, 4)) (brGc 0 (2, 2, 4)) (sjsuG 0 (2, 2, 4)) (2, 2, 4) := by
  have hn : brN 0 (2, 2, 4) = 4 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_2_4_0
  · exact brp_0_2_2_4_1
  · exact brp_0_2_2_4_2
  · exact brp_0_2_2_4_3

theorem brq_0_2_3_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 3, 0)) (brGc 0 (2, 3, 0)) (sjsuG 0 (2, 3, 0)) (2, 3, 0) := by
  have hn : brN 0 (2, 3, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_3_0_0

theorem brq_0_2_3_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 3, 1)) (brGc 0 (2, 3, 1)) (sjsuG 0 (2, 3, 1)) (2, 3, 1) := by
  have hn : brN 0 (2, 3, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_3_1_0
  · exact brp_0_2_3_1_1

theorem brq_0_2_3_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 3, 2)) (brGc 0 (2, 3, 2)) (sjsuG 0 (2, 3, 2)) (2, 3, 2) := by
  have hn : brN 0 (2, 3, 2) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_3_2_0
  · exact brp_0_2_3_2_1
  · exact brp_0_2_3_2_2

theorem brq_0_2_3_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 3, 3)) (brGc 0 (2, 3, 3)) (sjsuG 0 (2, 3, 3)) (2, 3, 3) := by
  have hn : brN 0 (2, 3, 3) = 4 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_3_3_0
  · exact brp_0_2_3_3_1
  · exact brp_0_2_3_3_2
  · exact brp_0_2_3_3_3

theorem brq_0_2_4_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 4, 0)) (brGc 0 (2, 4, 0)) (sjsuG 0 (2, 4, 0)) (2, 4, 0) := by
  have hn : brN 0 (2, 4, 0) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_4_0_0
  · exact brp_0_2_4_0_1

theorem brq_0_2_4_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 4, 1)) (brGc 0 (2, 4, 1)) (sjsuG 0 (2, 4, 1)) (2, 4, 1) := by
  have hn : brN 0 (2, 4, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_4_1_0
  · exact brp_0_2_4_1_1

theorem brq_0_2_4_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 4, 2)) (brGc 0 (2, 4, 2)) (sjsuG 0 (2, 4, 2)) (2, 4, 2) := by
  have hn : brN 0 (2, 4, 2) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_4_2_0
  · exact brp_0_2_4_2_1
  · exact brp_0_2_4_2_2

theorem brq_0_2_5_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 5, 0)) (brGc 0 (2, 5, 0)) (sjsuG 0 (2, 5, 0)) (2, 5, 0) := by
  have hn : brN 0 (2, 5, 0) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_5_0_0
  · exact brp_0_2_5_0_1

theorem brq_0_2_5_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 5, 1)) (brGc 0 (2, 5, 1)) (sjsuG 0 (2, 5, 1)) (2, 5, 1) := by
  have hn : brN 0 (2, 5, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_5_1_0
  · exact brp_0_2_5_1_1

theorem brq_0_2_6_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (2, 6, 0)) (brGc 0 (2, 6, 0)) (sjsuG 0 (2, 6, 0)) (2, 6, 0) := by
  have hn : brN 0 (2, 6, 0) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_2_6_0_0
  · exact brp_0_2_6_0_1

theorem brq_0_3_0_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 0, 0)) (brGc 0 (3, 0, 0)) (sjsuG 0 (3, 0, 0)) (3, 0, 0) := by
  have hn : brN 0 (3, 0, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_0_0_0

theorem brq_0_3_0_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 0, 1)) (brGc 0 (3, 0, 1)) (sjsuG 0 (3, 0, 1)) (3, 0, 1) := by
  have hn : brN 0 (3, 0, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_0_1_0

theorem brq_0_3_0_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 0, 2)) (brGc 0 (3, 0, 2)) (sjsuG 0 (3, 0, 2)) (3, 0, 2) := by
  have hn : brN 0 (3, 0, 2) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_0_2_0

theorem brq_0_3_0_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 0, 3)) (brGc 0 (3, 0, 3)) (sjsuG 0 (3, 0, 3)) (3, 0, 3) := by
  have hn : brN 0 (3, 0, 3) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_0_3_0
  · exact brp_0_3_0_3_1

theorem brq_0_3_0_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 0, 4)) (brGc 0 (3, 0, 4)) (sjsuG 0 (3, 0, 4)) (3, 0, 4) := by
  have hn : brN 0 (3, 0, 4) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_0_4_0
  · exact brp_0_3_0_4_1

theorem brq_0_3_0_5 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 0, 5)) (brGc 0 (3, 0, 5)) (sjsuG 0 (3, 0, 5)) (3, 0, 5) := by
  have hn : brN 0 (3, 0, 5) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_0_5_0
  · exact brp_0_3_0_5_1

theorem brq_0_3_1_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 1, 0)) (brGc 0 (3, 1, 0)) (sjsuG 0 (3, 1, 0)) (3, 1, 0) := by
  have hn : brN 0 (3, 1, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_1_0_0

theorem brq_0_3_1_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 1, 1)) (brGc 0 (3, 1, 1)) (sjsuG 0 (3, 1, 1)) (3, 1, 1) := by
  have hn : brN 0 (3, 1, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_1_1_0
  · exact brp_0_3_1_1_1

theorem brq_0_3_1_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 1, 2)) (brGc 0 (3, 1, 2)) (sjsuG 0 (3, 1, 2)) (3, 1, 2) := by
  have hn : brN 0 (3, 1, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_1_2_0
  · exact brp_0_3_1_2_1

theorem brq_0_3_1_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 1, 3)) (brGc 0 (3, 1, 3)) (sjsuG 0 (3, 1, 3)) (3, 1, 3) := by
  have hn : brN 0 (3, 1, 3) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_1_3_0
  · exact brp_0_3_1_3_1
  · exact brp_0_3_1_3_2

theorem brq_0_3_1_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 1, 4)) (brGc 0 (3, 1, 4)) (sjsuG 0 (3, 1, 4)) (3, 1, 4) := by
  have hn : brN 0 (3, 1, 4) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_1_4_0
  · exact brp_0_3_1_4_1
  · exact brp_0_3_1_4_2

theorem brq_0_3_2_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 2, 0)) (brGc 0 (3, 2, 0)) (sjsuG 0 (3, 2, 0)) (3, 2, 0) := by
  have hn : brN 0 (3, 2, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_2_0_0

theorem brq_0_3_2_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 2, 1)) (brGc 0 (3, 2, 1)) (sjsuG 0 (3, 2, 1)) (3, 2, 1) := by
  have hn : brN 0 (3, 2, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_2_1_0
  · exact brp_0_3_2_1_1

theorem brq_0_3_2_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 2, 2)) (brGc 0 (3, 2, 2)) (sjsuG 0 (3, 2, 2)) (3, 2, 2) := by
  have hn : brN 0 (3, 2, 2) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_2_2_0
  · exact brp_0_3_2_2_1
  · exact brp_0_3_2_2_2

theorem brq_0_3_2_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 2, 3)) (brGc 0 (3, 2, 3)) (sjsuG 0 (3, 2, 3)) (3, 2, 3) := by
  have hn : brN 0 (3, 2, 3) = 4 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_2_3_0
  · exact brp_0_3_2_3_1
  · exact brp_0_3_2_3_2
  · exact brp_0_3_2_3_3

theorem brq_0_3_3_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 3, 0)) (brGc 0 (3, 3, 0)) (sjsuG 0 (3, 3, 0)) (3, 3, 0) := by
  have hn : brN 0 (3, 3, 0) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_3_0_0
  · exact brp_0_3_3_0_1

theorem brq_0_3_3_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 3, 1)) (brGc 0 (3, 3, 1)) (sjsuG 0 (3, 3, 1)) (3, 3, 1) := by
  have hn : brN 0 (3, 3, 1) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_3_1_0
  · exact brp_0_3_3_1_1
  · exact brp_0_3_3_1_2

theorem brq_0_3_3_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 3, 2)) (brGc 0 (3, 3, 2)) (sjsuG 0 (3, 3, 2)) (3, 3, 2) := by
  have hn : brN 0 (3, 3, 2) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_3_2_0
  · exact brp_0_3_3_2_1
  · exact brp_0_3_3_2_2

theorem brq_0_3_4_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 4, 0)) (brGc 0 (3, 4, 0)) (sjsuG 0 (3, 4, 0)) (3, 4, 0) := by
  have hn : brN 0 (3, 4, 0) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_4_0_0
  · exact brp_0_3_4_0_1

theorem brq_0_3_4_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 4, 1)) (brGc 0 (3, 4, 1)) (sjsuG 0 (3, 4, 1)) (3, 4, 1) := by
  have hn : brN 0 (3, 4, 1) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_4_1_0
  · exact brp_0_3_4_1_1
  · exact brp_0_3_4_1_2

theorem brq_0_3_5_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (3, 5, 0)) (brGc 0 (3, 5, 0)) (sjsuG 0 (3, 5, 0)) (3, 5, 0) := by
  have hn : brN 0 (3, 5, 0) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_3_5_0_0
  · exact brp_0_3_5_0_1

theorem brq_0_4_0_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (4, 0, 0)) (brGc 0 (4, 0, 0)) (sjsuG 0 (4, 0, 0)) (4, 0, 0) := by
  have hn : brN 0 (4, 0, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_4_0_0_0

theorem brq_0_4_0_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (4, 0, 1)) (brGc 0 (4, 0, 1)) (sjsuG 0 (4, 0, 1)) (4, 0, 1) := by
  have hn : brN 0 (4, 0, 1) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_4_0_1_0

theorem brq_0_4_0_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (4, 0, 2)) (brGc 0 (4, 0, 2)) (sjsuG 0 (4, 0, 2)) (4, 0, 2) := by
  have hn : brN 0 (4, 0, 2) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_4_0_2_0
  · exact brp_0_4_0_2_1

theorem brq_0_4_0_3 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (4, 0, 3)) (brGc 0 (4, 0, 3)) (sjsuG 0 (4, 0, 3)) (4, 0, 3) := by
  have hn : brN 0 (4, 0, 3) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_4_0_3_0
  · exact brp_0_4_0_3_1

theorem brq_0_4_0_4 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (4, 0, 4)) (brGc 0 (4, 0, 4)) (sjsuG 0 (4, 0, 4)) (4, 0, 4) := by
  have hn : brN 0 (4, 0, 4) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_4_0_4_0
  · exact brp_0_4_0_4_1

theorem brq_0_4_1_0 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (4, 1, 0)) (brGc 0 (4, 1, 0)) (sjsuG 0 (4, 1, 0)) (4, 1, 0) := by
  have hn : brN 0 (4, 1, 0) = 1 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_4_1_0_0

theorem brq_0_4_1_1 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (4, 1, 1)) (brGc 0 (4, 1, 1)) (sjsuG 0 (4, 1, 1)) (4, 1, 1) := by
  have hn : brN 0 (4, 1, 1) = 2 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_4_1_1_0
  · exact brp_0_4_1_1_1

theorem brq_0_4_1_2 : BrPOk (brD 0) 25 30 true (Ftab 0) brInH 100
    (brN 0 (4, 1, 2)) (brGc 0 (4, 1, 2)) (sjsuG 0 (4, 1, 2)) (4, 1, 2) := by
  have hn : brN 0 (4, 1, 2) = 3 := by decide +kernel
  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩
  rw [hn] at hk
  interval_cases k
  · exact brp_0_4_1_2_0
  · exact brp_0_4_1_2_1
  · exact brp_0_4_1_2_2


end KAM.EffectiveStability.SJSU

end
