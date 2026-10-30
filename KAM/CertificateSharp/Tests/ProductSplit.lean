/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.ProductSplit

/-!
# Product-split tests

Toy instances (copies of the landed packed-product test data of `KAM.Certificate.Tests.Packed`,
exposed here so that the kernel can unfold them) on which the split product equals the whole
product. Every evaluation is by `decide +kernel`.

* **Shard groups.** On the two-block (`n = 2`) and the five-window products, `checkPackedSp` is its
  prefix together with every shard; `checkPackedSp_of_groups` with a two-group cover reproduces the
  whole check; on rejected advice both sides are `false`.
* **Real part.** `packedRealProduct_eq_of_sparse` (from the grouped check) and the two empty lemmas
  agree with the kernel value of the whole `packedRealProduct`.
* **Assembly.** `CertPoly.mulPacked_eq_of_parts`: the whole `mulPacked` equals the value assembled
  from its four separately proved parts and the separately proved decode.
-/

@[expose] public section

namespace KAM.Certificate

/-! ### Data (copied from `KAM.Certificate.Tests.Packed`) -/

/-- Keys `(0..1, -1..1)`, row stride `5`, one row per block. -/
def splitTestLay2 : PackLayout := ⟨[0, -1], [2, 3], [5, 1], 24, 1⟩

def splitTestTarget2 : PackLayout := ⟨[0, -2], [3, 5], [5, 1], 24, 1⟩

def splitTestA2 : List (CertKey × ℤ) :=
  [([0, -1], 3), ([0, 0], -5), ([0, 1], 7), ([1, -1], 2), ([1, 0], 11), ([1, 1], -4)]

def splitTestB2 : List (CertKey × ℤ) :=
  [([0, -1], 6), ([0, 0], 1), ([0, 1], -9), ([1, -1], -3), ([1, 0], 8), ([1, 1], 5)]

def splitTestAdv2 : PackedAdvice :=
  ⟨splitTestLay2, splitTestLay2, splitTestTarget2, 4,
    [[1, -2, 1, 3, -4, 0, 0, 0, 0], [0, 7, -5, -4, 4, 0, 0, 0, 0], [0, -1, 7, 1, -1, 0, 0, 0, 0]],
    0⟩

/-- One advice slot off by `+2` (rejected). -/
def splitTestAdv2Off : PackedAdvice :=
  ⟨splitTestLay2, splitTestLay2, splitTestTarget2, 4,
    [[1, -2, 1, 5, -4, 0, 0, 0, 0], [0, 7, -5, -4, 4, 0, 0, 0, 0], [0, -1, 7, 1, -1, 0, 0, 0, 0]],
    0⟩

/-- Keys `(-1..1, 0..1)`, row stride `3`: three blocks per factor, five shard windows. -/
def splitTestLayM : PackLayout := ⟨[-1, 0], [3, 2], [3, 1], 24, 1⟩

def splitTestTargetM : PackLayout := ⟨[-2, 0], [5, 3], [3, 1], 24, 1⟩

def splitTestAM : List (CertKey × ℤ) :=
  [([-1, 0], 9), ([-1, 1], -2), ([0, 0], 4), ([0, 1], 13), ([1, 0], -6), ([1, 1], 1)]

def splitTestBM : List (CertKey × ℤ) :=
  [([-1, 0], -5), ([-1, 1], 8), ([0, 0], 3), ([0, 1], 2), ([1, 0], 10), ([1, 1], -7)]

def splitTestAdvM : PackedAdvice :=
  ⟨splitTestLayM, splitTestLayM, splitTestTargetM, 4,
    [[-3, 5, -1, 0, 0], [0, -1, 6, 0, 0], [8, -6, 3, 0, 0], [1, 6, -6, 0, 0], [-4, 3, 0, 0, 0]],
    0⟩

/-- A fixed-point polynomial with the given real mantissas (scale `2^4`). -/
def splitTestRe (cs : List (CertKey × ℤ)) : CertPoly (CertFixed 4) :=
  ⟨cs.map fun t => (t.1, ⟨⟨t.2⟩, ⟨0⟩⟩)⟩

def splitTestW : CertWeight := ⟨1 / 100, 11 / 10⟩

/-- Bogus advice (scale zero), never consulted for an empty part. -/
def splitTestBogus : PackedAdvice := ⟨splitTestLay2, splitTestLay2, splitTestTarget2, 0, [], 0⟩

/-! ### Tests -/

/-- The split form of the sparse check, as a Boolean. -/
def splitCheckTest (adv : PackedAdvice) (ea eb : List (ℕ × ℤ)) : Bool :=
  checkPackedSpPrefix adv ea eb && adv.shardRange.all (checkShardAt adv ea eb)

def splitTestEa2 : List (ℕ × ℤ) := splitTestLay2.slotTerms splitTestA2
def splitTestEb2 : List (ℕ × ℤ) := splitTestLay2.slotTerms splitTestB2
def splitTestEaM : List (ℕ × ℤ) := splitTestLayM.slotTerms splitTestAM
def splitTestEbM : List (ℕ × ℤ) := splitTestLayM.slotTerms splitTestBM

/-- Whole equals split, on two passing products and on rejected advice (one advice slot changed;
descending slots). -/
theorem splitTest_agree :
    checkPackedSp splitTestAdv2 splitTestEa2 splitTestEb2 =
        splitCheckTest splitTestAdv2 splitTestEa2 splitTestEb2 ∧
      checkPackedSp splitTestAdvM splitTestEaM splitTestEbM =
        splitCheckTest splitTestAdvM splitTestEaM splitTestEbM ∧
      checkPackedSp splitTestAdv2Off splitTestEa2 splitTestEb2 =
        splitCheckTest splitTestAdv2Off splitTestEa2 splitTestEb2 ∧
      checkPackedSp splitTestAdv2 splitTestEa2.reverse splitTestEb2 =
        splitCheckTest splitTestAdv2 splitTestEa2.reverse splitTestEb2 ∧
      splitCheckTest splitTestAdv2Off splitTestEa2 splitTestEb2 = false := by
  decide +kernel

theorem splitTest_shardRangeM : splitTestAdvM.shardRange = [0, 1, 2, 3, 4] := by
  decide +kernel

/-- The five-window check from its prefix and two shard groups, each decided apart. -/
theorem splitTest_groupsM : checkPackedSp splitTestAdvM splitTestEaM splitTestEbM = true :=
  checkPackedSp_of_groups _ _ _ [[0, 1, 2], [3, 4]] (by decide +kernel)
    (by rw [splitTest_shardRangeM]; decide)
    (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · decide +kernel
      · decide +kernel)

/-- The real part from the grouped check equals the whole real part. -/
theorem splitTest_realM :
    packedRealProduct splitTestAdvM splitTestW 8 splitTestAM splitTestBM =
      some (splitTestAdvM.targetTerms, splitTestAdvM.remainderBound splitTestW 8) :=
  packedRealProduct_eq_of_sparse _ _ _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) splitTest_groupsM

theorem splitTest_realM_whole :
    packedRealProduct splitTestAdvM splitTestW 8 splitTestAM splitTestBM =
      some (splitTestAdvM.targetTerms, splitTestAdvM.remainderBound splitTestW 8) := by
  decide +kernel

/-- An empty factor: the bogus advice is never consulted. -/
theorem splitTest_nil :
    packedRealProduct splitTestBogus splitTestW 8 [] splitTestBM = some ([], 0) ∧
      packedRealProduct splitTestBogus splitTestW 8 splitTestAM [] = some ([], 0) :=
  ⟨packedRealProduct_eq_nil_left _ _ _ _ rfl, packedRealProduct_eq_nil_right _ _ _ _ rfl⟩

/-- The decoded real part, evaluated apart. -/
noncomputable def splitTestTRR : List (CertKey × CC (CertFixed 4)) :=
  (dyadicTerms 8 splitTestAdvM.scale (fun v => ⟨v, CertArith.ofInt 0⟩)
    splitTestAdvM.targetTerms).getD []

/-- The decode of the real part, proved apart (it succeeds; its value is `splitTestTRR`). -/
theorem splitTest_decodeM :
    dyadicTerms 8 splitTestAdvM.scale (fun v => ⟨v, CertArith.ofInt 0⟩)
      splitTestAdvM.targetTerms = some splitTestTRR := by
  have h : (dyadicTerms 8 splitTestAdvM.scale (fun v => (⟨v, CertArith.ofInt 0⟩ : CC (CertFixed 4)))
      splitTestAdvM.targetTerms).isSome = true := by decide +kernel
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  rw [splitTestTRR, ht]
  rfl

/-- The whole `mulPacked` equals its assembly from the separately proved parts (the imaginary
parts are empty). -/
theorem splitTest_mulPackedM :
    CertPoly.mulPacked (CertFixed.toMant 4) splitTestW 4 splitTestAdvM splitTestBogus
        splitTestBogus splitTestBogus (splitTestRe splitTestAM) (splitTestRe splitTestBM) =
      some (⟨splitTestTRR ++ [] ++ [] ++ []⟩,
        CertArith.ofRatUp (splitTestAdvM.remainderBound splitTestW 8 + 0 + 0 + 0)) :=
  CertPoly.mulPacked_eq_of_parts _ _ _ _ _ _ _ _ _
    (ma := (splitTestAM, [])) (mb := (splitTestBM, []))
    (pRR := (splitTestAdvM.targetTerms, splitTestAdvM.remainderBound splitTestW 8))
    (pII := ([], 0)) (pRI := ([], 0)) (pIR := ([], 0))
    (tII := []) (tRI := []) (tIR := [])
    (by decide +kernel) (by decide +kernel) splitTest_realM
    (packedRealProduct_eq_nil_left _ _ _ _ rfl) (packedRealProduct_eq_nil_right _ _ _ _ rfl)
    (packedRealProduct_eq_nil_left _ _ _ _ rfl) splitTest_decodeM rfl rfl rfl

end KAM.Certificate
