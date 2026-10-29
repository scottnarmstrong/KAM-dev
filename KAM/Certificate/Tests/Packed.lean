/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.Ops

/-!
# Packed-product tests (design §8, `Tests/Packed`)

Every check below is decided by `decide +kernel` (kernel reduction only).

* **Layout.** Dense lists by the linear fill (slots in order) and by the binary scatter (unsorted,
  repeated keys add); a key of the wrong length is outside the box.
* **Positive.** A two-dimensional product (`n = 2`, two blocks per factor), a three-dimensional
  one (`n = 3`, target a proper sub-box, so out-of-box slots use `outLog`) and a multi-shard one
  (three blocks per factor, five overlapping shard windows) pass `checkPackedProduct` with correct
  design-B advice, and `CertPoly.mulPacked` returns `some` on the fixed-point backend
  `CertFixed 4` with the production decoder `CertFixed.toMant`. The imaginary-part products of
  real data are skipped: bogus advice (scale zero) for them changes nothing. A real-times-imaginary
  product exercises the `re·im` route. One success is paired with `CertPoly.mulPacked_sound`.
* **Negative.** An advice slot off by `+2` (SO-REPLAY2's control); advice equal modulo the packing
  (`packSum` unchanged) but violating the slot range; a wrapping stride (`compat = false`); a
  mantissa decoder returning a wrong integer (`mantCheck` rejects); a key outside the layout box.
* **P2 (F12, audit 5).** Factors `[0, 0]`, advice `[16, -1, 0]` at `w = 4`, `scale = 1`: the packed
  residual decodes (the carry cancels), but `reconFits` rejects, hence `checkShard` and
  `checkPackedProduct`.
* **P3 (F13, positive).** Audit 6's overlap control: slot two receives two windows with error one
  each and the combined error `2 = 2^scale` is attained.
* **P4 (F13, negative).** Audit 5's blocks at `scale = 0`: every shard passes, the whole product is
  rejected (`checkPackedProduct_scale_zero`), and the combined error two exceeds `2^0`.
* **P5 (F14, audit 6).** The padding alias `[0]` versus `[0, 0]`: the same cut blocks, the long call
  passes and the short call is rejected by the raw-shape check.
-/

public section

namespace KAM.Certificate

/-! ### Positive: `n = 2` -/

/-- Keys `(0..1, -1..1)`, row stride `5` (no wrap: `5 ≥ 3 + 3 - 1`), one row per block. -/
def packedTestLay2 : PackLayout := ⟨[0, -1], [2, 3], [5, 1], 24, 1⟩

/-- The full product window `(0..2, -2..2)`. -/
def packedTestTarget2 : PackLayout := ⟨[0, -2], [3, 5], [5, 1], 24, 1⟩

def packedTestA2 : List (CertKey × ℤ) :=
  [([0, -1], 3), ([0, 0], -5), ([0, 1], 7), ([1, -1], 2), ([1, 0], 11), ([1, 1], -4)]

def packedTestB2 : List (CertKey × ℤ) :=
  [([0, -1], 6), ([0, 0], 1), ([0, 1], -9), ([1, -1], -3), ([1, 0], 8), ([1, 1], 5)]

/-- Correct design-B advice at `scale = 4` (nearest rounding per window). -/
def packedTestAdv2 : PackedAdvice :=
  ⟨packedTestLay2, packedTestLay2, packedTestTarget2, 4,
    [[1, -2, 1, 3, -4, 0, 0, 0, 0], [0, 7, -5, -4, 4, 0, 0, 0, 0], [0, -1, 7, 1, -1, 0, 0, 0, 0]],
    0⟩

theorem packedTest_dense2 :
    packedTestLay2.dense packedTestA2 = some [3, -5, 7, 0, 0, 2, 11, -4] ∧
      packedTestLay2.dense packedTestB2 = some [6, 1, -9, 0, 0, -3, 8, 5] := by
  decide +kernel

/-- Unsorted keys with a repeated key go through the binary scatter; repeated keys add. -/
theorem packedTest_dense2_scatter :
    packedTestLay2.dense [([1, 1], 2), ([0, -1], 3), ([1, 1], -6)] =
      some [3, 0, 0, 0, 0, 0, 0, -4] := by
  decide +kernel

/-- A key of the wrong length is outside the box. -/
theorem packedTest_dense2_badKey : packedTestLay2.dense [([0], 1)] = none := by
  decide +kernel

theorem packedTest_pass2 :
    checkPackedProduct packedTestAdv2 [3, -5, 7, 0, 0, 2, 11, -4] [6, 1, -9, 0, 0, -3, 8, 5] =
      true := by
  decide +kernel

/-- The slot contract on the passing `n = 2` product, at slot `8` (two windows overlap). -/
theorem packedTest_sound2 :
    |(listConv [3, -5, 7, 0, 0, 2, 11, -4] [6, 1, -9, 0, 0, -3, 8, 5]).getD 8 0 -
      2 ^ 4 * packedTestAdv2.combined.getD 8 0| ≤ 2 ^ 4 :=
  ((checkPackedProduct_sound packedTest_pass2).2 8 (by decide +kernel)).1 (by decide +kernel)

/-- A fixed-point polynomial with the given real mantissas (scale `2^4`). -/
def packedTestRe (cs : List (CertKey × ℤ)) : CertPoly (CertFixed 4) :=
  ⟨cs.map fun t => (t.1, ⟨⟨t.2⟩, ⟨0⟩⟩)⟩

/-- A fixed-point polynomial with the given imaginary mantissas (scale `2^4`). -/
def packedTestIm (cs : List (CertKey × ℤ)) : CertPoly (CertFixed 4) :=
  ⟨cs.map fun t => (t.1, ⟨⟨0⟩, ⟨t.2⟩⟩)⟩

/-- A strip weight `w = 11/10 ≥ e^{2π/100}`. -/
def packedTestW : CertWeight := ⟨1 / 100, 11 / 10⟩

theorem packedTest_weight : checkWeight packedTestW 0 6 = true := by decide +kernel

/-- Bogus advice (scale zero): it would fail every check; it is never consulted for a product
with an empty (all-zero) part. -/
def packedTestBogus : PackedAdvice := ⟨packedTestLay2, packedTestLay2, packedTestTarget2, 0, [], 0⟩

theorem packedTest_mulPacked2 :
    (CertPoly.mulPacked (CertFixed.toMant 4) packedTestW 4 packedTestAdv2 packedTestBogus
      packedTestBogus packedTestBogus (packedTestRe packedTestA2)
      (packedTestRe packedTestB2)).isSome = true := by
  decide +kernel

/-- The `n = 2` product on the packed route encloses the EXACT product on the strip. -/
theorem packedTest_mulPacked2_encloses :
    ∃ out, CertPoly.mulPacked (CertFixed.toMant 4) packedTestW 4 packedTestAdv2 packedTestBogus
      packedTestBogus packedTestBogus (packedTestRe packedTestA2) (packedTestRe packedTestB2) =
        some out ∧ ∀ θ ∈ complexStrip 2 packedTestW.rho,
          ‖(packedTestRe packedTestA2).eval 2 θ * (packedTestRe packedTestB2).eval 2 θ -
            out.1.eval 2 θ‖ ≤ CertArith.val out.2 := by
  obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp packedTest_mulPacked2
  exact ⟨out, hout, CertPoly.mulPacked_sound packedTest_weight hout⟩

/-- Real times imaginary: only the `re·im` product is nonzero (bogus advice elsewhere). -/
theorem packedTest_mulPacked2_reIm :
    (CertPoly.mulPacked (CertFixed.toMant 4) packedTestW 4 packedTestBogus packedTestBogus
      packedTestAdv2 packedTestBogus (packedTestRe packedTestA2)
      (packedTestIm packedTestB2)).isSome = true := by
  decide +kernel

/-! ### Positive: `n = 3`, target a proper sub-box -/

/-- Keys `{0,1}³`, strides `[9, 3, 1]` (no wrap: `3 ≥ 1·3`, `9 ≥ 3·3`), one row per block. -/
def packedTestLay3 : PackLayout := ⟨[0, 0, 0], [2, 2, 2], [9, 3, 1], 24, 1⟩

/-- The sub-box `k₀ ∈ {0, 1}` of the product window (slots with `k₀ = 2` are off the target). -/
def packedTestTarget3 : PackLayout := ⟨[0, 0, 0], [2, 3, 3], [9, 3, 1], 24, 1⟩

def packedTestA3 : List (CertKey × ℤ) :=
  [([0, 0, 0], 5), ([0, 1, 1], -3), ([1, 0, 1], 7), ([1, 1, 0], 2), ([0, 0, 1], 4)]

def packedTestB3 : List (CertKey × ℤ) :=
  [([0, 0, 0], -2), ([1, 1, 1], 6), ([0, 1, 0], 3), ([1, 0, 0], -7)]

def packedTestAdv3 : PackedAdvice :=
  ⟨packedTestLay3, packedTestLay3, packedTestTarget3, 4,
    [[-1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [-2, -3, 0, 0, 5, 2, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], 6⟩

theorem packedTest_pass3 :
    checkPackedProduct packedTestAdv3 [5, 4, 0, 0, -3, 0, 0, 0, 0, 0, 7, 0, 2, 0]
      [-2, 0, 0, 3, 0, 0, 0, 0, 0, -7, 0, 0, 0, 6] = true := by
  decide +kernel

theorem packedTest_mulPacked3 :
    (CertPoly.mulPacked (CertFixed.toMant 4) packedTestW 4 packedTestAdv3 packedTestBogus
      packedTestBogus packedTestBogus (packedTestRe packedTestA3)
      (packedTestRe packedTestB3)).isSome = true := by
  decide +kernel

/-! ### Positive: three blocks per factor (overlap-add over five windows) -/

/-- Keys `(-1..1, 0..1)`, row stride `3`, one row per block: three blocks per factor. -/
def packedTestLayM : PackLayout := ⟨[-1, 0], [3, 2], [3, 1], 24, 1⟩

def packedTestTargetM : PackLayout := ⟨[-2, 0], [5, 3], [3, 1], 24, 1⟩

def packedTestAM : List (CertKey × ℤ) :=
  [([-1, 0], 9), ([-1, 1], -2), ([0, 0], 4), ([0, 1], 13), ([1, 0], -6), ([1, 1], 1)]

def packedTestBM : List (CertKey × ℤ) :=
  [([-1, 0], -5), ([-1, 1], 8), ([0, 0], 3), ([0, 1], 2), ([1, 0], 10), ([1, 1], -7)]

def packedTestAdvM : PackedAdvice :=
  ⟨packedTestLayM, packedTestLayM, packedTestTargetM, 4,
    [[-3, 5, -1, 0, 0], [0, -1, 6, 0, 0], [8, -6, 3, 0, 0], [1, 6, -6, 0, 0], [-4, 3, 0, 0, 0]],
    0⟩

theorem packedTest_cutM :
    packedTestAdvM.cut [9, -2, 0, 4, 13, 0, -6, 1] = [[9, -2, 0], [4, 13, 0], [-6, 1, 0]] := by
  decide +kernel

theorem packedTest_passM :
    checkPackedProduct packedTestAdvM [9, -2, 0, 4, 13, 0, -6, 1] [-5, 8, 0, 3, 2, 0, 10, -7] =
      true := by
  decide +kernel

theorem packedTest_mulPackedM :
    (CertPoly.mulPacked (CertFixed.toMant 4) packedTestW 4 packedTestAdvM packedTestBogus
      packedTestBogus packedTestBogus (packedTestRe packedTestAM)
      (packedTestRe packedTestBM)).isSome = true := by
  decide +kernel

/-! ### Negative -/

/-- One advice slot off by `+2` (SO-REPLAY2's control). -/
def packedTestAdv2Off : PackedAdvice :=
  { packedTestAdv2 with
    rounded := [[1, -2, 1, 5, -4, 0, 0, 0, 0], [0, 7, -5, -4, 4, 0, 0, 0, 0],
      [0, -1, 7, 1, -1, 0, 0, 0, 0]] }

theorem packedTest_offByTwo :
    checkPackedProduct packedTestAdv2Off [3, -5, 7, 0, 0, 2, 11, -4]
      [6, 1, -9, 0, 0, -3, 8, 5] = false := by
  decide +kernel

/-- Advice packing to the same integer at `w = 24` (`+2^24` in one slot, `-1` in the next) but
outside the signed slot range: injectivity is essential, and `reconFits` rejects it. -/
def packedTestAdv2Alias : PackedAdvice :=
  { packedTestAdv2 with
    rounded := [[1, -2, 1, 3, -4, 0, 0, 0, 0], [0, 7 + 2 ^ 24, -5 - 1, -4, 4, 0, 0, 0, 0],
      [0, -1, 7, 1, -1, 0, 0, 0, 0]] }

theorem packedTest_alias_packs :
    packSum 24 [0, 7 + 2 ^ 24, -5 - 1, -4, 4, 0, 0, 0, 0] =
      packSum 24 [0, 7, -5, -4, 4, 0, 0, 0, 0] := by
  decide +kernel

theorem packedTest_alias_rejected :
    checkPackedProduct packedTestAdv2Alias [3, -5, 7, 0, 0, 2, 11, -4]
      [6, 1, -9, 0, 0, -3, 8, 5] = false := by
  decide +kernel

/-- A wrapping row stride (`4 < 3 + 3 - 1`). -/
def packedTestLayWrap : PackLayout := ⟨[0, -1], [2, 3], [4, 1], 24, 1⟩

theorem packedTest_wrap_compat :
    PackLayout.compat 2 packedTestLayWrap packedTestLayWrap = false := by
  decide +kernel

theorem packedTest_wrap_rejected :
    checkPackedProduct { packedTestAdv2 with la := packedTestLayWrap, lb := packedTestLayWrap }
      [3, -5, 7, 0, 2, 11, -4] [6, 1, -9, 0, -3, 8, 5] = false := by
  decide +kernel

/-- A decoder returning the wrong integer: `mantCheck` rejects, so the packed route fails. -/
theorem packedTest_wrongDecoder :
    CertPoly.mulPacked (fun P (a : CertFixed 4) => (CertFixed.toMant 4 P a).map (· + 1))
      packedTestW 4 packedTestAdv2 packedTestBogus packedTestBogus packedTestBogus
      (packedTestRe packedTestA2) (packedTestRe packedTestB2) = none := by
  decide +kernel

/-- A key outside the factor box: the layout rejects it, so the packed route fails. -/
theorem packedTest_keyOutside :
    CertPoly.mulPacked (CertFixed.toMant 4) packedTestW 4 packedTestAdv2 packedTestBogus
      packedTestBogus packedTestBogus (packedTestRe (([2, 0], 1) :: packedTestA2))
      (packedTestRe packedTestB2) = none := by
  decide +kernel

/-! ### P2 (F12): carry cancellation -/

/-- A two-slot layout at width `4`, two slots per block. -/
def packedTestLayP2 : PackLayout := ⟨[0], [2], [1], 4, 2⟩

/-- Audit 5's carry-cancelling advice `[16, -1, 0]` at `scale = 1`. -/
def packedTestAdvP2 : PackedAdvice :=
  ⟨packedTestLayP2, packedTestLayP2, ⟨[0], [3], [1], 4, 2⟩, 1, [[16, -1, 0]], 0⟩

theorem packedTest_P2_shape : packedTestAdvP2.shapeOK = true := by decide +kernel

/-- Without the guard the packed residual would decode: the carry cancels. -/
theorem packedTest_P2_decodes :
    intSlotsBound 4 3 (packedTestAdvP2.shardLogs 0)
      (shardPacked 4 [[0, 0]] [[0, 0]] 0 - ((2 ^ 1 : ℕ) : ℤ) * packShift 4 [16, -1, 0]) = true := by
  decide +kernel

theorem packedTest_P2_reconFits :
    reconFits 4 1 (packedTestAdvP2.shardLogs 0) [16, -1, 0] = false := by
  decide +kernel

theorem packedTest_P2_rejected :
    checkShard packedTestAdvP2 [[0, 0]] [[0, 0]] 0 = false ∧
      checkPackedProduct packedTestAdvP2 [0, 0] [0, 0] = false := by
  decide +kernel

/-! ### P3 (F13, positive): two overlapping windows attain `2^scale` -/

/-- Audit 6's control: `L = 2`, `w = 8`, factors `[1, 1, 0, 0]` and `[1, 1, 1, 0]`. -/
def packedTestLayP3 : PackLayout := ⟨[0], [4], [1], 8, 2⟩

def packedTestAdvP3 : PackedAdvice :=
  ⟨packedTestLayP3, packedTestLayP3, ⟨[0], [7], [1], 8, 2⟩, 1,
    [[0, 1, 0], [0, 0, 0], [0, 0, 0]], 0⟩

theorem packedTest_P3_passes :
    checkPackedProduct packedTestAdvP3 [1, 1, 0, 0] [1, 1, 1, 0] = true := by
  decide +kernel

/-- The combined error at slot two is exactly `2 = 2^scale`: the bound is attained. -/
theorem packedTest_P3_attained :
    (listConv [1, 1, 0, 0] [1, 1, 1, 0]).getD 2 0 - 2 ^ 1 * packedTestAdvP3.combined.getD 2 0 = 2 :=
  by decide +kernel

theorem packedTest_P3_bound :
    |(listConv [1, 1, 0, 0] [1, 1, 1, 0]).getD 2 0 - 2 ^ 1 * packedTestAdvP3.combined.getD 2 0|
      ≤ 2 ^ 1 :=
  ((checkPackedProduct_sound packedTest_P3_passes).2 2 (by decide +kernel)).1 (by decide +kernel)

/-! ### P4 (F13, negative): scale zero -/

/-- Audit 5's blocks `A = [[1,1],[0,0]]`, `B = [[1,1],[1,0]]` at `scale = 0`, `w = 8`, advice
`[1,2,0], [0,1,0], [0,0,0]`. -/
def packedTestAdvP4 : PackedAdvice :=
  ⟨packedTestLayP3, packedTestLayP3, ⟨[0], [7], [1], 8, 2⟩, 0,
    [[1, 2, 0], [0, 1, 0], [0, 0, 0]], 0⟩

/-- Every window meets `2^(0-1) = 1`: each shard passes on its own. -/
theorem packedTest_P4_shards :
    ∀ s < 3, checkShard packedTestAdvP4 [[1, 1], [0, 0]] [[1, 1], [1, 0]] s = true := by
  decide +kernel

theorem packedTest_P4_rejected :
    checkPackedProduct packedTestAdvP4 [1, 1, 0, 0] [1, 1, 1, 0] = false :=
  checkPackedProduct_scale_zero rfl _ _

/-- The combined error at slot two is `2 > 2^0`: accepting scale zero would be unsound. -/
theorem packedTest_P4_error :
    (listConv [1, 1, 0, 0] [1, 1, 1, 0]).getD 2 0 - 2 ^ 0 * packedTestAdvP4.combined.getD 2 0 = 2 :=
  by decide +kernel

/-! ### P5 (F14): the padding alias -/

/-- A two-slot layout (`denseLen = blockLen = 2`), `w = 8`, `scale = 1`, full three-slot target,
advice `[[0, 0, 0]]`. -/
def packedTestAdvP5 : PackedAdvice :=
  ⟨⟨[0], [2], [1], 8, 2⟩, ⟨[0], [2], [1], 8, 2⟩, ⟨[0], [3], [1], 8, 2⟩, 1, [[0, 0, 0]], 0⟩

theorem packedTest_P5_sameBlocks :
    packedTestAdvP5.cut [0] = [[0, 0]] ∧ packedTestAdvP5.cut [0, 0] = [[0, 0]] := by
  decide +kernel

theorem packedTest_P5_long : checkPackedProduct packedTestAdvP5 [0, 0] [0, 0] = true ∧
    packedTestAdvP5.combined = [0, 0, 0] ∧ (listConv [0, 0] [0, 0]).length = 3 := by
  decide +kernel

theorem packedTest_P5_short : checkPackedProduct packedTestAdvP5 [0] [0] = false :=
  checkPackedProduct_raw_length (Or.inl (by decide +kernel))

theorem packedTest_P5_short_kernel : checkPackedProduct packedTestAdvP5 [0] [0] = false := by
  decide +kernel

end KAM.Certificate
