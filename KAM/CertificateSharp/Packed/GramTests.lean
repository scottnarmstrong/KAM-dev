/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Gram

/-!
# Small kernel tests of the packed Gram stage (default build, cheap)

The identity embedding of `T²` (no angle or action terms, so `DK = (I; 0)` and `G = I`), the witness
`B = I` at `CertFixed 64`, on `3 × 3` boxes of stride `7`: the boundary entries and the core pass,
and the core fails when the bound `σ` is too small. The LG00-sized gate is
`scripts/packed/gram_gate_gen.py` (opt-in).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.GramTests

open KAM KAM.Certificate KAM.CertificateSharp.Packed

def tK : CertEmbedding F64 := ⟨[0, 0], [], [0, 0], []⟩

def one64 : CC F64 := ⟨⟨2 ^ 64⟩, ⟨0⟩⟩

def tB : List (List (CertPoly F64)) :=
  [[⟨[([0, 0], one64)]⟩, ⟨[]⟩], [⟨[]⟩, ⟨[([0, 0], one64)]⟩]]

def tW : CertWeight := ⟨1 / 10, 2⟩

def tCfg : ModelConfig F64 := ⟨24, 30, 12, CertFixed.toMant 64, []⟩

def tPe : PiEnclosure F64 := ⟨⟨57952155664616982739⟩, ⟨1000⟩, 5, 2⟩

def tL : PackLayout := ⟨[-1, -1], [3, 3], [7, 1], 260, 1⟩

def tBk : PGramBook := ⟨64, tL, tL, 2 ^ 64, 2 ^ 64, 8, 65, 65, 210⟩

/-- The memo of `DK = (I; 0)`: the angle rows carry `1` on the diagonal, the action rows nothing. -/
def tMemo : PGramMemo :=
  ⟨[[[([0, 0], 2 ^ 64)], []], [[], [([0, 0], 2 ^ 64)]], [[], []], [[], []]],
    [[[], []], [[], []], [[], []], [[], []]], [[0, 0], [0, 0], [0, 0], [0, 0]]⟩

example : pgEntries 2 tK tW tCfg tPe tBk tMemo = true := by decide +kernel
example : (gramPackedCore 2 tB tW tCfg tBk tMemo 2).isSome = true := by decide +kernel
example : (gramPackedCore 2 tB tW tCfg tBk tMemo (1 / 2)).isSome = false := by decide +kernel

end KAM.CertificateSharp.Packed.GramTests
