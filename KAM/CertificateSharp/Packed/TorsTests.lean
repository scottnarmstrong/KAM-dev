/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsBase
public import KAM.CertificateSharp.Packed.GramTests

/-!
# Small kernel tests of the packed torsion stage (default build, cheap)

The identity embedding of `T²` (`DK = (I; 0)`, `D²K = 0`), the witness `B = I` with radius `0`, the
jet slots of `H = ω·I + |I|²/2` at `I = 0` (`DX_H = [[0, I], [0, 0]]`, `DH = (0, ω)`), `ω = (1, 0)`,
`s = 1`: the bordered torsion is `[[I, s ω], [ωᵀ, 0]]` and its exact inverse is the witness. The
core passes with the bound `3` (the witness' row sum is `2`) and fails with `1`. The book is
`python3 -I scripts/packed/tors_gate_gen.py --toy`; the LG00-sized gate is the same script (opt-in).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.TorsTests

open KAM KAM.Certificate KAM.CertificateSharp.Packed KAM.CertificateSharp.Packed.GramTests

def tTb : PTorsBook where
  P := 64
  L1 := ⟨[-1, -1], [3, 3], [15, 1], 560, 1⟩
  LB := ⟨[-1, -1], [3, 3], [15, 1], 560, 1⟩
  LA := ⟨[-1, -1], [3, 3], [15, 1], 560, 1⟩
  LU0 := ⟨[0, 0], [1, 1], [15, 1], 560, 1⟩
  LU1 := ⟨[-3, -3], [7, 7], [15, 1], 560, 1⟩
  LU2 := ⟨[-2, -2], [5, 5], [15, 1], 560, 1⟩
  bK := 2 ^ 65
  bB := 2 ^ 65
  bD := 2 ^ 0
  bA := 2 ^ 65
  bF := 2 ^ 65
  q := 8
  lK := 66
  lB := 66
  lD := 1
  lA := 66
  lDL := 68
  lN := 138
  lDG := 142
  lC := 214
  lDGi := 286
  lXN := 410

/-- The constant `1` at scale `2^64`. -/
def e1 : MemoEntry := ([([0, 0], 2 ^ 64)], [], 0)

def e0 : MemoEntry := ([], [], 0)

/-- `D²K = 0`; `DX_H` has `1` at `(0, 2)` and `(1, 3)`; `DH` has `ω₁ = 1` at `2`. -/
def tTm : PTorsMemo where
  d2 := List.replicate 16 e0
  ax := [e0, e0, e1, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0]
  d1 := [e0, e0, e1, e0]

def tBox : FreqBox := [(1, 0), (0, 0)]

/-- An exact real constant at scale `2^64`. -/
def cc (v : ℤ) : CC F64 := ⟨⟨v * 2 ^ 64⟩, ⟨0⟩⟩

/-- The exact inverse of `[[1, 0, 1], [0, 1, 0], [1, 0, 0]]`. -/
def tS : List (List (CC F64)) := [[cc 0, cc 0, cc 1], [cc 0, cc 1, cc 0], [cc 1, cc 0, cc (-1)]]

example : torsPackedCore 2 tB tW tCfg tBox 1 tTb tMemo tTm ⟨0⟩ tS 3 = true := by decide +kernel
example : torsPackedCore 2 tB tW tCfg tBox 1 tTb tMemo tTm ⟨0⟩ tS 1 = false := by decide +kernel

end KAM.CertificateSharp.Packed.TorsTests
