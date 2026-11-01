/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsRBase
public import KAM.CertificateSharp.Packed.TorsTests

/-!
# Small kernel tests of the rounded packed torsion stage (default build, cheap)

The toy integrable case of `TorsTests` (identity embedding, `B = I`, `D²K = 0`,
`DX_H = [[0, I], [0, 0]]`, `DH = (0, ω)`, `ω = (1, 0)`, `s = 1`) on a box of half-width `1`: the
nodes are exact (`N = X_N = (I; 0)`, the others `0`), the averages `T = I`, `Y = ω`. The core passes
with the bound `3` and fails with `1`. The book and the memo are
`python3 -I scripts/packed/torsr_gate_gen.py --toy`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.TorsRTests

open KAM KAM.Certificate KAM.CertificateSharp.Packed KAM.CertificateSharp.Packed.GramTests
  KAM.CertificateSharp.Packed.TorsTests

def tRb : PRBook where
  P := 64
  Lb := ⟨[-1, -1], [3, 3], [5, 1], 168, 1⟩
  Lu := ⟨[-1, -1], [3, 3], [5, 1], 168, 1⟩
  LU0 := ⟨[0, 0], [1, 1], [5, 1], 168, 1⟩
  bK := 2 ^ 65
  bB := 2 ^ 65
  bD := 2 ^ 0
  bA := 2 ^ 65
  bF := 2 ^ 65
  bR := 2 ^ 66
  aW := 566229858556441603203055346766462303862784
  aL := 147573952589676412928
  q := 8
  lK := 66
  lB := 66
  lD := 1
  lA := 66
  lR := 67
  lW := 139
  lL := 132

/-- The node entry `1` (scale `2^64`, radius `0`, norm bound `1`) and the zero entry. -/
def nI : NodeEntry := ([([0, 0], 2 ^ 64)], [], 0, 1)

def n0 : NodeEntry := ([], [], 0, 0)

def tRm : PRMemo where
  N := [[nI, n0], [n0, nI], [n0, n0], [n0, n0]]
  DL := List.replicate 4 [n0, n0]
  DG := List.replicate 2 [n0, n0]
  C := List.replicate 2 [n0, n0]
  DGi := List.replicate 2 [n0, n0]
  DN := List.replicate 4 [n0, n0]
  XN := [[nI, n0], [n0, nI], [n0, n0], [n0, n0]]
  CT := [[(1, 0), (0, 0)], [(0, 0), (1, 0)]]
  RT := [[0, 0], [0, 0]]
  CY := [(1, 0), (0, 0)]
  RY := [0, 0]

example : torsRCore 2 tB tW tCfg tBox 1 tRb tMemo tTm tRm ⟨0⟩ tS 3 = true := by decide +kernel
example : torsRCore 2 tB tW tCfg tBox 1 tRb tMemo tTm tRm ⟨0⟩ tS 1 = false := by decide +kernel

end KAM.CertificateSharp.Packed.TorsRTests
