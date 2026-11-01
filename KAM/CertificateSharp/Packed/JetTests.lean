/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetIngest

/-!
# Small kernel tests of a packed jet segment (default build, cheap)

`n = 2`, the box of half-width `1` (`3 × 3`, row stride `5`, slots of `200` bits), its window
(`5 × 5`, the box at the offset `6`) and the one-slot layout, at `CertFixed 64`. The imported
slots `0` and `1` are the constant `1` and the character `e^{i θ₀}` at scale `2^64`
(zero slot `6`, key `(1, 0)` at slot `11`). Slot `2 = add 0 1` and slot `3 = mul 0 1`: the
product lives on the window at scale `2^128` and is reduced in the kernel to the box at `2^64`
(the candidate is computed by `zPC` and validated by `boxOk`; the residual is `0`).

The segment passes with the exact exports, and fails with a digit off by one or with a rounding
shift above `smax`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.JetTests

open KAM KAM.Certificate KAM.CertificateSharp.Packed

abbrev F := CertFixed 64

def tW : CertWeight := ⟨1 / 10, 2⟩

def tJb : JBook where
  Lb := ⟨[-1, -1], [3, 3], [5, 1], 200, 1⟩
  LU0 := ⟨[0, 0], [1, 1], [5, 1], 200, 1⟩
  Lw := ⟨[-2, -2], [5, 5], [5, 1], 200, 1⟩
  q := 8
  lb := 66
  lr := 141
  lrb := 141
  ln := 67
  aW := 2 ^ 140
  aB := 2 ^ 140
  smax := 64
  ls := 140
  lsb := 140
  off := 6
  P := 64
  aC := 2 ^ 66
  lc := 67
  lrc := 141
  lnc := 67

/-- A π enclosure and a configuration (not used by the checks below, which have no constant of
nonzero degree). -/
def tPe : PiEnclosure F := ⟨⟨0⟩, ⟨0⟩, 1, 1⟩

def tCfg : ModelConfig F := ⟨24, 30, 12, CertFixed.toMant 64, []⟩

def tP : Slp := ⟨[.const 1 0 0, .const 0 0 0, .add 0 1, .mul 0 1, .const 3 0 0, .mul 0 4]⟩

/-- The constant `1` and the character of key `(1, 0)` at scale `2^64`. -/
def nOne : JNode F := ⟨false, 2 ^ 65, 64, ⟨2 ^ 64 * 2 ^ (200 * 6), 0⟩, ⟨0⟩, ⟨2 ^ 64⟩⟩

def nChi : JNode F := ⟨false, 2 ^ 65, 64, ⟨2 ^ 64 * 2 ^ (200 * 11), 0⟩, ⟨0⟩, ⟨2 ^ 64⟩⟩

def tImports : List (ℕ × JNode F) := [(0, nOne), (1, nChi)]

def tSteps : List JStep := [(2, 0, 0), (3, 64, 0)]

def tExports (d : ℤ) : List (ℕ × JNode F) :=
  [(2, ⟨false, 2 ^ 66, 64, ⟨2 ^ 64 * 2 ^ (200 * 6) + 2 ^ 64 * 2 ^ (200 * 11), 0⟩, ⟨0⟩,
      ⟨2 ^ 66⟩⟩),
    (3, ⟨false, 2 ^ 66, 64, ⟨(2 ^ 64 + d) * 2 ^ (200 * 11), 0⟩, ⟨0⟩, ⟨2 ^ 70⟩⟩)]

example : jBookOk 2 tW tJb = true := by decide +kernel

/-- A constant (slot `4`, on the one-slot layout) and the product of slot `0` by it (slot `5`,
on the box at scale `2^128`). -/
example : jSegOk 2 tW tPe tCfg tJb tP 0 tImports [(4, 0, 0), (5, 0, 0)]
    [(5, ⟨false, 2 ^ 132, 128, ⟨3 * 2 ^ 128 * 2 ^ (200 * 6), 0⟩, ⟨2 ^ 70⟩, ⟨2 ^ 70⟩⟩)] = true := by
  decide +kernel

example : jSegOk 2 tW tPe tCfg tJb tP 0 tImports tSteps (tExports 0) = true := by decide +kernel

/-- A digit off by one. -/
example : jSegOk 2 tW tPe tCfg tJb tP 0 tImports tSteps (tExports 1) = false := by decide +kernel

/-- A rounding shift of `128 > smax`. -/
example : jSegOk 2 tW tPe tCfg tJb tP 0 tImports [(2, 0, 0), (3, 0, 0)] (tExports 0) = false := by
  decide +kernel

/-- Ingestion: the `3 × 3` box digits `1, -2, 3; 0, 0, 0; -8, 7, 1` at `5` bits spread to the
slots of width `200` (`9 ≤ 2^4` digits) and to rows of stride `5` (`3 ≤ 2^2` rows). -/
example : jSpread 3 3 5 200 5 4 2 19491115781585 =
    1 - 2 * 2 ^ (200 * 1) + 3 * 2 ^ (200 * 2) - 8 * 2 ^ (200 * 10) + 7 * 2 ^ (200 * 11) +
      2 ^ (200 * 12) := by
  decide +kernel

end KAM.CertificateSharp.Packed.JetTests
