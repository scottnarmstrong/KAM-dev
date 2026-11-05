/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Mantissa
public import KAM.Certificate.Defs

/-!
# Literal format of the generated `N = 65` lock data (LOCK-DATA)

The generated modules `KAM/SpinOrbit/Data/LockN65/*` (emitted by `scripts/spin_orbit/lock_lean.py`)
use the backend `LockBackend = CertFixed 112` and write

* a Fourier term as the row `tm k₀ k₁ re im` (mantissas at `2^{-112}`);
* an advice window as a run-length coded token list, decoded by `unzero` (a zero is followed by
  its run length);
* a long natural number as decimal chunks of `80` digits (`natChunks`).

The data are untrusted: the checker checks whatever these functions denote.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate

/-- The fixed-point precision of the lock certificate. -/
abbrev lockPrecision : ℕ := 112

/-- The backend of the lock certificate. -/
abbrev LockBackend : Type := CertFixed lockPrecision

/-- The term `(k₀, k₁) ↦ re + i im` of a polynomial over `LockBackend` (mantissas). -/
def tm (k₀ k₁ re im : ℤ) : CertKey × CC LockBackend := ([k₀, k₁], ⟨⟨re⟩, ⟨im⟩⟩)

/-- The run-length decoder of advice windows: `0, n` stands for `n` zeros. -/
def unzero : List ℤ → List ℤ
  | [] => []
  | 0 :: n :: t => List.replicate n.toNat 0 ++ unzero t
  | v :: t => v :: unzero t

/-- The natural number with decimal chunks `cs` (every chunk after the first has `80` digits). -/
def natChunks (cs : List ℕ) : ℕ := cs.foldl (fun a c => a * 10 ^ 80 + c) 0

/-- The rational `± a / b`. -/
def ratOf (neg : Bool) (a b : ℕ) : ℚ := mkRat (if neg then -(a : ℤ) else a) b

theorem unzero_test : unzero [5, 0, 3, -2] = [5, 0, 0, 0, -2] := by decide +kernel

end KAM.SpinOrbit.Data.LockN65
