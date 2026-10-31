/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.LunarAssemblyV2

/-!
# Literal format of the generated lunar data (track SO, SO-DATA-2; v2 backend, SO-DATA3)

The generated modules `KAM/SpinOrbit/Data/{Lower,Upper}/*` (emitted by
`scripts/spin_orbit/sofx_lean.py`, design §7.2 option A) write

* a Fourier term of the backend `SoBackendV2` as the row `tm k₀ k₁ re im` (mantissas at `2^{-96}`);
* an advice window as a run-length coded token list, decoded by `unzero` (a zero is followed by
  its run length);
* a long natural number as decimal chunks of `80` digits (`natChunks`).

The data are untrusted: the checker checks whatever these functions denote.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data

open KAM.Certificate

/-- The term `(k₀, k₁) ↦ re + i im` of a polynomial over `SoBackendV2` (mantissas). -/
def tm (k₀ k₁ re im : ℤ) : CertKey × CC SoBackendV2 := ([k₀, k₁], ⟨⟨re⟩, ⟨im⟩⟩)

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

end KAM.SpinOrbit.Data
