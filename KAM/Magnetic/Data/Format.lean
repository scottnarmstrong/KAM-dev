/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.Params

/-!
# Magnetic data format

The term constructor of the generated magnetic data over `MagBackend`, the run-length decoder of advice windows
and the chunked naturals (copies of `KAM.SpinOrbit.Data.Format`'s helpers, so that the magnetic application does
not require the lunar band's library).
-/

@[expose] public section

namespace KAM.Magnetic.Data

open KAM.Certificate

/-- The term `(k₀, k₁) ↦ re + i im` of a polynomial over `MagBackend` (mantissas). -/
def tm (k₀ k₁ re im : ℤ) : CertKey × CC MagBackend := ([k₀, k₁], ⟨⟨re⟩, ⟨im⟩⟩)

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

end KAM.Magnetic.Data

end
