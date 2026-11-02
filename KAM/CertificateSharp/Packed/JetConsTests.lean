/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetBase
public import KAM.CertificateSharp.Packed.TorsRTests

/-!
# Small kernel tests of the consumers of the packed jet (default build, cheap)

The toy integrable case of `TorsRTests` (identity embedding, `B = I`, `D²K = 0`, `ω = (1, 0)`,
`s = 1`, box of half-width `1`), now with `DX_H ∘ K` and `DH ∘ K` read from jet slots: the toy jet
`tJ` has `∂_a H` at slot `a` and `∂_a ∂_b H` at slot `4 + 4a + b`, and `H ∘ K` at slot `20`. The
slot values `tJs` are those of `H = ω · I` on `K`: `∂_{I₁} H = 1` (slot `2`) and
`∂_{I₁} ∂_{I₁} H`, `∂_{I₂} ∂_{I₂} H` read as `DX_H = [[0, I], [0, 0]]` (slots `14`, `19`), every
other slot `0`, every radius `0`.

* the torsion core passes with the bound `3` and fails with `1`;
* the invariance error `X_H ∘ K - DK ω` is `0`: every coordinate passes with `err = 1/1000`; a jet
  value `∂_{I₁} H = 2` fails coordinate `0`;
* the energy: `⟨H ∘ K⟩ = 0` passes with `E₀ = 0` and fails with `E₀ = 1`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.JetConsTests

open KAM KAM.Certificate KAM.CertificateSharp.Packed KAM.CertificateSharp.Packed.GramTests
  KAM.CertificateSharp.Packed.TorsTests KAM.CertificateSharp.Packed.TorsRTests

/-- The toy jet: `v0 = 20`, `d1 = [0, 1, 2, 3]`, `d2[a][b] = 4 + 4a + b`. -/
def tJ : HamJet where
  prog := ⟨[]⟩
  v0 := 20
  d1 := [0, 1, 2, 3]
  d2 := [[4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15], [16, 17, 18, 19]]
  d3 := []

/-- The constant `v` at scale `2^64` on the toy box. -/
def u (v : ℤ) : PC := pcUnit tRb.Lb.width (zslot 2 tRb.Lb) (v * 2 ^ 64)

/-- The toy slot values, with `∂_{I₁} H = d` at slot `2`. -/
def tJs (d : ℤ) : JSlots F64 :=
  ⟨fun i => if i == 2 then u d else if i == 14 || i == 19 then u 1 else ⟨0, 0⟩, fun _ => ⟨0⟩,
    fun _ => ⟨2 ^ 65⟩⟩

example : torsRCoreJ 2 tB tW tCfg tBox 1 tJ (tJs 1) tRb tMemo tTm tRm ⟨0⟩ tS 3 = true := by
  decide +kernel
example : torsRCoreJ 2 tB tW tCfg tBox 1 tJ (tJs 1) tRb tMemo tTm tRm ⟨0⟩ tS 1 = false := by
  decide +kernel

/-- The invariance book on the toy box. -/
def tIb : PIBook := ⟨64, tRb.Lb, tRb.LU0, 2 ^ 65, 2 ^ 65, 2 ^ 65, 8, 66, 133⟩

example : ivGuard 2 tW tBox 1 tIb tMemo = true := by decide +kernel
example : ((List.range 4).all fun a => ivRowOk 2 tW tBox 1 tJ (tJs 1) tIb tMemo (1 / 1000) a) =
    true := by decide +kernel
example : ivRowOk 2 tW tBox 1 tJ (tJs 2) tIb tMemo (1 / 1000) 0 = false := by decide +kernel

example : enGuard 2 tIb = true := by decide +kernel
example : enOk 2 tJ (tJs 1) tIb 0 (1 / 1000) = true := by decide +kernel
example : enOk 2 tJ (tJs 1) tIb 1 (1 / 1000) = false := by decide +kernel

end KAM.CertificateSharp.Packed.JetConsTests
