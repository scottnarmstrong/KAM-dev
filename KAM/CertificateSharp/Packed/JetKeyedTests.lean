/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetKeyed
public import KAM.CertificateSharp.Packed.JetTests

/-!
# Small kernel tests of the keyed chain (default build, cheap)

The toy program, book and arithmetic of `JetTests.lean`. Block `0` computes the constants `1`
(slot `0`) and `3` (slot `4`) on the one-slot layout; block `1` imports both and computes their
product (slot `5`, scale `2^128`). The nodes are on one ledger, the blocks give keys only, and the
order certificate names block `0` for both imports of block `1`.

The chain passes; it fails with an order certificate that names a later block, with a ledger
radius below the computed one, and with a wanted slot that no block exports.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.JetKeyedTests

open KAM KAM.Certificate KAM.CertificateSharp.Packed KAM.CertificateSharp.Packed.JetTests

/-- An empty embedding (the toy blocks read no embedding data). -/
def kK : CertEmbedding F := ⟨[], [], [], []⟩

/-- The ledger: the constants `1` and `3` and their product. The norm bound of slot `5` is
`d` (exactly `3` is the computed one). -/
def kL (d : ℚ) : JLedger :=
  [(slotK 0, ⟨true, 2 ^ 66, 64, ⟨2 ^ 64, 0⟩, 0, 1⟩), (slotK 4, ⟨true, 2 ^ 66, 64, ⟨3 * 2 ^ 64, 0⟩, 0, 3⟩),
    (slotK 5, ⟨true, 2 ^ 133, 128, ⟨3 * 2 ^ 128, 0⟩, 0, d⟩)]

def kB : List KBlock :=
  [.seg 0 [] [(0, 0, 0), (4, 0, 0)] [0, 4], .seg 5 [0, 4] [(5, 0, 0)] [5]]

example : jetChainOk 2 tW tPe tCfg tJb kK tP (kL 3) kB [[], [0, 0]] [5] = true := by
  decide +kernel

/-- An import certified by a block that is not earlier. -/
example : jetChainOk 2 tW tPe tCfg tJb kK tP (kL 3) kB [[], [1, 0]] [5] = false := by
  decide +kernel

/-- A ledger norm bound below the computed one. -/
example : jetChainOk 2 tW tPe tCfg tJb kK tP (kL 2) kB [[], [0, 0]] [5] = false := by
  decide +kernel

/-- A wanted slot that no block exports. -/
example : jetChainOk 2 tW tPe tCfg tJb kK tP (kL 3) kB [[], [0, 0]] [3] = false := by
  decide +kernel

/-- The canonical key: the partial sum of degree `0` reads the Taylor term of degree `0`. -/
example : canonKey (.inr (.sum 1 true 0)) = .inr (.term 1 true 0) := rfl

example : canonKey (.inr (.sum 1 true 2)) = .inr (.sum 1 true 2) := rfl

end KAM.CertificateSharp.Packed.JetKeyedTests
