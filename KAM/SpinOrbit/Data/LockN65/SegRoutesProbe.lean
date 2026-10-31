/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.Certificate.Arith.Rat

/-!
# Probe of the lock's memo routes on toy data (LOCK-DATA, B1)

The `inv` and `sqrt` arms of `composeStep` on the exact rational toy of `Tests/Sqrt` (`n = 1`), proved
through `composeStep_inv_eq` / `invWitnessRadius_eq_of_delta` (with the product rewritten by
`CertModel.mul_eq_of_polyProduct`) and `composeStep_sqrt_eq` / `sqrtWitnessRadius_eq_of_residual`,
the Boolean checks kernel computations (the toy's lookups and product by `rfl`: `CC ℚ` has no `DecidableEq`).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate CertArith

/-! ### Toy data (copied from `Tests/Sqrt`, whose bodies are not exposed) -/

def sqrtToyW : CertWeight := ⟨1 / 100, 11 / 10⟩
def sqrtToyPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩
def sqrtToyCfg : ModelConfig ℚ := ⟨100, 10, 4, fun _ _ => none, []⟩
def sqrtToyCos (c a : ℚ) : CertRealPoly ℚ := ⟨c, [([1], ⟨a / 2, 0⟩)]⟩
def sqrtToyK : CertEmbedding ℚ := ⟨[-1], [sqrtToyCos 0 (1 / 10)], [0], [sqrtToyCos 1 (1 / 100)]⟩
def sqrtTestWit (w anchor : ℚ) : SqrtWitness ℚ := ⟨⟨[([0], ⟨w, 0⟩)]⟩, anchor, 1 / 10⟩

/-- The state after the slot `4`. -/
def probeSt : ComposeState ℚ :=
  (⟨[], 0, 0, 0, []⟩ : ComposeState ℚ).pushSlot sqrtToyW (constModel 1 4 0 0)

/-- The inverse witness `1/4`. -/
def probeQ : CertPoly ℚ := ⟨[([0], ⟨1 / 4, 0⟩)]⟩

/-- The witnesses: one inverse, the square root of slot `0` keyed at slot `1`. -/
def probeWit : Witnesses ℚ := ⟨[], [probeQ], [], [(1, sqrtTestWit 2 2)]⟩

theorem probe_inv :
    composeStep 1 sqrtToyK probeWit sqrtToyW sqrtToyCfg sqrtToyPi probeSt (.inv 0) =
      some { probeSt.pushSlot sqrtToyW ⟨-(probeSt.slot sqrtToyW 0).1.deg, probeQ,
        upMul (upMul (probeQ.supNormUp sqrtToyW) 0) 1⟩ with nInv := probeSt.nInv + 1 } :=
  composeStep_inv_eq 1 sqrtToyK probeWit sqrtToyW sqrtToyCfg sqrtToyPi probeSt 0 rfl
    (invWitnessRadius_eq_of_delta 1 sqrtToyW _ _ probeQ
      (by
        rw [CertModel.mul_eq_of_polyProduct _ _ _ _ _ (out := (directItems probeQ.terms
          (probeSt.slot sqrtToyW 0).1.poly.terms, ofInt 0)) rfl]
        decide +kernel)
      (by decide +kernel) (by decide +kernel))

theorem probe_sqrt :
    composeStep 1 sqrtToyK probeWit sqrtToyW sqrtToyCfg sqrtToyPi probeSt (.sqrt 0) =
      some (probeSt.pushSlot sqrtToyW ⟨0, (sqrtTestWit 2 2).poly,
        upMul 0 (ofRatUp (1 / ((sqrtTestWit 2 2).anchor - (sqrtTestWit 2 2).margin)))⟩) :=
  composeStep_sqrt_eq 1 sqrtToyK probeWit sqrtToyW sqrtToyCfg sqrtToyPi probeSt 0 (i := 1) rfl
    (sqrtWitnessRadius_eq_of_residual 1 sqrtToyW _ _ _ (by decide +kernel) (by decide +kernel))

end KAM.SpinOrbit.Data.LockN65
