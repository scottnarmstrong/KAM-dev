/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Facts

/-!
# Stage memoization for the ℓ¹ check of route A with the ℓ¹ entry

`checkL1Claim` (`V2/RouteAL1Facts.lean`) recomputes, on its own strips, the models the landed
checks build: `dkModels`, the Gram certificate and `frameNModels`, `torsionModels`, and the
composition of `checkInvariance`. These equation lemmas reduce each of its four model checks to
its residual, the `l1Up` sums of literal models, given the memoized stages of `Kernel/Stage.lean`
(each stage a literal proved by its own kernel run), exactly as `checkFrameN_eq_of` and
`checkFrameT_eq_of` do for the frame majorants:

* `checkL1L_eq_of`: `dkModels` memoized;
* `checkL1N_eq_of`: the Gram certificate, its radius and `frameNModels` memoized;
* `checkL1T_eq_of`: the Gram certificate and `torsionModels` memoized;
* `checkL1E_eq_of`: the composition of the first derivatives along `K` (`cfgFull`) memoized;
* `checkL1Claim_of`: the check from its eight conjuncts.

Computation-only: no landed definition changes.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.L1

open KAM KAM.Certificate KAM.CertificateSharp CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- `checkL1L` with `dkModels` memoized. -/
theorem checkL1L_eq_of {c : TorusCertificate n α} {L : L1Claim} {Lm : ModelMatrix α}
    (hL : dkModels n c.emb c.weight c.piEnc = Lm) :
    checkL1L c L =
      (sumsOk (n := n) (fun a j => l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
          (modelMatrixEntry Lm a j)) L.aLt true &&
        sumsOk (n := n) (fun a j => l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
          (modelMatrixEntry Lm a j)) L.nuK false) := by
  simp only [checkL1L, hL]

/-- `checkL1N` with the Gram certificate, its radius and `frameNModels` memoized. -/
theorem checkL1N_eq_of {c : TorusCertificate n α} {L : L1Claim} {δβ : α × α} {eps : α}
    {M : ModelMatrix α}
    (hg : gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ) =
      some δβ)
    (he : gramInvRadius δβ = some eps)
    (hM : frameNModels n c.emb c.gramInv eps c.weight c.cfgLow c.piEnc = M) :
    checkL1N c L =
      (sumsOk (n := n) (fun a j => l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
          (modelMatrixEntry M a j)) L.aNt true &&
        sumsOk (n := n) (fun a j => l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
          (modelMatrixEntry M a j)) L.nuN false) := by
  simp only [checkL1N, frameGram, hg, he, hM]

/-- `checkL1T` with the Gram certificate and `torsionModels` memoized. -/
theorem checkL1T_eq_of {c : TorusCertificate n α} {L : L1Claim} {δβ : α × α} {T : ModelMatrix α}
    (hg : gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ) =
      some δβ)
    (ht : torsionModels n c.ham c.emb c.wit c.gramInv δβ c.freqBox c.params.s c.weight c.cfgLow
      c.piEnc = some T) :
    checkL1T c L = (List.finRange n).all fun i =>
      ble (sumUp (fun j : Fin n => l1Up L.WT (cothPowUp n (c.params.rho - L.WT.rho))
        (modelMatrixEntry T i.val j.val)) (List.finRange n)) (ofRatDown L.t1) := by
  simp only [checkL1T, frameGram, hg, ht]

/-- `checkL1E` with the composition of `checkInvariance` memoized. -/
theorem checkL1E_eq_of {c : TorusCertificate n α} {L : L1Claim} {ms : List (CertModel α)}
    (hms : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms) :
    checkL1E c L = (List.finRange (n + n)).all fun a =>
      ble (l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
        (invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms a.val))
        (ofRatDown L.aE) := by
  simp only [checkL1E, hms]

/-- **Sharding**: `checkL1Claim` from its eight conjuncts. -/
theorem checkL1Claim_of {c : TorusCertificate n α} {L : L1Claim}
    (hW1 : checkWeight L.W1 c.expHalvings c.expOrder = true)
    (hWT : checkWeight L.WT c.expHalvings c.expOrder = true) (h1 : L.W1.rho < c.params.rho)
    (hT : L.WT.rho < c.params.rho) (hL : checkL1L c L = true) (hN : checkL1N c L = true)
    (hTo : checkL1T c L = true) (hE : checkL1E c L = true) : checkL1Claim c L = true := by
  simp only [checkL1Claim, hW1, hWT, hL, hN, hTo, hE, decide_eq_true h1, decide_eq_true hT,
    Bool.and_self]

end KAM.CertificateSharp.V2.L1

end
