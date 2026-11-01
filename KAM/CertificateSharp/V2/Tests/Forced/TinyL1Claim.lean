/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram
public import KAM.CertificateSharp.V2.Tests.Forced.TinyL1HybData
public import KAM.CertificateSharp.Kernel.StageL1

/-!
# The ℓ¹ claim of the forced toy `Tiny` from its own models (the cheap part)

The literal `msF` (the composition of the first derivatives of `H` along `K` at the full stage,
`checkInvariance`'s) is re-proved by its own kernel run (`msF_eq`); with it and the Gram stages of
`TinyGram`, the ℓ¹ checks of `L = DK`, `N` and the invariance error reduce to their residuals
(`Kernel/StageL1.lean`): `l1L_ok`, `l1N_ok`, `l1E_ok` on the strip `ρ' = 1/10`, and the guards
of `checkL1Claim` (`l1W1_ok`, `l1WT_ok`). The torsion part (`checkL1T`, through every torsion
stage) and the assembled `checkL1Claim` are in the opt-in
`kernel-tests/CertificateSharp/V2/ForcedL1Hybrid.lean`.

Rejections: `l1E_rejects`, the claim `|E|₁ ≤ aE/2`; `l1E_tight`, the claim `aE` lowered by `10⁻³`
(the claim is the mirror's value rounded up by at most `3·10⁻⁴`: the Python mirror and the kernel
agree on `|E|₁` to that precision, from both sides).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem msF_eq : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgFull
    cert.piEnc (d1Slots 2 cert.ham.jet) = some msF :=
  eq_of_optModelsBeq (by decide +kernel)

theorem l1W1_ok : checkWeight l1Claim.W1 cert.expHalvings cert.expOrder = true := by
  decide +kernel

theorem l1WT_ok : checkWeight l1Claim.WT cert.expHalvings cert.expOrder = true := by
  decide +kernel

theorem l1L_ok : L1.checkL1L cert l1Claim = true := by
  rw [L1.checkL1L_eq_of L_eq]
  decide +kernel

theorem l1N_ok : L1.checkL1N cert l1Claim = true := by
  rw [L1.checkL1N_eq_of gram_eq eps_eq (frameNModels_eq_of_stage 2 cert.emb cert.gramInv eps
    cert.weight cert.cfgLow cert.piEnc L_eq Gi_eq N0_eq)]
  decide +kernel

theorem l1E_ok : L1.checkL1E cert l1Claim = true := by
  rw [L1.checkL1E_eq_of msF_eq]
  decide +kernel

/-- Rejected: a claim `|E|₁ ≤ aE/2`, below the ℓ¹ norm of the invariance error. -/
theorem l1E_rejects : L1.checkL1E cert { l1Claim with aE := l1Claim.aE / 2 } = false := by
  rw [L1.checkL1E_eq_of msF_eq]
  decide +kernel

/-- Rejected: the claim `aE` lowered by `10⁻³` (the mirror's value is within `3·10⁻⁴` below it). -/
theorem l1E_tight : L1.checkL1E cert { l1Claim with aE := l1Claim.aE * 999 / 1000 } = false := by
  rw [L1.checkL1E_eq_of msF_eq]
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
