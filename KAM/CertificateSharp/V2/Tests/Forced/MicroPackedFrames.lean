/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroPackedTors

/-!
# The packed frame majorants of the forced toy `Micro`

At the claim `MicroP.wit.R`, one kernel run each: `|Lᵀ|` from the packed `DK` entries (`hL`),
`|N|`, `|Nᵀ|` from the node memo of `N` (`hNok`), `sup |T|` from the packed torsion block on the
window (`hT`), `|ω*|` (`hOm`). With the facts the frames share with the torsion stage
(`MicroPackedTors`), `checkFrameMajorantsR_of` assembles the packed frame majorants (`frames_ok`).
No landed frame model is evaluated.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroP

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Packed KAM.CertificateSharp.V2

theorem hL : trFrameLOk (α := FB) 2 cert.weight rb mm wit.R.bL = true := by decide +kernel

theorem hNok : trFrameNOk (α := FB) 2 rb rm wit.R.bN wit.R.bNt = true := by decide +kernel

theorem hT : trFrameTOk (α := FB) 2 cert.weight rb rm wit.R.bT = true := by decide +kernel

theorem hOm : checkFrameOmega cert (freqNormUp cert.freqBox) = true := by decide +kernel

/-- **The packed frame majorants pass** on `MicroP.cert` at the claim of `MicroP.wit`. -/
theorem frames_ok : checkFrameMajorantsR bk mm rb tm rm cert (wit.R.frame cert.freqBox) = true :=
  checkFrameMajorantsR_of gram_eq eps_eq ms_eq rfl hent hlay hnrm hpk hN hDL hDG hC hDGi hDN hXN hL
    hNok hT hOm

end KAM.CertificateSharp.V2.Forced.MicroP

end
