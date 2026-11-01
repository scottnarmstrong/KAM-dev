/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroPacked

/-!
# Negative controls of the packed route on `Micro`

Sharp, one kernel run each:
* `ctl_entryMut`: the boundary entry `DK (0, 0)` against the memo `mmMut` (its first real mantissa
  plus one, `2^-96`) is rejected by `pgEntryOk`;
* `ctl_frameT_edge`, `ctl_frameT_ulp`: the packed `sup |T|` test passes at its edge `edgeT` (the
  largest packed row sum) and fails one ulp (`2^-96`) below it.
The ulp-low claim is rejected by the whole packed certifier (`ctl_reject`: the packed frames, then
the packed test, `checkFrameMajorantsR_eq_false_of_T`, `refinedTestPacked_eq_false_of_frames`), at
the facts of the passing run (`gram_eq`, `eps_eq`, `ms_eq`, `base_ok`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroP

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Packed KAM.CertificateSharp.V2

theorem ctl_entryMut :
    pgEntryOk 2 cert.emb cert.weight cert.cfgLow cert.piEnc bk mmMut 0 0 = false := by
  decide +kernel

theorem ctl_frameT_edge : trFrameTOk (α := FB) 2 cert.weight rb rm edgeT = true := by
  decide +kernel

/-- The witness `wit` with the claim `bT` one ulp below the edge of the packed `sup |T|` test. -/
def witLo : RefinedWit := { wit with R := { wit.R with bT := edgeT - 1 / 2 ^ 96 } }

theorem ctl_frameT_ulp :
    trFrameTOk (α := FB) 2 cert.weight rb rm (witLo.R.frame cert.freqBox).bT = false := by
  decide +kernel

theorem ctl_frames :
    checkFrameMajorantsR bk mm rb tm rm cert (witLo.R.frame cert.freqBox) = false :=
  checkFrameMajorantsR_eq_false_of_T gram_eq eps_eq ms_eq ctl_frameT_ulp

theorem ctl_test : refinedTestPacked bk mm rb tm rm cert witLo = false :=
  refinedTestPacked_eq_false_of_frames ctl_frames

/-- **Rejected**: the packed certifier at the witness `witLo`. -/
theorem ctl_reject :
    checkTorusCertificateMax cert (.torsR books) (.aPacked books witLo) = false := by
  refine (checkTorusCertificateMax_packed_eq cert bk mm rb tm rm witLo).trans ?_
  rw [base_ok, ctl_test]
  rfl

end KAM.CertificateSharp.V2.Forced.MicroP

end
