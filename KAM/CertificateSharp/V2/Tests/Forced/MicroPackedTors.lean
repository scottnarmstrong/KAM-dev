/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroPackedGram
public import KAM.CertificateSharp.V2.Tests.Forced.MicroPackedCompose

/-!
# The rounded packed torsion stage of the forced toy `Micro`

On `MicroP.cert`, one kernel run each: the boundary entries (`hent`: the landed `D²K`, `DX_H ∘ K`,
`DH ∘ K` entries against the memo `tm`), the layout and load guards (`hlay`, `hnrm`, `hpk`), the
seven nodes against the exact products of their memoized inputs (`hN` … `hXN`), the averages of `T`
and `Y` against the tables (`hTc`, `hYc`) and the landed averaged test on the tables (`hfin`).
Assembled: the core (`core_ok`, `torsRCore_of`) and the rounded packed torsion sub-check
(`tors_ok`, `checkTorsionR_of`). No landed torsion model is evaluated.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroP

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Packed KAM.CertificateSharp.V2

theorem hent :
    ptEntries 2 cert.emb cert.weight cert.cfgLow cert.piEnc rb.toT tm Micro.ms = true := by
  decide +kernel

theorem hlay : trLayOk 2 rb = true := by decide +kernel

theorem hnrm : trNormOk 2 cert.weight cert.freqBox cert.params.s rb = true := by decide +kernel

theorem hpk : ptPackOk 2 cert.gramInv cert.cfgLow rb.toT mm tm = true := by decide +kernel

theorem hN : trStN 2 cert.gramInv cert.weight cert.cfgLow rb mm rm eps = true := by decide +kernel

theorem hDL : trStDL (α := FB) 2 cert.weight cert.freqBox cert.params.s rb tm rm = true := by
  decide +kernel

theorem hDG : trStDG (α := FB) 2 cert.weight rb mm rm = true := by decide +kernel

theorem hC : trStC 2 cert.gramInv cert.weight cert.cfgLow rb rm eps = true := by decide +kernel

theorem hDGi : trStDGi 2 cert.gramInv cert.weight cert.cfgLow rb rm eps = true := by
  decide +kernel

theorem hDN : trStDN 2 cert.gramInv cert.weight cert.cfgLow rb mm rm eps = true := by
  decide +kernel

theorem hXN : trStXN (α := FB) 2 cert.weight rb tm rm = true := by decide +kernel

theorem hTc : trTCheck (α := FB) 2 rb rm = true := by decide +kernel

theorem hYc : trYCheck (α := FB) 2 cert.weight rb tm rm = true := by decide +kernel

theorem hfin : tabFinal 2 cert.cfgLow rb.P (trCentre 2 cert.freqBox cert.params.s rm)
    (trRad 2 cert.freqBox cert.params.s rm) cert.torsInv (cert.params.σT - cert.params.μ) =
      true := by
  decide +kernel

theorem core_ok : torsRCore 2 cert.gramInv cert.weight cert.cfgLow cert.freqBox cert.params.s rb mm
    tm rm eps cert.torsInv (cert.params.σT - cert.params.μ) = true :=
  torsRCore_of hlay hnrm hpk hN hDL hDG hC hDGi hDN hXN hTc hYc hfin

/-- **The rounded packed torsion sub-check passes** on `MicroP.cert`. -/
theorem tors_ok : checkTorsionR bk mm rb tm rm cert = true :=
  checkTorsionR_of gram_eq eps_eq ms_eq rfl hent core_ok

end KAM.CertificateSharp.V2.Forced.MicroP

end
