/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroBase
public import KAM.CertificateSharp.V2.Tests.Forced.MicroFreq
public import KAM.CertificateSharp.V2.Tests.Forced.Lemmas

/-!
# The sharp and frozen routes on the near-integrable forced toy `Micro`, in the kernel

`Micro` has `err = (109 / 250000000000000000000000000)`, below the thresholds of the landed sharp
engine and of the frozen forms of routes A and B (sharp `2.84e-18`, frozen A `8.45e-13`,
frozen B `5.44e-13`), so every one of them passes on the same certificate:
* `sharp_passes`: `routeV2All` at `Sum.inl ()` (the landed certifier `checkTorusCertificateSharp`);
* `frozenA_passes`: the witness of `routeAFrozen` (classical constants, `M₁ = M₂ = M`);
* `frozenB_passes`: the witness of `routeBFrozen` (`iso_g1_v2B_frozen`);
and `sharp_torus`, `frozenA_torus`, `frozenB_torus` are the certified tori.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Micro

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem sharp_test : sharpTest cert = true := by decide +kernel

/-- **The landed sharp certifier on `Micro`**, through `routeV2All`. -/
theorem sharp_passes : checkTorusCertificateV2 routeV2All cert (Sum.inl ()) = true := by
  refine (checkV2_eq routeV2All cert (Sum.inl ())).trans ?_
  rw [base_ok, Bool.true_and]
  exact (sharpV2_test cert ()).trans sharp_test

theorem sharp_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All sharp_passes freq dio

/-- The frozen route-A witness of `Micro`. -/
def frozenWit : FrozenWit :=
  { Xs := (467 / 10000), kp := 5, th := (1 / 8), c := [(4208757 / 50000000), (4139207 / 50000000),
    (410399 / 5000000), (1021567 / 12500000), (2038689 / 25000000)], cbar := [(971391 / 10000000),
    (1793607 / 20000000), (857079 / 10000000), (8365097 / 100000000), (8260329 / 100000000)],
    ctail := (8145851 / 100000000), sB := (102033477 / 100000000), sT := (117139349 / 100000000),
    sLt := (10200239 / 2500000), sN := (52039491 / 50000000), sNt := (104076481 / 25000000),
    t := (112782931 / 10000000), J := 20 }

theorem frozenA_core : frozenCore 2 cert.params cert.freqBox frozenWit = true := by decide +kernel

theorem frozenA_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl frozenWit))))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aFrozen]
  refine (checkV2_eq routeAFrozen cert frozenWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeAFrozen_test cert frozenWit).trans frozenA_core

theorem frozenA_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All frozenA_passes freq dio

/-- The frozen route-B witness of `Micro`. -/
def frozenBWit : RunBWit :=
  { Xs := (253 / 10000000), kp := 2, a := 2, ybar := 1 / 2, θ := 1 / 16, θξ := 1 / 8, θΩ := 1 / 8,
    q := 1 / 8, θN := 1 / 8, θω := 1 / 8, ts := 1 / 10, bF := (801 / 1000000000),
    selfcons := false, lam0 := (21037479 / 10000000000), lamW0 := (505514201 / 1000000000000),
    ePer0 := (505514201 / 1000000000000), c := [(4208757 / 50000000), (4139207 / 50000000)],
    c' := [(4139207 / 50000000), (410399 / 5000000)], cbar := [(971391 / 10000000),
    (1793607 / 20000000)], ctail := (410399 / 5000000), cbtail := (857079 / 10000000),
    sB := (51010257 / 50000000), sT := (115294989 / 100000000), sLt := (408043831 / 100000000),
    sN := (104062521 / 100000000), sNt := (416246791 / 100000000), J := 20 }

theorem frozenB_core : frozenBCore 2 cert.params cert.freqBox frozenBWit = true := by decide +kernel

theorem frozenB_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inr (Sum.inl frozenBWit))) = true := by
  rw [checkTorusCertificateV2_routeV2All_bFrozen]
  refine (checkV2_eq routeBFrozen cert frozenBWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeBFrozen_test cert frozenBWit).trans frozenB_core

theorem frozenB_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All frozenB_passes freq dio

end KAM.CertificateSharp.V2.Forced.Micro

end
