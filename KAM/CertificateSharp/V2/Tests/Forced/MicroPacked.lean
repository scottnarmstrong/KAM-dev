/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroPackedFrames
public import KAM.CertificateSharp.V2.Tests.Forced.MicroPackedClaim
public import KAM.CertificateSharp.V2.Tests.Forced.MicroChecksA
public import KAM.CertificateSharp.V2.Tests.Forced.MicroChecksB
public import KAM.CertificateSharp.V2.Tests.Forced.MicroFreq

/-!
# The packed route A refined on the whole forced toy `Micro`

`MicroP.cert` is `Micro.cert` with the production decoder in `cfgLow` (`MicroPackedData`). Along
the certifier `checkTorusCertificateMax` at the packed base `.torsR books` and the packed route
`.aPacked books wit` (`checkTorusCertificateMax_packed`: the packed Gram, the rounded packed
torsion and the packed frames), no landed Gram product, torsion model or frame model is evaluated:

* the landed sub-checks that do not read `cfgLow` are `Micro`'s (`MicroChecksA/B`), transferred by
  `rfl` (`checkStatic_cfgLow`, …): `static_ok`, `hamBounds_ok`, `embedding_ok`, `invariance_ok`,
  `energy_ok`;
* the packed Gram (`gram_ok`, `MicroPackedGram`) and the rounded packed torsion (`tors_ok`,
  `MicroPackedTors`) complete the packed base (`base_ok`);
* the disc pass, the packed frames and the refined core (`hamClaim_ok`, `frames_ok`,
  `refined_core`) give the packed test (`test_ok`);
* `packed_passes : checkTorusCertificateMax cert (.torsR books) (.aPacked books wit) = true`, and
  `packed_torus : CertifiedTorus cert Micro.ωstar` (`checkTorusCertificateMax_sound`, with `Micro`'s
  frequency facts). The conclusion does not read `cfgLow` (`certifiedTorus_cfgLow`), so this is the
  certified torus of `Micro.cert` itself: `Micro.packed_torus`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroP

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Packed KAM.CertificateSharp.V2

theorem static_ok : checkStatic cert = true :=
  (checkStatic_cfgLow Micro.cert _).trans Micro.static_ok

theorem hamBounds_ok : checkHamBounds cert = true :=
  (checkHamBounds_cfgLow Micro.cert _).trans Micro.hamBounds_ok

theorem embedding_ok : checkEmbedding cert = true :=
  (checkEmbedding_cfgLow Micro.cert _).trans Micro.embedding_ok

theorem invariance_ok : checkInvariance cert = true :=
  (checkInvariance_cfgLow Micro.cert _).trans Micro.invariance_ok

theorem energy_ok : checkEnergy cert = true :=
  (checkEnergy_cfgLow Micro.cert _).trans Micro.energy_ok

/-- **The packed base passes** on `MicroP.cert`. -/
theorem base_ok : (torsRBase bk mm rb tm rm).check cert = true :=
  torsRBase_check_of static_ok hamBounds_ok embedding_ok invariance_ok energy_ok gram_ok tors_ok

/-- **The packed test passes** on `MicroP.cert` at `MicroP.wit`. -/
theorem test_ok : refinedTestPacked bk mm rb tm rm cert wit = true :=
  refinedTestPacked_of hamClaim_ok frames_ok refined_core

/-- The books of the packed route and of its base. -/
def books : PackedBooks := ⟨bk, mm, rb, tm, rm⟩

/-- **The packed certifier passes on `MicroP.cert`**: the packed base and route A refined with the
packed frames, through `checkTorusCertificateMax`. -/
theorem packed_passes :
    checkTorusCertificateMax cert (.torsR books) (.aPacked books wit) = true :=
  checkTorusCertificateMax_packed_of base_ok test_ok

theorem freq : FreqEncloses 2 cert.freqBox Micro.ωstar := Micro.freq

theorem dio : IsDiophantine ((cert.params.γ : ℚ) : ℝ) ((cert.params.tau : ℕ) : ℝ) Micro.ωstar :=
  Micro.dio

/-- **The certified torus of `MicroP.cert`** along the packed route. -/
theorem packed_torus : CertifiedTorus cert Micro.ωstar :=
  checkTorusCertificateMax_sound packed_passes freq dio

end KAM.CertificateSharp.V2.Forced.MicroP

namespace KAM.CertificateSharp.V2.Forced.Micro

open KAM.Certificate

/-- **The certified torus of the landed `Micro.cert`**, along the packed route (`MicroP.cert`
differs by the decoder of `cfgLow`, which `CertifiedTorus` does not read). -/
theorem packed_torus : CertifiedTorus cert ωstar :=
  (certifiedTorus_cfgLow cert _ ωstar).mp MicroP.packed_torus

end KAM.CertificateSharp.V2.Forced.Micro

end
