/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.SharpEngine
public import KAM.Iso.Sharp.G1

/-!
# Soundness of the sharp certifier

`sharpEngine` is the engine of `KAM/CertificateSharp/SharpEngine.lean` instantiated with the proved sharp
isoenergetic a-posteriori theorem `KAM.Iso.Sharp.g1_sharp` (Rüssmann's small-divisor data). With it,
`checkTorusCertificateSharp_sound` is unconditional: a certificate that passes the sharp certifier, a reference
frequency in its box and a proved Diophantine premise give an exact analytic invariant torus within the certified
distance, exactly as `KAM.Certificate.checkTorusCertificate_sound` does for the old certifier.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Certificate CertArith

/-- The sharp isoenergetic theorem has the type the sharp engine expects. -/
theorem isoSharpG1 : IsoSharpG1 := KAM.Iso.Sharp.g1_sharp

/-- The sharp a-posteriori engine: the sharp threshold test, sound through `KAM.Iso.Sharp.g1_sharp`. -/
def sharpEngine : AposterioriEngine := sharpEngineOf isoSharpG1

/-- **The sharp certifier is sound.** A passing certificate, an exact reference vector `ωstar` in its box and a
proved Diophantine premise yield an exact analytic invariant torus within `disp` of the candidate. -/
theorem checkTorusCertificateSharp_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    {c : TorusCertificate n α} (h : checkTorusCertificateSharp c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateSharp_sound_of isoSharpG1 h hω hdio

end KAM.CertificateSharp

end
