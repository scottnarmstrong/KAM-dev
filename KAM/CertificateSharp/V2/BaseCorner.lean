/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Engine
public import KAM.CertificateSharp.Corner.Checks

/-!
# The v2 certifier with the corner bounds of C1

`cornerBase`: the sub-checks of `landedBase` with `checkEmbeddingCorner`, `checkInvarianceCorner`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith

/-- The sub-checks with the corner bounds of C1 for the embedding and the invariance. -/
def cornerBase : BaseChecker where
  check := fun c => checkStatic c && checkHamBounds c && checkEmbeddingCorner c &&
    checkInvarianceCorner c && checkEnergy c && checkGram c && checkTorsion c
  sound := by
    intro n α _ _ c h ωstar hω
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hi⟩, hen⟩, hg⟩, ht⟩ := h
    have hH := checkHamBounds_sound hs hh
    have hE := checkEmbeddingCorner_sound hs he
    obtain ⟨hTu, hTb⟩ := checkTorsion_sound_of hs hH hE ht hω
    exact ⟨hs, hH, hE, checkGram_sound hs hg, hTu, hTb,
      checkInvarianceCorner_sound_of hs hH hE hi hω, checkEnergy_sound_of hs hH hE hen⟩

end KAM.CertificateSharp.V2

end
