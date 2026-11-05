/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsRSound
public import KAM.CertificateSharp.Packed.GramBase

/-!
# The packed Gram and rounded packed torsion stages in the v2 certifier

`torsRBase bk mm rb tm rm : BaseChecker`: the landed sub-checks with `checkGram` replaced by
`checkGramPacked bk mm` and `checkTorsion` by `checkTorsionR bk mm rb tm rm`. Its `sound` field
yields the landed `BaseFacts`, so the landed `checkV2With_sound` gives the landed `CertifiedTorus`
(`checkV2With_torsRBase_sound`). No landed Gram certificate is evaluated; the landed jet composition
at `cfgLow` remains, as in the landed `checkTorsion`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.CertificateSharp.V2

/-- **The landed sub-checks with the packed Gram and rounded packed torsion stages.** -/
def torsRBase (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo) :
    BaseChecker where
  check := fun c => checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c &&
    checkEnergy c && checkGramPacked bk mm c && checkTorsionR bk mm rb tm rm c
  sound := by
    intro n α _ _ c h ωstar hω
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hi⟩, hen⟩, hg⟩, ht⟩ := h
    obtain ⟨hTu, hTb⟩ := checkTorsionR_sound hs (checkHamBounds_sound hs hh)
      (checkEmbedding_sound hs he) ht hω
    exact ⟨hs, checkHamBounds_sound hs hh, checkEmbedding_sound hs he,
      checkGramPacked_sound hs hg, hTu, hTb, checkInvariance_sound hs hh he hi hω,
      checkEnergy_sound hs hh he hen⟩

/-- **End to end**: a certificate passing the v2 certifier with the packed Gram and rounded packed
torsion stages is a landed `CertifiedTorus`. -/
theorem checkV2With_torsRBase_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo) (E : EngineV2)
    {c : TorusCertificate n α} {w : E.Wit}
    (h : checkV2With (torsRBase bk mm rb tm rm) E c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound (torsRBase bk mm rb tm rm) E h hω hdio

end KAM.CertificateSharp.Packed
