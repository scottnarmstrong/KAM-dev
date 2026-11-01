/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteMax

/-!
# Assembly lemmas for the packed route on a whole certificate

Stated over variables and proved by `rfl` or by Boolean conjunction, so that a test at concrete data
rewrites with them instead of evaluating a certifier inside a definitional-equality check (as
`Forced/Lemmas.lean`):

* **the decoder of `cfgLow`**: the landed sub-checks `checkStatic`, `checkHamBounds`,
  `checkEmbedding`, `checkInvariance`, `checkEnergy`, the disc pass `checkHamClaim`, and the
  conclusion `CertifiedTorus` do not read `cfgLow`; a certificate with another `cfgLow` has the same
  values (`checkStatic_cfgLow`, …, `certifiedTorus_cfgLow`, all `rfl`). Only the Gram and torsion
  checks (and their packed forms) read `cfgLow`;
* **the packed certifier from its parts**: `torsRCore_of` (the thirteen conjuncts of the rounded
  packed torsion core), `checkGramPacked_of`, `torsRBase_check_of` (the seven sub-checks of the
  packed base), `refinedTestPacked_of` (the claim, the packed frames, the refined core) and
  `checkTorusCertificateMax_packed_of` (the base and the test of `checkTorusCertificateMax` at
  `.torsR b`, `.aPacked b w`; `checkTorusCertificateMax_packed_eq`);
* **rejections**: a failing packed `sup |T|` test rejects the packed frame majorants
  (`checkFrameMajorantsR_eq_false_of_T`), and failing packed frames reject the packed test
  (`refinedTestPacked_eq_false_of_frames`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Packed KAM.CertificateSharp.V2

variable {n : ℕ} {α : Type} [CertArith α]

section Decoder

variable (c : TorusCertificate n α) (cfg : ModelConfig α)

theorem checkStatic_cfgLow : checkStatic { c with cfgLow := cfg } = checkStatic c := rfl

theorem checkHamBounds_cfgLow : checkHamBounds { c with cfgLow := cfg } = checkHamBounds c := rfl

theorem checkEmbedding_cfgLow : checkEmbedding { c with cfgLow := cfg } = checkEmbedding c := rfl

theorem checkInvariance_cfgLow :
    checkInvariance { c with cfgLow := cfg } = checkInvariance c := rfl

theorem checkEnergy_cfgLow : checkEnergy { c with cfgLow := cfg } = checkEnergy c := rfl

omit [CertArith α] in
theorem checkHamClaim_cfgLow (R : RefClaim) :
    checkHamClaim { c with cfgLow := cfg } R = checkHamClaim c R := rfl

/-- The conclusion of the certifier does not read `cfgLow`. -/
theorem certifiedTorus_cfgLow (ωstar : Fin n → ℝ) :
    CertifiedTorus { c with cfgLow := cfg } ωstar ↔ CertifiedTorus c ωstar := Iff.rfl

end Decoder

/-- The core of the rounded packed torsion check from its thirteen conjuncts. -/
theorem torsRCore_of {Binv : List (List (CertPoly α))} {W : CertWeight} {cfg : ModelConfig α}
    {box : FreqBox} {s : ℚ} {rb : PRBook} {mm : PGramMemo} {tm : PTorsMemo} {rm : PRMemo} {eps : α}
    {S : List (List (CC α))} {σTμ : ℚ} (h1 : trLayOk n rb = true)
    (h2 : trNormOk n W box s rb = true) (h3 : ptPackOk n Binv cfg rb.toT mm tm = true)
    (h4 : trStN n Binv W cfg rb mm rm eps = true) (h5 : trStDL (α := α) n W box s rb tm rm = true)
    (h6 : trStDG (α := α) n W rb mm rm = true) (h7 : trStC n Binv W cfg rb rm eps = true)
    (h8 : trStDGi n Binv W cfg rb rm eps = true) (h9 : trStDN n Binv W cfg rb mm rm eps = true)
    (h10 : trStXN (α := α) n W rb tm rm = true) (h11 : trTCheck (α := α) n rb rm = true)
    (h12 : trYCheck (α := α) n W rb tm rm = true)
    (h13 : tabFinal n cfg rb.P (trCentre n box s rm) (trRad n box s rm) S σTμ = true) :
    torsRCore n Binv W cfg box s rb mm tm rm eps S σTμ = true := by
  unfold torsRCore
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  rfl

/-- The packed Gram sub-check from the packed Gram check. -/
theorem checkGramPacked_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {δβ : α × α}
    (h : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) :
    checkGramPacked bk mm c = true := by
  unfold checkGramPacked
  rw [h]
  rfl

/-- The packed base from its seven sub-checks. -/
theorem torsRBase_check_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true) (hi : checkInvariance c = true)
    (hen : checkEnergy c = true) (hg : checkGramPacked bk mm c = true)
    (ht : checkTorsionR bk mm rb tm rm c = true) : (torsRBase bk mm rb tm rm).check c = true := by
  show (checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c &&
    checkEnergy c && checkGramPacked bk mm c && checkTorsionR bk mm rb tm rm c) = true
  rw [hs, hh, he, hi, hen, hg, ht]
  rfl

/-- The test of the packed route A refined from the claim, the packed frames and the core. -/
theorem refinedTestPacked_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {w : RefinedWit}
    (hH : checkHamClaim c w.R = true)
    (hF : checkFrameMajorantsR bk mm rb tm rm c (w.R.frame c.freqBox) = true)
    (hc : refinedCore n c.params c.freqBox w = true) :
    refinedTestPacked bk mm rb tm rm c w = true := by
  unfold refinedTestPacked
  rw [hH, hF, hc]
  rfl

/-- **The packed certifier** at the base `.torsR` and the route `.aPacked` of the same books, from
the packed base and the packed test. -/
theorem checkTorusCertificateMax_packed_of {c : TorusCertificate n α} {bk : PGramBook}
    {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {w : RefinedWit}
    (hb : (torsRBase bk mm rb tm rm).check c = true)
    (ht : refinedTestPacked bk mm rb tm rm c w = true) :
    checkTorusCertificateMax c (.torsR ⟨bk, mm, rb, tm, rm⟩) (.aPacked ⟨bk, mm, rb, tm, rm⟩ w) =
      true := by
  rw [checkTorusCertificateMax_packed]
  show ((torsRBase bk mm rb tm rm).check c && refinedTestPacked bk mm rb tm rm c w) = true
  rw [hb, ht]
  rfl

/-- The packed certifier at `.torsR`, `.aPacked` of the same books is the packed base and the packed
test. -/
theorem checkTorusCertificateMax_packed_eq (c : TorusCertificate n α) (bk : PGramBook)
    (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo) (w : RefinedWit) :
    checkTorusCertificateMax c (.torsR ⟨bk, mm, rb, tm, rm⟩) (.aPacked ⟨bk, mm, rb, tm, rm⟩ w) =
      ((torsRBase bk mm rb tm rm).check c && refinedTestPacked bk mm rb tm rm c w) := rfl

/-- The packed frame majorants reject a claim whose `sup |T|` test fails (for negative controls:
the rejection of one frame test is the rejection of the packed frames). -/
theorem checkFrameMajorantsR_eq_false_of_T {c : TorusCertificate n α} {bk : PGramBook}
    {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {δβ : α × α} {eps : α}
    {ms : List (CertModel α)} {b : FrameBounds}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hcomp : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
      (torsionSlots n c.ham.jet) = some ms)
    (hT : trFrameTOk (α := α) n c.weight rb rm b.bT = false) :
    checkFrameMajorantsR bk mm rb tm rm c b = false := by
  unfold checkFrameMajorantsR checkFrameTR
  rw [hG]
  dsimp only
  rw [heps, hcomp]
  dsimp only
  rw [hT]
  simp only [Bool.and_false, Bool.false_and]

/-- The packed test rejects a witness whose packed frame majorants fail. -/
theorem refinedTestPacked_eq_false_of_frames {c : TorusCertificate n α} {bk : PGramBook}
    {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {w : RefinedWit}
    (hF : checkFrameMajorantsR bk mm rb tm rm c (w.R.frame c.freqBox) = false) :
    refinedTestPacked bk mm rb tm rm c w = false := by
  unfold refinedTestPacked
  rw [hF]
  simp only [Bool.and_false, Bool.false_and]

end KAM.CertificateSharp.V2.Forced

end
