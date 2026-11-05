/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Gram
public import KAM.CertificateSharp.V2.Engine

/-!
# The packed Gram stage in the v2 certifier

* `checkGramPacked bk mm c`: the packed Gram check at the certificate's data (the landed
  `checkGram`'s arguments, the decoder of `cfgLow`), with `checkGramPacked_sound` giving exactly the
  conclusion of
  the landed `checkGram_sound`, i.e. the Gram field `hG` of the landed `BaseFacts`.
* `gramPackedBase bk mm : BaseChecker`: the landed sub-checks with `checkGram` replaced by
  `checkGramPacked bk mm` (`mm`: the memoized `DK` boundary, re-checked entry by entry). Its
  `sound` field yields the landed `BaseFacts`, so the landed
  `checkV2With_sound` gives the landed `CertifiedTorus` (`checkV2With_gramPacked_sound`).

The torsion sub-check is landed and repeats the landed Gram certificate internally
(`checkTorsion`); its soundness is taken from `checkTorsion_sound_of`, which needs only the
Hamiltonian and embedding facts. So `gramPackedBase` replaces the Gram fact, not the Gram work
inside `checkTorsion`; that work disappears only with a packed torsion stage.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.CertificateSharp.V2
open scoped Matrix.Norms.Operator

variable {n : ℕ} {α : Type} [CertArith α]

/-- The packed Gram check at the certificate's data, with bound `σB - μ`. -/
def checkGramPacked (bk : PGramBook) (mm : PGramMemo) (c : TorusCertificate n α) : Bool :=
  (gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
    (c.params.σB - c.params.μ)).isSome

/-- **Soundness of the packed Gram sub-check**: the conclusion of the landed `checkGram_sound`. -/
theorem checkGramPacked_sound [LawfulCertArith α] {bk : PGramBook} {mm : PGramMemo}
    {c : TorusCertificate n α} (hs : checkStatic c = true) (h : checkGramPacked bk mm c = true) :
    ∀ θ ∈ complexStrip n c.params.rho, IsUnit (gramMatrix c.K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ := by
  have hS := checkStatic_sound hs
  intro θ hθ
  unfold checkGramPacked at h
  obtain ⟨δβ, hδβ⟩ := Option.isSome_iff_exists.mp h
  have hθ' : θ ∈ complexStrip n c.weight.rho := by rw [hS.hrho]; exact hθ
  obtain ⟨hu, hb, -⟩ :=
    (gramPackedCheck_sound (by have := hS.hn; omega) c.emb c.gramInv hS.hW c.cfgLow hS.hpe bk mm _
      hδβ).2 θ hθ'
  exact ⟨hu, fun i => by have := hb i; push_cast at this; exact this⟩

/-- **The landed sub-checks with the packed Gram stage.** -/
def gramPackedBase (bk : PGramBook) (mm : PGramMemo) : BaseChecker where
  check := fun c => checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c &&
    checkEnergy c && checkGramPacked bk mm c && checkTorsion c
  sound := by
    intro n α _ _ c h ωstar hω
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hi⟩, hen⟩, hg⟩, ht⟩ := h
    obtain ⟨hTu, hTb⟩ := checkTorsion_sound_of hs (checkHamBounds_sound hs hh)
      (checkEmbedding_sound hs he) ht hω
    exact ⟨hs, checkHamBounds_sound hs hh, checkEmbedding_sound hs he,
      checkGramPacked_sound hs hg, hTu, hTb, checkInvariance_sound hs hh he hi hω,
      checkEnergy_sound hs hh he hen⟩

/-- **End to end**: a certificate passing the v2 certifier with the packed Gram stage is a landed
`CertifiedTorus`. -/
theorem checkV2With_gramPacked_sound [LawfulCertArith α] (bk : PGramBook) (mm : PGramMemo)
    (E : EngineV2) {c : TorusCertificate n α} {w : E.Wit}
    (h : checkV2With (gramPackedBase bk mm) E c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound (gramPackedBase bk mm) E h hω hdio

end KAM.CertificateSharp.Packed
