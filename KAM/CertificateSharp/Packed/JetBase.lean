/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetConsEnergy
public import KAM.CertificateSharp.Packed.JetConsFrames

/-!
# The packed base checker on the packed jet (`jetBase`, design `V2-PACKED.md` §12.2)

`jetBase` is the landed `checkStatic`, `checkHamBounds` and `checkEmbedding`, the packed Gram
check (B2), and the three consumers of the packed jet chains:

* `checkTorsionJ` (B3b's rounded torsion, `DX_H ∘ K` and `DH ∘ K` from the `cfgLow` chain);
* `checkInvarianceJ` (`X_H ∘ K - DK (s ω)` from the `cfgFull` chain's `d1` slots, the Gram memo and
  the frequency, one packed norm per coordinate);
* `checkEnergyJ` (the zero mode of the `cfgFull` chain's `v0` slot).

Each consumer holds its jet check (`jetLowOk`, `jetFullOk`: kamx-packed's `jetCheck`), so the
whole is sound through `jetPacked_sound`, and **no landed `Slp.compose` is evaluated**. The
soundness `jetBase.sound` yields the landed `BaseFacts`, so `checkV2With_jetBase_sound` concludes
the landed `CertifiedTorus` for any engine; `checkV2With_jetBasePackedJ_sound` is the end to end
with route A refined on the packed frames of the jet's torsion (`routeARefinedPackedJ`).

`jetBase_check_of` assembles the Boolean from its parts, each shared conjunct (the Gram check, each
jet chain, the guards, every stage) established once in its own declaration.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.CertificateSharp.V2

/-- **The packed base checker on the packed jet.** The book `bk`, the memos `mm`, `tm`, `rm`, the
torsion book `rb`, the invariance book `ib` and the keyed jet chains `jl` (`cfgLow`) and `jf`
(`cfgFull`) are untrusted data. -/
def jetBase (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jl : JetData) (ib : PIBook) (jf : JetData) : BaseChecker where
  check := fun c => checkStatic c && checkHamBounds c && checkEmbedding c &&
    checkGramPacked bk mm c && checkTorsionJ bk mm rb tm rm jl c &&
    checkInvarianceJ bk mm ib jf c && checkEnergyJ ib jf c
  sound := by
    intro n α _ _ c h ωstar hω
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hg⟩, ht⟩, hi⟩, hen⟩ := h
    have hH := checkHamBounds_sound hs hh
    have hE := checkEmbedding_sound hs he
    obtain ⟨hTu, hTb⟩ := checkTorsionJ_sound hs hH hE ht hω
    exact ⟨hs, hH, hE, checkGramPacked_sound hs hg, hTu, hTb, checkInvarianceJ_sound hs hH hE hi hω,
      checkEnergyJ_sound hs hH hE hen⟩

/-- **End to end, any engine**: a certificate passing the v2 certifier with the packed base
checker on the packed jet is a landed `CertifiedTorus`. -/
theorem checkV2With_jetBase_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jl : JetData) (ib : PIBook) (jf : JetData) (E : EngineV2) {c : TorusCertificate n α}
    {w : E.Wit} (h : checkV2With (jetBase bk mm rb tm rm jl ib jf) E c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound (jetBase bk mm rb tm rm jl ib jf) E h hω hdio

/-- **End to end, the packed route**: the packed base checker on the packed jet and route A
refined on the packed frames of the jet's torsion; no landed Gram product, torsion model, frame
model or `Slp.compose` is evaluated. -/
theorem checkV2With_jetBasePackedJ_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jl : JetData) (ib : PIBook) (jf : JetData) {c : TorusCertificate n α} {w : RefinedWit}
    (h : checkV2With (jetBase bk mm rb tm rm jl ib jf) (routeARefinedPackedJ bk mm rb tm rm jl) c
      w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound _ _ h hω hdio

/-- **`jetBase` from its parts** (for proofs split across declarations): the landed checks, the
packed Gram check, the torsion consumer's parts (`checkTorsionJ_of`), the invariance consumer's
(`checkInvarianceJ_of`) and the energy consumer's (`checkEnergyJ_of`). -/
theorem jetBase_check_of {n : ℕ} {α : Type} [CertArith α] {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jl : JetData} {ib : PIBook} {jf : JetData}
    {c : TorusCertificate n α} {δβ : α × α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true)
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ)
    (ht : checkTorsionJ bk mm rb tm rm jl c = true) (hi : checkInvarianceJ bk mm ib jf c = true)
    (hen : checkEnergyJ ib jf c = true) :
    (jetBase bk mm rb tm rm jl ib jf).check c = true := by
  have hg : checkGramPacked bk mm c = true := by
    simp only [checkGramPacked, hG, Option.isSome_some]
  simp only [jetBase, hs, hh, he, hg, ht, hi, hen, Bool.and_self]

end KAM.CertificateSharp.Packed
