/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Frames
public import KAM.CertificateSharp.V2.RouteARefinedS

/-!
# The packed sharp-site engine

LG00 runs route A refined with the certified sharp sites (`routeV2AllS = routeV2All.orElse
routeARefinedS`, `V2/RouteARefinedS.lean`): its test is `checkHamClaim && checkFrameMajorants &&
refinedCoreS`. The landed `checkFrameMajorants` re-evaluates the landed Gram check and torsion
models; `Packed/Frames.lean` reads the same bounds from the packed objects (`checkFrameMajorantsR`).
This module puts the two together.

`refinedCoreS` reads only the rational witness, the parameters and the frequency box (`RefinedWitS`,
`CertParams`, `FreqBox`): no Gram, torsion or frame model. So it is reused verbatim.

* `FrameChecker`: a Boolean test of the frame majorants with the landed `FrameMajorants` as its
  soundness, under `BaseFacts`. Instances: the landed `checkFrameMajorants` (`landedFrames`) and the
  packed `checkFrameMajorantsR` of B2/B3b (`framesR`). A later packed frame test (the jet-fed
  torsion) is one more instance, with no new engine.
* `refinedTestSWith F`, `routeARefinedSWith F`: route A refined with the sharp sites and the frame
  checker `F`; `refinedTestSWith landedFrames` is `refinedTestS` by `rfl`.
* `refinedTestPackedS`, `routeARefinedPackedS`: the instance at `framesR`, i.e.
  `checkHamClaim && checkFrameMajorantsR … && refinedCoreS`.
* `routeV2AllPackedS`: `routeV2AllS.orElse routeARefinedPackedS`; every witness of `routeV2AllS`
  runs unchanged.
* Soundness for every base checker (`checkV2With_routeARefinedSWith_sound`), in particular B3b's
  `torsRBase` (`checkV2With_packedS_sound`): the landed `CertifiedTorus`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-! ### Frame checkers -/

/-- A Boolean test of the frame majorants, sound for the landed `FrameMajorants` under `BaseFacts`
(which carries the hypotheses of the landed `checkFrameMajorants_sound`). -/
structure FrameChecker where
  /-- The test of the bounds `b`. -/
  check : {n : ℕ} → {α : Type} → [CertArith α] → TorusCertificate n α → FrameBounds → Bool
  /-- A passing test gives the landed frame majorants at every frequency of the box. -/
  sound : ∀ {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α] {c : TorusCertificate n α}
    {b : FrameBounds} {ωstar : Fin n → ℝ}, BaseFacts c ωstar → check c b = true →
    FreqEncloses n c.freqBox ωstar → FrameMajorants c b ωstar

/-- The landed frame majorants (`Frame/Majorants.lean`). -/
def landedFrames : FrameChecker where
  check := fun c b => checkFrameMajorants c b
  sound := fun B h hω => checkFrameMajorants_sound B.hs B.hH B.hEm h hω

/-- The packed frame majorants of B2/B3b (`Packed/Frames.lean`). -/
noncomputable def framesR (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) : FrameChecker where
  check := fun c b => checkFrameMajorantsR bk mm rb tm rm c b
  sound := fun B h hω => checkFrameMajorantsR_sound B.hs B.hH B.hEm h hω

/-- The frame majorants of a frame checker as `FrameFacts` of a claim. -/
theorem FrameChecker.facts (F : FrameChecker) {n : ℕ} {α : Type} [CertArith α]
    [LawfulCertArith α] {c : TorusCertificate n α} {R : RefClaim} {ωstar : Fin n → ℝ}
    (B : BaseFacts c ωstar) (h : F.check c (R.frame c.freqBox) = true)
    (hω : FreqEncloses n c.freqBox ωstar) : FrameFacts c R ωstar := by
  obtain ⟨h1, h2, h3, h4, -⟩ := F.sound B h hω
  exact ⟨h1, h2, h3, h4⟩

/-! ### Route A refined with the sharp sites, at a frame checker -/

section Engine

variable (F : FrameChecker)

/-- The test of route A refined with the sharp sites and the frame checker `F`. -/
def refinedTestSWith {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α)
    (ws : RefinedWitS) : Bool :=
  checkHamClaim c ws.base.R && F.check c (ws.base.R.frame c.freqBox) &&
    refinedCoreS n c.params c.freqBox ws

/-- **Route A refined with the sharp sites and the frame checker `F`.** -/
def routeARefinedSWith : EngineV2 where
  Wit := RefinedWitS
  test := fun c w => refinedTestSWith F c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTestSWith, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedCoreS_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (F.facts B hF hω) hc

/-- `refinedTestSWith` from its parts (for proofs split across declarations). -/
theorem refinedTestSWith_of {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α}
    {ws : RefinedWitS} (hH : checkHamClaim c ws.base.R = true)
    (hF : F.check c (ws.base.R.frame c.freqBox) = true)
    (hc : refinedCoreS n c.params c.freqBox ws = true) : refinedTestSWith F c ws = true := by
  simp only [refinedTestSWith, hH, hF, hc, Bool.and_self]

/-- **Soundness for every base checker.** -/
theorem checkV2With_routeARefinedSWith_sound {n : ℕ} {α : Type} [CertArith α]
    [LawfulCertArith α] (B : BaseChecker) {c : TorusCertificate n α} {w : RefinedWitS}
    (h : checkV2With B (routeARefinedSWith F) c w = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound B (routeARefinedSWith F) h hω hdio

end Engine

/-- At the landed frames this is the landed sharp-site test. -/
theorem refinedTestSWith_landed {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α)
    (ws : RefinedWitS) : refinedTestSWith landedFrames c ws = refinedTestS c ws := rfl

/-- At the landed frames the engine has the landed sharp-site test. -/
theorem routeARefinedSWith_landed_test {n : ℕ} {α : Type} [CertArith α]
    (c : TorusCertificate n α) (ws : RefinedWitS) :
    (routeARefinedSWith landedFrames).test c ws = routeARefinedS.test c ws := rfl

/-! ### The packed instance -/

section Packed

variable (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)

/-- The test of route A refined with the sharp sites and the packed frames:
`checkHamClaim && checkFrameMajorantsR … && refinedCoreS`. -/
noncomputable def refinedTestPackedS {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α)
    (ws : RefinedWitS) : Bool :=
  refinedTestSWith (framesR bk mm rb tm rm) c ws

/-- The packed sharp-site test, unfolded. -/
theorem refinedTestPackedS_eq {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α)
    (ws : RefinedWitS) :
    refinedTestPackedS bk mm rb tm rm c ws = (checkHamClaim c ws.base.R &&
      checkFrameMajorantsR bk mm rb tm rm c (ws.base.R.frame c.freqBox) &&
        refinedCoreS n c.params c.freqBox ws) := rfl

/-- **The packed sharp-site engine**: route A refined with the certified sharp sites
(`refinedCoreS`) and the packed frames of B2/B3b (`checkFrameMajorantsR`). -/
noncomputable def routeARefinedPackedS : EngineV2 := routeARefinedSWith (framesR bk mm rb tm rm)

/-- `routeV2AllS` and the packed sharp-site engine: the witness chooses the route. -/
noncomputable def routeV2AllPackedS : EngineV2 :=
  routeV2AllS.orElse (routeARefinedPackedS bk mm rb tm rm)

/-- `refinedTestPackedS` from its parts. -/
theorem refinedTestPackedS_of {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α}
    {ws : RefinedWitS} (hH : checkHamClaim c ws.base.R = true)
    (hF : checkFrameMajorantsR bk mm rb tm rm c (ws.base.R.frame c.freqBox) = true)
    (hc : refinedCoreS n c.params c.freqBox ws = true) :
    refinedTestPackedS bk mm rb tm rm c ws = true :=
  refinedTestSWith_of (framesR bk mm rb tm rm) hH hF hc

/-- **Never worse than the packed engine with classical sites:** a passing witness of
`routeARefinedPacked` passes here at its own box. -/
theorem refinedTestPackedS_ofPacked {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α}
    {w : RefinedWit} (h : refinedTestPacked bk mm rb tm rm c w = true) :
    refinedTestPackedS bk mm rb tm rm c ⟨w, false, c.freqBox⟩ = true := by
  simp only [refinedTestPacked, Bool.and_eq_true] at h
  obtain ⟨⟨hH, hF⟩, hc⟩ := h
  exact refinedTestPackedS_of bk mm rb tm rm hH hF (refinedCoreS_ofRefined hc)

/-- The witnesses of `routeV2AllS` run unchanged, at every base checker. -/
theorem checkV2With_routeV2AllPackedS_inl {n : ℕ} {α : Type} [CertArith α] (B : BaseChecker)
    (c : TorusCertificate n α) (w : routeV2AllS.Wit) :
    checkV2With B (routeV2AllPackedS bk mm rb tm rm) c (Sum.inl w) =
      checkV2With B routeV2AllS c w := rfl

/-- The witness of the packed sharp-site engine. -/
theorem checkV2With_routeV2AllPackedS_inr {n : ℕ} {α : Type} [CertArith α] (B : BaseChecker)
    (c : TorusCertificate n α) (w : RefinedWitS) :
    checkV2With B (routeV2AllPackedS bk mm rb tm rm) c (Sum.inr w) =
      checkV2With B (routeARefinedPackedS bk mm rb tm rm) c w := rfl

/-- The certifier with a base checker and the packed sharp-site engine, from its parts. -/
theorem checkV2With_packedS_of {n : ℕ} {α : Type} [CertArith α] {B : BaseChecker}
    {c : TorusCertificate n α} {ws : RefinedWitS} (hB : B.check c = true)
    (hT : refinedTestPackedS bk mm rb tm rm c ws = true) :
    checkV2With B (routeARefinedPackedS bk mm rb tm rm) c ws = true := by
  simp only [checkV2With, Bool.and_eq_true]
  exact ⟨hB, hT⟩

/-- **End to end, at B3b's base checker**: a certificate passing the v2 certifier with the packed
Gram and torsion stages (`torsRBase`) and the packed sharp-site engine is a landed
`CertifiedTorus`. -/
theorem checkV2With_packedS_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    {c : TorusCertificate n α} {w : RefinedWitS}
    (h : checkV2With (torsRBase bk mm rb tm rm) (routeARefinedPackedS bk mm rb tm rm) c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound (torsRBase bk mm rb tm rm) (routeARefinedPackedS bk mm rb tm rm) h hω hdio

/-- **End to end, at every base checker and the combined engine.** -/
theorem checkV2With_routeV2AllPackedS_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    (B : BaseChecker) {c : TorusCertificate n α} {w : (routeV2AllPackedS bk mm rb tm rm).Wit}
    (h : checkV2With B (routeV2AllPackedS bk mm rb tm rm) c w = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound B (routeV2AllPackedS bk mm rb tm rm) h hω hdio

end Packed

end KAM.CertificateSharp.Packed

end
