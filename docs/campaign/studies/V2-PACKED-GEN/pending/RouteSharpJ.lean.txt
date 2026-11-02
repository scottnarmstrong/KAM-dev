/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.RouteSharp
public import KAM.CertificateSharp.Packed.JetConsFrames
public import KAM.CertificateSharp.Packed.JetBase

/-!
# The packed sharp-site engine on the jet's torsion

The frame checker of the jet-fed packed frames (`checkFrameMajorantsRJ`,
`Packed/JetConsFrames.lean`) and route A refined with the certified sharp sites at it
(`routeARefinedSWith`, `Packed/RouteSharp.lean`). With the jet base checker (`jetBase`,
`Packed/JetBase.lean`) no landed `Slp.compose`, Gram product, torsion model or frame model is
evaluated.

* `ptD2All_of`: the `D²K` entries from each entry (`torsRCoreJ_of` is kamx-pk-cons');
* `framesRJ`, `routeARefinedPackedSJ`, `refinedTestPackedSJ_of`;
* `checkV2With_jetSharp_of`, `checkV2With_jetSharp_sound`: the landed `CertifiedTorus`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-! ### Assembly of the jet's torsion from its parts -/

section Asm

variable {α : Type} [CertArith α] {n : ℕ}

/-- The `D²K` boundary entries from each entry. -/
theorem ptD2All_of {K : CertEmbedding α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {tb : PTorsBook} {tm : PTorsMemo}
    (h : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2Ok n K W cfg pe tb tm r j l = true) :
    ptD2All n K W cfg pe tb tm = true := by
  simp only [ptD2All, List.all_eq_true, List.mem_range]
  exact h

end Asm

/-! ### The engine -/

/-- The jet-fed packed frame majorants as a frame checker. -/
noncomputable def framesRJ (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) : FrameChecker where
  check := fun c b => checkFrameMajorantsRJ bk mm rb tm rm jd c b
  sound := fun B h hω => checkFrameMajorantsRJ_sound B.hs B.hH B.hEm h hω

section J

variable (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
  (jl : JetData)

/-- **The packed sharp-site engine on the jet's torsion.** -/
noncomputable def routeARefinedPackedSJ : EngineV2 :=
  routeARefinedSWith (framesRJ bk mm rb tm rm jl)

/-- Its test from its parts. -/
theorem refinedTestPackedSJ_of {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α}
    {ws : RefinedWitS} (hH : checkHamClaim c ws.base.R = true)
    (hF : checkFrameMajorantsRJ bk mm rb tm rm jl c (ws.base.R.frame c.freqBox) = true)
    (hc : refinedCoreS n c.params c.freqBox ws = true) :
    refinedTestSWith (framesRJ bk mm rb tm rm jl) c ws = true :=
  refinedTestSWith_of (framesRJ bk mm rb tm rm jl) hH hF hc

/-- The certifier with the jet base checker and the jet-fed sharp-site engine, from its parts. -/
theorem checkV2With_jetSharp_of {n : ℕ} {α : Type} [CertArith α] {ib : PIBook} {jf : JetData}
    {c : TorusCertificate n α} {ws : RefinedWitS}
    (hB : (jetBase bk mm rb tm rm jl ib jf).check c = true)
    (hT : refinedTestSWith (framesRJ bk mm rb tm rm jl) c ws = true) :
    checkV2With (jetBase bk mm rb tm rm jl ib jf) (routeARefinedPackedSJ bk mm rb tm rm jl) c ws =
      true := by
  simp only [checkV2With, Bool.and_eq_true]
  exact ⟨hB, hT⟩

/-- **End to end on the jet route**: the landed `CertifiedTorus`. -/
theorem checkV2With_jetSharp_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    {ib : PIBook} {jf : JetData} {c : TorusCertificate n α} {w : RefinedWitS}
    (h : checkV2With (jetBase bk mm rb tm rm jl ib jf) (routeARefinedPackedSJ bk mm rb tm rm jl) c
      w = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound _ _ h hω hdio

end J

end KAM.CertificateSharp.Packed

end
