/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAllE
public import KAM.CertificateSharp.V2.RouteARefinedS
public import KAM.CertificateSharp.V2.Fiber.RouteBGS
public import KAM.CertificateSharp.V2.BaseCorner
public import KAM.CertificateSharp.V2.BaseTrig
public import KAM.CertificateSharp.Hybrid.Iso
public import KAM.CertificateSharp.Packed.Frames
public import KAM.CertificateSharp.Packed.TorsBase

/-!
# One engine with every route

`routeMax` is a single `EngineV2` whose witness names the route. Its witness type `RouteMaxWit` has
one named constructor per route now in the library; each constructor runs exactly that engine's
test, and every row of the table below is a theorem by `rfl`, at **every** base checker `B`
(`checkV2With B routeMax c (.r w) = checkV2With B E c w`). In particular, at the landed base,
`checkTorusCertificateV2 routeMax c (.r w)` is `checkTorusCertificateV2 E c w`.

| Constructor | Engine | Witness |
|---|---|---|
| `.old` | `EngineV2.ofEngine oldEngine` (the original `checkTorusCertificate`) | none |
| `.sharp` | `sharpV2` (the landed certifier) | none |
| `.aFrozen w` | `routeAFrozen` | `FrozenWit` |
| `.aRefined w` | `routeARefined` | `RefinedWit` |
| `.aRefinedR w` | `routeARefinedR` (lever L8′) | `RefinedWitR` |
| `.aL1 w` | `L1.routeAL1` (the ℓ¹ entry) | `L1.L1Wit` |
| `.bFrozen w` | `routeBFrozen` | `RunBWit` |
| `.bRefined w` | `routeBRefined` | `RefinedBWit` |
| `.bLN w` | `routeBRefinedLN` (no torsion majorant) | `RefinedBWit` |
| `.bE w` | `routeBRefinedE` (energy row `y₀ = dh s_N`) | `RefinedBWit` |
| `.aG w` | `routeARefinedG` (three-frequency fibred sites) | `RefinedWitG` |
| `.bG w` | `routeBRefinedG` (three-frequency fibred sites) | `RefinedBWitG` |
| `.aS w` | `routeARefinedS` (sign-tolerant sites) | `RefinedWitS` |
| `.hybrid w` | `Hybrid.routeHybrid` (the hybrid restart) | `Hybrid.HybWit` |
| `.aPacked b w` | `Packed.routeARefinedPacked b…` (packed frames) | `PackedBooks`, `RefinedWit` |
| `.bGSLN w` | `routeBRefinedGSLN` (general sites, no torsion majorant) | `RefinedBWitGS` |
| `.bGSE w` | `routeBRefinedGSE` (general sites, energy row) | `RefinedBWitGS` |

`routeMax.sound` is proved branch by branch from each engine's own `sound`; there is no hypothesis
beyond those of `EngineV2.sound`, so `checkTorusCertificateV2_sound routeMax` concludes the landed
`CertifiedTorus` (`checkTorusCertificateV2_routeMax_sound`).

**The older combined engines.** `RouteMaxWit.ofAV2`, `ofAV2'`, `ofAV2L1`, `ofABV2`, `ofV2All`,
`ofV2AllLN`, `ofV2AllE`, `ofV2AllS`, `ofAV2G`, `ofV2G`, `ofV2Hyb` translate a witness of `routeAV2`,
`routeAV2'`, `routeAV2L1`, `routeABV2`, `routeV2All`, `routeV2AllLN`, `routeV2AllE`, `routeV2AllS`,
`routeAV2G`, `routeV2G`, `routeV2Hyb`; the certifier gives the same verdict at every base
(`checkV2With_routeMax_ofV2All` …, by cases and `rfl`).

**The packed route and its base.** The packed route A refined fits the `EngineV2` split as an engine
branch: its books and memos are witness data (`PackedBooks`), and its test needs only `BaseFacts`.
Its packed **base** `Packed.torsRBase` (the packed Gram and rounded packed torsion stages) cannot be
chosen by an engine witness: `checkTorusCertificateV2` fixes the base to `landedBase`, and a
`BaseChecker` reads no witness. `checkTorusCertificateMax c b w` therefore pairs the engine witness
with a base selection `b : BaseSel` (landed, corner, cosh, packed Gram, packed torsion, rounded
packed torsion); its soundness is `checkV2With_sound` at `b.toBase`
(`checkTorusCertificateMax_sound`). At `b = .landed` it is `checkTorusCertificateV2 routeMax`
(`rfl`), and at `b = .torsR bs`, `w = .aPacked bs w'` it is the packed certifier of
`Packed.checkV2With_packed_sound` (`rfl`), along which no landed Gram product, torsion model or
frame model is evaluated.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate

/-- The untrusted books and memos of the packed route (`Packed.routeARefinedPacked`) and of its base
(`Packed.torsRBase`). -/
structure PackedBooks where
  /-- The packed Gram book. -/
  bk : Packed.PGramBook
  /-- The packed Gram memo. -/
  mm : Packed.PGramMemo
  /-- The book of the rounded packed torsion stage. -/
  rb : Packed.PRBook
  /-- The boundary memo of the packed torsion. -/
  tm : Packed.PTorsMemo
  /-- The node memos of the rounded packed torsion stage. -/
  rm : Packed.PRMemo

/-- The packed route A refined at the books `b`. -/
noncomputable def PackedBooks.engine (b : PackedBooks) : EngineV2 :=
  Packed.routeARefinedPacked b.bk b.mm b.rb b.tm b.rm

/-- The packed base at the books `b`. -/
def PackedBooks.base (b : PackedBooks) : BaseChecker :=
  Packed.torsRBase b.bk b.mm b.rb b.tm b.rm

/-- The witness of `routeMax`: the constructor names the route (module docstring). -/
inductive RouteMaxWit where
  /-- The original landed engine (`checkSmallness`, `g1_explicit`). -/
  | old
  /-- The landed sharp engine. -/
  | sharp
  /-- Route A at the frozen data. -/
  | aFrozen (w : FrozenWit)
  /-- Route A at the refined data. -/
  | aRefined (w : RefinedWit)
  /-- Route A at the refined data, lever L8′. -/
  | aRefinedR (w : RefinedWitR)
  /-- Route A with the ℓ¹ entry. -/
  | aL1 (w : L1.L1Wit)
  /-- Route B at the frozen data. -/
  | bFrozen (w : RunBWit)
  /-- Route B at the refined data. -/
  | bRefined (w : RefinedBWit)
  /-- Route B at the refined data, without the torsion majorant. -/
  | bLN (w : RefinedBWit)
  /-- Route B at the refined data, with the gradient bound in the energy row. -/
  | bE (w : RefinedBWit)
  /-- Route A at the refined data, with general (three-frequency) sites. -/
  | aG (w : RefinedWitG)
  /-- Route B at the refined data, with general (three-frequency) sites. -/
  | bG (w : RefinedBWitG)
  /-- Route A at the refined data, with the sites on a box of the witness (sign-tolerant). -/
  | aS (w : RefinedWitS)
  /-- The hybrid restart. -/
  | hybrid (w : Hybrid.HybWit)
  /-- Route A at the refined data, with the packed frame checks. -/
  | aPacked (b : PackedBooks) (w : RefinedWit)
  /-- Route B with general sites on a box of the witness, without the torsion majorant. -/
  | bGSLN (w : RefinedBWitGS)
  /-- Route B with general sites on a box of the witness, with the energy row at `dh`. -/
  | bGSE (w : RefinedBWitGS)

/-- The test of `routeMax`: the test of the engine the constructor names. -/
noncomputable def routeMaxTest {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) :
    RouteMaxWit → Bool
  | .old => (EngineV2.ofEngine oldEngine).test c ()
  | .sharp => sharpV2.test c ()
  | .aFrozen w => routeAFrozen.test c w
  | .aRefined w => routeARefined.test c w
  | .aRefinedR w => routeARefinedR.test c w
  | .aL1 w => L1.routeAL1.test c w
  | .bFrozen w => routeBFrozen.test c w
  | .bRefined w => routeBRefined.test c w
  | .bLN w => routeBRefinedLN.test c w
  | .bE w => routeBRefinedE.test c w
  | .aG w => routeARefinedG.test c w
  | .bG w => routeBRefinedG.test c w
  | .aS w => routeARefinedS.test c w
  | .hybrid w => Hybrid.routeHybrid.test c w
  | .aPacked b w => b.engine.test c w
  | .bGSLN w => routeBRefinedGSLN.test c w
  | .bGSE w => routeBRefinedGSE.test c w

/-- **The engine with every route.** Its soundness is each engine's own, branch by branch. -/
noncomputable def routeMax : EngineV2 where
  Wit := RouteMaxWit
  test := fun c w => routeMaxTest c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    cases w with
    | old => exact (EngineV2.ofEngine oldEngine).sound c () hω hdio B h
    | sharp => exact sharpV2.sound c () hω hdio B h
    | aFrozen w => exact routeAFrozen.sound c w hω hdio B h
    | aRefined w => exact routeARefined.sound c w hω hdio B h
    | aRefinedR w => exact routeARefinedR.sound c w hω hdio B h
    | aL1 w => exact L1.routeAL1.sound c w hω hdio B h
    | bFrozen w => exact routeBFrozen.sound c w hω hdio B h
    | bRefined w => exact routeBRefined.sound c w hω hdio B h
    | bLN w => exact routeBRefinedLN.sound c w hω hdio B h
    | bE w => exact routeBRefinedE.sound c w hω hdio B h
    | aG w => exact routeARefinedG.sound c w hω hdio B h
    | bG w => exact routeBRefinedG.sound c w hω hdio B h
    | aS w => exact routeARefinedS.sound c w hω hdio B h
    | hybrid w => exact Hybrid.routeHybrid.sound c w hω hdio B h
    | aPacked b w => exact b.engine.sound c w hω hdio B h
    | bGSLN w => exact routeBRefinedGSLN.sound c w hω hdio B h
    | bGSE w => exact routeBRefinedGSE.sound c w hω hdio B h

variable {n : ℕ} {α : Type} [CertArith α]

/-- **Soundness of the v2 certifier at `routeMax`**: the landed `CertifiedTorus`, under the
premises of `checkTorusCertificateV2_sound` only. -/
theorem checkTorusCertificateV2_routeMax_sound [LawfulCertArith α] {c : TorusCertificate n α}
    {w : RouteMaxWit} (h : checkTorusCertificateV2 routeMax c w = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateV2_sound routeMax h hω hdio

/-! ### Each engine on its witness branch, at every base (`rfl`) -/

section Branches

variable (B : BaseChecker) (c : TorusCertificate n α)

/-- **Never worse than the original landed certifier** `checkTorusCertificate`. -/
theorem checkTorusCertificateV2_routeMax_old :
    checkTorusCertificateV2 routeMax c .old = checkTorusCertificate c := rfl

theorem checkV2With_routeMax_old :
    checkV2With B routeMax c .old = checkV2With B (EngineV2.ofEngine oldEngine) c () := rfl

/-- **v2 is never worse than the landed certifier**, at `routeMax`. -/
theorem checkTorusCertificateV2_routeMax_sharp :
    checkTorusCertificateV2 routeMax c .sharp = checkTorusCertificateSharp c := rfl

theorem checkV2With_routeMax_sharp :
    checkV2With B routeMax c .sharp = checkV2With B sharpV2 c () := rfl

theorem checkV2With_routeMax_aFrozen (w : FrozenWit) :
    checkV2With B routeMax c (.aFrozen w) = checkV2With B routeAFrozen c w := rfl

theorem checkV2With_routeMax_aRefined (w : RefinedWit) :
    checkV2With B routeMax c (.aRefined w) = checkV2With B routeARefined c w := rfl

theorem checkV2With_routeMax_aRefinedR (w : RefinedWitR) :
    checkV2With B routeMax c (.aRefinedR w) = checkV2With B routeARefinedR c w := rfl

theorem checkV2With_routeMax_aL1 (w : L1.L1Wit) :
    checkV2With B routeMax c (.aL1 w) = checkV2With B L1.routeAL1 c w := rfl

theorem checkV2With_routeMax_bFrozen (w : RunBWit) :
    checkV2With B routeMax c (.bFrozen w) = checkV2With B routeBFrozen c w := rfl

theorem checkV2With_routeMax_bRefined (w : RefinedBWit) :
    checkV2With B routeMax c (.bRefined w) = checkV2With B routeBRefined c w := rfl

theorem checkV2With_routeMax_bLN (w : RefinedBWit) :
    checkV2With B routeMax c (.bLN w) = checkV2With B routeBRefinedLN c w := rfl

theorem checkV2With_routeMax_bE (w : RefinedBWit) :
    checkV2With B routeMax c (.bE w) = checkV2With B routeBRefinedE c w := rfl

theorem checkV2With_routeMax_aG (w : RefinedWitG) :
    checkV2With B routeMax c (.aG w) = checkV2With B routeARefinedG c w := rfl

theorem checkV2With_routeMax_bG (w : RefinedBWitG) :
    checkV2With B routeMax c (.bG w) = checkV2With B routeBRefinedG c w := rfl

theorem checkV2With_routeMax_aS (w : RefinedWitS) :
    checkV2With B routeMax c (.aS w) = checkV2With B routeARefinedS c w := rfl

theorem checkV2With_routeMax_hybrid (w : Hybrid.HybWit) :
    checkV2With B routeMax c (.hybrid w) = checkV2With B Hybrid.routeHybrid c w := rfl

theorem checkV2With_routeMax_aPacked (b : PackedBooks) (w : RefinedWit) :
    checkV2With B routeMax c (.aPacked b w) =
      checkV2With B (Packed.routeARefinedPacked b.bk b.mm b.rb b.tm b.rm) c w := rfl

theorem checkV2With_routeMax_bGSLN (w : RefinedBWitGS) :
    checkV2With B routeMax c (.bGSLN w) = checkV2With B routeBRefinedGSLN c w := rfl

theorem checkV2With_routeMax_bGSE (w : RefinedBWitGS) :
    checkV2With B routeMax c (.bGSE w) = checkV2With B routeBRefinedGSE c w := rfl

end Branches

/-! ### The witnesses of the older combined engines -/

/-- A witness of `routeAV2` (`sharpV2`, `routeAFrozen`, `routeARefined`). -/
def RouteMaxWit.ofAV2 : Unit ⊕ (FrozenWit ⊕ RefinedWit) → RouteMaxWit
  | .inl () => .sharp
  | .inr (.inl w) => .aFrozen w
  | .inr (.inr w) => .aRefined w

/-- A witness of `routeAV2'` (`routeAV2` and lever L8′). -/
def RouteMaxWit.ofAV2' : Unit ⊕ ((FrozenWit ⊕ RefinedWit) ⊕ RefinedWitR) → RouteMaxWit
  | .inl () => .sharp
  | .inr (.inl (.inl w)) => .aFrozen w
  | .inr (.inl (.inr w)) => .aRefined w
  | .inr (.inr w) => .aRefinedR w

/-- A witness of `routeAV2L1` (`routeAV2'` and the ℓ¹ entry). -/
def RouteMaxWit.ofAV2L1 :
    Unit ⊕ (((FrozenWit ⊕ RefinedWit) ⊕ RefinedWitR) ⊕ L1.L1Wit) → RouteMaxWit
  | .inl () => .sharp
  | .inr (.inl (.inl (.inl w))) => .aFrozen w
  | .inr (.inl (.inl (.inr w))) => .aRefined w
  | .inr (.inl (.inr w)) => .aRefinedR w
  | .inr (.inr w) => .aL1 w

/-- A witness of `routeABV2` (`routeAV2` and both forms of route B). -/
def RouteMaxWit.ofABV2 : Unit ⊕ ((FrozenWit ⊕ RefinedWit) ⊕ (RunBWit ⊕ RefinedBWit)) → RouteMaxWit
  | .inl () => .sharp
  | .inr (.inl (.inl w)) => .aFrozen w
  | .inr (.inl (.inr w)) => .aRefined w
  | .inr (.inr (.inl w)) => .bFrozen w
  | .inr (.inr (.inr w)) => .bRefined w

/-- A witness of `routeV2All`. -/
def RouteMaxWit.ofV2All :
    Unit ⊕ ((((FrozenWit ⊕ RefinedWit) ⊕ RefinedWitR) ⊕ L1.L1Wit) ⊕ (RunBWit ⊕ RefinedBWit)) →
      RouteMaxWit
  | .inl () => .sharp
  | .inr (.inl (.inl (.inl (.inl w)))) => .aFrozen w
  | .inr (.inl (.inl (.inl (.inr w)))) => .aRefined w
  | .inr (.inl (.inl (.inr w))) => .aRefinedR w
  | .inr (.inl (.inr w)) => .aL1 w
  | .inr (.inr (.inl w)) => .bFrozen w
  | .inr (.inr (.inr w)) => .bRefined w

/-- A witness of `routeV2AllLN`. -/
def RouteMaxWit.ofV2AllLN : routeV2All.Wit ⊕ RefinedBWit → RouteMaxWit
  | .inl w => .ofV2All w
  | .inr w => .bLN w

/-- A witness of `routeV2AllE`. -/
def RouteMaxWit.ofV2AllE : routeV2AllLN.Wit ⊕ RefinedBWit → RouteMaxWit
  | .inl w => .ofV2AllLN w
  | .inr w => .bE w

/-- A witness of `routeV2AllS`. -/
def RouteMaxWit.ofV2AllS : routeV2All.Wit ⊕ RefinedWitS → RouteMaxWit
  | .inl w => .ofV2All w
  | .inr w => .aS w

/-- A witness of `routeAV2G`. -/
def RouteMaxWit.ofAV2G : routeAV2.Wit ⊕ RefinedWitG → RouteMaxWit
  | .inl w => .ofAV2 w
  | .inr w => .aG w

/-- A witness of `routeV2G`. -/
def RouteMaxWit.ofV2G : routeAV2G.Wit ⊕ (RunBWit ⊕ RefinedBWitG) → RouteMaxWit
  | .inl w => .ofAV2G w
  | .inr (.inl w) => .bFrozen w
  | .inr (.inr w) => .bG w

/-- A witness of `routeV2Hyb`. -/
def RouteMaxWit.ofV2Hyb :
    Unit ⊕ (((((FrozenWit ⊕ RefinedWit) ⊕ RefinedWitR) ⊕ L1.L1Wit) ⊕ (RunBWit ⊕ RefinedBWit)) ⊕
      Hybrid.HybWit) → RouteMaxWit
  | .inl () => .sharp
  | .inr (.inl w) => .ofV2All (.inr w)
  | .inr (.inr w) => .hybrid w

section Older

variable (B : BaseChecker) (c : TorusCertificate n α)

theorem checkV2With_routeMax_ofAV2 (w : routeAV2.Wit) :
    checkV2With B routeMax c (.ofAV2 w) = checkV2With B routeAV2 c w := by
  rcases w with _ | w | w <;> rfl

theorem checkV2With_routeMax_ofAV2' (w : routeAV2'.Wit) :
    checkV2With B routeMax c (.ofAV2' w) = checkV2With B routeAV2' c w := by
  rcases w with _ | ((w | w) | w) <;> rfl

theorem checkV2With_routeMax_ofAV2L1 (w : routeAV2L1.Wit) :
    checkV2With B routeMax c (.ofAV2L1 w) = checkV2With B routeAV2L1 c w := by
  rcases w with _ | (((w | w) | w) | w) <;> rfl

theorem checkV2With_routeMax_ofABV2 (w : routeABV2.Wit) :
    checkV2With B routeMax c (.ofABV2 w) = checkV2With B routeABV2 c w := by
  rcases w with _ | ((w | w) | (w | w)) <;> rfl

theorem checkV2With_routeMax_ofV2All (w : routeV2All.Wit) :
    checkV2With B routeMax c (.ofV2All w) = checkV2With B routeV2All c w := by
  rcases w with _ | ((((w | w) | w) | w) | (w | w)) <;> rfl

theorem checkV2With_routeMax_ofV2AllLN (w : routeV2AllLN.Wit) :
    checkV2With B routeMax c (.ofV2AllLN w) = checkV2With B routeV2AllLN c w := by
  rcases w with w | w
  · exact checkV2With_routeMax_ofV2All B c w
  · rfl

theorem checkV2With_routeMax_ofV2AllE (w : routeV2AllE.Wit) :
    checkV2With B routeMax c (.ofV2AllE w) = checkV2With B routeV2AllE c w := by
  rcases w with w | w
  · exact checkV2With_routeMax_ofV2AllLN B c w
  · rfl

theorem checkV2With_routeMax_ofV2AllS (w : routeV2AllS.Wit) :
    checkV2With B routeMax c (.ofV2AllS w) = checkV2With B routeV2AllS c w := by
  rcases w with w | w
  · exact checkV2With_routeMax_ofV2All B c w
  · rfl

theorem checkV2With_routeMax_ofAV2G (w : routeAV2G.Wit) :
    checkV2With B routeMax c (.ofAV2G w) = checkV2With B routeAV2G c w := by
  rcases w with w | w
  · exact checkV2With_routeMax_ofAV2 B c w
  · rfl

theorem checkV2With_routeMax_ofV2G (w : routeV2G.Wit) :
    checkV2With B routeMax c (.ofV2G w) = checkV2With B routeV2G c w := by
  rcases w with w | w | w
  · exact checkV2With_routeMax_ofAV2G B c w
  · rfl
  · rfl

theorem checkV2With_routeMax_ofV2Hyb (w : Hybrid.routeV2Hyb.Wit) :
    checkV2With B routeMax c (.ofV2Hyb w) = checkV2With B Hybrid.routeV2Hyb c w := by
  rcases w with _ | w | w
  · rfl
  · exact checkV2With_routeMax_ofV2All B c (.inr w)
  · rfl

end Older

/-! ### The choice of the base -/

/-- A choice of the sub-checks other than the threshold test. -/
inductive BaseSel where
  /-- `landedBase`. -/
  | landed
  /-- `cornerBase`: the corner bounds of C1 for the embedding and the invariance. -/
  | corner
  /-- `trigBase`: the cosh bounds. -/
  | trig
  /-- `Packed.gramPackedBase`: the packed Gram stage. -/
  | gramPacked (bk : Packed.PGramBook) (mm : Packed.PGramMemo)
  /-- `Packed.torsPackedBase`: the packed Gram and packed torsion stages. -/
  | torsPacked (bk : Packed.PGramBook) (mm : Packed.PGramMemo) (tb : Packed.PTorsBook)
      (tm : Packed.PTorsMemo)
  /-- `Packed.torsRBase`: the packed Gram and rounded packed torsion stages. -/
  | torsR (b : PackedBooks)

/-- The base checker of a selection. -/
def BaseSel.toBase : BaseSel → BaseChecker
  | .landed => landedBase
  | .corner => cornerBase
  | .trig => trigBase
  | .gramPacked bk mm => Packed.gramPackedBase bk mm
  | .torsPacked bk mm tb tm => Packed.torsPackedBase bk mm tb tm
  | .torsR b => b.base

/-- **The certifier with every route and every base**: the base the selection `b` names, then the
route the witness `w` names. -/
noncomputable def checkTorusCertificateMax (c : TorusCertificate n α) (b : BaseSel)
    (w : RouteMaxWit) : Bool :=
  checkV2With b.toBase routeMax c w

/-- **Soundness**: the landed `CertifiedTorus`, under the premises of
`checkTorusCertificateV2_sound` only. -/
theorem checkTorusCertificateMax_sound [LawfulCertArith α] {c : TorusCertificate n α}
    {b : BaseSel} {w : RouteMaxWit} (h : checkTorusCertificateMax c b w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound b.toBase routeMax h hω hdio

/-- At the landed base the certifier is `checkTorusCertificateV2 routeMax`. -/
theorem checkTorusCertificateMax_landed (c : TorusCertificate n α) (w : RouteMaxWit) :
    checkTorusCertificateMax c .landed w = checkTorusCertificateV2 routeMax c w := rfl

/-- **The packed certifier** of `Packed.checkV2With_packed_sound` is one selection. -/
theorem checkTorusCertificateMax_packed (c : TorusCertificate n α) (b : PackedBooks)
    (w : RefinedWit) :
    checkTorusCertificateMax c (.torsR b) (.aPacked b w) =
      checkV2With (Packed.torsRBase b.bk b.mm b.rb b.tm b.rm)
        (Packed.routeARefinedPacked b.bk b.mm b.rb b.tm b.rm) c w := rfl

/-- Every selection and route is the certifier of that base and that engine (with the rows of the
branch table above). -/
theorem checkTorusCertificateMax_eq (c : TorusCertificate n α) (b : BaseSel) (w : RouteMaxWit) :
    checkTorusCertificateMax c b w = (b.toBase.check c && routeMaxTest c w) := rfl

end KAM.CertificateSharp.V2

end
