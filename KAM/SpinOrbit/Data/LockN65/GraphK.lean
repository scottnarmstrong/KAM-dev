/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Cert
public import KAM.SpinOrbit.Data.LockN65.RealLowerK

/-!
# The graph check with a product key per SOS square (lock-owned)

`checkSoGraphK` is the landed `checkSoGraph` (`KAM/SpinOrbit/Graph/Cert.lean`) with the three SOS
squares under the keys `[7, 0]` (mono), `[7, 1]` (pLo) and `[7, 2]` (pHi) of `checkRealLowerBoundK`,
so that each square can carry its own packed advice. `checkSoGraphK_sound` gives the same four facts
as `checkSoGraph_sound`; its proof is the landed one with `checkRealLowerBoundK_sound`.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.SpinOrbit CertArith
open SoGraph

/-- **The graph check, a key per SOS square**: as `checkSoGraph`, the squares under `[7, 0]`,
`[7, 1]`, `[7, 2]`. -/
def checkSoGraphK {α : Type} [CertArith α] (g : SoGraphCert α) : Bool :=
  decide (g.base.params.disp < g.mono * g.base.params.rhoInf) &&
    checkRealLowerBoundK g.base.weight g.base.cfgLow [7, 0] (soGraphMonoModel g) g.mono₀ g.mono
      g.sosMono &&
    checkRealLowerBoundK g.base.weight g.base.cfgLow [7, 1] (soGraphActionModel g) g.pLo₀ g.pLo
      g.sosLo &&
    checkRealLowerBoundK g.base.weight g.base.cfgLow [7, 2] (soGraphActionModel g).negM (-g.pHi₀)
      (-g.pHi) g.sosHi

variable {α : Type} [CertArith α] [LawfulCertArith α]

theorem checkSoGraphK_sound {g : SoGraphCert α}
    (hW : checkWeight g.base.weight g.base.expHalvings g.base.expOrder = true)
    (hpe : checkPiEnclosure g.base.piEnc = true) (hg : checkSoGraphK g = true) :
    (g.base.params.disp : ℝ) < g.mono * g.base.params.rhoInf ∧
      (∀ x y : ℝ, (g.mono : ℝ) ≤ ((fderiv ℂ g.base.K (realPt x y) (realPt 1 0)).1 0).re) ∧
      (∀ x y : ℝ, (g.pLo : ℝ) ≤ ((g.base.K (realPt x y)).2 0).re) ∧
      (∀ x y : ℝ, ((g.base.K (realPt x y)).2 0).re ≤ g.pHi) := by
  simp only [checkSoGraphK, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨hm, hmono⟩, hlo⟩, hhi⟩ := hg
  have hM : (soGraphMonoModel g).Encloses 2 g.base.weight.rho
      fun θ => (fderiv ℂ g.base.K θ (Pi.single 0 1)).1 0 :=
    ((dkModels_encloses (n := 2) hW hpe g.base.emb (.inl 0) 0).toDeg hW hpe 0).of_eq_fun
      fun θ => by rw [KAM.Torus.tangentMat_apply, KAM.Torus.sumVec_apply, Sum.elim_inl]; rfl
  have hA : (soGraphActionModel g).Encloses 2 g.base.weight.rho
      fun θ => (g.base.K θ).2 0 :=
    (realCompModel_encloses 2 _ _ _).toDeg hW hpe 0
  refine ⟨by exact_mod_cast hm, fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [realPt_one_zero]
    exact checkRealLowerBoundK_sound hW _ _ hM hmono ![x, y]
  · exact checkRealLowerBoundK_sound hW _ _ hA hlo ![x, y]
  · have h := checkRealLowerBoundK_sound hW _ _ hA.negM hhi ![x, y]
    have e : (fun i => ((![x, y] i : ℝ) : ℂ)) = realPt x y := rfl
    rw [e, Complex.neg_re] at h
    push_cast at h
    linarith

end KAM.SpinOrbit.Data.LockN65
