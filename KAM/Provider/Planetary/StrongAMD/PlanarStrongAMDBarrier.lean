/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary

/-!
# Provider for `KAM.Planetary.StrongAMD.planar_strongAMD_barrier`

Provider for the frozen theorem `KAM.Planetary.StrongAMD.planar_strongAMD_barrier`, anchor LP0 (the
planar sharp strong barrier (full MAIN Lemma 5));
track LP (`LP:MAIN L5 (162–166), with L2–L4 (110–160); N11`).

The theorem `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_barrier` states the anchor's exact
type text (its draft file under `docs/tracks/LP/freeze/draft7/`) and is proved in one line by the
implementation theorem `KAM.Planetary.StrongAMD.lp0_planar_barrier_source`. This module is
quarantined: no module other than the anchor may import it (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

theorem planar_strongAMD_barrier {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUch : U ⊆ chamber ν) (m : ℝ) (hm : 0 < m) :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      (∀ I : Fin n → ℝ, ∀ hI : I ∈ U, ∀ e : Fin n → ℝ,
        (∀ i, e i ∈ Set.Icc (0 : ℝ) 1) →
        (∑ i, I i * eccDeficit (e i)) ≤ orderedStrongThreshold hn ⟨I, hUch hI⟩ - m →
        (∀ i, dStar ≤ actionAxis ν I i * (1 - e i)) ∧
        (∀ a : AdjIdx n, dPair ≤ actionAxis ν I a.upperIdx * (1 - e a.upperIdx) -
          actionAxis ν I a.1 * (1 + e a.1))) ∧
      ∃ K : Set (Phase (n * 2)), IsCompact K ∧
        (∀ w ∈ K, NoCollision w.1 ∧ ∀ i, keplerEnergy ν w i < 0) ∧
      ∀ z : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) →
        ∀ hΛ : (fun i => keplerAction ν z i) ∈ U,
        ∀ h : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0,
        sourceStrongAMD (⟨z, h⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hUch hΛ⟩ - m →
        (∀ i, dStar ≤ keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i))) ∧
        (∀ a : AdjIdx n, dPair ≤ keplerAxis ν z a.upperIdx *
            (1 - planeLength (keplerEccVector ν z a.upperIdx)) -
            keplerAxis ν z a.1 * (1 + planeLength (keplerEccVector ν z a.1))) ∧
        (∀ i, dStar ≤ planeLength (bodyVector z.1 i)) ∧
        (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)) ∧
        z ∈ K ∧
        (∀ i, m ≤ |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ∧
          0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) * totalMomentum z) := by
  exact _root_.KAM.Planetary.StrongAMD.lp0_planar_barrier_source hn ν hν U hU hUch m hm

end KAM.Provider.Planetary.StrongAMD

end
