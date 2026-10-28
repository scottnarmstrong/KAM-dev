/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Beta

/-!
# Planar quartic torsion: uniform lower bound on a compact set (P11C, package T17)

Blueprint P, Part 11b (`bpP:p11b:remain`): the determinant of `p11c_beta` is bounded away from
zero on a compact set where it is continuous and nonvanishing, by the compact minimum of `|det|`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
namespace KAM.Planetary
open KAM KAM.Kepler

theorem remain (p : PlanarData) (K : Set (Fin 2 → ℝ)) (hK : IsCompact K)
    (hn : ∀ a ∈ K, (p11c_beta p a).det ≠ 0)
    (hc : ContinuousOn (fun a => (p11c_beta p a).det) K) :
    ∃ B : ℝ, 0 < B ∧ ∀ a ∈ K, B ≤ |(p11c_beta p a).det| := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨a₀, ha₀, hmin⟩ := hK.exists_isMinOn hne hc.abs
  exact ⟨|(p11c_beta p a₀).det|, abs_pos.mpr (hn a₀ ha₀), fun a ha => hmin ha⟩

end KAM.Planetary
