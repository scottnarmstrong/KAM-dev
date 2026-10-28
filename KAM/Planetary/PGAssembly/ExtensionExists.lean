/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.HigherCauchy
public import KAM.Planetary.PGAssembly.ExtensionProps

/-!
# P Part 5: existence of the extension (`bpP:p5:ext`, `stepP:p5:ext-H0`)

The holomorphic extension of `H0` to a thin tube over `closure V` (P5-CG on the compact
`closure V`, using `hfreq.1`), Cauchy estimates for its first two derivatives, and the assembly of
a `PGExtension d` from the periodized `PGTube.P` and this `H0` extension.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

variable {a b : ℕ}

/-- Cauchy estimates on a thin tube. -/
theorem tube_fderiv_bounds {n : ℕ} {X : Set (Fin n → ℝ)} {H : (Fin n → ℂ) → ℂ} {rho M : ℝ}
    (hrho : 0 < rho) (hH : DifferentiableOn ℂ H (KAM.actionNbhd X rho))
    (hb : ∀ z ∈ KAM.actionNbhd X rho, ‖H z‖ ≤ M) {delta : ℝ} (hd : delta ≤ rho / 4)
    {I : Fin n → ℂ} (hI : I ∈ KAM.actionNbhd X delta) :
    ‖fderiv ℂ H I‖ ≤ M / (rho / 2) ∧ ‖fderiv ℂ (fderiv ℂ H) I‖ ≤ 4 * M / (rho / 2) ^ 2 := by
  obtain ⟨J, hJ, hIJ⟩ := mem_actionNbhd_iff.1 hI
  have hball : closedBall I (rho / 2) ⊆ KAM.actionNbhd X rho := by
    intro z hz
    refine mem_actionNbhd_iff.2 ⟨J, hJ, ?_⟩
    rw [mem_closedBall_iff_norm] at hz
    calc ‖z - KAM.realInclusion n J‖ = ‖(z - I) + (I - KAM.realInclusion n J)‖ := by
          congr 1; abel
      _ ≤ ‖z - I‖ + ‖I - KAM.realInclusion n J‖ := norm_add_le _ _
      _ < rho := by linarith
  have hr2 : 0 < rho / 2 := by positivity
  have h1 := KAM.norm_fderiv_le_of_closedBall_bound (isOpen_actionNbhd X rho) hH hr2 hball
    (fun w hw => hb w (hball hw))
  have h2 := KAM.norm_iteratedFDeriv_two_le_of_closedBall (isOpen_actionNbhd X rho) hH hr2 hball
    (fun w hw => hb w (hball hw))
  refine ⟨h1, ?_⟩
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact h2

theorem exists_H0_tube (d : PGData a b) :
    ∃ (rho M : ℝ) (H : (Fin a → ℂ) → ℂ), 0 < rho ∧ 0 < M ∧
      DifferentiableOn ℂ H (KAM.actionNbhd (closure d.V) rho) ∧
      (∀ I : Fin a → ℝ, KAM.realInclusion a I ∈ KAM.actionNbhd (closure d.V) rho →
        H (KAM.realInclusion a I) = (d.H0 I : ℂ)) ∧
      (∀ z ∈ KAM.actionNbhd (closure d.V) rho, ‖H z‖ ≤ M) :=
  compact_real_complexification d.hVb.isCompact_closure (d.hfreq.1.mono d.hVW)

theorem pgExtension_exists (d : PGData a b) : Nonempty (PGExtension d) := by
  obtain ⟨T⟩ := pgTube_exists d
  obtain ⟨rhoH, MH, H, hrhoH, hMH, hH, hHreal, hHb⟩ := exists_H0_tube d
  set delta := min T.rho (min (rhoH / 4) (1 / 2)) with hdelta
  have hd0 : 0 < delta := lt_min T.rho_pos (lt_min (by positivity) (by norm_num))
  have hd1 : delta ≤ T.rho := min_le_left _ _
  have hd2 : delta ≤ rhoH / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hd3 : delta ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : ∀ I ∈ KAM.actionNbhd (closure d.V) delta, I ∈ KAM.actionNbhd (closure d.V) rhoH :=
    fun I hI => mem_actionNbhd_mono (by linarith) hI
  have hr2 : 0 < rhoH / 2 := by positivity
  refine ⟨{ delta := delta
            MP := max T.M 1
            M0 := max MH (max (MH / (rhoH / 2)) (4 * MH / (rhoH / 2) ^ 2))
            P := T.P
            H0 := H
            delta_pos := hd0
            delta_lt := by linarith
            MP_pos := lt_max_of_lt_right one_pos
            M0_pos := lt_max_of_lt_left hMH
            holo := fun mu hmu => T.P_holo hd1 hmu
            continuous := T.P_continuous hd1
            agrees := fun mu hmu w hw hwd => T.P_agrees hd1 hmu hw hwd
            periodic := fun mu hmu z hz k => T.P_periodic hd1 hmu hz k
            bound := fun mu hmu z hz => (T.P_bound hd1 hmu hz).trans (le_max_left _ _)
            h0holo := hH.mono hsub
            h0real := fun I hI => hHreal I (hsub _ hI)
            h0bounds := fun I hI => ?_ }⟩
  obtain ⟨h1, h2⟩ := tube_fderiv_bounds hrhoH hH hHb hd2 hI
  refine ⟨(hHb I (hsub I hI)).trans (le_max_left _ _), h1.trans ?_, h2.trans ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

end KAM.Planetary

end
