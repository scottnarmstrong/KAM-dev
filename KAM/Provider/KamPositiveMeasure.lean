/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Defs
import KAM.Head.Assembly
import KAM.Head.Frequency
import KAM.Head.Parameters
import KAM.Frozen.Theorems.AposterioriKam
import KAM.Frozen.Theorems.LocalUniquenessFlow
import KAM.Frozen.Theorems.VolumeNotDiophantineLe

/-!
# Provider for the frozen theorem `KAM.kam_positive_measure`

The proof of `KAM.kam_positive_measure` is assembled here as `KAM.Provider.kam_positive_measure`,
from graph predecessors and approved external inputs only. While the frozen anchor is `DRAFT_SORRY`,
this module is quarantined: no module other than the anchor may import it.

This file is the one place that may import the sealed frozen theorems `KAM.aposteriori_kam` (G1),
`KAM.local_uniqueness_flow` (G2) and `KAM.volume_not_diophantine_le` (G3).

* `KAM.Provider.exists_gValid` discharges the premise `KAM.Head.GValid` of the Part 4 modules: it
  produces the constants of G1 at the two tuples of Definition `bp:p4:parameters`, of G2 at
  `ρ = s/16`, and of G3 for `Ω = ∇h(B)`, together with their defining properties.
* `KAM.Provider.kam_positive_measure` is the HEAD theorem with exactly the type of the frozen
  `KAM.kam_positive_measure`. It builds `Head.Data` from the binders, takes the constants from
  `exists_gValid`, and applies `KAM.Head.head_of_gValid`.
-/

public section

open MeasureTheory KAM.Head

namespace KAM.Provider

/-- The constants of the frozen G1 (two tuples), G2 and G3 exist for the data of HEAD. Lives in
`KAM/Provider/KamPositiveMeasure.lean` (the only module allowed to import the sealed anchors). -/
theorem exists_gValid {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
    (hD : Data τ s₀ r₀ B h Lh) : ∃ gc : GConsts, GValid τ s₀ r₀ B h Lh gc := by
  obtain ⟨⟨⟨hn, hτ⟩, ⟨h8, h84⟩, ⟨h16, h1632⟩, hM, hσK, hσB, hσT, hμ⟩, -⟩ := parameters hD
  obtain ⟨C11, C21, h11, h21, hb1⟩ :=
    KAM.aposteriori_kam hn hτ h8 h84 hM hσK hσB hσT hμ (one_pos : (0 : ℝ) < 1)
  obtain ⟨C12, C22, h12, h22, hb2⟩ :=
    KAM.aposteriori_kam hn hτ h16 h1632 hM hσK hσB hσT hμ (one_pos : (0 : ℝ) < 1)
  obtain ⟨cG, hcG, hb3⟩ := KAM.local_uniqueness_flow hn hτ h16 hM hσK hσB hσT hμ
  obtain ⟨C3, hC3⟩ := KAM.volume_not_diophantine_le hD.tau_gt (freq_map hD).2.2.2.2.2.2
  exact ⟨⟨C11, C21, C12, C22, cG, C3⟩, ⟨⟨h11, h21, h12, h22, hcG⟩, hb1, hb2, hb3, hC3⟩⟩

/-- **HEAD.** Positive-measure KAM theorem with rate: the provider of the frozen
`KAM.kam_positive_measure`, with exactly its type. -/
theorem kam_positive_measure {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 < τ)
    {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} (hB_open : IsOpen B) (hB_bdd : Bornology.IsBounded B)
    (hB_layer : ∃ C_B : ℝ, ∀ δ : ℝ, 0 < δ →
      volume {I ∈ B | Metric.infDist I Bᶜ < δ} ≤ ENNReal.ofReal (C_B * δ))
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    (h_nondeg : ∃ L : ℝ, ∀ I ∈ closure B, ∀ J ∈ closure B,
      ‖I - J‖ ≤ L * ‖frequencyMap h I - frequencyMap h J‖) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
          f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
        (∀ θ I : Fin n → ℝ,
          ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
          (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
        volume (fundamentalDomain B \
            kamCover h f B r₀ τ (C * Real.sqrt ε)) ≤
          ENNReal.ofReal (C * ε ^ ((1 : ℝ) / 4)) := by
  obtain ⟨CB, hCB⟩ := hB_layer
  obtain ⟨Lh, hLh⟩ := h_nondeg
  have hD : Data τ s₀ r₀ B h Lh := ⟨hn, hτ, hs₀, hr₀, hB_open, hB_bdd, hh, hh_real, hLh⟩
  obtain ⟨gc, hgc⟩ := exists_gValid hD
  exact head_of_gValid hD hCB hgc

end KAM.Provider
