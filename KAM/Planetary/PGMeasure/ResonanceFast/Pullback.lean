/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.Setting
public import KAM.Planetary.PGMeasure.ResonanceLarge.Frequency
public import KAM.Measure.Lipschitz

/-!
# P Part 4: the pullback from frequency coordinates (`stepP:p4:dm-y`)

`pullMap d (y, ξ) = (g y, ξ)` is the inverse of `Φ(I, ξ) = (ω_{H₀} I, ξ)`. It is `Λ_g`-Lipschitz on
`ω(core) × ℝᵇ`, so it multiplies measure by at most `Λ_g^(a+b)` (`volume_pullMap_image_le`), and the
resonant set of a mode in actions `(I, ξ)` lies in the image under `pullMap` of its frequency
coordinate set `resonanceSet` (`mem_pullMap_image_of_resonant`). Internal helper for
`two_scale_diophantine_measure`; design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RA.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- `stepP:p4:dm-y`: the product map `(y, ξ) ↦ (g y, ξ)` on flat coordinates. -/
def pullMap (d : MeasureData a b) (z : Fin (a+b) → ℝ) : Fin (a+b) → ℝ :=
  Fin.append (d.g (blockFast z)) (blockSlow z)

theorem norm_append_le {u : Fin a → ℝ} {v : Fin b → ℝ} {c : ℝ} (hu : ‖u‖ ≤ c) (hv : ‖v‖ ≤ c)
    (hc : 0 ≤ c) : ‖Fin.append u v‖ ≤ c := by
  refine (pi_norm_le_iff_of_nonneg hc).mpr fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa using (norm_le_pi_norm u i).trans hu
  · simpa using (norm_le_pi_norm v i).trans hv

theorem pullMap_lip (d : MeasureData a b) {z z' : Fin (a+b) → ℝ} (hz : blockFast z ∈ freqCore d)
    (hz' : blockFast z' ∈ freqCore d) : ‖pullMap d z - pullMap d z'‖ ≤ d.Lg * ‖z - z'‖ := by
  have hLg := d.hLg
  have hn := norm_nonneg (z - z')
  have e : pullMap d z - pullMap d z' =
      Fin.append (d.g (blockFast z) - d.g (blockFast z')) (blockSlow z - blockSlow z') := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [pullMap]
  rw [e]
  refine norm_append_le ?_ ?_ (by positivity)
  · refine (dist_g_le d hz hz').trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    exact norm_blockFast_le (z - z')
  · refine (norm_blockSlow_le (z - z')).trans ?_
    nlinarith

/-- `stepP:p4:dm-y`: the Lipschitz-image bound `μ(Ψ(S)) ≤ Λ_g^(a+b) μ(S)` for `S ⊆ ω(core) × ℝᵇ`. -/
theorem volume_pullMap_image_le (d : MeasureData a b) {S : Set (Fin (a+b) → ℝ)}
    (hS : ∀ z ∈ S, blockFast z ∈ freqCore d) :
    volume (pullMap d '' S) ≤ ENNReal.ofReal (d.Lg ^ (a+b)) * volume S :=
  KAM.lip_image fun z hz z' hz' => pullMap_lip d (hS z hz) (hS z' hz')

/-- The frequency-coordinate point over a flat action point `J`. -/
def pushMap (d : MeasureData a b) (J : Fin (a+b) → ℝ) : Fin (a+b) → ℝ :=
  Fin.append (fastFrequency d.H0 (blockFast J)) (blockSlow J)

theorem pullMap_pushMap (d : MeasureData a b) {J : Fin (a+b) → ℝ} (hJ : blockFast J ∈ d.core) :
    pullMap d (pushMap d J) = J := by
  have hW : blockFast J ∈ d.W := d.hVW (subset_closure (d.hcoreV hJ))
  have : pullMap d (pushMap d J) = Fin.append (blockFast J) (blockSlow J) := by
    simp [pullMap, pushMap, blockFast_append_large, blockSlow_append_large, d.hinv _ hW]
  rw [this]
  exact Fin.append_castAdd_natAdd (f := J)

theorem pushMap_mem_sliceDomain (d : MeasureData a b) {Q : Set (Fin b → ℝ)}
    {J : Fin (a+b) → ℝ} (hJ : J ∈ joinedActions d.core Q) :
    blockFast (pushMap d J) ∈ freqCore d ∧ blockSlow (pushMap d J) ∈ Q := by
  refine ⟨?_, ?_⟩
  · rw [pushMap, blockFast_append_large]
    exact ⟨blockFast J, hJ.1, rfl⟩
  · simpa [pushMap, blockSlow_append_large] using hJ.2

/-- `stepP:p4:dm-y`: a resonant action point `J ∈ core × Q` with a mode `k` is the `pullMap`-image
of a point of the frequency-coordinate resonant set of `k`. -/
theorem mem_pullMap_image_of_resonant (d : MeasureData a b) (mu : ℝ) {Q : Set (Fin b → ℝ)}
    {J : Fin (a+b) → ℝ} (hJ : J ∈ joinedActions d.core Q) {k : Fin (a+b) → ℤ} {alpha : ℝ}
    (hk : |∑ i, (k i : ℝ) * freq d.H0 d.P0 d.Omega d.beta mu J i| < alpha) :
    J ∈ pullMap d '' resonanceSet d mu Q k alpha := by
  have hp := pullMap_pushMap d hJ.1
  have hs := pushMap_mem_sliceDomain d hJ
  refine ⟨pushMap d J, ⟨hs.1, hs.2, ?_⟩, hp⟩
  have : pullFreq d mu k (pushMap d J) = ∑ i, (k i : ℝ) * freq d.H0 d.P0 d.Omega d.beta mu J i := by
    unfold pullFreq
    have := hp
    unfold pullMap at this
    rw [this]
  rw [this]
  exact hk

end KAM.Planetary

end
