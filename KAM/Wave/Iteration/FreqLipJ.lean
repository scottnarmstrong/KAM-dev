/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ConvSource
public import KAM.Wave.Iteration.PrepShiftJ
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: Lipschitz frequencies with the blueprint's constants (`bpW:w6:freq-lip`,
`bpW:w6:exclusion`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w6:freq-lip`, `bpW:w6:exclusion`.

W6-ITER's `W6PrepHyp.w6WaveFamily` has the constants `ε₁ = 0`, `ε₂ = 3γα + 4ε₀` (deviation D4: the
normal shift of the preparatory step was only available with the weight `J^{1/2}`). With the
`J`-weighted shift `W6PrepHyp.shift_Omega_J` (W5's frequency bridge, module `PrepShiftJ`),
W6-PREP's `w6IsFreqPair_of_bounds` applies verbatim and gives the blueprint's constants
`ε_ω = 6πγα + 8πε₀`, `ε₁ = 3γα`, `ε₂ = 4ε₀`, `θ`:

* `W6PrepHyp.w6wavePairJ`: (H1)–(H2) at every stage with these constants;
* `W6PrepHyp.w6WaveFamilyJ`: the admissible family (`D_ν = Π_{ν-1}`, thresholds `K_ν`; same
  domains and frequencies as `w6WaveFamily`);
* `W6PrepHyp.w6ExclusionJ`: `Π ∖ Π_* ⊆ ℰ` for this family.
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.Wave

namespace W6PrepHyp

variable {m : ℝ} {hm : 0 < m} {Pi : Set (Fin 2 → ℝ)} {α r ε : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase} {ε₀ : ℝ}

/-- **(H1)–(H2) at every stage, blueprint constants** (`bpW:w6:freq-lip`, steps `fl-size`,
`fl-lip`, `fl-borel`): `ε_ω = 6πγα + 8πε₀`, `ε₁ = 3γα`, `ε₂ = 4ε₀`, `θ`. -/
theorem w6wavePairJ (hS : MeasSetup m hm Pi α) (H : W6PrepHyp m hm Pi α r ε P X)
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) (ν : ℕ) :
    IsFreqPair m hm Pi α (H.waveD ε₀ ν) (H.waveSeq ε₀ ν).om
      (fun ξ => w6Om7 ((H.waveSeq ε₀ ν).Om ξ))
      (6 * π * w6Gamma m hm * α + 8 * π * ε₀) (3 * w6Gamma m hm * α) (4 * ε₀)
      (w6Theta m hm) := by
  have hR := w6StepReal_holds
  have hRm := w6StepRealMod_holds
  have hC := H.w6Applicable_of_stepRealMod hRm hlo hhi
  have hε₀ : 0 < ε₀ := lt_of_lt_of_le (w6EpsFlat_pos H.hα H.hε) hlo
  have hsub := H.waveD_subset (ε₀ := ε₀) ν
  have hl0 : (w6WaveSeq m hm α r ε ε₀).lam 0 = alphaCheck α / w6M0 m hm :=
    waveSeq_lam_zero r ε ε₀
  obtain ⟨hc0, -, -, -, -, -⟩ := alpha_facts m hm H.hα H.hα0
  have hlam0 : 0 < alphaCheck α / w6M0 m hm := div_pos hc0 (w6M0_pos m hm)
  have hlam : 0 < α / w6M m hm := div_pos H.hα (w6M_pos m hm)
  obtain ⟨b₀, b₁, hb0, hb1, hbs, hbb, hbl⟩ := H.shift_omega
  obtain ⟨c₀, c₁, hc0', hc1, hcs, hcb, hcl⟩ := H.shift_Omega_J
  have hmem := fun {ξ} (hξ : ξ ∈ H.waveD ε₀ ν) => H.waveD_mem hR hRm hlo hhi ν hξ
  have hmul : ∀ {L x c y : ℝ}, 0 < L → x ≤ c / L * y → L * x ≤ c * y := fun {L x c y} hL h => by
    have := mul_le_mul_of_nonneg_left h hL.le
    rwa [show L * (c / L * y) = c * y by field_simp] at this
  refine w6IsFreqPair_of_bounds (H.waveD_meas hR hRm hS hlo hhi ν)
    (hsub.trans Set.sdiff_subset) H.hα H.hα0 H.hε.le H.hεγ hε₀.le hhi
    (ωh := fun ξ => H.om0 ξ - omegaTan m hm ξ) (ω0 := H.om0)
    (Ωh := fun ξ j => w6Om7 (H.Om0 ξ) j - omegaNor m hm ξ j)
    (Ω0 := fun ξ => w6Om7 (H.Om0 ξ))
    (fun ξ _ => by abel) (fun ξ _ j => by ring)
    (fun ξ hξ => le_trans (hbb ξ (hsub hξ)) (by nlinarith))
    (fun ξ hξ ζ hζ => ?_) (fun ξ hξ j => le_trans (hcb ξ (hsub hξ) j) (by nlinarith))
    (fun ξ hξ ζ hζ j => ?_) (fun ξ hξ => ?_) (fun ξ hξ ζ hζ => ?_) (fun ξ hξ j => ?_)
    (fun ξ hξ ζ hζ j => ?_)
  · have h := hbl ξ (hsub hξ) ζ (hsub hζ)
    have := mul_le_mul_of_nonneg_left h hlam.le
    have hn := norm_nonneg (ξ - ζ)
    have : α / w6M m hm * (b₁ * ‖ξ - ζ‖) ≤ 6 * π * ε * ‖ξ - ζ‖ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) hn
    have e : H.om0 ξ - omegaTan m hm ξ - (H.om0 ζ - omegaTan m hm ζ) =
        (H.om0 ξ - omegaTan m hm ξ) - (H.om0 ζ - omegaTan m hm ζ) := rfl
    linarith
  · have h := hcl ξ (hsub hξ) ζ (hsub hζ) j
    have := mul_le_mul_of_nonneg_left h hlam.le
    have hn := norm_nonneg (ξ - ζ)
    have : α / w6M m hm * (c₁ * ‖ξ - ζ‖) ≤ 3 * ε * ‖ξ - ζ‖ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) hn
    linarith
  · exact (w6Seq_om_partial hR hC ν (hmem hξ) (hmem hξ)).1
  · have h := (w6Seq_om_partial hR hC ν (hmem hξ) (hmem hζ)).2
    rw [hl0] at h
    exact hmul hlam0 h
  · exact (w6Seq_Om_partial hR hC ν (hmem hξ) (hmem hξ) j).1
  · have h := (w6Seq_Om_partial hR hC ν (hmem hξ) (hmem hζ) j).2
    rw [hl0] at h
    exact hmul hlam0 h

/-- **Lipschitz frequencies, blueprint constants** (`bpW:w6:freq-lip`): the admissible family of
the wave iteration, `D_ν = Π_{ν-1}`, thresholds `K_ν`, `ε_ω = 6πγα + 8πε₀`, `ε₁ = 3γα`,
`ε₂ = 4ε₀`, `θ`. -/
def w6WaveFamilyJ (hS : MeasSetup m hm Pi α) (H : W6PrepHyp m hm Pi α r ε P X)
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    AdmissibleFamily m hm Pi α :=
  w6AdmissibleFamilyOfPairs (w6WaveSeq m hm α r ε ε₀)
    (w6WaveSeq_valid H.hα H.hα0 H.hr H.hε (lt_of_lt_of_le (w6EpsFlat_pos H.hα H.hε) hlo))
    (H.waveD ε₀) (fun ν => (H.waveSeq ε₀ ν).om) (fun ν ξ => w6Om7 ((H.waveSeq ε₀ ν).Om ξ))
    _ _ _ _ (H.w6wavePairJ hS hlo hhi)

/-- **Exclusion** (`bpW:w6:exclusion`) for the family with the blueprint constants:
`Π ∖ Π_* ⊆ ℰ`. -/
theorem w6ExclusionJ (hS : MeasSetup m hm Pi α) (H : W6PrepHyp m hm Pi α r ε P X)
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    Pi \ H.wavePiStar ε₀ ⊆ exclSet m hm (H.w6WaveFamilyJ hS hlo hhi) := by
  have hC := H.w6Applicable_of_stepRealMod w6StepRealMod_holds hlo hhi
  have h := w6_exclusion_seq m hm (w6WaveSeq m hm α r ε ε₀)
    (w6WaveSeq_valid H.hα H.hα0 H.hr H.hε (lt_of_lt_of_le (w6EpsFlat_pos H.hα H.hε) hlo)) rfl
    (H.w6WaveFamilyJ hS hlo hhi) (fun _ => rfl) (fun _ => rfl)
  unfold wavePiStar
  rw [w6PiStarIt_eq_of_stepReal w6StepReal_holds hC]
  exact h

end W6PrepHyp

end KAM.Wave
