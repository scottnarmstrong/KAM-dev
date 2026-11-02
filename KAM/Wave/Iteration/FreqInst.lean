/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.WaveInst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the wave iteration's admissible family, exclusion and final frequencies
(`bpW:w6:freq-lip`, `bpW:w6:exclusion`, `bpW:w6:final-freq`)

Blueprint labels `bpW:w6:freq-lip`, `bpW:w6:exclusion`, `bpW:w6:final-freq`
(milestone W6).

For the data of Lemma `bpW:w6:prep-step` (`H : W6PrepHyp …`, `MeasSetup`) and a starting size
`ε₀ ∈ [ε^♭_0, γ₁ α̌]`, the wave iteration is `w6Seq` started at `w6Start` with the prep-step outputs
(Definition `bpW:w6:wave-iteration`). All results here are **conditional helpers** on W5's reality
clauses `W6StepReal` (unmodified step) and `W6StepRealMod` (modified step); these clauses hold
(`w6StepReal_holds`, `w6StepRealMod_holds`), and the unconditional label statements are in
`KAM.Wave.Iteration.ConvSource` (`w6WaveFamily`, `w6Exclusion`, `w6FinalFreq`):

* `w6WaveFamily_of_stepReal`: the admissible family `(D_ν, ω_ν, Ω_ν, K_ν)` with `D_ν = Π_{ν-1}`
  (`bpW:w6:freq-lip`), constants `ε_ω = 6πγα + 8πε₀`, `ε₁ = 0`, `ε₂ = 3γα + 4ε₀`, `θ` (deviation:
  the normal shift of the prep-step enters `ε₂`, since W5's `stepTheoremMod` gives it with the
  weight `J^{1/2}`);
* `w6Exclusion_of_stepReal`: `Π ∖ Π_* ⊆ ℰ` (`bpW:w6:exclusion`);
* `w6FinalFreq_of_stepReal`: on `Π_*`, `|⟨k, ω_*⟩| ≥ α̌/(2A_k)` (`k ≠ 0`), `|ω_* - ω⁰| ≤ ε_ω`, and
  `ω_*` is Lipschitz with constant `N_A + θ` (`bpW:w6:final-freq`).
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.Wave

namespace W6PrepHyp

variable {m : ℝ} {hm : 0 < m} {Pi : Set (Fin 2 → ℝ)} {α r ε : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase} {ε₀ : ℝ}

/-- The wave iteration (Definition `bpW:w6:wave-iteration`). -/
def waveSeq (H : W6PrepHyp m hm Pi α r ε P X) (ε₀ : ℝ) : ℕ → W6State :=
  w6Seq (w6WaveSeq m hm α r ε ε₀)
    (w6Start (w6WaveSeq m hm α r ε ε₀) (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0)

/-- `D_ν = Π_{ν-1}` of the wave iteration (`Π_{-1} = Π ∖ Ξ`). -/
def waveD (H : W6PrepHyp m hm Pi α r ε P X) (ε₀ : ℝ) (ν : ℕ) : Set (Fin 2 → ℝ) :=
  w6PiSeq (Pi \ prepSet m hm Pi α) (fun n => (H.waveSeq ε₀ n).om)
    (fun n ξ => w6Om7 ((H.waveSeq ε₀ n).Om ξ)) (w6WaveSeq m hm α r ε ε₀).alpha
    (w6WaveSeq m hm α r ε ε₀).KprevNu ν

variable (hR : W6StepReal) (hRm : W6StepRealMod) (hS : MeasSetup m hm Pi α)
  (H : W6PrepHyp m hm Pi α r ε P X) (hlo : w6EpsFlat α ε ≤ ε₀)
  (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α)

include hR hRm hlo hhi in
theorem waveD_mem (ν : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ H.waveD ε₀ ν) :
    ∀ μ < ν, ξ ∈ (H.waveSeq ε₀ μ).Pi := by
  intro μ hμ
  obtain ⟨n, rfl⟩ : ∃ n, ν = n + 1 := ⟨ν - 1, by omega⟩
  unfold waveD waveSeq at hξ
  unfold waveSeq
  rw [← w6Seq_Pi_eq_of_stepReal hR (H.w6Applicable_of_stepRealMod hRm hlo hhi) n] at hξ
  exact w6Seq_Pi_antitone _ _ (Nat.lt_succ_iff.1 hμ) hξ

theorem waveD_subset (ν : ℕ) : H.waveD ε₀ ν ⊆ Pi \ prepSet m hm Pi α :=
  w6PiSeq_subset _ _ _ _ _ ν

include hR hRm hS hlo hhi in
theorem waveD_meas (ν : ℕ) : MeasurableSet (H.waveD ε₀ ν) := by
  have hC := H.w6Applicable_of_stepRealMod hRm hlo hhi
  cases ν with
  | zero => exact w6PiMinus_measurableSet m hm hS
  | succ n =>
    unfold waveD waveSeq
    rw [← w6Seq_Pi_eq_of_stepReal hR hC n]
    exact (w6ConvBorel_of_stepReal hR hC (w6PiMinus_measurableSet m hm hS)).1 n

include hR hRm hS hlo hhi in
/-- **(H1)–(H2) at every stage** (`bpW:w6:freq-lip`, steps `fl-size`, `fl-lip`, `fl-borel`). -/
theorem w6wavePair (ν : ℕ) :
    IsFreqPair m hm Pi α (H.waveD ε₀ ν) (H.waveSeq ε₀ ν).om
      (fun ξ => w6Om7 ((H.waveSeq ε₀ ν).Om ξ))
      (6 * π * w6Gamma m hm * α + 8 * π * ε₀) 0 (3 * w6Gamma m hm * α + 4 * ε₀)
      (w6Theta m hm) := by
  have hC := H.w6Applicable_of_stepRealMod hRm hlo hhi
  have hε₀ : 0 < ε₀ := lt_of_lt_of_le (w6EpsFlat_pos H.hα H.hε) hlo
  have hsub := H.waveD_subset (ε₀ := ε₀) ν
  have hl0 : (w6WaveSeq m hm α r ε ε₀).lam 0 = alphaCheck α / w6M0 m hm :=
    waveSeq_lam_zero r ε ε₀
  obtain ⟨hc0, -, -, -, -, -⟩ := alpha_facts m hm H.hα H.hα0
  have hlam0 : 0 < alphaCheck α / w6M0 m hm := div_pos hc0 (w6M0_pos m hm)
  have hlam : 0 < α / w6M m hm := div_pos H.hα (w6M_pos m hm)
  obtain ⟨b₀, b₁, hb0, hb1, hbs, hbb, hbl⟩ := H.shift_omega
  obtain ⟨c₀, c₁, hc0', hc1, hcs, hcb, hcl⟩ := H.shift_Omega
  have hmem := fun {ξ} (hξ : ξ ∈ H.waveD ε₀ ν) => H.waveD_mem hR hRm hlo hhi ν hξ
  -- `x ≤ c/L * y` gives `L x ≤ c y`
  have hmul : ∀ {L x c y : ℝ}, 0 < L → x ≤ c / L * y → L * x ≤ c * y := fun {L x c y} hL h => by
    have := mul_le_mul_of_nonneg_left h hL.le
    rwa [show L * (c / L * y) = c * y by field_simp] at this
  refine w6IsFreqPair_of_bounds_half (H.waveD_meas hR hRm hS hlo hhi ν)
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

/-- **Lipschitz frequencies** (`bpW:w6:freq-lip`; conditional helper on `W6StepReal`,
`W6StepRealMod`): the admissible family of the wave iteration, `D_ν = Π_{ν-1}`, thresholds `K_ν`. -/
def w6WaveFamily_of_stepReal : AdmissibleFamily m hm Pi α :=
  w6AdmissibleFamilyOfPairs (w6WaveSeq m hm α r ε ε₀)
    (w6WaveSeq_valid H.hα H.hα0 H.hr H.hε (lt_of_lt_of_le (w6EpsFlat_pos H.hα H.hε) hlo))
    (H.waveD ε₀) (fun ν => (H.waveSeq ε₀ ν).om) (fun ν ξ => w6Om7 ((H.waveSeq ε₀ ν).Om ξ))
    _ _ _ _ (H.w6wavePair hR hRm hS hlo hhi)

/-- `Π_* = ⋂_ν Π_ν` of the wave iteration. -/
def wavePiStar (H : W6PrepHyp m hm Pi α r ε P X) (ε₀ : ℝ) : Set (Fin 2 → ℝ) :=
  w6PiStarIt (w6WaveSeq m hm α r ε ε₀)
    (w6Start (w6WaveSeq m hm α r ε ε₀) (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0)

include hR hRm hS hlo hhi in
/-- **Exclusion** (`bpW:w6:exclusion`; conditional helper on `W6StepReal`, `W6StepRealMod`):
`Π ∖ Π_* ⊆ ℰ`, W7's excluded set for the admissible family of the wave iteration (levels
`α_ν ≤ α̌`, thresholds `K_ν ≥ 2^ν`). -/
theorem w6Exclusion_of_stepReal :
    Pi \ H.wavePiStar ε₀ ⊆ exclSet m hm (H.w6WaveFamily_of_stepReal hR hRm hS hlo hhi) := by
  have hC := H.w6Applicable_of_stepRealMod hRm hlo hhi
  have h := w6_exclusion_seq m hm (w6WaveSeq m hm α r ε ε₀)
    (w6WaveSeq_valid H.hα H.hα0 H.hr H.hε (lt_of_lt_of_le (w6EpsFlat_pos H.hα H.hε) hlo)) rfl
    (H.w6WaveFamily_of_stepReal hR hRm hS hlo hhi) (fun _ => rfl) (fun _ => rfl)
  unfold wavePiStar
  rw [w6PiStarIt_eq_of_stepReal hR hC]
  exact h

include hR hRm hS hlo hhi in
/-- **Final frequencies** (`bpW:w6:final-freq`; conditional helper on `W6StepReal`,
`W6StepRealMod`): for `ξ ∈ Π_*`, `|⟨k, ω_*⟩| ≥ α̌/(2A_k)` (`k ≠ 0`), `|ω_* - ω⁰|_∞ ≤ ε_ω`, and
`ω_*` is Lipschitz on `Π_*` with constant `N_A + θ`. -/
theorem w6FinalFreq_of_stepReal :
    (∀ ξ ∈ H.wavePiStar ε₀, ∀ k : Fin 2 → ℤ, k ≠ 0 →
      alphaCheck α / (2 * kAk k) ≤
        |∑ i, (k i : ℝ) * w6OmStar (w6WaveSeq m hm α r ε ε₀) (w6Start (w6WaveSeq m hm α r ε ε₀)
          (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0) ξ i|) ∧
    (∀ ξ ∈ H.wavePiStar ε₀,
      ‖w6OmStar (w6WaveSeq m hm α r ε ε₀) (w6Start (w6WaveSeq m hm α r ε ε₀)
          (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0) ξ - omegaTan m hm ξ‖ ≤
        6 * π * w6Gamma m hm * α + 8 * π * ε₀) ∧
    (∀ ξ ∈ H.wavePiStar ε₀, ∀ ζ ∈ H.wavePiStar ε₀,
      ‖w6OmStar (w6WaveSeq m hm α r ε ε₀) (w6Start (w6WaveSeq m hm α r ε ε₀)
          (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0) ξ -
        w6OmStar (w6WaveSeq m hm α r ε ε₀) (w6Start (w6WaveSeq m hm α r ε ε₀)
          (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0) ζ‖ ≤
        (measNA m hm + w6Theta m hm) * ‖ξ - ζ‖) := by
  have hC := H.w6Applicable_of_stepRealMod hRm hlo hhi
  have hd := hC.valid
  set F := H.w6WaveFamily_of_stepReal hR hRm hS hlo hhi
  have hS' : ∀ ν, H.wavePiStar ε₀ ⊆ F.D ν := fun ν => by
    show _ ⊆ H.waveD ε₀ ν
    unfold wavePiStar waveD waveSeq
    rw [w6PiStarIt_eq_of_stepReal hR hC]
    exact w6PiStar_subset_seq _ _ _ _ _ ν
  exact w6FinalFreq_of_limits m hm F hS' _ (w6Seq_om_limit hR hC).1
    (w6WaveSeq m hm α r ε ε₀).alpha (fun ν => W6SeqData.half_le_alpha hd ν)
    fun ξ hξ ν k hk => by
      have h := (w6Seq_stage_of_stepReal hR hC ν).mel ξ (mem_w6PiStarIt hξ ν) k 0
        ⟨Or.inl rfl, Or.inl hk⟩
      rw [japL_zero, mul_one] at h
      have e : ∀ f : ℕ → ℝ, linF 0 f = 0 := fun f => by simp [linF]
      rw [e, add_zero] at h
      exact h

end W6PrepHyp

end KAM.Wave
