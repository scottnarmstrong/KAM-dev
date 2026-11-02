/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.FreqInst

/-!
# W6: convergence and the wave instances, unconditional (`bpW:w6:convergence` (i), (ii),
`bpW:w6:freq-lip`, `bpW:w6:exclusion`, `bpW:w6:final-freq`)

The hypothesis-taking variants of `ConvFreq` and `FreqInst` assume W5's reality clauses
`W6StepReal`, `W6StepRealMod`; these hold (`w6StepReal_holds`, `w6StepRealMod_holds`, from W5's
`stepTheorem_reality_of_eps0_pos`, `stepTheoremMod_reality_of_eps0_pos`). The statements below are
those of the helpers with the clauses discharged:

* `w6Seq_Pi_eq`, `w6PiStarIt_eq`, `w6ConvParams`, `w6ConvBorel` (`bpW:w6:convergence` (i));
* `w6ConvFreq` (`bpW:w6:convergence` (ii));
* `W6PrepHyp.w6WaveFamily` (`bpW:w6:freq-lip`), `W6PrepHyp.w6Exclusion` (`bpW:w6:exclusion`),
  `W6PrepHyp.w6FinalFreq` (`bpW:w6:final-freq`).
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.Wave

section conv

variable {d : W6SeqData} {Pm : Set (Fin 2 → ℝ)} {ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ}
  {Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ} {P0 : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X0 : (Fin 2 → ℝ) → KamPhase → KamPhase} {β₀ : ℝ}

local notation "𝒮" => w6Seq d (w6Start d Pm ω0 Ω0 P0 X0)

/-- **Parameters** (`bpW:w6:convergence` (i)): `Π_ν` is W6-PREP's `w6PiSeq` (index `ν + 1`) of the
output frequencies `(ω_n, Ω_n)`, levels `α_n` and thresholds `K_{n-1}`. -/
theorem w6Seq_Pi_eq (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) (ν : ℕ) :
    (𝒮 ν).Pi = w6PiSeq Pm (fun n => (𝒮 n).om) (fun n ξ => w6Om7 ((𝒮 n).Om ξ)) d.alpha d.KprevNu
      (ν + 1) :=
  w6Seq_Pi_eq_of_stepReal w6StepReal_holds hC ν

/-- `Π_* = ⋂_ν Π_ν` is W6-PREP's `w6PiStar` of the output frequencies (`bpW:w6:convergence` (i)). -/
theorem w6PiStarIt_eq (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) :
    w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0) =
      w6PiStar Pm (fun n => (𝒮 n).om) (fun n ξ => w6Om7 ((𝒮 n).Om ξ)) d.alpha d.KprevNu :=
  w6PiStarIt_eq_of_stepReal w6StepReal_holds hC

/-- **Convergence (i)** (`bpW:w6:convergence` (i)): for the iteration,
`Π_{-1} ∖ Π_* = ⋃_{ν ≥ 0} ⋃_{(k,l) ∈ Z, |k| > K_{ν-1}} R^ν_{kl}`, with `R^ν_{kl}` the zone of
`(ω_ν, Ω_ν)` at level `α_ν` in `Π_{ν-1}`. -/
theorem w6ConvParams (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) :
    Pm \ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0) =
      ⋃ (ν : ℕ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (_ : InZ k l ∧ d.KprevNu ν < kAbs k),
        zoneSet (w6PiSeq Pm (fun n => (𝒮 n).om) (fun n ξ => w6Om7 ((𝒮 n).Om ξ)) d.alpha d.KprevNu ν)
          ((𝒮 ν).om) (fun ξ => w6Om7 ((𝒮 ν).Om ξ)) (d.alpha ν) k l :=
  w6ConvParams_of_stepReal w6StepReal_holds hC

/-- **Convergence (i), Borel** (`bpW:w6:convergence` (i)): if `Π_{-1}` is Borel, every `Π_ν` and
`Π_*` are Borel. -/
theorem w6ConvBorel (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) (hPm : MeasurableSet Pm) :
    (∀ ν, MeasurableSet (𝒮 ν).Pi) ∧ MeasurableSet (w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0)) :=
  w6ConvBorel_of_stepReal w6StepReal_holds hC hPm

/-- **Convergence (ii)** (`bpW:w6:convergence` (ii)): `ω_ν → ω_*`, `Ω_ν → Ω_*` uniformly on `Π_*`
(each `Ω_{·,j}`, W7 index), with `|ω_* - ω_0| ≤ 8πε₀`, `|ω_* - ω_0|^ℒ ≤ 64πε₀/λ₀`,
`sup_j (j+2)^{1/2} |Ω_{*,j} - Ω_{0,j}| ≤ 4ε₀`, its Lipschitz constant `≤ 16ε₀/λ₀`, and
`|⟨k, ω_*⟩ + ⟨l, Ω_*⟩| ≥ (α₀/2)⟨l⟩/A_k` for `(k,l) ∈ Z`. -/
theorem w6ConvFreq (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) :
    TendstoUniformlyOn (fun ν => (𝒮 ν).om) (w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0)) atTop
      (w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0)) ∧
    (∀ j, TendstoUniformlyOn (fun ν ξ => w6Om7 ((𝒮 ν).Om ξ) j)
      (fun ξ => w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ j) atTop
      (w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0))) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      ‖w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ - ω0 ξ‖ ≤ 8 * π * d.eps0) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      ∀ ζ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      ‖(w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ - ω0 ξ) -
        (w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ζ - ω0 ζ)‖ ≤
        64 * π * d.eps0 / d.lam 0 * ‖ξ - ζ‖) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0), ∀ j : ℕ,
      normLab j ^ (1 / 2 : ℝ) * |w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ j - w6Om7 (Ω0 ξ) j| ≤
        4 * d.eps0) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0),
      ∀ ζ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0), ∀ j : ℕ,
      normLab j ^ (1 / 2 : ℝ) *
        |(w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ j - w6Om7 (Ω0 ξ) j) -
          (w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ζ j - w6Om7 (Ω0 ζ) j)| ≤
        16 * d.eps0 / d.lam 0 * ‖ξ - ζ‖) ∧
    (∀ ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0), ∀ (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ), InZ k l →
      d.al0 / 2 * japL l / kAk k ≤
        |∑ i, (k i : ℝ) * w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ i +
          linF l (w6OmStar7 d (w6Start d Pm ω0 Ω0 P0 X0) ξ)|) :=
  w6ConvFreq_of_stepReal w6StepReal_holds hC

end conv

namespace W6PrepHyp

variable {m : ℝ} {hm : 0 < m} {Pi : Set (Fin 2 → ℝ)} {α r ε : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase} {ε₀ : ℝ}

/-- **Lipschitz frequencies** (`bpW:w6:freq-lip`): the admissible family of the wave iteration,
`D_ν = Π_{ν-1}`, thresholds `K_ν`, constants `ε_ω = 6πγα + 8πε₀`, `ε₁ = 0`, `ε₂ = 3γα + 4ε₀`, `θ`
(the modified shift weight). -/
def w6WaveFamily (hS : MeasSetup m hm Pi α) (H : W6PrepHyp m hm Pi α r ε P X)
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    AdmissibleFamily m hm Pi α :=
  H.w6WaveFamily_of_stepReal w6StepReal_holds w6StepRealMod_holds hS hlo hhi

/-- **Exclusion** (`bpW:w6:exclusion`): `Π ∖ Π_* ⊆ ℰ`, W7's excluded set for the admissible family
of the wave iteration (levels `α_ν ≤ α̌`, thresholds `K_ν ≥ 2^ν`). -/
theorem w6Exclusion (hS : MeasSetup m hm Pi α) (H : W6PrepHyp m hm Pi α r ε P X)
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    Pi \ H.wavePiStar ε₀ ⊆ exclSet m hm (H.w6WaveFamily hS hlo hhi) :=
  H.w6Exclusion_of_stepReal w6StepReal_holds w6StepRealMod_holds hS hlo hhi

/-- **Final frequencies** (`bpW:w6:final-freq`): for `ξ ∈ Π_*`, `|⟨k, ω_*⟩| ≥ α̌/(2A_k)`
(`k ≠ 0`), `|ω_* - ω⁰|_∞ ≤ ε_ω`, and `ω_*` is Lipschitz on `Π_*` with constant `N_A + θ`. -/
theorem w6FinalFreq (hS : MeasSetup m hm Pi α) (H : W6PrepHyp m hm Pi α r ε P X)
    (hlo : w6EpsFlat α ε ≤ ε₀) (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
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
        (measNA m hm + w6Theta m hm) * ‖ξ - ζ‖) :=
  H.w6FinalFreq_of_stepReal w6StepReal_holds w6StepRealMod_holds hS hlo hhi

end W6PrepHyp

end KAM.Wave
