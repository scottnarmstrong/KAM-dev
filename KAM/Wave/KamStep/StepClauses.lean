/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepFlowClauses
public import KAM.Wave.KamStep.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The clauses (ii)–(iv) of the KAM step (blueprint-W `bpW:w5:step`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

(ii) `P_+` is a smoothing Hamiltonian on `D_+` (`StepCore.Pplus_smoothing`), periodic
(`StepCore.Pplus_periodic`), with the `λ`-bound `C₂(ε²/(α σ^t η²) + η ε)` for `X_{P_+}`
(`StepCore.Xplus_fam`). (iii) The frequency corrections (`StepCore.freq_*`); (iv) the divisors
(`StepCore.divisors`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

open KAM

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ}
  {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT) [Fact (0 < r)]

include H

/-- `P_+ ∈ 𝒮_{p_+}(D_+)` (`bpW:w5:step` (ii)). -/
theorem Pplus_smoothing {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    IsSmoothing (p := p) H.ha H.pb_pos (kamDomain (s - 5 * σ) (η * r))
      (fun w : KamPhase => H.Pplus ξ (StepPhase.ofK (r := r) w))
      (fun w : KamPhase => StepPhase.toK (H.Xplus ξ (StepPhase.ofK (r := r) w))) :=
  stepPlus_isSmoothing H.ha H.hp H.hpb H.hσ H.hσ1 H.hσs H.hη0 H.hη (H.hP ξ hξ) (H.R ξ) (FT ξ)
    (e₁ := 3 * ε₀) (by linarith [H.hε₀]) (H.R_field ξ hξ)
    (homNhat_fieldBound_gen H.ha H.hp H.hpb H.hr H.hs (H.R ξ) (H.R_field ξ hξ))
    (H.F_field ξ hξ) H.M₀_pos H.mf_le_sigma

/-- `P_+` is periodic. -/
theorem Pplus_periodic {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (i : Fin 2) {w : KamPhase}
    (hw : w ∈ kamDomain (s - 5 * σ) (η * r)) :
    H.Pplus ξ (StepPhase.ofK (r := r) (w + stepTau i)) = H.Pplus ξ (StepPhase.ofK (r := r) w) := by
  have h := stepPplusS_periodic (r := r) H.ha H.hp H.hpb H.hσ H.hσ1 H.hσs H.hη0 H.hη
    (H.hper ξ hξ) (H.R ξ) (FT ξ) (H.F_field ξ hξ) H.M₀_pos H.mf_le_sigma
    (w := StepPhase.ofK (r := r) w) hw i
  exact h

/-- **The bound of the new error** (`bpW:w5:step` (ii), `(6)`). -/
theorem Xplus_fam :
    FamBound Par (kamDomain (s - 5 * σ) (η * r)) (η * r) lam
      ((896 + 168 * cF) * (ε ^ 2 / (α * σ ^ tF * η ^ 2) + η * ε))
      (fun ξ w => StepPhase.toK (H.Xplus ξ (StepPhase.ofK (r := r) w))) := by
  have hMs : 16 * stepMF (cF) (tF) α σ ε ≤ σ * η ^ 2 := by
    have := H.mf_small; linarith
  have h := stepPlus_famBound (r := r) H.ha H.hp H.hpb H.hs H.hσ H.hσ1 H.hσs H.hη0 H.hη
    (Par := Par) (P := P) (X := X) (lam := lam) (ε := ε) (ε₀ := ε₀) (ε₁ := ε₁)
    (M₀ := M₀) (M₁ := M₁)
    (MF := stepMF (cF) (tF) α σ ε) H.hlam0 H.hP H.hper H.hε₀.le H.hε₁
    H.M₀_pos H.M₁_nonneg H.hb H.hdiff H.hε H.M_sum (FT) H.F_field H.F_sub hMs
  refine FamBound.famMono h (fun w hw => hw) ?_
  have := stepEstimate_arith (c := cF) (t := tF) H.hα H.hσ H.hη0
    H.hc.le H.ε_pos.le
  have e : (7 * 24 : ℝ) = 168 := by norm_num
  rw [e] at this
  exact this

theorem omegaPlus_sub (ξ : Fin 2 → ℝ) : H.omegaPlus ξ - ω ξ = stepOmegaHat (H.R ξ) := by
  funext k; simp [omegaPlus]

theorem OmegaPlus_sub (ξ : Fin 2 → ℝ) (j : ℕ+) :
    H.OmegaPlus ξ j - Ω ξ j = stepOmegaTail (H.R ξ) j := by
  simp [OmegaPlus]

/-- `|ω_+ - ω| ≤ 6π ε₀` (`bpW:w5:step` (iii)). -/
theorem freq_sup {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) : ‖H.omegaPlus ξ - ω ξ‖ ≤ 6 * Real.pi * ε₀ := by
  rw [H.omegaPlus_sub]
  have := stepOmegaHat_bound H.ha H.hp H.hpb H.hr H.hs (H.R ξ) (H.R_field ξ hξ)
  linarith

/-- The Lipschitz part: `|(ω_+-ω)(ξ) - (ω_+-ω)(ζ)| ≤ 6π ε₁ |ξ-ζ|`. -/
theorem freq_lip {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) :
    ‖(H.omegaPlus ξ - ω ξ) - (H.omegaPlus ζ - ω ζ)‖ ≤ 6 * Real.pi * ε₁ * ‖ξ - ζ‖ := by
  rw [H.omegaPlus_sub, H.omegaPlus_sub, stepOmegaHat_sub H.hs]
  have := stepOmegaHat_bound H.ha H.hp H.hpb H.hr H.hs _ (H.R_sub ξ hξ ζ hζ)
  linarith

theorem tail_sup {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (j : ℕ+) :
    ((j : ℝ) + 2) ^ (pb - p) * |H.OmegaPlus ξ j - Ω ξ j| ≤ 3 * ε₀ := by
  rw [H.OmegaPlus_sub]
  exact stepOmegaTail_bound H.ha H.hp H.hpb H.hr H.hs (H.R ξ) (H.R_field ξ hξ) j

theorem tail_lip {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) (j : ℕ+) :
    ((j : ℝ) + 2) ^ (pb - p) *
        |(H.OmegaPlus ξ j - Ω ξ j) - (H.OmegaPlus ζ j - Ω ζ j)| ≤ 3 * ε₁ * ‖ξ - ζ‖ := by
  rw [H.OmegaPlus_sub, H.OmegaPlus_sub, stepOmegaTail_sub H.hs]
  exact stepOmegaTail_bound H.ha H.hp H.hpb H.hr H.hs _ (H.R_sub ξ hξ ζ hζ) j

/-- **The frequency hypothesis after the step** (`bpW:w5:step` (iii)), `λ > 0`. -/
theorem freq_hyp (hl : 0 < lam) :
    HomFreqHyp Par H.omegaPlus H.OmegaPlus (M0 + 3 * ε) (Mω + 6 * Real.pi * ε / lam)
      (MΩ + 3 * ε / lam) := by
  have hl1 : lam * ε₁ ≤ ε := by linarith [H.hε₀, H.hε]
  refine stepFreqHyp H.freq H.ε_pos.le hl H.hpp (fun ξ hξ ζ hζ => ?_) (fun ξ hξ j => ?_)
    (fun ξ hξ ζ hζ j => ?_)
  · refine (H.freq_lip hξ hζ).trans ?_
    have hpi := Real.pi_pos
    rw [show 6 * Real.pi * ε / lam * ‖ξ - ζ‖ = (6 * Real.pi * ε / lam) * ‖ξ - ζ‖ from rfl]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [le_div_iff₀ hl]; nlinarith
  · exact (H.tail_sup hξ j).trans (by linarith [H.ε₀_le])
  · refine (H.tail_lip hξ hζ j).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [le_div_iff₀ hl]; nlinarith

/-- **The divisors after the step** (`bpW:w5:step` (iv)). -/
theorem divisors (hH : HomMelnikov τ α Par ω Ω) {K α' : ℝ} (hK : 1 ≤ K)
    (hα' : 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α') {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    {k : Fin 2 → ℤ} {l : ℕ+ →₀ ℤ} (hkl : (k, l) ∈ homZ) (hkK : Fourier.modeSize k ≤ K) :
    α' * (homJap l : ℝ) / waveA τ k ≤
      |homPairZ k (H.omegaPlus ξ) + homPairL l (H.OmegaPlus ξ)| := by
  have hpi := Real.pi_pos
  refine stepDivisors (ω' := H.omegaPlus) (Ω' := H.OmegaPlus) H.hτ H.ε_pos.le hK hH
    (fun ξ hξ => (H.freq_sup hξ).trans (by nlinarith [H.ε₀_le])) (fun ξ hξ j => ?_) hα' hξ hkl hkK
  rw [H.OmegaPlus_sub]
  have h := stepOmegaTail_bound H.ha H.hp H.hpb H.hr H.hs (H.R ξ) (H.R_field ξ hξ) j
  have hj : (1 : ℝ) ≤ ((j : ℝ) + 2) ^ (pb - p) :=
    Real.one_le_rpow (by have : (0 : ℝ) ≤ j := by positivity
                         linarith) (by linarith [H.hpp])
  calc |stepOmegaTail (H.R ξ) j| ≤ ((j : ℝ) + 2) ^ (pb - p) * |stepOmegaTail (H.R ξ) j| :=
        le_mul_of_one_le_left (abs_nonneg _) hj
    _ ≤ 3 * ε₀ := h
    _ ≤ 3 * ε := by linarith [H.ε₀_le]

end StepCore

end KAM.Wave
