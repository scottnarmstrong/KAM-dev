/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepHyp
public import KAM.Wave.KamStep.StepNplus
public import KAM.Wave.KamStep.NewHamConj
public import KAM.Wave.KamStep.StepPeriodicFlow
public import KAM.Wave.KamStep.StepSymplectic
public import KAM.Wave.KamStep.StepFlowFam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `H ∘ Φ = N_+ + P_+ + â₀` for the step data (blueprint-W `bpW:w5:step` (i))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

The objects of the step: `StepHyp.Phi` (`Φ = φ¹`), `StepHyp.Pplus`, `StepHyp.Xplus`,
`StepHyp.omegaPlus`, `StepHyp.OmegaPlus` (`ω_+ = ω + ω̂`, `Ω_+ = Ω + Ω̂`), `StepHyp.a0`.
`StepHyp.conj_eq`: `N(Φ w) + P(Φ w) = N_+(w) + P_+(w) + â₀`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

namespace StepHyp

variable (H : StepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)

/-- `ω_+ = ω + ω̂`. -/
def omegaPlus (ξ : Fin 2 → ℝ) : Fin 2 → ℝ := fun k => ω ξ k + stepOmegaHat (H.R ξ) k

/-- `Ω_+ = Ω + Ω̂`. -/
def OmegaPlus (ξ : Fin 2 → ℝ) : ℕ+ → ℝ := fun j => Ω ξ j + stepOmegaTail (H.R ξ) j

/-- `â₀(ξ)`. -/
def a0 (ξ : Fin 2 → ℝ) : ℂ := homCoeff (H.R ξ).a0 0

variable [Fact (0 < r)]

/-- The transformation `Φ = φ¹` of the flow of `X_F`. -/
def Phi (ξ : Fin 2 → ℝ) : StepPhase r → StepPhase r :=
  holoFlow (smoothField (stepEmbedCLM a p pb H.hpb r) (stepFieldS H.ha H.hp H.hpb (H.FT ξ) r)) 1

/-- The new Hamiltonian `P_+`. -/
def Pplus (ξ : Fin 2 → ℝ) : StepPhase r → ℂ :=
  stepPplusS H.ha H.hp H.hpb (P ξ) (H.R ξ) (H.FT ξ)

/-- The field of `P_+`. -/
def Xplus (ξ : Fin 2 → ℝ) : StepPhase r → StepPhase r :=
  stepXplusS H.ha H.hp H.hpb (X ξ) (H.R ξ) (H.FT ξ)

include H

theorem hK0 : 0 ≤ 1 + M0 := by linarith [H.freq.consts_nonneg.1]

theorem hKp : 0 ≤ 1 + M0 + 3 * ε := by linarith [H.freq.consts_nonneg.1, H.ε_pos]

theorem ε₀_le : ε₀ ≤ ε := by
  have := mul_nonneg H.hlam0 H.hε₁
  linarith [H.hε]

theorem tail_bound {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (j : ℕ+) :
    |stepOmegaTail (H.R ξ) j| ≤ 3 * ε₀ * ((j : ℝ) + 2) := by
  have h := stepOmegaTail_bound H.ha H.hp H.hpb H.hr H.hs (H.R ξ) (H.R_field ξ hξ) j
  have hj : (1 : ℝ) ≤ (j : ℝ) + 2 := by
    have : (0 : ℝ) ≤ j := by positivity
    linarith
  have h1 : (1 : ℝ) ≤ ((j : ℝ) + 2) ^ (pb - p) := Real.one_le_rpow hj (by linarith [H.hpp])
  have h2 : |stepOmegaTail (H.R ξ) j| ≤ 3 * ε₀ := by
    calc |stepOmegaTail (H.R ξ) j| ≤ ((j : ℝ) + 2) ^ (pb - p) * |stepOmegaTail (H.R ξ) j| :=
          le_mul_of_one_le_left (abs_nonneg _) h1
      _ ≤ 3 * ε₀ := h
  calc |stepOmegaTail (H.R ξ) j| ≤ 3 * ε₀ := h2
    _ ≤ 3 * ε₀ * ((j : ℝ) + 2) := le_mul_of_one_le_right (by linarith [H.hε₀]) hj

theorem omegaPlus_bound {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (j : ℕ+) :
    |H.OmegaPlus ξ j| ≤ (1 + M0 + 3 * ε) * ((j : ℝ) + 2) := by
  have h1 := homOmega_le H.freq hξ j
  have h2 := H.tail_bound hξ j
  have hj : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
  unfold OmegaPlus
  calc |Ω ξ j + stepOmegaTail (H.R ξ) j| ≤ |Ω ξ j| + |stepOmegaTail (H.R ξ) j| := abs_add_le _ _
    _ ≤ (1 + M0) * ((j : ℝ) + 2) + 3 * ε₀ * ((j : ℝ) + 2) := add_le_add h1 h2
    _ ≤ (1 + M0 + 3 * ε) * ((j : ℝ) + 2) := by
      nlinarith [H.ε₀_le, mul_le_mul_of_nonneg_right H.ε₀_le hj]

theorem mf_le_sigma : stepM₀ τ σ α ε₀ ≤ σ / 1024 := by
  have h1 := (stepMF_margins H.hσ H.hη0 H.hη H.mf_small).1
  have := mul_nonneg H.hlam0 (H.M₁_nonneg)
  have := H.M_sum
  linarith

theorem equation {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : KamPhase} (hw : w.1 ∈ complexStrip 2 (s - σ)) :
    stepFun H.ha (homPP H.hp H.hpb) (H.R ξ) w +
        ((homDN H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ) (stepToHom w)).comp stepToHom)
          (kamHomEmbed a p pb H.hpb (stepField H.ha H.hp H.hpb (H.FT ξ) w)) =
      stepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen (H.R ξ)) w + H.a0 ξ := by
  rw [H.FT_eq hξ]
  exact stepSolve_equation H.freq H.mel H.ha H.hp H.hpb H.hp1 H.hG H.hr H.hτ H.hα H.hσ H.hσs' hξ
    (H.R ξ) (H.R_field ξ hξ) hw

theorem nplus_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (w : KamPhase) :
    stepNfun H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ) w +
        stepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen (H.R ξ)) w =
      stepNfun H.hG H.hKp (Ω := H.OmegaPlus ξ) (H.omegaPlus_bound hξ) (H.omegaPlus ξ) w := by
  have hb : ∀ k, (homCoeff (H.R ξ).b 0 k).im = 0 := by
    rw [H.R_eq hξ]
    exact homCoeff_b_real H.ha H.hp H.hpb H.pb_pos H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ)
      (H.hreal ξ hξ)
  have hQ : ∀ j, (homNormalEntry_gen a p pb (homCoeff (H.R ξ).Q 0) j j).im = 0 := by
    rw [H.R_eq hξ]
    exact homCoeff_Q_real H.ha H.hp H.hpb H.pb_pos H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ)
      (H.hreal ξ hξ)
  exact stepNfun_add_Nhat (K' := 3 * ε₀) H.hG H.hK0 (by linarith [H.hε₀])
    H.hKp H.ha H.hp H.hpb (H.R ξ) (homOmega_le H.freq hξ)
    (fun j => by simpa using H.tail_bound hξ j) (H.omegaPlus_bound hξ) (ω ξ) hb hQ w

theorem conj_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) {w : StepPhase r}
    (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    stepNfun H.hG H.hK0 (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.Phi ξ w)) +
        P ξ (StepPhase.toK (H.Phi ξ w)) =
      stepNfun H.hG H.hKp (Ω := H.OmegaPlus ξ) (H.omegaPlus_bound hξ) (H.omegaPlus ξ)
        (StepPhase.toK w) + H.Pplus ξ w + H.a0 ξ := by
  have hD : ∀ z ∈ stepDomain r (s - σ) r, StepPhase.toK z ∈ kamDomain s r := fun z hz =>
    kamDomain_mono (by linarith [H.hσ]) H.hr le_rfl hz
  have hPd : DifferentiableOn ℂ (stepPS (P ξ) r) (stepDomain r (s - σ) r) :=
    ((H.hP ξ hξ).holoP.comp (stepToKCLM r).differentiable.differentiableOn
      (fun z hz => hD z hz)).mono (fun z hz => hz)
  have hMf : stepM₀ τ σ α ε₀ ≤ σ / 1024 := H.mf_le_sigma
  have key := stepNewHam_concrete (r := r) (σ := σ) (η := η) H.hG H.hK0 (homOmega_le H.freq hξ)
    (ω ξ) H.ha H.hp H.hpb H.hσ H.hσ1 H.hσs H.hη0 H.hη (P ξ) (H.R ξ) (H.FT ξ)
    (H.F_field ξ hξ) H.M₀_pos hMf (H.a0 ξ) hPd
    (fun w hw => H.equation hξ hw) hw
  have hn := H.nplus_eq hξ (StepPhase.toK w)
  unfold Phi Pplus stepPplusS
  unfold stepFS stepPS at key ⊢
  linear_combination key + hn

end StepHyp

end KAM.Wave
