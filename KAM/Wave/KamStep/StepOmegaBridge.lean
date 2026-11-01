/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepHypMod
public import KAM.Wave.KamStep.StepClauses
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The new frequencies of the modified step through the `p+1` Taylor family
(blueprint-W `bpW:w5:step`)

Off-frontier, source-faithful infrastructure (W5-STEP-B-FIX, ruling D2 of `W5-STEP-B-audit-1.md`);
the dependency graph is still being built.

In the modified (preparatory) step the core Taylor family is that of the reweighted field
`D_ρ ∘ X` at the exponent `p_+`; the frequency corrections only see the diagonal entries of `Q`,
which the reweighting preserves (`homNormalEntry_rho`). Bridge:

* `stepOmegaTail_taylorRho`: `Ω̂` of the reweighted Taylor element equals `Ω̂` of the `p+1` element;
* `StepHypMod.core_OmegaPlus_eq`: `Ω_{+,j} = Ω_j + Ω̂_j(R1_ξ)` with `R1` the `p+1` Taylor family
  (`StepHypMod.R1`), and `StepHypMod.core_omegaPlus_eq`: `ω_+ = ω + ω̂(R1_ξ)`;
* consequently the `J`-weighted (`(j+2)^{(p+1)-p}`) bounds `StepHypMod.OmegaPlus_tail_bound_J`
  (`≤ 3ε₀`) and `StepHypMod.OmegaPlus_tail_lip_J` (`≤ 3ε₁|ξ-ζ|`), for W6.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ}

section agree

variable {P : KamPhase → ℂ} {X : KamPhase → KamPhase}
  (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) (hs : 0 < s) (hr : 0 < r)
  (hP : IsSmoothing (p := p) (pb := p + 1) ha (stepRho_nn2 hp) (kamDomain s r) P X)
  (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
  (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε)

include hs in
theorem stepOmegaTail_reweight (R : HomTaylor_gen a p (p + 1) s) (j : ℕ+) :
    stepOmegaTail (homReweight hc R) j = stepOmegaTail R j := by
  have hQ : homCoeff (homReweight hc R).Q 0 = (homModRho a p pb hc).comp (homCoeff R.Q 0) := by
    show homCoeff (fun z => homModRhoL a p pb hc (R.Q z)) 0 = _
    rw [homCoeff_clm hs R.comp_Q.1]
    rfl
  unfold stepOmegaTail
  rw [hQ, homNormalEntry_rho]

/-- `Ω̂` of the reweighted Taylor element is `Ω̂` of the `p+1` one. -/
theorem stepOmegaTail_taylorRho (j : ℕ+) :
    stepOmegaTail (stepTaylorRho ha hp hpb hc hs hr hP hper hb) j =
      stepOmegaTail (stepTaylorP1 ha hp hs hr hP hper hb) j := by
  have hh := hP.holoX
  have hQ : homCoeff (stepTaylorRho ha hp hpb hc hs hr hP hper hb).Q 0 =
      homCoeff (homReweight hc (stepTaylorP1 ha hp hs hr hP hper hb)).Q 0 :=
    homCoeff_congr_real (fun x => tQ_rhoK hr hh hc (realTheta_mem_strip hs x)) 0
  rw [← stepOmegaTail_reweight hc hs (stepTaylorP1 ha hp hs hr hP hper hb) j]
  unfold stepOmegaTail
  rw [hQ]

end agree

variable {σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

namespace StepHypMod

variable (H : StepHypMod a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X) [Fact (0 < r)]
include H

theorem core_R_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    H.core.R ξ = stepTaylorRho H.ha H.hp H.hpb H.hc H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ)
      (H.hb ξ hξ) :=
  stepTaylorFam_of_mem H.ha H.hp H.hpb H.hs H.hr H.hP' H.hper H.hb' hξ

theorem R1_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    H.R1 ξ = stepTaylorP1 H.ha H.hp H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ) :=
  stepTaylorFam_of_mem H.ha H.hp (homModPP1 p) H.hs H.hr H.hP H.hper H.hb hξ

/-- **D2 bridge**: `Ω_{+,j}(ξ) = Ω_j(ξ) + Ω̂_j(R1_ξ)` (`R1` the `p+1` Taylor family). -/
theorem core_OmegaPlus_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (j : ℕ+) :
    H.core.OmegaPlus ξ j = Ω ξ j + stepOmegaTail (H.R1 ξ) j := by
  show Ω ξ j + stepOmegaTail (H.core.R ξ) j = _
  rw [H.core_R_eq hξ, H.R1_eq hξ, stepOmegaTail_taylorRho]

/-- `ω_+(ξ) = ω(ξ) + ω̂(R1_ξ)`. -/
theorem core_omegaPlus_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    H.core.omegaPlus ξ = fun k => ω ξ k + stepOmegaHat (H.R1 ξ) k := by
  show (fun k => ω ξ k + stepOmegaHat (H.core.R ξ) k) = _
  rw [H.core_R_eq hξ, H.R1_eq hξ]
  rfl

/-- The `J`-weighted tail bound `(j+2) |Ω_{+,j} - Ω_j| ≤ 3ε₀` (via `R1`). -/
theorem OmegaPlus_tail_bound_J {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (j : ℕ+) :
    ((j : ℝ) + 2) ^ ((p + 1) - p) * |H.core.OmegaPlus ξ j - Ω ξ j| ≤ 3 * ε₀ := by
  rw [H.core_OmegaPlus_eq hξ, add_sub_cancel_left (Ω ξ j)]
  exact stepOmegaTail_bound H.ha H.hp (homModPP1 p) H.hr H.hs (H.R1 ξ) (H.R1_field ξ hξ) j

/-- The `J`-weighted Lipschitz bound `(j+2) |Δ_ξ - Δ_ζ| ≤ 3ε₁ |ξ - ζ|`, `Δ = Ω_+ - Ω`. -/
theorem OmegaPlus_tail_lip_J {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) (j : ℕ+) :
    ((j : ℝ) + 2) ^ ((p + 1) - p) *
        |(H.core.OmegaPlus ξ j - Ω ξ j) - (H.core.OmegaPlus ζ j - Ω ζ j)| ≤
      3 * ε₁ * ‖ξ - ζ‖ := by
  rw [H.core_OmegaPlus_eq hξ, H.core_OmegaPlus_eq hζ, add_sub_cancel_left (Ω ξ j),
    add_sub_cancel_left (Ω ζ j), stepOmegaTail_sub H.hs]
  exact stepOmegaTail_bound H.ha H.hp (homModPP1 p) H.hr H.hs _ (H.R1_sub ξ hξ ζ hζ) j

end StepHypMod

end KAM.Wave

end
