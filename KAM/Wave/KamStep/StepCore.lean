/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepSetup
public import KAM.Wave.KamStep.TaylorReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The abstract core of the KAM step (blueprint-W `bpW:w5:data`, `bpW:w5:step`)

`StepCore`: everything the proof of the step theorem uses about the data of the step, with the
divisor hypothesis (`HomMelnikov` / `HomMelnikovMod`) and the supplier of the solution family `F`
abstracted away. The data are a smoothing family `(P, X)` at the exponent `p_+` (`pb`), the family
`F = FT` of solutions of the homological equation with its field bounds `M₀`, `M₁` and the
equation `R + DN·X_F = N̂ + â₀` for `R = stepTaylorFam`, and the constants `cF`, `tF` of the
smallness condition. The non-modified case (`WaveStepHyp`) and the modified case (`StepHypMod`) each
construct a `StepCore`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The constants `M₀`, `M₁` of `X_F` (sup and `ξ`-Lipschitz). -/
def stepM₀ (τ σ α ε₀ : ℝ) : ℝ := (7 + 10 * homKS) * (waveBW τ σ * (3 * ε₀) / α)

def stepM₁ (τ σ α ε₀ ε₁ Mω MΩ : ℝ) : ℝ :=
  (7 + 10 * homKS) * (waveBW τ σ / α * (3 * ε₁ + 2 * (Mω + MΩ) * (3 * ε₀) / α))

section family

variable {a p pb s r ε₀ ε₁ : ℝ} {Par : Set (Fin 2 → ℝ)} {P : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

theorem stepTaylorFam_field (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hr : 0 < r)
    (hP : ∀ ξ ∈ Par, IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) (P ξ) (X ξ))
    (hper : ∀ ξ ∈ Par, ∀ i, ∀ w ∈ kamDomain s r, P ξ (w + stepTau i) = P ξ w)
    (hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀) :
    ∀ ξ ∈ Par, HomFieldBound_gen ha hp hpb r (3 * ε₀)
      (stepTaylorFam ha hp hpb hs hr Par P X hP hper hb ξ) := fun ξ hξ => by
  haveI : Fact (0 < r) := ⟨hr⟩
  rw [stepTaylorFam_of_mem ha hp hpb hs hr hP hper hb hξ]
  exact stepTaylor_fieldBound ha hp hpb hs hr (hP ξ hξ) (hper ξ hξ) (hb ξ hξ)

theorem stepTaylorFam_sub (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hr : 0 < r)
    (hP : ∀ ξ ∈ Par, IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) (P ξ) (X ξ))
    (hper : ∀ ξ ∈ Par, ∀ i, ∀ w ∈ kamDomain s r, P ξ (w + stepTau i) = P ξ w)
    (hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀)
    (hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r,
      kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖) :
    ∀ ξ ∈ Par, ∀ ζ ∈ Par, HomFieldBound_gen ha hp hpb r (3 * ε₁ * ‖ξ - ζ‖)
      ((stepTaylorFam ha hp hpb hs hr Par P X hP hper hb ξ).homSub
        (stepTaylorFam ha hp hpb hs hr Par P X hP hper hb ζ)) := fun ξ hξ ζ hζ => by
  haveI : Fact (0 < r) := ⟨hr⟩
  rw [stepTaylorFam_of_mem ha hp hpb hs hr hP hper hb hξ,
    stepTaylorFam_of_mem ha hp hpb hs hr hP hper hb hζ,
    show 3 * ε₁ * ‖ξ - ζ‖ = 3 * (ε₁ * ‖ξ - ζ‖) by ring]
  exact stepTaylor_subFieldBound ha hp hpb hs hr (hP ξ hξ) (hP ζ hζ)
    (hper ξ hξ) (hper ζ hζ) (hb ξ hξ) (hb ζ hζ) (hdiff ξ hξ ζ hζ)

end family

/-- The core of the KAM step: step data at the exponent `p_+ = pb` for a smoothing family `(P, X)`,
with the solution family `FT` of the homological equation, its bounds `M₀`, `M₁` and the constants
`cF`, `tF` of the smallness condition `ε ≤ α σ^{tF} η²/(16 cF)`. -/
structure StepCore (a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ)
    (Par : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ)
    (P : (Fin 2 → ℝ) → KamPhase → ℂ) (X : (Fin 2 → ℝ) → KamPhase → KamPhase)
    (FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)) : Prop where
  ha : 0 ≤ a
  hp : 0 ≤ p
  hpb : p ≤ pb
  hp1 : 1 ≤ p + pb
  hpp : 1 / 2 ≤ pb - p
  hG : HomGuard a p γ
  hτ : 0 ≤ τ
  hα : 0 < α
  hs : 0 < s
  hr : 0 < r
  hσ : 0 < σ
  hσ1 : σ ≤ 1
  hσs : 5 * σ < s
  hη0 : 0 < η
  hη : η ≤ 1 / 8
  freq : HomFreqHyp Par ω Ω M0 Mω MΩ
  hM : 0 < Mω + MΩ
  hlam0 : 0 ≤ lam
  hlam : lam ≤ α / (Mω + MΩ)
  hP : ∀ ξ ∈ Par, IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) (P ξ) (X ξ)
  hper : ∀ ξ ∈ Par, ∀ i, ∀ w ∈ kamDomain s r, P ξ (w + stepTau i) = P ξ w
  hreal : ∀ ξ ∈ Par, ∀ w ∈ kamDomain s r, StepReal w → (P ξ w).im = 0
  hε₀ : 0 < ε₀
  hε₁ : 0 ≤ ε₁
  hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀
  hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖
  hε : ε₀ + lam * ε₁ ≤ ε
  hc : 0 < cF
  small : ε ≤ α * σ ^ tF * η ^ 2 / (16 * cF)
  M₀_pos : 0 < M₀
  M₁_nonneg : 0 ≤ M₁
  M_sum : M₀ + lam * M₁ ≤ stepMF cF tF α σ ε
  F_field : ∀ ξ ∈ Par, HomFieldBound_gen ha hp hpb r M₀ (FT ξ)
  F_sub : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
    HomFieldBound_gen ha hp hpb r (M₁ * ‖ξ - ζ‖) ((FT ξ).homSub (FT ζ))
  equation : ∀ ξ (hξ : ξ ∈ Par), ∀ w : KamPhase, w.1 ∈ complexStrip 2 (s - σ) →
    waveStepFun ha (homPP hp hpb) (stepTaylorFam ha hp hpb hs hr Par P X hP hper hb ξ) w +
        ((homDN hG (by linarith [freq.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le freq hξ) (ω ξ)
            (stepToHom w)).comp stepToHom)
          (kamHomEmbed a p pb hpb (stepField ha hp hpb (FT ξ) w)) =
      waveStepFun ha (homPP hp hpb)
          (homNhatTaylor_gen (stepTaylorFam ha hp hpb hs hr Par P X hP hper hb ξ)) w +
        homCoeff (stepTaylorFam ha hp hpb hs hr Par P X hP hper hb ξ).a0 0

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT)
include H

theorem ε_pos : 0 < ε := by
  have := mul_nonneg H.hlam0 H.hε₁
  linarith [H.hε₀, H.hε]

theorem hσs' : σ < s := by linarith [H.hσs, H.hσ]

theorem pb_pos : 0 ≤ pb + p := by linarith [H.hp, H.hpb]

/-- `M_F ≤ σ η²/16`. -/
theorem mf_small : stepMF cF tF α σ ε ≤ σ * η ^ 2 / 16 :=
  stepMF_le_of_small H.hc H.hα H.hσ H.small

/-- The Taylor family `R_ξ`. -/
protected def R : (Fin 2 → ℝ) → HomTaylor_gen a p pb s :=
  stepTaylorFam H.ha H.hp H.hpb H.hs H.hr Par P X H.hP H.hper H.hb

theorem R_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    H.R ξ = stepTaylorOf H.ha H.hp H.hpb H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ) :=
  haveI : Fact (0 < r) := ⟨H.hr⟩
  stepTaylorFam_of_mem H.ha H.hp H.hpb H.hs H.hr H.hP H.hper H.hb hξ

theorem R_field : ∀ ξ ∈ Par, HomFieldBound_gen H.ha H.hp H.hpb r (3 * ε₀) (H.R ξ) :=
  stepTaylorFam_field H.ha H.hp H.hpb H.hs H.hr H.hP H.hper H.hb

theorem R_sub : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
    HomFieldBound_gen H.ha H.hp H.hpb r (3 * ε₁ * ‖ξ - ζ‖) ((H.R ξ).homSub (H.R ζ)) :=
  stepTaylorFam_sub H.ha H.hp H.hpb H.hs H.hr H.hP H.hper H.hb H.hdiff

end StepCore

end KAM.Wave
