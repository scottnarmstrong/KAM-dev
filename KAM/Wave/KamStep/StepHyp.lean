/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The hypotheses of the KAM step (blueprint-W `bpW:w5:data`, non-modified case)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`StepHyp`: step data and the smallness condition. `ε₀, ε₁` are the two bounds that make up
`|X_P|^λ ≤ ε` read as a conjunction (`ε₀ + λ ε₁ ≤ ε`); `ε₀ > 0` (it can always be arranged by
enlarging `ε₀` when `X_P ≢ 0`, and `ε₀ := ε/2`, `ε₁ := 0` when `X_P = 0`).
`StepHyp.setup`: the field bounds of `R_ξ = stepTaylorFam` and `F_ξ = stepFTfam`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- Step data (non-modified case) and the smallness condition `ε ≤ α σ^t η²/c₀`. -/
structure StepHyp (a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ))
    (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ)
    (P : (Fin 2 → ℝ) → KamPhase → ℂ) (X : (Fin 2 → ℝ) → KamPhase → KamPhase) : Prop where
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
  mel : HomMelnikov τ α Par ω Ω
  hP : ∀ ξ ∈ Par, IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) (P ξ) (X ξ)
  hper : ∀ ξ ∈ Par, ∀ i, ∀ w ∈ kamDomain s r, P ξ (w + stepTau i) = P ξ w
  hreal : ∀ ξ ∈ Par, ∀ w ∈ kamDomain s r, StepReal w → (P ξ w).im = 0
  hε₀ : 0 < ε₀
  hε₁ : 0 ≤ ε₁
  hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀
  hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖
  hε : ε₀ + lam * ε₁ ≤ ε
  small : ε ≤ α * σ ^ stepExpT τ * η ^ 2 / (16 * stepCF τ)

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- The constants `M₀`, `M₁` of `X_F` (sup and `ξ`-Lipschitz). -/
def stepM₀ (τ σ α ε₀ : ℝ) : ℝ := (7 + 10 * homKS) * (waveBW τ σ * (3 * ε₀) / α)

def stepM₁ (τ σ α ε₀ ε₁ Mω MΩ : ℝ) : ℝ :=
  (7 + 10 * homKS) * (waveBW τ σ / α * (3 * ε₁ + 2 * (Mω + MΩ) * (3 * ε₀) / α))

namespace StepHyp

variable (H : StepHyp a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
include H

theorem ε_pos : 0 < ε := by
  have := mul_nonneg H.hlam0 H.hε₁
  linarith [H.hε₀, H.hε]

theorem hσs' : σ < s := by linarith [H.hσs, H.hσ]

theorem pb_pos : 0 ≤ pb + p := by linarith [H.hp, H.hpb]

/-- `M_F`. -/
theorem mf_small : stepMF (stepCF τ) (stepExpT τ) α σ ε ≤ σ * η ^ 2 / 16 :=
  stepMF_le_of_small (stepCF_pos H.hτ) H.hα H.hσ H.small

/-- The Taylor family `R_ξ`. -/
def R : (Fin 2 → ℝ) → HomTaylor_gen a p pb s :=
  stepTaylorFam H.ha H.hp H.hpb H.hs H.hr Par P X H.hP H.hper H.hb

/-- The solution family `F_ξ`. -/
def FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ) :=
  stepFTfam H.freq H.mel H.hτ H.hα H.hσ H.hσs' H.R

theorem R_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    H.R ξ = stepTaylorOf H.ha H.hp H.hpb H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ) :=
  haveI : Fact (0 < r) := ⟨H.hr⟩
  stepTaylorFam_of_mem H.ha H.hp H.hpb H.hs H.hr H.hP H.hper H.hb hξ

theorem FT_eq {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    H.FT ξ = homSolveTaylor_gen H.hτ H.hα H.hσ H.hσs' (homMultBounds_of H.freq H.hα H.mel hξ)
      (H.R ξ) := stepFTfam_of_mem H.freq H.mel H.hτ H.hα H.hσ H.hσs' H.R hξ

theorem R_field : ∀ ξ ∈ Par, HomFieldBound_gen H.ha H.hp H.hpb r (3 * ε₀) (H.R ξ) :=
  stepTaylorFam_field H.ha H.hp H.hpb H.hs H.hr H.hP H.hper H.hb

theorem R_sub : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
    HomFieldBound_gen H.ha H.hp H.hpb r (3 * ε₁ * ‖ξ - ζ‖) ((H.R ξ).homSub (H.R ζ)) :=
  stepTaylorFam_sub H.ha H.hp H.hpb H.hs H.hr H.hP H.hper H.hb H.hdiff

theorem F_field : ∀ ξ ∈ Par, HomFieldBound_gen H.ha H.hp H.hpb r (stepM₀ τ σ α ε₀) (H.FT ξ) := fun
    ξ hξ => by
  rw [H.FT_eq hξ]
  exact homLemma1_fieldBound_gen H.freq H.mel H.ha H.hp H.hpb H.hr H.hτ H.hα H.hσ H.hσs' hξ
    (H.R ξ) (H.R_field ξ hξ)

theorem F_sub : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
    HomFieldBound_gen H.ha H.hp H.hpb r (stepM₁ τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖) ((H.FT ξ).homSub (H.FT
        ζ)) :=
  fun ξ hξ ζ hζ => by
  rw [H.FT_eq hξ, H.FT_eq hζ]
  have := homLemma1_lipschitz_gen H.freq H.mel H.ha H.hp H.hpb H.hr H.hτ H.hα
    (by linarith [H.hε₁] : 0 ≤ 3 * ε₁) H.hσ H.hσs' hξ hζ (H.R ξ) (H.R ζ) (H.R_field ξ hξ)
    (H.R_field ζ hζ) (H.R_sub ξ hξ ζ hζ)
  have e : stepM₁ τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖ = (7 + 10 * homKS) * (waveBW τ σ / α *
      (3 * ε₁ + 2 * (Mω + MΩ) * (3 * ε₀) / α) * ‖ξ - ζ‖) := by unfold stepM₁; ring
  rw [e]
  exact this

theorem M₀_pos : 0 < stepM₀ τ σ α ε₀ := by
  have := waveBW_pos H.hτ H.hσ
  have := H.hα
  have := H.hε₀
  have := one_le_homKS
  unfold stepM₀
  positivity

theorem M₁_nonneg : 0 ≤ stepM₁ τ σ α ε₀ ε₁ Mω MΩ := by
  have := waveBW_nonneg τ σ
  have := H.hα
  have := H.hε₀
  have := H.hε₁
  have := one_le_homKS
  have := H.hM
  unfold stepM₁
  positivity

theorem M_sum : stepM₀ τ σ α ε₀ + lam * stepM₁ τ σ α ε₀ ε₁ Mω MΩ ≤ stepMF (stepCF τ) (stepExpT τ) α
    σ ε := by
  have hex := (stepSolve_fam_explicit H.freq H.mel H.ha H.hp H.hpb (r := r) (ε := 3 * ε₀)
    (εL := 3 * ε₁) (lam := lam) (σ := σ) H.hr H.hτ H.hα H.hσ H.hσ1 H.hσs' H.hM H.hlam0 H.hlam
    (by linarith [H.hε₀]) (by linarith [H.hε₁]) H.R H.FT (fun ξ hξ => H.FT_eq hξ) H.R_field
    (fun ξ hξ ζ hζ => H.R_sub ξ hξ ζ hζ)).1
  have hsb := stepSolve_bound H.hτ H.hα H.hσ H.hσ1 H.ε_pos.le
  have hB := waveBW_nonneg τ σ
  have hC : 0 ≤ 3 * stepC1 * waveBW τ σ / α := by
    have := stepC1_pos; have := H.hα; positivity
  have h1 : 3 * (7 + 10 * homKS) * waveBW τ σ / α * (3 * ε₀ + lam * (3 * ε₁)) ≤
      3 * stepC1 * waveBW τ σ / α * (3 * ε) := by
    have e : 3 * (7 + 10 * homKS) * waveBW τ σ / α = 3 * stepC1 * waveBW τ σ / α := by
      unfold stepC1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by nlinarith [H.hε]) hC
  exact (show stepM₀ τ σ α ε₀ + lam * stepM₁ τ σ α ε₀ ε₁ Mω MΩ ≤ _ from hex).trans (h1.trans hsb)

/-- A `StepHyp` is a `StepCore` (`F` solved with unmodified divisors). -/
theorem core : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ (stepM₀ τ σ α ε₀)
    (stepM₁ τ σ α ε₀ ε₁ Mω MΩ) (stepCF τ) (stepExpT τ) Par ω Ω P X H.FT where
  ha := H.ha
  hp := H.hp
  hpb := H.hpb
  hp1 := H.hp1
  hpp := H.hpp
  hG := H.hG
  hτ := H.hτ
  hα := H.hα
  hs := H.hs
  hr := H.hr
  hσ := H.hσ
  hσ1 := H.hσ1
  hσs := H.hσs
  hη0 := H.hη0
  hη := H.hη
  freq := H.freq
  hM := H.hM
  hlam0 := H.hlam0
  hlam := H.hlam
  hP := H.hP
  hper := H.hper
  hreal := H.hreal
  hε₀ := H.hε₀
  hε₁ := H.hε₁
  hb := H.hb
  hdiff := H.hdiff
  hε := H.hε
  hc := stepCF_pos H.hτ
  small := H.small
  M₀_pos := H.M₀_pos
  M₁_nonneg := H.M₁_nonneg
  M_sum := H.M_sum
  F_field := H.F_field
  F_sub := H.F_sub
  equation := fun ξ hξ w hw => by
    rw [H.FT_eq hξ]
    exact stepSolve_equation H.freq H.mel H.ha H.hp H.hpb H.hp1 H.hG H.hr H.hτ H.hα H.hσ H.hσs' hξ
      (H.R ξ) (H.R_field ξ hξ) hw

end StepHyp

end KAM.Wave
