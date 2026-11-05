/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepCore
public import KAM.Wave.KamStep.StepReweightTaylor
public import KAM.Wave.KamStep.ModifiedStepSolve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The hypotheses of the KAM step, modified case (blueprint-W `bpW:w5:data`, `bpW:w5:w4-modified`)

`StepHypMod`: step data with modified divisors (`HomMelnikovMod`, `2β ≤ p+1-p₊`), `P ∈ 𝒮_{p+1}`,
smallness with `c♮_F`, `t♮`. `StepHypMod.core`: its `StepCore` for the pair `(P, D_ρ ∘ X)` at the
exponent `p₊`, with the solution family `stepFTfamMod` (modified divisors applied to the `p+1`
Taylor element) and the equation transferred along `D_ρ`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The constant `M₁` of the modified case (`B^♮_σ` in place of `B^W_σ`). -/
def stepM₁n (τ σ α ε₀ ε₁ Mω MΩ : ℝ) : ℝ :=
  (7 + 10 * homKS) * (waveBN τ σ / α * (3 * ε₁ + 2 * (Mω + MΩ) * (3 * ε₀) / α))

open Classical in
/-- The family `F_ξ` of solutions with modified divisors (zero off `Π`). -/
def stepFTfamMod {a p pb s σ τ α β : ℝ} {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hβ0 : 0 ≤ β) (hβ : β ≤ p + 1 - pb) (hH : HomMelnikovMod τ α β Par ω Ω)
    (R : (Fin 2 → ℝ) → HomTaylor_gen a p (p + 1) s) (ξ : Fin 2 → ℝ) :
    HomTaylor_gen a p pb (s - σ) :=
  if hξ : ξ ∈ Par then
    homModSolveTaylor hτ hα hσ hσs (homMod_pb_le hβ0 hβ) (homModMultBounds_of hα hβ0 hβ hH hξ) (R ξ)
  else zeroTaylor a p pb (s - σ)

theorem stepFTfamMod_of_mem {a p pb s σ τ α β : ℝ} {Par : Set (Fin 2 → ℝ)}
    {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} (hτ : 0 ≤ τ) (hα : 0 < α)
    (hσ : 0 < σ) (hσs : σ < s) (hβ0 : 0 ≤ β) (hβ : β ≤ p + 1 - pb)
    (hH : HomMelnikovMod τ α β Par ω Ω) (R : (Fin 2 → ℝ) → HomTaylor_gen a p (p + 1) s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    stepFTfamMod (pb := pb) hτ hα hσ hσs hβ0 hβ hH R ξ =
      homModSolveTaylor hτ hα hσ hσs (homMod_pb_le hβ0 hβ) (homModMultBounds_of hα hβ0 hβ hH hξ)
        (R ξ) := by
  classical
  simp [stepFTfamMod, hξ]

/-- Step data (modified case) and the smallness condition `ε ≤ α σ^{t♮} η²/c♮₀`. -/
structure StepHypMod (a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ))
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
  hβ0 : 0 ≤ β
  h2β : 2 * β ≤ p + 1 - pb
  mel : HomMelnikovMod τ α β Par ω Ω
  hP : ∀ ξ ∈ Par, IsSmoothing (p := p) (pb := p + 1) ha (by linarith : 0 ≤ (p + 1) + p)
    (kamDomain s r) (P ξ) (X ξ)
  hper : ∀ ξ ∈ Par, ∀ i, ∀ w ∈ kamDomain s r, P ξ (w + stepTau i) = P ξ w
  hreal : ∀ ξ ∈ Par, ∀ w ∈ kamDomain s r, StepReal w → (P ξ w).im = 0
  hε₀ : 0 < ε₀
  hε₁ : 0 ≤ ε₁
  hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀
  hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖
  hε : ε₀ + lam * ε₁ ≤ ε
  small : ε ≤ α * σ ^ stepTn τ * η ^ 2 / (16 * stepCFn τ)

variable {a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

namespace StepHypMod

variable (H : StepHypMod a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
include H

theorem hc : pb ≤ p + 1 := by linarith [H.hβ0, H.h2β]

theorem hβ : β ≤ p + 1 - pb := by linarith [H.hβ0, H.h2β]

theorem hσs' : σ < s := by linarith [H.hσs, H.hσ]

/-- The reweighted field family `D_ρ ∘ X`. -/
def X' : (Fin 2 → ℝ) → KamPhase → KamPhase := fun ξ w => stepRhoK a p pb H.hc (X ξ w)

/-- The Taylor family at `p̄ = p+1`. -/
def R1 : (Fin 2 → ℝ) → HomTaylor_gen a p (p + 1) s :=
  stepTaylorFam H.ha H.hp (homModPP1 p) H.hs H.hr Par P X H.hP H.hper H.hb

/-- The solution family with modified divisors. -/
def FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ) :=
  stepFTfamMod H.hτ H.hα H.hσ H.hσs' H.hβ0 H.hβ H.mel H.R1

theorem R1_field : ∀ ξ ∈ Par, HomFieldBound_gen H.ha H.hp (homModPP1 p) r (3 * ε₀) (H.R1 ξ) :=
  stepTaylorFam_field H.ha H.hp (homModPP1 p) H.hs H.hr H.hP H.hper H.hb

theorem R1_sub : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
    HomFieldBound_gen H.ha H.hp (homModPP1 p) r (3 * ε₁ * ‖ξ - ζ‖) ((H.R1 ξ).homSub (H.R1 ζ)) :=
  stepTaylorFam_sub H.ha H.hp (homModPP1 p) H.hs H.hr H.hP H.hper H.hb H.hdiff

theorem hP' : ∀ ξ ∈ Par, IsSmoothing (p := p) H.ha (by linarith [H.hp, H.hpb] : 0 ≤ pb + p)
    (kamDomain s r) (P ξ) (H.X' ξ) := fun ξ hξ =>
  IsSmoothing.rhoK H.ha H.hc _ (by linarith [H.hp]) (H.hP ξ hξ)

theorem hb' : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (H.X' ξ z) ≤ ε₀ :=
  fun ξ hξ z hz => stepRhoK_bound H.hc H.hr (H.hb ξ hξ) z hz

theorem M₀_pos : 0 < stepM₀ τ σ α ε₀ := by
  have := waveBW_pos H.hτ H.hσ
  have := H.hα
  have := H.hε₀
  have := one_le_homKS
  unfold stepM₀
  positivity

theorem M₁_nonneg : 0 ≤ stepM₁n τ σ α ε₀ ε₁ Mω MΩ := by
  have := (waveBW_nonneg τ σ).trans (waveBW_le_waveBN H.hτ H.hσ)
  have := H.hα
  have := H.hε₀
  have := H.hε₁
  have := one_le_homKS
  have := H.hM
  unfold stepM₁n
  positivity

theorem M_sum : stepM₀ τ σ α ε₀ + lam * stepM₁n τ σ α ε₀ ε₁ Mω MΩ ≤
    stepMF (stepCFn τ) (stepTn τ) α σ ε := by
  have hε : 0 < ε := by
    have := mul_nonneg H.hlam0 H.hε₁
    linarith [H.hε₀, H.hε]
  have h2 := (homModLemma2 (α := α) (M := Mω + MΩ) (lam := lam) (σ := σ) (ε := 3 * ε₀)
    (εL := 3 * ε₁) H.hτ H.hα H.hM H.hlam0 H.hlam H.hσ H.hσ1 (by linarith [H.hε₀])
    (by linarith [H.hε₁])).1
  unfold homLamNorm at h2
  have hsb := stepSolve_bound_mod H.hτ H.hα H.hσ H.hσ1 hε.le
  have hBN := (waveBW_nonneg τ σ).trans (waveBW_le_waveBN H.hτ H.hσ)
  have hC : 0 ≤ 3 * stepC1 * waveBN τ σ / α := by
    have := stepC1_pos; have := H.hα; positivity
  have h1 : 3 * (7 + 10 * homKS) * waveBN τ σ / α * (3 * ε₀ + lam * (3 * ε₁)) ≤
      3 * stepC1 * waveBN τ σ / α * (3 * ε) := by
    have e : 3 * (7 + 10 * homKS) * waveBN τ σ / α = 3 * stepC1 * waveBN τ σ / α := by
      unfold stepC1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by nlinarith [H.hε]) hC
  have e0 : stepM₀ τ σ α ε₀ = (7 + 10 * homKS) * (waveBW τ σ * (3 * ε₀) / α) := rfl
  have e1 : stepM₁n τ σ α ε₀ ε₁ Mω MΩ = (7 + 10 * homKS) * (waveBN τ σ / α *
      (3 * ε₁ + 2 * (Mω + MΩ) * (3 * ε₀) / α)) := rfl
  rw [e0, e1]
  exact h2.trans (h1.trans hsb)

theorem F_field : ∀ ξ ∈ Par, HomFieldBound_gen H.ha H.hp H.hpb r (stepM₀ τ σ α ε₀) (H.FT ξ) :=
  fun ξ hξ => by
  unfold FT
  rw [stepFTfamMod_of_mem H.hτ H.hα H.hσ H.hσs' H.hβ0 H.hβ H.mel H.R1 hξ]
  exact homModLemma_fieldBound H.mel H.hβ0 H.hβ H.ha H.hp H.hpb H.hr H.hτ H.hα H.hσ H.hσs' hξ
    (H.R1 ξ) (H.R1_field ξ hξ)

theorem F_sub : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
    HomFieldBound_gen H.ha H.hp H.hpb r (stepM₁n τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖)
      ((H.FT ξ).homSub (H.FT ζ)) := fun ξ hξ ζ hζ => by
  unfold FT
  rw [stepFTfamMod_of_mem H.hτ H.hα H.hσ H.hσs' H.hβ0 H.hβ H.mel H.R1 hξ,
    stepFTfamMod_of_mem H.hτ H.hα H.hσ H.hσs' H.hβ0 H.hβ H.mel H.R1 hζ]
  have := homModLemma_lipschitz H.freq H.mel H.hβ0 H.h2β H.ha H.hp H.hpb H.hr H.hτ H.hα
    (by linarith [H.hε₁] : 0 ≤ 3 * ε₁) H.hσ H.hσs' hξ hζ (H.R1 ξ) (H.R1 ζ) (H.R1_field ξ hξ)
    (H.R1_field ζ hζ) (H.R1_sub ξ hξ ζ hζ)
  have e : stepM₁n τ σ α ε₀ ε₁ Mω MΩ * ‖ξ - ζ‖ = (7 + 10 * homKS) * (waveBN τ σ / α *
      (3 * ε₁ + 2 * (Mω + MΩ) * (3 * ε₀) / α) * ‖ξ - ζ‖) := by unfold stepM₁n; ring
  rw [e]
  exact this

theorem equation (ξ : Fin 2 → ℝ) (hξ : ξ ∈ Par) (w : KamPhase)
    (hw : w.1 ∈ complexStrip 2 (s - σ)) :
    waveStepFun H.ha (homPP H.hp H.hpb)
        (stepTaylorFam H.ha H.hp H.hpb H.hs H.hr Par P H.X' H.hP' H.hper H.hb' ξ) w +
        ((homDN H.hG (by linarith [H.freq.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le H.freq hξ)
            (ω ξ) (stepToHom w)).comp stepToHom)
          (kamHomEmbed a p pb H.hpb (stepField H.ha H.hp H.hpb (H.FT ξ) w)) =
      waveStepFun H.ha (homPP H.hp H.hpb) (homNhatTaylor_gen
          (stepTaylorFam H.ha H.hp H.hpb H.hs H.hr Par P H.X' H.hP' H.hper H.hb' ξ)) w +
        homCoeff (stepTaylorFam H.ha H.hp H.hpb H.hs H.hr Par P H.X' H.hP' H.hper H.hb' ξ).a0 0 :=
          by
  haveI : Fact (0 < r) := ⟨H.hr⟩
  have hws : w.1 ∈ complexStrip 2 s := fun i => lt_trans (hw i) (by linarith [H.hσ])
  have hF : H.FT ξ = homModSolveTaylor H.hτ H.hα H.hσ H.hσs' (homMod_pb_le H.hβ0 H.hβ)
      (homModMultBounds_of H.hα H.hβ0 H.hβ H.mel hξ) (H.R1 ξ) := by
    unfold FT; exact stepFTfamMod_of_mem H.hτ H.hα H.hσ H.hσs' H.hβ0 H.hβ H.mel H.R1 hξ
  have hR1 : H.R1 ξ = stepTaylorP1 H.ha H.hp H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ) :=
    stepTaylorFam_of_mem H.ha H.hp (homModPP1 p) H.hs H.hr H.hP H.hper H.hb hξ
  have hR : stepTaylorFam H.ha H.hp H.hpb H.hs H.hr Par P H.X' H.hP' H.hper H.hb' ξ =
      stepTaylorRho H.ha H.hp H.hpb H.hc H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ) :=
    stepTaylorFam_of_mem H.ha H.hp H.hpb H.hs H.hr H.hP' H.hper H.hb' hξ
  have key := stepSolveMod_equation H.freq H.mel H.hβ0 H.hβ H.ha H.hp H.hpb H.hp1 H.hG H.hr H.hτ
    H.hα H.hσ H.hσs' hξ (H.R1 ξ) (H.R1_field ξ hξ) hw
  rw [← hF] at key
  rw [hR, stepFun_taylorRho H.ha H.hp H.hpb H.hc H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ) (H.hb ξ hξ)
    hws, stepFun_nhat_taylorRho H.ha H.hp H.hpb H.hc H.hs H.hr (H.hP ξ hξ) (H.hper ξ hξ)
    (H.hb ξ hξ)]
  rw [hR1] at key
  exact key

/-- A `StepHypMod` is a `StepCore` for `(P, D_ρ ∘ X)`. -/
protected theorem core : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ (stepM₀ τ σ α ε₀)
    (stepM₁n τ σ α ε₀ ε₁ Mω MΩ) (stepCFn τ) (stepTn τ) Par ω Ω P H.X' H.FT where
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
  hP := H.hP'
  hper := H.hper
  hreal := H.hreal
  hε₀ := H.hε₀
  hε₁ := H.hε₁
  hb := H.hb'
  hdiff := fun ξ hξ ζ hζ z hz => by
    refine (kamNorm_stepRhoK_sub_le H.hc H.hr _ _).trans ?_
    exact H.hdiff ξ hξ ζ hζ z hz
  hε := H.hε
  hc := stepCFn_pos H.hτ
  small := H.small
  M₀_pos := H.M₀_pos
  M₁_nonneg := H.M₁_nonneg
  M_sum := H.M_sum
  F_field := H.F_field
  F_sub := H.F_sub
  equation := fun ξ hξ w hw => H.equation ξ hξ w hw

end StepHypMod

end KAM.Wave
