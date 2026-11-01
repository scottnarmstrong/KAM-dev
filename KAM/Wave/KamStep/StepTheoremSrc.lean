/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepTheoremMod
public import KAM.Wave.KamStep.RealWeakConj
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One KAM step: the source-facing theorems (blueprint-W `bpW:w5:step`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

The premise `ε₀ > 0` of the conditional helpers (`stepTheorem_of_eps0_pos`,
`stepTheoremMod_of_eps0_pos`) is not a blueprint premise. The hypotheses `StepHypSrc`,
`StepHypModSrc` assume only `ε₀ ≥ 0` and the blueprint's `ε > 0` (Definition `bpW:w5:data`:
"a number `ε > 0` with `ε ≥ |X_P|^λ`", `w5-kamstep.tex` l. 336). The theorems `stepTheorem`,
`stepTheoremMod` state the blueprint's clauses (i)-(v) in terms of `ε`, with the `λ`-norms read as
conjunctions of a sup bound and a Lipschitz bound with total `≤ (constant)·ε`. They are derived from
the helpers for the splitting `(ε₀*, ε₁*)` = `(ε₀, ε₁)` if `ε₀ > 0` and `(ε, 0)` if `ε₀ = 0`
(then `X_P ≡ 0` on `D(s,r)`), which satisfies `ε₀* + λ ε₁* ≤ ε`. The objects `Φ`, `P_+`, ...
are those of `H.hyp`, the `WaveStepHyp` for this splitting; they do not depend on the splitting.
Clause (iv) is conditional on `HomMelnikov` (blueprint: "whenever the same holds with `α`").

Clause (i) also contains "`Φ` is real on real points", "`DΦ(w)` maps `𝒫^{p_+}` onto itself" and the
weak conjugacy of `bpW:w5:new-ham` (iii) in field form, and clause (ii) "`P_+` is real"; they are
derived from the conditional helpers `stepTheorem_reality_of_eps0_pos`,
`stepTheorem_dPhi_smooth_onto_of_eps0_pos`, `stepTheorem_weakConj_field_of_eps0_pos` (and their
`Mod` forms, W5-REAL) applied to `H.hyp`, so no premise `ε₀ > 0` appears.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem kamNorm_sub_le {r : ℝ} (hr : 0 < r) (W W' : KamPhase) :
    kamNorm r (W - W') ≤ kamNorm r W + kamNorm r W' := by
  have h := kamNorm_add_le hr W (-W')
  have e : kamNorm r (-W') = kamNorm r W' := by unfold kamNorm; simp
  rw [sub_eq_add_neg]
  linarith

/-- The splitting `ε₀*`: `ε₀` if positive, else `ε`. -/
def stepE0 (ε ε₀ : ℝ) : ℝ := if 0 < ε₀ then ε₀ else ε

/-- The splitting `ε₁*`: `ε₁` if `ε₀` is positive, else `0`. -/
def stepE1 (ε₀ ε₁ : ℝ) : ℝ := if 0 < ε₀ then ε₁ else 0

/-- The splitting `(ε₀*, ε₁*)`. -/
theorem eps_split_spec {r lam ε ε₀ ε₁ : ℝ} {Par : Set (Fin 2 → ℝ)} {s : ℝ}
    {X : (Fin 2 → ℝ) → KamPhase → KamPhase} (hr : 0 < r) (hε : 0 < ε) (hε₀ : 0 ≤ ε₀)
    (hε₁ : 0 ≤ ε₁) (hlam : 0 ≤ lam)
    (hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀)
    (hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r,
      kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖) (hsum : ε₀ + lam * ε₁ ≤ ε) :
    0 < stepE0 ε ε₀ ∧ 0 ≤ stepE1 ε₀ ε₁ ∧ stepE0 ε ε₀ + lam * stepE1 ε₀ ε₁ ≤ ε ∧
      (∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ stepE0 ε ε₀) ∧
      (∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r,
        kamNorm r (X ξ z - X ζ z) ≤ stepE1 ε₀ ε₁ * ‖ξ - ζ‖) := by
  by_cases h : 0 < ε₀
  · have h0 : stepE0 ε ε₀ = ε₀ := if_pos h
    have h1 : stepE1 ε₀ ε₁ = ε₁ := if_pos h
    rw [h0, h1]
    exact ⟨h, hε₁, hsum, hb, hdiff⟩
  · have h0 : stepE0 ε ε₀ = ε := if_neg h
    have h1 : stepE1 ε₀ ε₁ = 0 := if_neg h
    have hz : ε₀ = 0 := le_antisymm (not_lt.mp h) hε₀
    rw [h0, h1]
    refine ⟨hε, le_rfl, by linarith, fun ξ hξ z hz' => ?_, fun ξ hξ ζ hζ z hz' => ?_⟩
    · have := hb ξ hξ z hz'
      rw [hz] at this
      linarith [hε]
    · have h1 := hb ξ hξ z hz'
      have h2 := hb ζ hζ z hz'
      rw [hz] at h1 h2
      have := kamNorm_sub_le hr (X ξ z) (X ζ z)
      simp only [zero_mul]
      linarith

/-- Source-facing step data (only `ε₀ ≥ 0`, `ε > 0`). -/
structure StepHypSrc (a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ))
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
  hε₀ : 0 ≤ ε₀
  hεpos : 0 < ε
  hε₁ : 0 ≤ ε₁
  hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀
  hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖
  hε : ε₀ + lam * ε₁ ≤ ε
  small : ε ≤ α * σ ^ stepExpT τ * η ^ 2 / (16 * stepCF τ)

/-- Source-facing step data (only `ε₀ ≥ 0`, `ε > 0`). -/
structure StepHypModSrc (a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ))
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
  hε₀ : 0 ≤ ε₀
  hεpos : 0 < ε
  hε₁ : 0 ≤ ε₁
  hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀
  hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖
  hε : ε₀ + lam * ε₁ ≤ ε
  small : ε ≤ α * σ ^ stepTn τ * η ^ 2 / (16 * stepCFn τ)

variable {a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ : ℝ} {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

namespace StepHypSrc

variable (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
include H

theorem split_spec : 0 < (stepE0 ε ε₀) ∧ 0 ≤ (stepE1 ε₀ ε₁) ∧ (stepE0 ε ε₀) + lam * (stepE1 ε₀ ε₁)
  ≤ ε ∧
    (∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ (stepE0 ε ε₀)) ∧
    (∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r,
      kamNorm r (X ξ z - X ζ z) ≤ (stepE1 ε₀ ε₁) * ‖ξ - ζ‖) :=
  eps_split_spec H.hr H.hεpos H.hε₀ H.hε₁ H.hlam0 H.hb H.hdiff H.hε

/-- The `WaveStepHyp` for the splitting `(ε₀*, ε₁*)`. -/
theorem hyp :
    WaveStepHyp a p pb s r σ η τ α lam ε (stepE0 ε ε₀) (stepE1 ε₀ ε₁) γ M0 Mω MΩ Par ω Ω P X
  :=
  let sp := H.split_spec
  { ha := H.ha
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
    mel := H.mel
    hP := H.hP
    hper := H.hper
    hreal := H.hreal
    hε₀ := sp.1
    hε₁ := sp.2.1
    hb := sp.2.2.2.1
    hdiff := sp.2.2.2.2
    hε := sp.2.2.1
    small := H.small }

end StepHypSrc

/-- **One KAM step, non-modified case** (`bpW:w5:step`), the blueprint's clauses (i)-(v) in terms of
`ε` (`λ`-norms as conjunctions of a sup and a Lipschitz bound; (iv) is conditional on
`HomMelnikov`). Clause (i) includes: `Φ` real on real points, `DΦ(w)` maps `𝒫^{p_+} = range ι`
onto itself, and the weak conjugacy of `bpW:w5:new-ham` (iii) in field form; clause (ii) includes
`P_+` real at the real points of `D_+`. The objects are those of `H.hyp`. -/
theorem stepTheorem (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    -- (i)
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      StepPhase.toK (H.hyp.core.Phi ξ w) ∈ kamDomain (s - 4 * σ) (2 * η * r)) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      stepNfun H.hG H.hyp.core.hK0 (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.hyp.core.Phi ξ
        w)) +
          P ξ (StepPhase.toK (H.hyp.core.Phi ξ w)) =
        stepNfun H.hG H.hyp.core.hKp (Ω := H.hyp.core.OmegaPlus ξ) (H.hyp.core.omegaPlus_bound hξ)
          (H.hyp.core.omegaPlus ξ)
          (StepPhase.toK w) + H.hyp.core.Pplus ξ w + H.hyp.core.a0 ξ) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W : StepPhase r,
      ((homDN H.hG H.hyp.core.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK (H.hyp.core.Phi ξ w)))).comp stepToHom).comp (stepToKCLM r)
          (fderiv ℂ (H.hyp.core.Phi ξ) w W) +
        stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r
          (stepEmbedCLM a p pb H.hpb r (stepXPS (X ξ) r (H.hyp.core.Phi ξ w))) (fderiv ℂ
            (H.hyp.core.Phi ξ)
            w W) =
      ((homDN H.hG H.hyp.core.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK w))).comp stepToHom).comp (stepToKCLM r) W +
        stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r
          (stepEmbedCLM a p pb H.hpb r
            (stepFieldS H.ha H.hp H.hpb (homNhatTaylor_gen (H.hyp.core.R ξ)) r w)) W +
        stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r
          (stepEmbedCLM a p pb H.hpb r (H.hyp.core.Xplus ξ w)) W) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W W' : StepPhase r,
      stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r (fderiv ℂ (H.hyp.core.Phi ξ) w W)
          (fderiv ℂ (H.hyp.core.Phi ξ) w W') =
        stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r W W') ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ k : Fin 2,
      H.hyp.core.Phi ξ (w + stepTauS r k) = H.hyp.core.Phi ξ w + stepTauS r k) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      StepReal (StepPhase.toK (H.hyp.core.Phi ξ w))) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      (∀ W' : StepPhase r, ∃ W'' : StepPhase r,
        fderiv ℂ (H.hyp.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
          stepEmbedCLM a p pb H.hpb r W'') ∧
      (∀ W'' : StepPhase r, ∃ W' : StepPhase r,
        fderiv ℂ (H.hyp.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
          stepEmbedCLM a p pb H.hpb r W'')) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W' W'' : StepPhase r,
      fderiv ℂ (H.hyp.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'' →
      stepSymp (q := p - 1) (q' := pb) H.ha H.hyp.core.hqq1
          (stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ)
              (StepPhase.toK (H.hyp.core.Phi ξ w)) +
            kamHomEmbed a (p - 1) pb H.hyp.core.hpm (X ξ (StepPhase.toK (H.hyp.core.Phi ξ w))))
          (StepPhase.toK W'') =
        stepSymp (q := p - 1) (q' := pb) H.ha H.hyp.core.hqq1
          (stepXN (a := a) (p := p) (H.hyp.core.omegaPlus_bound hξ) (H.hyp.core.omegaPlus ξ)
              (StepPhase.toK w) +
            kamHomEmbed a (p - 1) pb H.hyp.core.hpm (StepPhase.toK (H.hyp.core.Xplus ξ w)))
          (StepPhase.toK W')) ∧
    -- (ii)
    (∀ ξ ∈ Par, IsSmoothing (p := p) H.ha H.hyp.core.pb_pos (kamDomain (s - 5 * σ) (η * r))
      (fun w : KamPhase => H.hyp.core.Pplus ξ (StepPhase.ofK (r := r) w))
      (fun w : KamPhase => StepPhase.toK (H.hyp.core.Xplus ξ (StepPhase.ofK (r := r) w)))) ∧
    (∀ ξ ∈ Par, ∀ i : Fin 2, ∀ w ∈ kamDomain (s - 5 * σ) (η * r),
      H.hyp.core.Pplus ξ (StepPhase.ofK (r := r) (w + stepTau i)) = H.hyp.core.Pplus ξ
        (StepPhase.ofK (r :=
        r) w)) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      (H.hyp.core.Pplus ξ w).im = 0) ∧
    FamBound Par (kamDomain (s - 5 * σ) (η * r)) (η * r) lam
      (stepC2 τ * (ε ^ 2 / (α * σ ^ stepExpT τ * η ^ 2) + η * ε))
      (fun ξ w => StepPhase.toK (H.hyp.core.Xplus ξ (StepPhase.ofK (r := r) w))) ∧
    -- (iii)
    (∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ b₀ + lam * b₁ ≤ 6 * Real.pi * ε ∧
      (∀ ξ ∈ Par, ‖H.hyp.core.omegaPlus ξ - ω ξ‖ ≤ b₀) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par,
        ‖(H.hyp.core.omegaPlus ξ - ω ξ) - (H.hyp.core.omegaPlus ζ - ω ζ)‖ ≤ b₁ * ‖ξ - ζ‖) ∧
    (∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + lam * c₁ ≤ 3 * ε ∧
      (∀ ξ ∈ Par, ∀ j : ℕ+,
        ((j : ℝ) + 2) ^ (pb - p) * |H.hyp.core.OmegaPlus ξ j - Ω ξ j| ≤ c₀) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
        |(H.hyp.core.OmegaPlus ξ j - Ω ξ j) - (H.hyp.core.OmegaPlus ζ j - Ω ζ j)| ≤
          c₁ * ‖ξ - ζ‖) ∧
    (0 < lam → HomFreqHyp Par H.hyp.core.omegaPlus H.hyp.core.OmegaPlus (M0 + 3 * ε) (Mω + 6 *
      Real.pi * ε
      / lam)
      (MΩ + 3 * ε / lam)) ∧
    -- (iv)
    (HomMelnikov τ α Par ω Ω → ∀ K α' : ℝ, 1 ≤ K → 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α'
      →
      ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (l : ℕ+ →₀ ℤ), (k, l) ∈ homZ → Fourier.modeSize k ≤ K →
        α' * (homJap l : ℝ) / waveA τ k ≤
          |homPairZ k (H.hyp.core.omegaPlus ξ) + homPairL l (H.hyp.core.OmegaPlus ξ)|) ∧
    -- (v)
    (∃ A₀ A₁ B₀ B₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      A₀ + lam * A₁ ≤ 2 * stepMF (stepCF τ) (stepExpT τ) α σ ε ∧
      B₀ + lam * B₁ ≤ 16 * stepMF (stepCF τ) (stepExpT τ) α σ ε / σ ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
        ‖H.hyp.core.Phi ξ w - w‖ ≤ A₀ ∧
        ‖(H.hyp.core.Phi ξ w - w) - (H.hyp.core.Phi ζ w - w)‖ ≤ A₁ * ‖ξ - ζ‖ ∧
        ‖fderiv ℂ (H.hyp.core.Phi ξ) w - ContinuousLinearMap.id ℂ _‖ ≤ B₀ ∧
        ‖fderiv ℂ (H.hyp.core.Phi ξ) w - fderiv ℂ (H.hyp.core.Phi ζ) w‖ ≤ B₁ * ‖ξ - ζ‖) := by
  have h := stepTheorem_of_eps0_pos H.hyp
  have hre := stepTheorem_reality_of_eps0_pos H.hyp
  have hon : ∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), _ :=
    fun ξ hξ w hw => stepTheorem_dPhi_smooth_onto_of_eps0_pos H.hyp hξ hw
  have hwc : ∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), _ :=
    fun ξ hξ w hw => (stepTheorem_weakConj_field_of_eps0_pos H.hyp hξ hw).2
  unfold WaveStepHyp.Conclusion at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := h
  obtain ⟨he0, he1, hsum, -, -⟩ := H.split_spec
  have hM0 := H.hyp.M₀_pos.le
  have hM1 := H.hyp.M₁_nonneg
  have hσ := H.hσ
  have hlam := H.hlam0
  have hpi := Real.pi_pos
  refine ⟨c1, c2, c3, c4, c5, hre.1, hon, hwc, c6, c7, hre.2, c8, ?_, ?_, c11, c12, ?_⟩
  · refine ⟨6 * Real.pi * (stepE0 ε ε₀), 6 * Real.pi * (stepE1 ε₀ ε₁), by positivity, by
    positivity, by nlinarith,
      fun ξ hξ => (c9 ξ hξ).1, fun ξ hξ ζ hζ => (c10 ξ hξ ζ hζ).1⟩
  · refine ⟨3 * (stepE0 ε ε₀), 3 * (stepE1 ε₀ ε₁), by positivity, by positivity, by nlinarith,
      fun ξ hξ j => (c9 ξ hξ).2 j, fun ξ hξ ζ hζ j => (c10 ξ hξ ζ hζ).2 j⟩
  · refine ⟨stepM₀ τ σ α (stepE0 ε ε₀), 2 * (stepM₁ τ σ α (stepE0 ε ε₀) (stepE1 ε₀ ε₁) Mω MΩ), 8 *
    stepM₀ τ σ α (stepE0 ε ε₀) / σ, 16 * (stepM₁ τ σ α (stepE0 ε ε₀) (stepE1 ε₀ ε₁) Mω MΩ) / σ,
      hM0, by positivity, by positivity,
      by positivity, by nlinarith, ?_, fun ξ hξ ζ hζ w hw => ?_⟩
    · have e : 8 * stepM₀ τ σ α (stepE0 ε ε₀) / σ + lam * (16 * (stepM₁ τ σ α (stepE0 ε ε₀) (stepE1
      ε₀ ε₁) Mω MΩ) / σ) =
          (8 * stepM₀ τ σ α (stepE0 ε ε₀) + 16 * lam * (stepM₁ τ σ α (stepE0 ε ε₀) (stepE1 ε₀ ε₁)
            Mω MΩ)) / σ := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (by nlinarith [c13]) hσ.le
    · obtain ⟨d1, d2, d3, d4⟩ := c14 ξ hξ ζ hζ w hw
      exact ⟨d1, d2.trans_eq (by ring), d3, d4.trans_eq (by ring)⟩

namespace StepHypModSrc

variable (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
include H

theorem split_spec : 0 < (stepE0 ε ε₀) ∧ 0 ≤ (stepE1 ε₀ ε₁) ∧ (stepE0 ε ε₀) + lam * (stepE1 ε₀ ε₁)
  ≤ ε ∧
    (∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ (stepE0 ε ε₀)) ∧
    (∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r,
      kamNorm r (X ξ z - X ζ z) ≤ (stepE1 ε₀ ε₁) * ‖ξ - ζ‖) :=
  eps_split_spec H.hr H.hεpos H.hε₀ H.hε₁ H.hlam0 H.hb H.hdiff H.hε

/-- The `StepHypMod` for the splitting `(ε₀*, ε₁*)`. -/
theorem hyp : StepHypMod a p pb s r σ η τ α β lam ε (stepE0 ε ε₀) (stepE1 ε₀ ε₁) γ M0 Mω MΩ Par ω Ω
  P X :=
  let sp := H.split_spec
  { ha := H.ha
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
    hβ0 := H.hβ0
    h2β := H.h2β
    mel := H.mel
    hP := H.hP
    hper := H.hper
    hreal := H.hreal
    hε₀ := sp.1
    hε₁ := sp.2.1
    hb := sp.2.2.2.1
    hdiff := sp.2.2.2.2
    hε := sp.2.2.1
    small := H.small }

end StepHypModSrc

/-- **One KAM step, modified case** (`bpW:w5:step`), the blueprint's clauses (i)-(v) in terms of
`ε` (`λ`-norms as conjunctions of a sup and a Lipschitz bound; (iv) is conditional on
`HomMelnikov`). Clause (i) includes: `Φ` real on real points, `DΦ(w)` maps `𝒫^{p_+} = range ι`
onto itself, and the weak conjugacy of `bpW:w5:new-ham` (iii) in field form; clause (ii) includes
`P_+` real at the real points of `D_+`. The objects are those of `H.hyp`. -/
theorem stepTheoremMod (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    -- (i)
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      StepPhase.toK (H.hyp.core.Phi ξ w) ∈ kamDomain (s - 4 * σ) (2 * η * r)) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      stepNfun H.hG H.hyp.core.hK0 (homOmega_le H.freq hξ) (ω ξ) (StepPhase.toK (H.hyp.core.Phi ξ
        w)) +
          P ξ (StepPhase.toK (H.hyp.core.Phi ξ w)) =
        stepNfun H.hG H.hyp.core.hKp (Ω := H.hyp.core.OmegaPlus ξ) (H.hyp.core.omegaPlus_bound hξ)
          (H.hyp.core.omegaPlus ξ)
          (StepPhase.toK w) + H.hyp.core.Pplus ξ w + H.hyp.core.a0 ξ) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W : StepPhase r,
      ((homDN H.hG H.hyp.core.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK (H.hyp.core.Phi ξ w)))).comp stepToHom).comp (stepToKCLM r)
          (fderiv ℂ (H.hyp.core.Phi ξ) w W) +
        stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r
          (stepEmbedCLM a p pb H.hpb r (stepXPS (H.hyp.X' ξ) r (H.hyp.core.Phi ξ w))) (fderiv ℂ
            (H.hyp.core.Phi
            ξ) w W) =
      ((homDN H.hG H.hyp.core.hK0 (homOmega_le H.freq hξ) (ω ξ)
          (stepToHom (StepPhase.toK w))).comp stepToHom).comp (stepToKCLM r) W +
        stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r
          (stepEmbedCLM a p pb H.hpb r
            (stepFieldS H.ha H.hp H.hpb (homNhatTaylor_gen (H.hyp.core.R ξ)) r w)) W +
        stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r
          (stepEmbedCLM a p pb H.hpb r (H.hyp.core.Xplus ξ w)) W) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W W' : StepPhase r,
      stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r (fderiv ℂ (H.hyp.core.Phi ξ) w W)
          (fderiv ℂ (H.hyp.core.Phi ξ) w W') =
        stepSympCLM (q := p) (q' := p) H.ha H.hyp.core.two_p r W W') ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ k : Fin 2,
      H.hyp.core.Phi ξ (w + stepTauS r k) = H.hyp.core.Phi ξ w + stepTauS r k) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      StepReal (StepPhase.toK (H.hyp.core.Phi ξ w))) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      (∀ W' : StepPhase r, ∃ W'' : StepPhase r,
        fderiv ℂ (H.hyp.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
          stepEmbedCLM a p pb H.hpb r W'') ∧
      (∀ W'' : StepPhase r, ∃ W' : StepPhase r,
        fderiv ℂ (H.hyp.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
          stepEmbedCLM a p pb H.hpb r W'')) ∧
    (∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ W' W'' : StepPhase r,
      fderiv ℂ (H.hyp.core.Phi ξ) w (stepEmbedCLM a p pb H.hpb r W') =
        stepEmbedCLM a p pb H.hpb r W'' →
      stepSymp (q := p - 1) (q' := pb) H.ha H.hyp.core.hqq1
          (stepXN (a := a) (p := p) (homOmega_le H.freq hξ) (ω ξ)
              (StepPhase.toK (H.hyp.core.Phi ξ w)) +
            kamHomEmbed a (p - 1) pb H.hyp.core.hpm
              (H.hyp.X' ξ (StepPhase.toK (H.hyp.core.Phi ξ w))))
          (StepPhase.toK W'') =
        stepSymp (q := p - 1) (q' := pb) H.ha H.hyp.core.hqq1
          (stepXN (a := a) (p := p) (H.hyp.core.omegaPlus_bound hξ) (H.hyp.core.omegaPlus ξ)
              (StepPhase.toK w) +
            kamHomEmbed a (p - 1) pb H.hyp.core.hpm (StepPhase.toK (H.hyp.core.Xplus ξ w)))
          (StepPhase.toK W')) ∧
    -- (ii)
    (∀ ξ ∈ Par, IsSmoothing (p := p) H.ha H.hyp.core.pb_pos (kamDomain (s - 5 * σ) (η * r))
      (fun w : KamPhase => H.hyp.core.Pplus ξ (StepPhase.ofK (r := r) w))
      (fun w : KamPhase => StepPhase.toK (H.hyp.core.Xplus ξ (StepPhase.ofK (r := r) w)))) ∧
    (∀ ξ ∈ Par, ∀ i : Fin 2, ∀ w ∈ kamDomain (s - 5 * σ) (η * r),
      H.hyp.core.Pplus ξ (StepPhase.ofK (r := r) (w + stepTau i)) = H.hyp.core.Pplus ξ
        (StepPhase.ofK (r :=
        r) w)) ∧
    (∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      (H.hyp.core.Pplus ξ w).im = 0) ∧
    FamBound Par (kamDomain (s - 5 * σ) (η * r)) (η * r) lam
      (stepC2n τ * (ε ^ 2 / (α * σ ^ stepTn τ * η ^ 2) + η * ε))
      (fun ξ w => StepPhase.toK (H.hyp.core.Xplus ξ (StepPhase.ofK (r := r) w))) ∧
    -- (iii)
    (∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ b₀ + lam * b₁ ≤ 6 * Real.pi * ε ∧
      (∀ ξ ∈ Par, ‖H.hyp.core.omegaPlus ξ - ω ξ‖ ≤ b₀) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par,
        ‖(H.hyp.core.omegaPlus ξ - ω ξ) - (H.hyp.core.omegaPlus ζ - ω ζ)‖ ≤ b₁ * ‖ξ - ζ‖) ∧
    (∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + lam * c₁ ≤ 3 * ε ∧
      (∀ ξ ∈ Par, ∀ j : ℕ+,
        ((j : ℝ) + 2) ^ (pb - p) * |H.hyp.core.OmegaPlus ξ j - Ω ξ j| ≤ c₀) ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
        |(H.hyp.core.OmegaPlus ξ j - Ω ξ j) - (H.hyp.core.OmegaPlus ζ j - Ω ζ j)| ≤
          c₁ * ‖ξ - ζ‖) ∧
    (0 < lam → HomFreqHyp Par H.hyp.core.omegaPlus H.hyp.core.OmegaPlus (M0 + 3 * ε) (Mω + 6 *
      Real.pi * ε
      / lam)
      (MΩ + 3 * ε / lam)) ∧
    -- (iv)
    (HomMelnikov τ α Par ω Ω → ∀ K α' : ℝ, 1 ≤ K → 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α'
      →
      ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (l : ℕ+ →₀ ℤ), (k, l) ∈ homZ → Fourier.modeSize k ≤ K →
        α' * (homJap l : ℝ) / waveA τ k ≤
          |homPairZ k (H.hyp.core.omegaPlus ξ) + homPairL l (H.hyp.core.OmegaPlus ξ)|) ∧
    -- (v)
    (∃ A₀ A₁ B₀ B₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      A₀ + lam * A₁ ≤ 2 * stepMF (stepCFn τ) (stepTn τ) α σ ε ∧
      B₀ + lam * B₁ ≤ 16 * stepMF (stepCFn τ) (stepTn τ) α σ ε / σ ∧
      ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
        ‖H.hyp.core.Phi ξ w - w‖ ≤ A₀ ∧
        ‖(H.hyp.core.Phi ξ w - w) - (H.hyp.core.Phi ζ w - w)‖ ≤ A₁ * ‖ξ - ζ‖ ∧
        ‖fderiv ℂ (H.hyp.core.Phi ξ) w - ContinuousLinearMap.id ℂ _‖ ≤ B₀ ∧
        ‖fderiv ℂ (H.hyp.core.Phi ξ) w - fderiv ℂ (H.hyp.core.Phi ζ) w‖ ≤ B₁ * ‖ξ - ζ‖) := by
  have h := stepTheoremMod_of_eps0_pos H.hyp
  have hre := stepTheoremMod_reality_of_eps0_pos H.hyp
  have hon : ∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), _ :=
    fun ξ hξ w hw => stepTheoremMod_dPhi_smooth_onto_of_eps0_pos H.hyp hξ hw
  have hwc : ∀ ξ (hξ : ξ ∈ Par), ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), _ :=
    fun ξ hξ w hw => (stepTheoremMod_weakConj_field_of_eps0_pos H.hyp hξ hw).2
  unfold StepHypMod.Conclusion at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := h
  obtain ⟨he0, he1, hsum, -, -⟩ := H.split_spec
  have hM0 := H.hyp.M₀_pos.le
  have hM1 := H.hyp.M₁_nonneg
  have hσ := H.hσ
  have hlam := H.hlam0
  have hpi := Real.pi_pos
  refine ⟨c1, c2, c3, c4, c5, hre.1, hon, hwc, c6, c7, hre.2, c8, ?_, ?_, c11, c12, ?_⟩
  · refine ⟨6 * Real.pi * (stepE0 ε ε₀), 6 * Real.pi * (stepE1 ε₀ ε₁), by positivity, by
    positivity, by nlinarith,
      fun ξ hξ => (c9 ξ hξ).1, fun ξ hξ ζ hζ => (c10 ξ hξ ζ hζ).1⟩
  · refine ⟨3 * (stepE0 ε ε₀), 3 * (stepE1 ε₀ ε₁), by positivity, by positivity, by nlinarith,
      fun ξ hξ j => (c9 ξ hξ).2 j, fun ξ hξ ζ hζ j => (c10 ξ hξ ζ hζ).2 j⟩
  · refine ⟨stepM₀ τ σ α (stepE0 ε ε₀), 2 * (stepM₁n τ σ α (stepE0 ε ε₀) (stepE1 ε₀ ε₁) Mω MΩ), 8 *
    stepM₀ τ σ α (stepE0 ε ε₀) / σ, 16 * (stepM₁n τ σ α (stepE0 ε ε₀) (stepE1 ε₀ ε₁) Mω MΩ) / σ,
      hM0, by positivity, by positivity,
      by positivity, by nlinarith, ?_, fun ξ hξ ζ hζ w hw => ?_⟩
    · have e : 8 * stepM₀ τ σ α (stepE0 ε ε₀) / σ + lam * (16 * (stepM₁n τ σ α (stepE0 ε ε₀)
      (stepE1 ε₀ ε₁) Mω MΩ) / σ) =
          (8 * stepM₀ τ σ α (stepE0 ε ε₀) + 16 * lam * (stepM₁n τ σ α (stepE0 ε ε₀) (stepE1 ε₀ ε₁)
            Mω MΩ)) / σ := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (by nlinarith [c13]) hσ.le
    · obtain ⟨d1, d2, d3, d4⟩ := c14 ξ hξ ζ hζ w hw
      exact ⟨d1, d2.trans_eq (by ring), d3, d4.trans_eq (by ring)⟩

end KAM.Wave
