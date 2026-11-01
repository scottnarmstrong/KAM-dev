/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepTheoremMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One KAM step: the source-facing theorems (blueprint-W `bpW:w5:step`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

The premise `ε₀ > 0` of the conditional helpers (`stepTheorem_of_eps0_pos`,
`stepTheoremMod_of_eps0_pos`) is not a blueprint premise. The hypotheses `StepHypSrc`,
`StepHypModSrc` assume only `ε₀ ≥ 0` and the blueprint's `ε > 0`. The theorems `stepTheorem`,
`stepTheoremMod` produce a positive splitting `(ε₀', ε₁')` with `ε₀' + λ ε₁' ≤ ε`, dominating the
field (`ε₀' = ε₀`, `ε₁' = ε₁` if `ε₀ > 0`; if `ε₀ = 0` then `X_P ≡ 0` on `D(s,r)` and
`ε₀' = ε/2`, `ε₁' = 0`), and the clauses of the helper hold for it; every constant in the
conclusion is that of the splitting.
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

/-- The splitting `(ε₀', ε₁')`. -/
theorem exists_eps_split {r lam ε ε₀ ε₁ : ℝ} {Par : Set (Fin 2 → ℝ)} {s : ℝ}
    {X : (Fin 2 → ℝ) → KamPhase → KamPhase} (hr : 0 < r) (hε : 0 < ε) (hε₀ : 0 ≤ ε₀)
    (hε₁ : 0 ≤ ε₁) (hlam : 0 ≤ lam)
    (hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀)
    (hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r,
      kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖) (hsum : ε₀ + lam * ε₁ ≤ ε) :
    ∃ ε₀' ε₁' : ℝ, 0 < ε₀' ∧ 0 ≤ ε₁' ∧ ε₀' + lam * ε₁' ≤ ε ∧
      (∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀') ∧
      (∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r,
        kamNorm r (X ξ z - X ζ z) ≤ ε₁' * ‖ξ - ζ‖) := by
  rcases hε₀.lt_or_eq with h | h
  · exact ⟨ε₀, ε₁, h, hε₁, hsum, hb, hdiff⟩
  · refine ⟨ε / 2, 0, by positivity, le_rfl, by linarith, fun ξ hξ z hz => ?_,
      fun ξ hξ ζ hζ z hz => ?_⟩
    · have := hb ξ hξ z hz
      rw [← h] at this
      linarith
    · have h1 := hb ξ hξ z hz
      have h2 := hb ζ hζ z hz
      rw [← h] at h1 h2
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

/-- **One KAM step** (`bpW:w5:step`), non-modified case, from the blueprint premises. There is a
splitting `ε₀' + λ ε₁' ≤ ε` of the `λ`-norm bound, and a conditional-helper hypothesis for it,
whose conclusion (`StepHyp.Conclusion`) holds; the objects `Φ`, `P_+`, `X_+`, `ω_+`, `Ω_+`, `â₀`
are those of that hypothesis. -/
theorem stepTheorem (H : StepHypSrc a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)] :
    ∃ ε₀' ε₁' : ℝ, ∃ H' : StepHyp a p pb s r σ η τ α lam ε ε₀' ε₁' γ M0 Mω MΩ Par ω Ω P X,
      H'.Conclusion := by
  obtain ⟨e0, e1, h0, h1, hs2, hb2, hd2⟩ := exists_eps_split H.hr H.hεpos H.hε₀ H.hε₁ H.hlam0
    H.hb H.hdiff H.hε
  exact ⟨e0, e1,
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
      hε₀ := h0
      hε₁ := h1
      hb := hb2
      hdiff := hd2
      hε := hs2
      small := H.small },
    stepTheorem_of_eps0_pos _⟩

/-- **One KAM step, modified case** (`bpW:w5:step`), from the blueprint premises. `hH` is the
hypothesis of clause (iv) ("whenever the same holds with `α` for `ω, Ω`"). -/
theorem stepTheoremMod
    (H : StepHypModSrc a p pb s r σ η τ α β lam ε ε₀ ε₁ γ M0 Mω MΩ Par ω Ω P X)
    (hH : HomMelnikov τ α Par ω Ω) [Fact (0 < r)] :
    ∃ ε₀' ε₁' : ℝ, ∃ H' : StepHypMod a p pb s r σ η τ α β lam ε ε₀' ε₁' γ M0 Mω MΩ Par ω Ω P X,
      H'.Conclusion := by
  obtain ⟨e0, e1, h0, h1, hs2, hb2, hd2⟩ := exists_eps_split H.hr H.hεpos H.hε₀ H.hε₁ H.hlam0
    H.hb H.hdiff H.hε
  exact ⟨e0, e1,
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
      hε₀ := h0
      hε₁ := h1
      hb := hb2
      hdiff := hd2
      hε := hs2
      small := H.small },
    stepTheoremMod_of_eps0_pos _ hH⟩

end KAM.Wave
