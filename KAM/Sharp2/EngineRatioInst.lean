/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.EngineRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `converge_checked` is the instance `a = 2`, `ȳ = 1/2` of `converge_ratio`

The ratio schedule at `a = 2` is B5's schedule (`bite0R 2 = bite0`, `biteSR 2 = biteS`,
`stripSR 2 = stripS`, `xSeqR 2 (κ + 1) = xSeq κ`, `1/(1 - 1/2) = 2`), so
`StageScheme.converge_ratio` at `a = 2`, `ȳ = 1/2` has exactly the hypotheses and conclusion of
`StageScheme.converge_checked`. The theorem `converge_checked_of_ratio` below derives the latter
from the former; the original proof is kept (it is merged and used downstream).
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Sharp2

theorem bite0R_two (ρ ρinf : ℝ) : bite0R 2 ρ ρinf = bite0 ρ ρinf := by
  simp only [bite0R, bite0]
  congr 1
  ring

theorem biteSR_two (ρ ρinf : ℝ) (s : ℕ) : biteSR 2 ρ ρinf s = biteS ρ ρinf s := by
  simp only [biteSR, biteS, bite0R_two]

theorem stripSR_two (ρ ρinf : ℝ) (s : ℕ) : stripSR 2 ρ ρinf s = stripS ρ ρinf s := by
  simp only [stripSR, stripS, bite0R_two]
  norm_num
  ring

theorem xSeqR_two (κ : ℝ) (Q : ℕ → ℝ) (X0 : ℝ) (s : ℕ) :
    xSeqR 2 (κ + 1) Q X0 s = xSeq κ Q X0 s := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [xSeqR, xSeq, ih]

/-- `converge_checked` from `converge_ratio` at `a = 2`, `ȳ = 1/2`. -/
theorem StageScheme.converge_checked_of_ratio {n k : ℕ} {α : Type*} {S : StageScheme n k α}
    {κ γ ρ ρinf β₀ μ₀ : ℝ} {C : ℝ → StageConsts k} {σ m₀ : Fin k → ℝ} {x₀ : α} (kpre : ℕ)
    (Ctail : StageConsts k)
    (hS : S.IsNewton κ γ (min 1 ((ρ - ρinf) / 6)) C σ) (hγ : 0 < γ) (hρinf : 0 < ρinf)
    (hρ : ρinf < ρ) (hx₀ : S.Adm ρ β₀ μ₀ m₀ x₀)
    (htail : ∀ δ, 0 < δ → δ ≤ min 1 ((ρ - ρinf) / 6) / 2 ^ kpre →
      (C δ).Q ≤ Ctail.Q ∧ (∀ X, Ctail.cond X → (C δ).cond X) ∧ (C δ).CDK ≤ Ctail.CDK ∧
        (C δ).Cp ≤ Ctail.Cp ∧ ∀ i, (C δ).rate i * (C δ).wt i ≤ Ctail.rate i * Ctail.wt i)
    (hJ1 : ∀ s < kpre, (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).cond
      (xSeq κ (fun s => (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).Q)
        (μ₀ / (γ * min 1 ((ρ - ρinf) / 6) ^ (κ + 1))) s))
    (hJ2 : 2 ^ (κ + 1) * Ctail.Q *
      xSeq κ (fun s => (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).Q)
        (μ₀ / (γ * min 1 ((ρ - ρinf) / 6) ^ (κ + 1))) kpre ≤ 1 / 2)
    (hJ3 : ∀ i, m₀ i + (∑ s ∈ Finset.range kpre,
        (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).rate i * (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).wt i *
        xSeq κ (fun s => (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).Q)
          (μ₀ / (γ * min 1 ((ρ - ρinf) / 6) ^ (κ + 1))) s) +
      2 * Ctail.rate i * Ctail.wt i *
        xSeq κ (fun s => (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).Q)
          (μ₀ / (γ * min 1 ((ρ - ρinf) / 6) ^ (κ + 1))) kpre ≤ σ i)
    (hnn : ∀ δ, 0 < δ → δ ≤ min 1 ((ρ - ρinf) / 6) →
      0 ≤ (C δ).Q ∧ 0 ≤ (C δ).CDK ∧ ∀ i, 0 ≤ (C δ).rate i * (C δ).wt i)
    (hcondT : ∀ X, 0 ≤ X → X ≤ xSeq κ (fun s => (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).Q)
      (μ₀ / (γ * min 1 ((ρ - ρinf) / 6) ^ (κ + 1))) kpre → Ctail.cond X)
    (hball : stageBall κ γ ρ ρinf μ₀ C kpre Ctail < β₀) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (pinf : ℝ),
      DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧ IsPrimaryOnStrip Kinf ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ s, ∃ r β μ m, S.Adm r β μ m (Nat.rec x₀ (fun j x =>
        S.step (ρ - 6 * min 1 ((ρ - ρinf) / 6) *
        (1 - (2 : ℝ)⁻¹ ^ j)) (min 1 ((ρ - ρinf) / 6) / 2 ^ j) x) s) ∧ ρinf < r ∧
        (∀ i, m i ≤ σ i)) ∧
      TendstoUniformlyOn (fun s => S.tor (Nat.rec x₀ (fun j x =>
        S.step (ρ - 6 * min 1 ((ρ - ρinf) / 6) *
        (1 - (2 : ℝ)⁻¹ ^ j)) (min 1 ((ρ - ρinf) / 6) / 2 ^ j) x) s)) Kinf atTop
        (complexStrip n ρinf) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - S.tor x₀ θ‖ ≤
        stageBall κ γ ρ ρinf μ₀ C kpre Ctail) := by
  have e0 : ∀ s : ℕ, biteSR 2 ρ ρinf s = min 1 ((ρ - ρinf) / 6) / 2 ^ s := fun s => by
    rw [biteSR_two]
  have e1 : bite0R 2 ρ ρinf = min 1 ((ρ - ρinf) / 6) := bite0R_two ρ ρinf
  have e2 : ∀ j : ℕ, stripSR 2 ρ ρinf j =
      ρ - 6 * min 1 ((ρ - ρinf) / 6) * (1 - (2 : ℝ)⁻¹ ^ j) := fun j => by
    rw [stripSR_two]
  have e4 : ∀ (x : ℝ), x / (1 - (1 / 2 : ℝ)) = 2 * x := fun x => by norm_num; ring
  have eb : stageBallR 2 κ γ ρ ρinf μ₀ (1 / 2) C kpre Ctail =
      stageBall κ γ ρ ρinf μ₀ C kpre Ctail := by
    simp only [stageBallR, stageBall, xSeqR_two, e0, e1, e4]
    ring
  have hball' : stageBallR 2 κ γ ρ ρinf μ₀ (1 / 2) C kpre Ctail < β₀ := eb ▸ hball
  have := StageScheme.converge_ratio (S := S) (a := 2) (ybar := 1 / 2) (C := C) (σ := σ)
    (m₀ := m₀) (x₀ := x₀) kpre Ctail (by rw [e1]; exact hS) (by norm_num) (by norm_num)
    (by norm_num) hγ hρinf hρ hx₀
    (by simpa only [e0, e1] using htail)
    (fun s hs => by simp only [e0, e1, xSeqR_two]; exact hJ1 s hs)
    (by simp only [e0, e1, xSeqR_two]; exact hJ2)
    (fun i => by
      have := hJ3 i
      simp only [e0, e1, xSeqR_two, e4]
      linarith)
    (by simpa only [e1] using hnn)
    (fun X hX hXle => hcondT X hX (by simpa only [e0, e1, xSeqR_two] using hXle)) hball'
  rw [eb] at this
  simpa only [e2, e0] using this

end KAM.Sharp2

end
