/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.EngineRatioPar

/-!
# `converge_ratio` from `converge_ratio_par`

Replace the scheme by `S' = S` with `par := 0` and the constants by `Cp := 0`: the parameter clause
of `IsNewton` becomes `|0 - 0| ≤ 0 * μ`, so `S'` is Newton with the same data, the iterates and
admissibility are those of `S`, and `converge_ratio_par` for `S'` gives the conclusion of
`converge_ratio` (the parameter conclusions are discarded). The only extra hypothesis is
`0 ≤ κ + 1`, which `converge_ratio_par` needs for the tail comparison of `δ_s^{κ+1}`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Sharp2

/-- The scheme with the parameter forgotten. -/
def StageScheme.noPar {n k : ℕ} {α : Type*} (S : StageScheme n k α) : StageScheme n k α :=
  { S with par := fun _ => 0 }

/-- The constants with `Cp := 0`. -/
def StageConsts.noCp {k : ℕ} (c : StageConsts k) : StageConsts k := { c with Cp := 0 }

theorem StageScheme.IsNewton.noPar {n k : ℕ} {α : Type*} {S : StageScheme n k α}
    {κ γ δmax : ℝ} {C : ℝ → StageConsts k} {σ : Fin k → ℝ} (hS : S.IsNewton κ γ δmax C σ) :
    S.noPar.IsNewton κ γ δmax (fun δ => (C δ).noCp) σ where
  regular := fun h => hS.regular h
  step := fun h hδ hδm h3 hc hb hcap => by
    obtain ⟨h1, h2, -⟩ := hS.step h hδ hδm h3 hc hb hcap
    exact ⟨h1, h2, by simp [StageScheme.noPar, StageConsts.noCp]⟩

/-- `converge_ratio` from `converge_ratio_par` (with `0 ≤ κ + 1`). -/
theorem StageScheme.converge_ratio_of_par {n k : ℕ} {α : Type*} {S : StageScheme n k α}
    {κ γ ρ ρinf β₀ μ₀ a ybar : ℝ}
    {C : ℝ → StageConsts k} {σ m₀ : Fin k → ℝ} {x₀ : α} (kpre : ℕ) (Ctail : StageConsts k)
    (hS : S.IsNewton κ γ (bite0R a ρ ρinf) C σ) (ha : 1 < a) (hy0 : 0 < ybar)
    (hy1 : ybar < 1) (hγ : 0 < γ)
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hx₀ : S.Adm ρ β₀ μ₀ m₀ x₀)
    (htail : ∀ δ, 0 < δ → δ ≤ biteSR a ρ ρinf kpre →
      (C δ).Q ≤ Ctail.Q ∧ (∀ X, Ctail.cond X → (C δ).cond X) ∧ (C δ).CDK ≤ Ctail.CDK ∧
        (C δ).Cp ≤ Ctail.Cp ∧ ∀ i, (C δ).rate i * (C δ).wt i ≤ Ctail.rate i * Ctail.wt i)
    (hJ1 : ∀ s < kpre, (C (biteSR a ρ ρinf s)).cond
      (xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q)
        (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1))) s))
    (hJ2 : a ^ (κ + 1) * Ctail.Q *
      xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q)
        (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1))) kpre ≤ ybar)
    (hJ3 : ∀ i, m₀ i + (∑ s ∈ Finset.range kpre,
        (C (biteSR a ρ ρinf s)).rate i * (C (biteSR a ρ ρinf s)).wt i *
        xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q)
          (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1))) s) +
      Ctail.rate i * Ctail.wt i *
        xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q)
          (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1))) kpre / (1 - ybar) ≤ σ i)
    (hnn : ∀ δ, 0 < δ → δ ≤ bite0R a ρ ρinf →
      0 ≤ (C δ).Q ∧ 0 ≤ (C δ).CDK ∧ ∀ i, 0 ≤ (C δ).rate i * (C δ).wt i)
    (hcondT : ∀ X, 0 ≤ X → X ≤ xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q)
      (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1))) kpre → Ctail.cond X)
    (hκ : 0 ≤ κ + 1)
    (hball : stageBallR a κ γ ρ ρinf μ₀ ybar C kpre Ctail < β₀) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (pinf : ℝ),
      DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧ IsPrimaryOnStrip Kinf ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ s, ∃ r β μ m, S.Adm r β μ m (Nat.rec x₀ (fun j x =>
          S.step (stripSR a ρ ρinf j) (biteSR a ρ ρinf j) x) s) ∧
        ρinf < r ∧ (∀ i, m i ≤ σ i)) ∧
      TendstoUniformlyOn (fun s => S.tor (Nat.rec x₀ (fun j x =>
          S.step (stripSR a ρ ρinf j) (biteSR a ρ ρinf j) x) s))
        Kinf atTop (complexStrip n ρinf) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - S.tor x₀ θ‖ ≤
        stageBallR a κ γ ρ ρinf μ₀ ybar C kpre Ctail) := by
  have key := StageScheme.converge_ratio_par (S := S.noPar) (C := fun δ => (C δ).noCp)
    (σ := σ) (m₀ := m₀) (x₀ := x₀) (κ := κ) (γ := γ) (ρ := ρ) (ρinf := ρinf) (β₀ := β₀)
    (μ₀ := μ₀) (a := a) (ybar := ybar) kpre Ctail.noCp hS.noPar ha hy0 hy1 hγ hρinf hρ hx₀
    (fun δ hδ hδ' => by
      obtain ⟨q, c, d, -, r⟩ := htail δ hδ hδ'
      exact ⟨q, c, d, le_rfl, r⟩)
    hJ1 hJ2 hJ3 hnn hcondT hκ (fun δ _ _ => le_rfl) hball
  obtain ⟨K, p, h1, h2, h3, h4, h5, h6, -⟩ := key
  exact ⟨K, p, h1, h2, h3, h4, h5, h6⟩

end KAM.Sharp2

end
