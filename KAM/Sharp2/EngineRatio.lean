/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Engine
public import KAM.Sharp2.EngineRatioArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The engine with schedule ratio `a` and decay bound `ȳ` (`bp:p2s2:engine`)

The signatures of `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt` (B5 delta):
`bite0R`, `biteSR`, `stripSR`, `xSeqR` (in `EngineRatioArith`), `stageBallR` and
`StageScheme.converge_ratio`, B5's proof with `2 → a`, `1/2 → ȳ`. The Cauchy estimate on the
derivative increments uses the margin `3δ_s/(a-1)` (`r_{s+1} - ρ∞ ≥ 3δ_s/(a-1)`), which equals
B5's `3δ_s` at `a = 2`. The case `a = 2`, `ȳ = 1/2` is `converge_checked`
(`KAM/Sharp2/EngineRatioInst.lean`).
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Sharp2

/-- `δ₀ = min {1, (ρ - ρ∞)(a - 1)/(3a)}`. -/
abbrev bite0R (a ρ ρinf : ℝ) : ℝ := min 1 ((ρ - ρinf) * (a - 1) / (3 * a))
/-- `δ_s = δ₀ a^{-s}`. -/
abbrev biteSR (a ρ ρinf : ℝ) (s : ℕ) : ℝ := bite0R a ρ ρinf / a ^ s
/-- `r_s = ρ - 3δ₀(1 - a^{-s})/(1 - a^{-1})`, so `r_s - 3δ_s = r_{s+1}`. -/
abbrev stripSR (a ρ ρinf : ℝ) (s : ℕ) : ℝ :=
  ρ - 3 * bite0R a ρ ρinf * (1 - a⁻¹ ^ s) / (1 - a⁻¹)

/-- The iterates `x_{s+1} = Φ(r_s, δ_s; x_s)` of the ratio schedule. -/
def stageIterR {n k : ℕ} {α : Type*} (S : StageScheme n k α) (a ρ ρinf : ℝ) (x₀ : α) :
    ℕ → α :=
  fun s => Nat.rec x₀ (fun j x => S.step (stripSR a ρ ρinf j) (biteSR a ρ ρinf j) x) s

section Schedule

variable {a ρ ρinf : ℝ}

theorem bite0R_pos (ha : 1 < a) (hρ : ρinf < ρ) : 0 < bite0R a ρ ρinf := by
  have : 0 < a - 1 := by linarith
  exact lt_min one_pos (by have : 0 < 3 * a := by linarith
                           positivity)

theorem biteSR_pos (ha : 1 < a) (hρ : ρinf < ρ) (s : ℕ) : 0 < biteSR a ρ ρinf s :=
  div_pos (bite0R_pos ha hρ) (by have : 0 < a := by linarith
                                 positivity)

theorem biteSR_le (ha : 1 < a) (hρ : ρinf < ρ) (s : ℕ) : biteSR a ρ ρinf s ≤ bite0R a ρ ρinf :=
  div_le_self (bite0R_pos ha hρ).le (one_le_pow₀ ha.le)

theorem three_bite0R_le (ha : 1 < a) :
    3 * bite0R a ρ ρinf * a / (a - 1) ≤ ρ - ρinf := by
  have h1 : bite0R a ρ ρinf ≤ (ρ - ρinf) * (a - 1) / (3 * a) := min_le_right _ _
  have h2 : 0 < a - 1 := by linarith
  have h3 : 0 < a := by linarith
  rw [div_le_iff₀ h2]
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

theorem stripSR_eq (ha : 1 < a) (s : ℕ) :
    stripSR a ρ ρinf s = ρ - 3 * bite0R a ρ ρinf * a / (a - 1) +
      3 * biteSR a ρ ρinf s * a / (a - 1) := by
  have h2 : a - 1 ≠ 0 := by linarith
  have h3 : a ≠ 0 := by linarith
  simp only [stripSR, biteSR, inv_pow]
  field_simp
  ring

theorem stripSR_gt (ha : 1 < a) (hρ : ρinf < ρ) (s : ℕ) : ρinf < stripSR a ρ ρinf s := by
  rw [stripSR_eq ha]
  have h1 := biteSR_pos ha hρ s
  have h2 := three_bite0R_le (ρ := ρ) (ρinf := ρinf) ha
  have h3 : 0 < a - 1 := by linarith
  have : 0 < 3 * biteSR a ρ ρinf s * a / (a - 1) := by
    have : 0 < a := by linarith
    positivity
  linarith

theorem stripSR_succ (ha : 1 < a) (s : ℕ) :
    stripSR a ρ ρinf s - 3 * biteSR a ρ ρinf s = stripSR a ρ ρinf (s + 1) := by
  rw [stripSR_eq ha, stripSR_eq ha]
  have h2 : a - 1 ≠ 0 := by linarith
  have h3 : a ≠ 0 := by linarith
  simp only [biteSR, pow_succ]
  field_simp
  ring

theorem stripSR_zero (ha : 1 < a) : stripSR a ρ ρinf 0 = ρ := by simp [stripSR]

end Schedule

/-- The ball sum with the tail factor `1/(1 - ȳ)`. -/
def stageBallR {k : ℕ} (a κ γ ρ ρinf μ₀ ybar : ℝ) (C : ℝ → StageConsts k) (kpre : ℕ)
    (Ctail : StageConsts k) : ℝ :=
  (∑ s ∈ Finset.range kpre, (C (biteSR a ρ ρinf s)).CDK * biteSR a ρ ρinf s *
      xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q)
        (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1))) s) +
    Ctail.CDK * biteSR a ρ ρinf kpre *
      xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q)
        (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1))) kpre / (1 - ybar)

section Converge

variable {n k : ℕ} {α : Type*}

/-- Blueprint `bp:p2s2:engine` with ratio `a > 1` and decay bound `ȳ ∈ (0,1)` (FH24 §3.3: `a`,
`κ`); for `a = 2`, `ȳ = 1/2` it is `StageScheme.converge_checked` (B5). Route B: exponent
`κ + 1`; route A uses B9's `SchemeA`. -/
theorem StageScheme.converge_ratio {n k : ℕ} {α : Type*} {S : StageScheme n k α}
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
  classical
  have ha0 : 0 < a := by linarith
  have hδ0 := bite0R_pos ha hρ
  have hΓ : (0 : ℝ) < γ * bite0R a ρ ρinf ^ (κ + 1) := mul_pos hγ (Real.rpow_pos_of_pos hδ0 _)
  have hX0 : 0 ≤ μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1)) := div_nonneg (hS.regular hx₀).1 hΓ.le
  have hbs : ∀ s, kpre ≤ s → biteSR a ρ ρinf s ≤ bite0R a ρ ρinf / a ^ kpre := fun s hs =>
    div_le_div_of_nonneg_left hδ0.le (by positivity) (pow_le_pow_right₀ ha.le hs)
  have hQ : ∀ s, 0 ≤ (C (biteSR a ρ ρinf s)).Q := fun s =>
    (hnn _ (biteSR_pos ha hρ s) (biteSR_le ha hρ s)).1
  have hQt : ∀ s, kpre ≤ s → (C (biteSR a ρ ρinf s)).Q ≤ Ctail.Q := fun s hs =>
    (htail _ (biteSR_pos ha hρ s) (hbs s hs)).1
  -- the normalised errors
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ, X = xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q)
      (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1))) := ⟨_, rfl⟩
  have hXnn : ∀ s, 0 ≤ X s := by
    rw [hXdef]; exact xSeqR_nonneg ha0 hQ hX0
  have hXd : ∀ s, kpre ≤ s → X s ≤ X kpre * ybar ^ (s - kpre) := by
    rw [hXdef]; exact xSeqR_tail ha0 hy0.le hy1.le hQ hX0 hQt hJ2
  have hXsucc : ∀ s, X (s + 1) = a ^ (κ + 1) * (C (biteSR a ρ ρinf s)).Q * X s ^ 2 := by
    intro s; rw [hXdef]; rfl
  have hX00 : X 0 = μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1)) := by rw [hXdef]; rfl
  -- the increments
  obtain ⟨aB, haB⟩ : ∃ aB : ℕ → ℝ, ∀ s, aB s = (C (biteSR a ρ ρinf s)).CDK * biteSR a ρ ρinf s :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨aC, haC⟩ : ∃ aC : Fin k → ℕ → ℝ, ∀ i s,
      aC i s = (C (biteSR a ρ ρinf s)).rate i * (C (biteSR a ρ ρinf s)).wt i := ⟨_, fun _ _ => rfl⟩
  have haB0 : ∀ t, 0 ≤ aB t := fun t => by
    rw [haB]
    exact mul_nonneg (hnn _ (biteSR_pos ha hρ t) (biteSR_le ha hρ t)).2.1
      (biteSR_pos ha hρ t).le
  have haC0 : ∀ i t, 0 ≤ aC i t := fun i t => by
    rw [haC]; exact (hnn _ (biteSR_pos ha hρ t) (biteSR_le ha hρ t)).2.2 i
  have hCDKt : 0 ≤ Ctail.CDK :=
    (hnn _ (biteSR_pos ha hρ kpre) (biteSR_le ha hρ kpre)).2.1.trans
      (htail _ (biteSR_pos ha hρ kpre) le_rfl).2.2.1
  have haBA : ∀ t, kpre ≤ t → aB t ≤ Ctail.CDK * biteSR a ρ ρinf kpre := fun t ht => by
    rw [haB]
    exact mul_le_mul (htail _ (biteSR_pos ha hρ t) (hbs t ht)).2.2.1 (hbs t ht)
      (biteSR_pos ha hρ t).le hCDKt
  have haCA : ∀ i t, kpre ≤ t → aC i t ≤ Ctail.rate i * Ctail.wt i := fun i t ht => by
    rw [haC]; exact (htail _ (biteSR_pos ha hρ t) (hbs t ht)).2.2.2.2 i
  -- the critical sums
  have hballLe : ∀ N, ∑ t ∈ Finset.range N, aB t * X t ≤
      stageBallR a κ γ ρ ρinf μ₀ ybar C kpre Ctail := by
    intro N
    have h1 := partial_sum_leR N hy0.le hy1 haB0 hXnn hXd haBA
    have e : ∑ t ∈ Finset.range kpre, aB t * X t = ∑ s ∈ Finset.range kpre,
        (C (biteSR a ρ ρinf s)).CDK * biteSR a ρ ρinf s * X s :=
      Finset.sum_congr rfl fun t _ => by rw [haB]
    have hb : stageBallR a κ γ ρ ρinf μ₀ ybar C kpre Ctail = ∑ s ∈ Finset.range kpre,
        (C (biteSR a ρ ρinf s)).CDK * biteSR a ρ ρinf s * X s +
        Ctail.CDK * biteSR a ρ ρinf kpre * X kpre / (1 - ybar) := by
      rw [hXdef]; rfl
    rw [e] at h1
    linarith
  have hballTot : ∀ N, ∑ t ∈ Finset.range N, aB t * X t < β₀ := fun N =>
    (hballLe N).trans_lt hball
  have hcapTot : ∀ i N, m₀ i + ∑ t ∈ Finset.range N, aC i t * X t ≤ σ i := by
    intro i N
    have h1 := partial_sum_leR N hy0.le hy1 (haC0 i) hXnn hXd (haCA i)
    have e : ∑ t ∈ Finset.range kpre, aC i t * X t = ∑ s ∈ Finset.range kpre,
        (C (biteSR a ρ ρinf s)).rate i * (C (biteSR a ρ ρinf s)).wt i * X s :=
      Finset.sum_congr rfl fun t _ => by rw [haC]
    have hj := hJ3 i
    rw [← hXdef] at hj
    rw [e] at h1
    linarith
  -- the explicit data of the admissible states
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℝ, ∀ s, β s = β₀ - ∑ t ∈ Finset.range s, aB t * X t :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ → Fin k → ℝ, ∀ s i, m s i = m₀ i + ∑ t ∈ Finset.range s, aC i t * X t :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℕ → ℝ, ∀ s, μ s = X s * (γ * biteSR a ρ ρinf s ^ (κ + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hΓs : ∀ s, 0 < γ * biteSR a ρ ρinf s ^ (κ + 1) := fun s =>
    mul_pos hγ (Real.rpow_pos_of_pos (biteSR_pos ha hρ s) _)
  have hμX : ∀ s, μ s / (γ * biteSR a ρ ρinf s ^ (κ + 1)) = X s := fun s => by
    rw [hμ]; exact mul_div_cancel_right₀ _ (hΓs s).ne'
  have hCDKμ : ∀ s, (C (biteSR a ρ ρinf s)).CDK * μ s / (γ * biteSR a ρ ρinf s ^ κ) =
      aB s * X s := by
    intro s
    have hδ := biteSR_pos ha hρ s
    have h1 : biteSR a ρ ρinf s ^ (κ + 1) = biteSR a ρ ρinf s ^ κ * biteSR a ρ ρinf s :=
      Real.rpow_add_one hδ.ne' κ
    have h2 : 0 < biteSR a ρ ρinf s ^ κ := Real.rpow_pos_of_pos hδ _
    rw [hμ, haB, h1]
    field_simp
  have hQμ : ∀ s, (C (biteSR a ρ ρinf s)).Q * μ s ^ 2 / (γ * biteSR a ρ ρinf s ^ (κ + 1)) =
      μ (s + 1) := by
    intro s
    have hδ := biteSR_pos ha hρ s
    have h1 : biteSR a ρ ρinf (s + 1) = biteSR a ρ ρinf s / a := by
      simp only [biteSR, pow_succ]; field_simp
    have h2 : (biteSR a ρ ρinf s / a) ^ (κ + 1) = biteSR a ρ ρinf s ^ (κ + 1) / a ^ (κ + 1) :=
      Real.div_rpow hδ.le (by linarith) _
    have h3 : 0 < biteSR a ρ ρinf s ^ (κ + 1) := Real.rpow_pos_of_pos hδ _
    have h4 : (0 : ℝ) < a ^ (κ + 1) := Real.rpow_pos_of_pos (by linarith) _
    rw [hμ, hμ, hXsucc, h1, h2]
    field_simp
  -- the step hypotheses
  have hcond : ∀ s, (C (biteSR a ρ ρinf s)).cond (μ s / (γ * biteSR a ρ ρinf s ^ (κ + 1))) := by
    intro s
    rw [hμX]
    by_cases hs : s < kpre
    · rw [hXdef]; exact hJ1 s hs
    · have hs' : kpre ≤ s := not_lt.mp hs
      refine (htail _ (biteSR_pos ha hρ s) (hbs s hs')).2.1 _ (hcondT _ (hXnn s) ?_)
      rw [← hXdef]
      exact (hXd s hs').trans
        (mul_le_of_le_one_right (hXnn kpre) (pow_le_one₀ hy0.le hy1.le))
  have hballc : ∀ s, (C (biteSR a ρ ρinf s)).CDK * μ s / (γ * biteSR a ρ ρinf s ^ κ) < β s := by
    intro s
    rw [hCDKμ, hβ]
    have := hballTot (s + 1)
    rw [Finset.sum_range_succ] at this
    linarith
  have hcap : ∀ s i, m s i + (C (biteSR a ρ ρinf s)).rate i * (C (biteSR a ρ ρinf s)).wt i *
      (μ s / (γ * biteSR a ρ ρinf s ^ (κ + 1))) ≤ σ i := by
    intro s i
    rw [hμX, hm]
    have := hcapTot i (s + 1)
    rw [Finset.sum_range_succ, haC] at this
    linarith
  -- the admissible states
  have hAdm : ∀ s, S.Adm (stripSR a ρ ρinf s) (β s) (μ s) (m s) (stageIterR S a ρ ρinf x₀ s) := by
    intro s
    induction s with
    | zero =>
      have hm0 : m 0 = m₀ := funext fun i => by rw [hm]; simp
      have hμ0 : μ 0 = μ₀ := by
        rw [hμ, hX00]; simp only [biteSR, pow_zero, div_one]
        field_simp
      rw [stripSR_zero ha, hβ, hm0, hμ0]
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
      exact hx₀
    | succ s ih =>
      have hδ := biteSR_pos ha hρ s
      have h3 : 3 * biteSR a ρ ρinf s < stripSR a ρ ρinf s := by
        have := stripSR_succ ha (ρ := ρ) (ρinf := ρinf) s
        have := stripSR_gt ha hρ (s + 1)
        linarith
      obtain ⟨h1, -, -⟩ := hS.step ih hδ (biteSR_le ha hρ s) h3 (hcond s) (hballc s) (hcap s)
      rw [stripSR_succ ha, hQμ] at h1
      have hb : β s - (C (biteSR a ρ ρinf s)).CDK * μ s / (γ * biteSR a ρ ρinf s ^ κ) =
          β (s + 1) := by
        rw [hCDKμ, hβ, hβ, Finset.sum_range_succ]; ring
      have hmm : (fun i => m s i + (C (biteSR a ρ ρinf s)).rate i * (C (biteSR a ρ ρinf s)).wt i *
          (μ s / (γ * biteSR a ρ ρinf s ^ (κ + 1)))) = m (s + 1) := by
        funext i
        rw [hμX, hm, hm, Finset.sum_range_succ, haC]; ring
      rw [hb, hmm] at h1
      exact h1
  -- the limit
  have hreg : ∀ s, 0 ≤ μ s ∧ DifferentiableOn ℂ (S.tor (stageIterR S a ρ ρinf x₀ s))
      (complexStrip n (stripSR a ρ ρinf s)) ∧ IsPrimaryOnStrip (S.tor (stageIterR S a ρ ρinf x₀ s))
        (stripSR a ρ ρinf s) ∧ IsRealOnReals (S.tor (stageIterR S a ρ ρinf x₀ s)) :=
    fun s => hS.regular (hAdm s)
  have hsub : ∀ s, complexStrip n ρinf ⊆ complexStrip n (stripSR a ρ ρinf s) := fun s =>
    KAM.Apost.Triangular.strip_mono (stripSR_gt ha hρ s).le
  have hstepfull : ∀ s, ∀ θ ∈ complexStrip n (stripSR a ρ ρinf (s + 1)),
      ‖S.tor (stageIterR S a ρ ρinf x₀ (s + 1)) θ - S.tor (stageIterR S a ρ ρinf x₀ s) θ‖ ≤
        aB s * X s := by
    intro s
    have hδ := biteSR_pos ha hρ s
    have h3 : 3 * biteSR a ρ ρinf s < stripSR a ρ ρinf s := by
      have := stripSR_succ ha (ρ := ρ) (ρinf := ρinf) s
      have := stripSR_gt ha hρ (s + 1)
      linarith
    obtain ⟨-, h2, -⟩ := hS.step (hAdm s) hδ (biteSR_le ha hρ s) h3 (hcond s) (hballc s) (hcap s)
    rw [stripSR_succ ha, hCDKμ] at h2
    exact h2
  have hdsum : Summable fun s => aB s * X s := summable_mul_decayR hy0.le hy1 haB0 hXnn hXd haBA
  have hdiff : ∀ s, ∀ θ ∈ complexStrip n ρinf,
      ‖S.tor (stageIterR S a ρ ρinf x₀ (s + 1)) θ - S.tor (stageIterR S a ρ ρinf x₀ s) θ‖ ≤
        aB s * X s := fun s θ hθ => hstepfull s θ (hsub (s + 1) hθ)
  -- the derivatives, by Cauchy on the difference
  have hder : ∀ s, ∀ θ ∈ complexStrip n ρinf,
      ‖fderiv ℂ (S.tor (stageIterR S a ρ ρinf x₀ (s + 1))) θ -
          fderiv ℂ (S.tor (stageIterR S a ρ ρinf x₀ s)) θ‖ ≤
        n * (3 * biteSR a ρ ρinf s / (a - 1))⁻¹ * (aB s * X s) := by
    intro s θ hθ
    have hδ := biteSR_pos ha hρ s
    have hmono : complexStrip n (stripSR a ρ ρinf (s + 1)) ⊆ complexStrip n (stripSR a ρ ρinf s) :=
      KAM.Apost.Triangular.strip_mono
        (by have := stripSR_succ ha (ρ := ρ) (ρinf := ρinf) s; linarith)
    have hg : DifferentiableOn ℂ (fun θ => S.tor (stageIterR S a ρ ρinf x₀ (s + 1)) θ -
        S.tor (stageIterR S a ρ ρinf x₀ s) θ) (complexStrip n (stripSR a ρ ρinf (s + 1))) :=
      (hreg (s + 1)).2.1.sub ((hreg s).2.1.mono hmono)
    have ha1 : 0 < a - 1 := by linarith
    obtain ⟨-, hc⟩ := KAM.cauchy_strip hg (hstepfull s)
      (δ := 3 * biteSR a ρ ρinf s / (a - 1)) (by positivity)
    have hge : ρinf ≤ stripSR a ρ ρinf (s + 1) - 3 * biteSR a ρ ρinf s / (a - 1) := by
      have h1 : biteSR a ρ ρinf (s + 1) = biteSR a ρ ρinf s / a := by
        simp only [biteSR, pow_succ]; field_simp
      have h2 := stripSR_eq ha (ρ := ρ) (ρinf := ρinf) (s + 1)
      have h3 := three_bite0R_le ha (ρ := ρ) (ρinf := ρinf)
      have h4 : 3 * biteSR a ρ ρinf (s + 1) * a / (a - 1) = 3 * biteSR a ρ ρinf s / (a - 1) := by
        rw [h1]; field_simp
      linarith
    have hθ' := hc θ (KAM.Apost.Triangular.strip_mono hge hθ)
    have hd1 : DifferentiableAt ℂ (S.tor (stageIterR S a ρ ρinf x₀ (s + 1))) θ :=
      ((hreg (s + 1)).2.1).differentiableAt
        ((isOpen_complexStrip n _).mem_nhds (hsub (s + 1) hθ))
    have hd0 : DifferentiableAt ℂ (S.tor (stageIterR S a ρ ρinf x₀ s)) θ :=
      ((hreg s).2.1).differentiableAt ((isOpen_complexStrip n _).mem_nhds (hsub s hθ))
    have := fderiv_sub hd1 hd0
    rw [show (fun θ => S.tor (stageIterR S a ρ ρinf x₀ (s + 1)) θ -
        S.tor (stageIterR S a ρ ρinf x₀ s) θ) = S.tor (stageIterR S a ρ ρinf x₀ (s + 1)) -
          S.tor (stageIterR S a ρ ρinf x₀ s) from rfl] at hθ'
    rw [this] at hθ'
    exact hθ'
  have hesum : Summable fun s => n * (3 * biteSR a ρ ρinf s / (a - 1))⁻¹ * (aB s * X s) := by
    have hfun : (fun s => n * (3 * biteSR a ρ ρinf s / (a - 1))⁻¹ * (aB s * X s)) =
        fun s => (n * (a - 1) / 3 * (C (biteSR a ρ ρinf s)).CDK) * X s := by
      funext s
      have hδ := (biteSR_pos ha hρ s).ne'
      have ha1 : a - 1 ≠ 0 := by linarith
      rw [haB]; field_simp
    rw [hfun]
    refine summable_mul_decayR hy0.le hy1 (A := n * (a - 1) / 3 * Ctail.CDK) (fun t => ?_)
      hXnn hXd (fun t ht => ?_)
    · exact mul_nonneg (by positivity) (hnn _ (biteSR_pos ha hρ t) (biteSR_le ha hρ t)).2.1
    · exact mul_le_mul_of_nonneg_left (htail _ (biteSR_pos ha hρ t) (hbs t ht)).2.2.1
        (by positivity)
  let L : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) := fun θ =>
    if θ ∈ complexStrip n ρinf then limUnder atTop (fun s => S.tor (stageIterR S a ρ ρinf x₀ s) θ)
    else S.tor (stageIterR S a ρ ρinf x₀ 0) θ
  obtain ⟨hconv, hpt, hLG⟩ := KAM.Apost.lim_k
    (Ks := fun s => S.tor (stageIterR S a ρ ρinf x₀ s)) (L := L) hdsum hdiff
    (fun θ hθ => by simp only [L, hθ, ite_true])
  obtain ⟨Λ, hΛ⟩ := KAM.Apost.lim_dk
    (Ks := fun s => S.tor (stageIterR S a ρ ρinf x₀ s)) hesum hder
  obtain ⟨hholo, -⟩ := KAM.Apost.lim_holo
    (Ks := fun s => S.tor (stageIterR S a ρ ρinf x₀ s)) (L := L)
    (fun s => (hreg s).2.1.mono (hsub s)) hpt hΛ
  obtain ⟨hprim, hreal⟩ := KAM.Apost.lim_primary
    (Ks := fun s => S.tor (stageIterR S a ρ ρinf x₀ s)) (L := L) hρinf hpt
    (fun s θ hθ kk => (hreg s).2.2.1 θ (hsub s hθ) kk) (fun s => (hreg s).2.2.2)
  refine ⟨L, 0, hholo, hprim, hreal, fun s => ?_, hconv, fun θ hθ => ?_⟩
  · exact ⟨stripSR a ρ ρinf s, β s, μ s, m s, hAdm s, stripSR_gt ha hρ s, fun i => by
      rw [hm]; exact hcapTot i s⟩
  · have h1 := KAM.Apost.lim_close (Ks := fun s => S.tor (stageIterR S a ρ ρinf x₀ s)) (L := L)
      hdsum hdiff hLG θ hθ
    exact h1.trans (Real.tsum_le_of_sum_range_le (fun t => mul_nonneg (haB0 t) (hXnn t)) hballLe)

end Converge

end KAM.Sharp2

end
