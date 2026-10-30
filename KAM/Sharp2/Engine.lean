/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.EngineArith
public import KAM.Apost.Limit
public import KAM.Strip.Bridges
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The stage-dependent engine (blueprint `bp:p2s2:engine`)

`StageScheme`, `StageConsts`, `StageScheme.IsNewton` and `xSeq` are the signatures of
`docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt`, verbatim.

**Design signal.** The signed `StageScheme.converge` is not provable as written: it omits hypotheses
of the blueprint's (J1)–(J3) and of the scheme's step (counterexamples in the handoff
`docs/campaign/handoffs/SHARP2-B5.md`):
* the ball budget (the `< β` hypothesis of the step, which no hypothesis of `converge` controls);
* the tail step conditions at `X_k` (J1, second half) and their persistence;
* nonnegativity of `Q`, `CDK` and of the products `rate * wt` (partial sums of the caps need the
  prefix increments to be nonnegative, `J3` only bounds the total).

`StageScheme.converge_checked` proves the conclusion of `converge` under the signed hypotheses plus
exactly these three extra hypotheses (`hnn`, `hcondT`, `hball`), under a distinct name.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Sharp2

/-- An abstract Newton scheme with weighted errors: states, torus, scalar parameter, admissibility
`Adm r β μ m x` (strip, ball margin, weighted error, cap values) and the step `Φ r δ x`. -/
structure StageScheme (n k : ℕ) (α : Type*) where
  tor : α → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)
  par : α → ℝ
  Adm : ℝ → ℝ → ℝ → (Fin k → ℝ) → α → Prop
  step : ℝ → ℝ → α → α

/-- The constants of one bite: contraction `Q`, step conditions, displacement, parameter change, cap
rates and their weights (`bp:p2s2:engine`, (J1)–(J3)). -/
structure StageConsts (k : ℕ) where
  Q : ℝ
  cond : ℝ → Prop
  CDK : ℝ
  Cp : ℝ
  rate : Fin k → ℝ
  wt : Fin k → ℝ

/-- (N1), (N2) for the bite `δ ≤ δmax`: an admissible state with `X = μ/(γ δ^{κ+1})` satisfying the
step conditions and the caps goes to an admissible state with weighted error
`≤ Q μ²/(γ δ^{κ+1})`. -/
structure StageScheme.IsNewton {n k : ℕ} {α : Type*} (S : StageScheme n k α) (κ γ δmax : ℝ)
    (C : ℝ → StageConsts k) (σ : Fin k → ℝ) : Prop where
  regular : ∀ {r β μ m x}, S.Adm r β μ m x → 0 ≤ μ ∧
    DifferentiableOn ℂ (S.tor x) (complexStrip n r) ∧
    IsPrimaryOnStrip (S.tor x) r ∧ IsRealOnReals (S.tor x)
  step : ∀ {r β μ δ m x}, S.Adm r β μ m x → 0 < δ → δ ≤ δmax → 3 * δ < r →
    (C δ).cond (μ / (γ * δ ^ (κ + 1))) → (C δ).CDK * μ / (γ * δ ^ κ) < β →
    (∀ i, m i + (C δ).rate i * (C δ).wt i * (μ / (γ * δ ^ (κ + 1))) ≤ σ i) →
    S.Adm (r - 3 * δ) (β - (C δ).CDK * μ / (γ * δ ^ κ)) ((C δ).Q * μ ^ 2 / (γ * δ ^ (κ + 1)))
        (fun i => m i + (C δ).rate i * (C δ).wt i * (μ / (γ * δ ^ (κ + 1)))) (S.step r δ x) ∧
      (∀ θ ∈ complexStrip n (r - 3 * δ), ‖S.tor (S.step r δ x) θ - S.tor x θ‖ ≤
        (C δ).CDK * μ / (γ * δ ^ κ)) ∧
      |S.par (S.step r δ x) - S.par x| ≤ (C δ).Cp * μ

/-- The initial bite `δ₀ = min {1, (ρ - ρ∞)/6}`. -/
abbrev bite0 (ρ ρinf : ℝ) : ℝ := min 1 ((ρ - ρinf) / 6)
/-- The bite `δ_s = δ₀/2^s`. -/
abbrev biteS (ρ ρinf : ℝ) (s : ℕ) : ℝ := bite0 ρ ρinf / 2 ^ s
/-- The strip `r_s = ρ - 6δ₀(1 - 2^{-s})`. -/
abbrev stripS (ρ ρinf : ℝ) (j : ℕ) : ℝ := ρ - 6 * bite0 ρ ρinf * (1 - (2 : ℝ)⁻¹ ^ j)

/-- The iterates `x_{s+1} = Φ(r_s, δ_s; x_s)`. -/
def stageIter {n k : ℕ} {α : Type*} (S : StageScheme n k α) (ρ ρinf : ℝ) (x₀ : α) : ℕ → α :=
  fun s => Nat.rec x₀ (fun j x => S.step (stripS ρ ρinf j) (biteS ρ ρinf j) x) s

theorem stageIter_succ {n k : ℕ} {α : Type*} (S : StageScheme n k α) (ρ ρinf : ℝ) (x₀ : α)
    (s : ℕ) : stageIter S ρ ρinf x₀ (s + 1) =
      S.step (stripS ρ ρinf s) (biteS ρ ρinf s) (stageIter S ρ ρinf x₀ s) := rfl

section Schedule

variable {ρ ρinf : ℝ}

theorem bite0_pos (hρ : ρinf < ρ) : 0 < bite0 ρ ρinf :=
  lt_min one_pos (by linarith)

theorem biteS_pos (hρ : ρinf < ρ) (s : ℕ) : 0 < biteS ρ ρinf s :=
  div_pos (bite0_pos hρ) (by positivity)

theorem biteS_le (hρ : ρinf < ρ) (s : ℕ) : biteS ρ ρinf s ≤ bite0 ρ ρinf :=
  div_le_self (bite0_pos hρ).le (one_le_pow₀ (by norm_num))

theorem six_bite0_le : 6 * bite0 ρ ρinf ≤ ρ - ρinf := by
  have : bite0 ρ ρinf ≤ (ρ - ρinf) / 6 := min_le_right _ _
  linarith

theorem stripS_eq (s : ℕ) :
    stripS ρ ρinf s = ρ - 6 * bite0 ρ ρinf + 6 * biteS ρ ρinf s := by
  simp only [stripS, biteS, inv_pow]
  field_simp
  ring

theorem stripS_gt (hρ : ρinf < ρ) (s : ℕ) : ρinf < stripS ρ ρinf s := by
  rw [stripS_eq]
  have := biteS_pos hρ s
  have := six_bite0_le (ρ := ρ) (ρinf := ρinf)
  linarith

theorem stripS_succ (s : ℕ) :
    stripS ρ ρinf s - 3 * biteS ρ ρinf s = stripS ρ ρinf (s + 1) := by
  rw [stripS_eq, stripS_eq]
  simp only [biteS, pow_succ]
  field_simp
  ring

theorem stripS_zero : stripS ρ ρinf 0 = ρ := by simp [stripS]

end Schedule

/-- The total ball budget of the iteration: `∑_{s<k} C_Δ(δ_s) δ_s X_s + 2 C_Δ^∞ δ_k X_k`
(prefix plus the critical sum of the tail). -/
def stageBall {k : ℕ} (κ γ ρ ρinf μ₀ : ℝ) (C : ℝ → StageConsts k) (kpre : ℕ)
    (Ctail : StageConsts k) : ℝ :=
  (∑ s ∈ Finset.range kpre, (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).CDK *
      (min 1 ((ρ - ρinf) / 6) / 2 ^ s) *
      xSeq κ (fun s => (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).Q)
        (μ₀ / (γ * min 1 ((ρ - ρinf) / 6) ^ (κ + 1))) s) +
    2 * Ctail.CDK * (min 1 ((ρ - ρinf) / 6) / 2 ^ kpre) *
      xSeq κ (fun s => (C (min 1 ((ρ - ρinf) / 6) / 2 ^ s)).Q)
        (μ₀ / (γ * min 1 ((ρ - ρinf) / 6) ^ (κ + 1))) kpre

section Converge

variable {n k : ℕ} {α : Type*}

/-- The iteration, with the three extra hypotheses of the design signal (`hnn`, `hcondT`, `hball`),
converges: the conclusion of the signed `StageScheme.converge`. -/
theorem StageScheme.converge_checked {S : StageScheme n k α} {κ γ ρ ρinf β₀ μ₀ : ℝ}
    {C : ℝ → StageConsts k} {σ m₀ : Fin k → ℝ} {x₀ : α} (kpre : ℕ) (Ctail : StageConsts k)
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
    -- the extra hypotheses
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
  classical
  have hδ0 := bite0_pos hρ
  have hΓ : (0 : ℝ) < γ * bite0 ρ ρinf ^ (κ + 1) := mul_pos hγ (Real.rpow_pos_of_pos hδ0 _)
  have hX0 : 0 ≤ μ₀ / (γ * bite0 ρ ρinf ^ (κ + 1)) := div_nonneg (hS.regular hx₀).1 hΓ.le
  have hbs : ∀ s, kpre ≤ s → biteS ρ ρinf s ≤ bite0 ρ ρinf / 2 ^ kpre := fun s hs =>
    div_le_div_of_nonneg_left hδ0.le (by positivity) (pow_le_pow_right₀ (by norm_num) hs)
  have hQ : ∀ s, 0 ≤ (C (biteS ρ ρinf s)).Q := fun s =>
    (hnn _ (biteS_pos hρ s) (biteS_le hρ s)).1
  have hQt : ∀ s, kpre ≤ s → (C (biteS ρ ρinf s)).Q ≤ Ctail.Q := fun s hs =>
    (htail _ (biteS_pos hρ s) (hbs s hs)).1
  -- the normalised errors
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ, X = xSeq κ (fun s => (C (biteS ρ ρinf s)).Q)
      (μ₀ / (γ * bite0 ρ ρinf ^ (κ + 1))) := ⟨_, rfl⟩
  have hXnn : ∀ s, 0 ≤ X s := by
    rw [hXdef]; exact xSeq_nonneg hQ hX0
  have hXd : ∀ s, kpre ≤ s → X s ≤ X kpre / 2 ^ (s - kpre) := by
    rw [hXdef]; exact xSeq_tail hQ hX0 hQt hJ2
  have hXsucc : ∀ s, X (s + 1) = 2 ^ (κ + 1) * (C (biteS ρ ρinf s)).Q * X s ^ 2 := by
    intro s; rw [hXdef]; rfl
  have hX00 : X 0 = μ₀ / (γ * bite0 ρ ρinf ^ (κ + 1)) := by rw [hXdef]; rfl
  -- the increments
  obtain ⟨aB, haB⟩ : ∃ aB : ℕ → ℝ, ∀ s, aB s = (C (biteS ρ ρinf s)).CDK * biteS ρ ρinf s :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨aC, haC⟩ : ∃ aC : Fin k → ℕ → ℝ, ∀ i s,
      aC i s = (C (biteS ρ ρinf s)).rate i * (C (biteS ρ ρinf s)).wt i := ⟨_, fun _ _ => rfl⟩
  have haB0 : ∀ t, 0 ≤ aB t := fun t => by
    rw [haB]; exact mul_nonneg (hnn _ (biteS_pos hρ t) (biteS_le hρ t)).2.1 (biteS_pos hρ t).le
  have haC0 : ∀ i t, 0 ≤ aC i t := fun i t => by
    rw [haC]; exact (hnn _ (biteS_pos hρ t) (biteS_le hρ t)).2.2 i
  have hCDKt : 0 ≤ Ctail.CDK :=
    (hnn _ (biteS_pos hρ kpre) (biteS_le hρ kpre)).2.1.trans
      (htail _ (biteS_pos hρ kpre) le_rfl).2.2.1
  have haBA : ∀ t, kpre ≤ t → aB t ≤ Ctail.CDK * biteS ρ ρinf kpre := fun t ht => by
    rw [haB]
    exact mul_le_mul (htail _ (biteS_pos hρ t) (hbs t ht)).2.2.1 (hbs t ht)
      (biteS_pos hρ t).le hCDKt
  have haCA : ∀ i t, kpre ≤ t → aC i t ≤ Ctail.rate i * Ctail.wt i := fun i t ht => by
    rw [haC]; exact (htail _ (biteS_pos hρ t) (hbs t ht)).2.2.2.2 i
  -- the critical sums
  have hballLe : ∀ N, ∑ t ∈ Finset.range N, aB t * X t ≤
      stageBall κ γ ρ ρinf μ₀ C kpre Ctail := by
    intro N
    have h1 := partial_sum_le N haB0 hXnn hXd haBA
    have e : ∑ t ∈ Finset.range kpre, aB t * X t = ∑ s ∈ Finset.range kpre,
        (C (biteS ρ ρinf s)).CDK * biteS ρ ρinf s * X s :=
      Finset.sum_congr rfl fun t _ => by rw [haB]
    have e2 : 2 * (Ctail.CDK * biteS ρ ρinf kpre) * X kpre =
        2 * Ctail.CDK * (min 1 ((ρ - ρinf) / 6) / 2 ^ kpre) * X kpre := by
      simp only [biteS]; ring
    have hb : stageBall κ γ ρ ρinf μ₀ C kpre Ctail = ∑ s ∈ Finset.range kpre,
        (C (biteS ρ ρinf s)).CDK * biteS ρ ρinf s * X s +
        2 * Ctail.CDK * (min 1 ((ρ - ρinf) / 6) / 2 ^ kpre) * X kpre := by
      rw [hXdef]; rfl
    rw [e, e2] at h1
    linarith
  have hballTot : ∀ N, ∑ t ∈ Finset.range N, aB t * X t < β₀ := fun N =>
    (hballLe N).trans_lt hball
  have hcapTot : ∀ i N, m₀ i + ∑ t ∈ Finset.range N, aC i t * X t ≤ σ i := by
    intro i N
    have h1 := partial_sum_le N (haC0 i) hXnn hXd (haCA i)
    have e : ∑ t ∈ Finset.range kpre, aC i t * X t = ∑ s ∈ Finset.range kpre,
        (C (biteS ρ ρinf s)).rate i * (C (biteS ρ ρinf s)).wt i * X s :=
      Finset.sum_congr rfl fun t _ => by rw [haC]
    have hj := hJ3 i
    rw [← hXdef] at hj
    have e2 : 2 * (Ctail.rate i * Ctail.wt i) * X kpre =
        2 * Ctail.rate i * Ctail.wt i * X kpre := by
      ring
    rw [e, e2] at h1
    linarith
  -- the explicit data of the admissible states
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℝ, ∀ s, β s = β₀ - ∑ t ∈ Finset.range s, aB t * X t :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ → Fin k → ℝ, ∀ s i, m s i = m₀ i + ∑ t ∈ Finset.range s, aC i t * X t :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℕ → ℝ, ∀ s, μ s = X s * (γ * biteS ρ ρinf s ^ (κ + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hΓs : ∀ s, 0 < γ * biteS ρ ρinf s ^ (κ + 1) := fun s =>
    mul_pos hγ (Real.rpow_pos_of_pos (biteS_pos hρ s) _)
  have hμX : ∀ s, μ s / (γ * biteS ρ ρinf s ^ (κ + 1)) = X s := fun s => by
    rw [hμ]; exact mul_div_cancel_right₀ _ (hΓs s).ne'
  have hCDKμ : ∀ s, (C (biteS ρ ρinf s)).CDK * μ s / (γ * biteS ρ ρinf s ^ κ) = aB s * X s := by
    intro s
    have hδ := biteS_pos hρ s
    have h1 : biteS ρ ρinf s ^ (κ + 1) = biteS ρ ρinf s ^ κ * biteS ρ ρinf s :=
      Real.rpow_add_one hδ.ne' κ
    have h2 : 0 < biteS ρ ρinf s ^ κ := Real.rpow_pos_of_pos hδ _
    rw [hμ, haB, h1]
    field_simp
  have hQμ : ∀ s, (C (biteS ρ ρinf s)).Q * μ s ^ 2 / (γ * biteS ρ ρinf s ^ (κ + 1)) =
      μ (s + 1) := by
    intro s
    have hδ := biteS_pos hρ s
    have h1 : biteS ρ ρinf (s + 1) = biteS ρ ρinf s / 2 := by simp only [biteS, pow_succ]; ring
    have h2 : (biteS ρ ρinf s / 2) ^ (κ + 1) = biteS ρ ρinf s ^ (κ + 1) / 2 ^ (κ + 1) :=
      Real.div_rpow hδ.le (by norm_num) _
    have h3 : 0 < biteS ρ ρinf s ^ (κ + 1) := Real.rpow_pos_of_pos hδ _
    have h4 : (0 : ℝ) < 2 ^ (κ + 1) := Real.rpow_pos_of_pos (by norm_num) _
    rw [hμ, hμ, hXsucc, h1, h2]
    field_simp
  -- the step hypotheses
  have hcond : ∀ s, (C (biteS ρ ρinf s)).cond (μ s / (γ * biteS ρ ρinf s ^ (κ + 1))) := by
    intro s
    rw [hμX]
    by_cases hs : s < kpre
    · rw [hXdef]; exact hJ1 s hs
    · have hs' : kpre ≤ s := not_lt.mp hs
      refine (htail _ (biteS_pos hρ s) (hbs s hs')).2.1 _ (hcondT _ (hXnn s) ?_)
      rw [← hXdef]
      exact (hXd s hs').trans (div_le_self (hXnn kpre) (one_le_pow₀ (by norm_num)))
  have hballc : ∀ s, (C (biteS ρ ρinf s)).CDK * μ s / (γ * biteS ρ ρinf s ^ κ) < β s := by
    intro s
    rw [hCDKμ, hβ]
    have := hballTot (s + 1)
    rw [Finset.sum_range_succ] at this
    linarith
  have hcap : ∀ s i, m s i + (C (biteS ρ ρinf s)).rate i * (C (biteS ρ ρinf s)).wt i *
      (μ s / (γ * biteS ρ ρinf s ^ (κ + 1))) ≤ σ i := by
    intro s i
    rw [hμX, hm]
    have := hcapTot i (s + 1)
    rw [Finset.sum_range_succ, haC] at this
    linarith
  -- the admissible states
  have hAdm : ∀ s, S.Adm (stripS ρ ρinf s) (β s) (μ s) (m s) (stageIter S ρ ρinf x₀ s) := by
    intro s
    induction s with
    | zero =>
      have hm0 : m 0 = m₀ := funext fun i => by rw [hm]; simp
      have hμ0 : μ 0 = μ₀ := by
        rw [hμ, hX00]; simp only [biteS, pow_zero, div_one]
        field_simp
      rw [stripS_zero, hβ, hm0, hμ0]
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
      exact hx₀
    | succ s ih =>
      have hδ := biteS_pos hρ s
      have h3 : 3 * biteS ρ ρinf s < stripS ρ ρinf s := by
        have := stripS_succ (ρ := ρ) (ρinf := ρinf) s
        have := stripS_gt hρ (s + 1)
        linarith
      obtain ⟨h1, -, -⟩ := hS.step ih hδ (biteS_le hρ s) h3 (hcond s) (hballc s) (hcap s)
      rw [stripS_succ, hQμ] at h1
      have hb : β s - (C (biteS ρ ρinf s)).CDK * μ s / (γ * biteS ρ ρinf s ^ κ) = β (s + 1) := by
        rw [hCDKμ, hβ, hβ, Finset.sum_range_succ]; ring
      have hmm : (fun i => m s i + (C (biteS ρ ρinf s)).rate i * (C (biteS ρ ρinf s)).wt i *
          (μ s / (γ * biteS ρ ρinf s ^ (κ + 1)))) = m (s + 1) := by
        funext i
        rw [hμX, hm, hm, Finset.sum_range_succ, haC]; ring
      rw [hb, hmm] at h1
      exact h1
  -- the limit
  have hreg : ∀ s, 0 ≤ μ s ∧ DifferentiableOn ℂ (S.tor (stageIter S ρ ρinf x₀ s))
      (complexStrip n (stripS ρ ρinf s)) ∧ IsPrimaryOnStrip (S.tor (stageIter S ρ ρinf x₀ s))
        (stripS ρ ρinf s) ∧ IsRealOnReals (S.tor (stageIter S ρ ρinf x₀ s)) :=
    fun s => hS.regular (hAdm s)
  have hsub : ∀ s, complexStrip n ρinf ⊆ complexStrip n (stripS ρ ρinf s) := fun s =>
    KAM.Apost.Triangular.strip_mono (stripS_gt hρ s).le
  have hstepfull : ∀ s, ∀ θ ∈ complexStrip n (stripS ρ ρinf (s + 1)),
      ‖S.tor (stageIter S ρ ρinf x₀ (s + 1)) θ - S.tor (stageIter S ρ ρinf x₀ s) θ‖ ≤
        aB s * X s := by
    intro s
    have hδ := biteS_pos hρ s
    have h3 : 3 * biteS ρ ρinf s < stripS ρ ρinf s := by
      have := stripS_succ (ρ := ρ) (ρinf := ρinf) s
      have := stripS_gt hρ (s + 1)
      linarith
    obtain ⟨-, h2, -⟩ := hS.step (hAdm s) hδ (biteS_le hρ s) h3 (hcond s) (hballc s) (hcap s)
    rw [stripS_succ, hCDKμ] at h2
    exact h2
  have hdsum : Summable fun s => aB s * X s := summable_mul_decay haB0 hXnn hXd haBA
  have hdiff : ∀ s, ∀ θ ∈ complexStrip n ρinf,
      ‖S.tor (stageIter S ρ ρinf x₀ (s + 1)) θ - S.tor (stageIter S ρ ρinf x₀ s) θ‖ ≤
        aB s * X s := fun s θ hθ => hstepfull s θ (hsub (s + 1) hθ)
  -- the derivatives, by Cauchy on the difference
  have hder : ∀ s, ∀ θ ∈ complexStrip n ρinf,
      ‖fderiv ℂ (S.tor (stageIter S ρ ρinf x₀ (s + 1))) θ -
          fderiv ℂ (S.tor (stageIter S ρ ρinf x₀ s)) θ‖ ≤
        n * (3 * biteS ρ ρinf s)⁻¹ * (aB s * X s) := by
    intro s θ hθ
    have hδ := biteS_pos hρ s
    have hmono : complexStrip n (stripS ρ ρinf (s + 1)) ⊆ complexStrip n (stripS ρ ρinf s) :=
      KAM.Apost.Triangular.strip_mono (by have := stripS_succ (ρ := ρ) (ρinf := ρinf) s; linarith)
    have hg : DifferentiableOn ℂ (fun θ => S.tor (stageIter S ρ ρinf x₀ (s + 1)) θ -
        S.tor (stageIter S ρ ρinf x₀ s) θ) (complexStrip n (stripS ρ ρinf (s + 1))) :=
      (hreg (s + 1)).2.1.sub ((hreg s).2.1.mono hmono)
    obtain ⟨-, hc⟩ := KAM.cauchy_strip hg (hstepfull s) (δ := 3 * biteS ρ ρinf s) (by positivity)
    have hge : ρinf ≤ stripS ρ ρinf (s + 1) - 3 * biteS ρ ρinf s := by
      have h1 : biteS ρ ρinf (s + 1) = biteS ρ ρinf s / 2 := by simp only [biteS, pow_succ]; ring
      have h2 := stripS_eq (ρ := ρ) (ρinf := ρinf) (s + 1)
      have h3 := six_bite0_le (ρ := ρ) (ρinf := ρinf)
      linarith
    have hθ' := hc θ (KAM.Apost.Triangular.strip_mono hge hθ)
    have hd1 : DifferentiableAt ℂ (S.tor (stageIter S ρ ρinf x₀ (s + 1))) θ :=
      ((hreg (s + 1)).2.1).differentiableAt
        ((isOpen_complexStrip n _).mem_nhds (hsub (s + 1) hθ))
    have hd0 : DifferentiableAt ℂ (S.tor (stageIter S ρ ρinf x₀ s)) θ :=
      ((hreg s).2.1).differentiableAt ((isOpen_complexStrip n _).mem_nhds (hsub s hθ))
    have := fderiv_sub hd1 hd0
    rw [show (fun θ => S.tor (stageIter S ρ ρinf x₀ (s + 1)) θ -
        S.tor (stageIter S ρ ρinf x₀ s) θ) = S.tor (stageIter S ρ ρinf x₀ (s + 1)) -
          S.tor (stageIter S ρ ρinf x₀ s) from rfl] at hθ'
    rw [this] at hθ'
    exact hθ'
  have hesum : Summable fun s => n * (3 * biteS ρ ρinf s)⁻¹ * (aB s * X s) := by
    have hfun : (fun s => n * (3 * biteS ρ ρinf s)⁻¹ * (aB s * X s)) =
        fun s => (n / 3 * (C (biteS ρ ρinf s)).CDK) * X s := by
      funext s
      have hδ := (biteS_pos hρ s).ne'
      rw [haB]; field_simp
    rw [hfun]
    refine summable_mul_decay (A := n / 3 * Ctail.CDK) (fun t => ?_) hXnn hXd (fun t ht => ?_)
    · exact mul_nonneg (by positivity) (hnn _ (biteS_pos hρ t) (biteS_le hρ t)).2.1
    · exact mul_le_mul_of_nonneg_left (htail _ (biteS_pos hρ t) (hbs t ht)).2.2.1 (by positivity)
  let L : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) := fun θ =>
    if θ ∈ complexStrip n ρinf then limUnder atTop (fun s => S.tor (stageIter S ρ ρinf x₀ s) θ)
    else S.tor (stageIter S ρ ρinf x₀ 0) θ
  obtain ⟨hconv, hpt, hLG⟩ := KAM.Apost.lim_k
    (Ks := fun s => S.tor (stageIter S ρ ρinf x₀ s)) (L := L) hdsum hdiff
    (fun θ hθ => by simp only [L, hθ, if_true])
  obtain ⟨Λ, hΛ⟩ := KAM.Apost.lim_dk
    (Ks := fun s => S.tor (stageIter S ρ ρinf x₀ s)) hesum hder
  obtain ⟨hholo, -⟩ := KAM.Apost.lim_holo
    (Ks := fun s => S.tor (stageIter S ρ ρinf x₀ s)) (L := L)
    (fun s => (hreg s).2.1.mono (hsub s)) hpt hΛ
  obtain ⟨hprim, hreal⟩ := KAM.Apost.lim_primary
    (Ks := fun s => S.tor (stageIter S ρ ρinf x₀ s)) (L := L) hρinf hpt
    (fun s θ hθ kk => (hreg s).2.2.1 θ (hsub s hθ) kk) (fun s => (hreg s).2.2.2)
  refine ⟨L, 0, hholo, hprim, hreal, fun s => ?_, hconv, fun θ hθ => ?_⟩
  · exact ⟨stripS ρ ρinf s, β s, μ s, m s, hAdm s, stripS_gt hρ s, fun i => by
      rw [hm]; exact hcapTot i s⟩
  · have h1 := KAM.Apost.lim_close (Ks := fun s => S.tor (stageIter S ρ ρinf x₀ s)) (L := L)
      hdsum hdiff hLG θ hθ
    exact h1.trans (Real.tsum_le_of_sum_range_le (fun t => mul_nonneg (haB0 t) (hXnn t)) hballLe)

end Converge

end KAM.Sharp2

end
