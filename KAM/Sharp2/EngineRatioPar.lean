/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.EngineRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The parameter limit of the ratio engine (SHARP2-B7 erratum 1)

`StageScheme.converge_ratio_par` strengthens `converge_ratio`: it also uses the step's parameter
clause `|par (step x) - par x| ≤ Cp μ`, and concludes that `par` of the iterates converges to
`pinf` with `|pinf - par x₀| ≤ parSumR …` (prefix `∑ Cp_s μ_s` plus tail term
`Cp_∞ μ_k/(1-ȳ)`), together with the admissibility of the iterates with the explicit ball margin
`engBeta`, weighted error `engMu` and caps `engCap`. Extra hypotheses (conservative):
`0 ≤ κ + 1` (so `δ_s^{κ+1}` decreases along the tail) and `0 ≤ Cp` for the bites.
`converge_ratio_of_par` recovers `converge_ratio`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Sharp2

/-- The normalised errors of the ratio engine. -/
abbrev engX {k : ℕ} (a κ γ ρ ρinf μ₀ : ℝ) (C : ℝ → StageConsts k) : ℕ → ℝ :=
  xSeqR a (κ + 1) (fun s => (C (biteSR a ρ ρinf s)).Q) (μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1)))

/-- The weighted error `μ_s = X_s γ δ_s^{κ+1}` at stage `s`. -/
def engMu {k : ℕ} (a κ γ ρ ρinf μ₀ : ℝ) (C : ℝ → StageConsts k) (s : ℕ) : ℝ :=
  engX a κ γ ρ ρinf μ₀ C s * (γ * biteSR a ρ ρinf s ^ (κ + 1))

/-- The ball margin `β_s = β₀ - ∑_{t<s} C_Δ(δ_t) δ_t X_t` at stage `s`. -/
def engBeta {k : ℕ} (a κ γ ρ ρinf β₀ μ₀ : ℝ) (C : ℝ → StageConsts k) (s : ℕ) : ℝ :=
  β₀ - ∑ t ∈ Finset.range s, (C (biteSR a ρ ρinf t)).CDK * biteSR a ρ ρinf t *
    engX a κ γ ρ ρinf μ₀ C t

/-- The cap values `m_s i = m₀ i + ∑_{t<s} rate_t wt_t X_t` at stage `s`. -/
def engCap {k : ℕ} (a κ γ ρ ρinf : ℝ) (m₀ : Fin k → ℝ) (μ₀ : ℝ) (C : ℝ → StageConsts k)
    (s : ℕ) (i : Fin k) : ℝ :=
  m₀ i + ∑ t ∈ Finset.range s, (C (biteSR a ρ ρinf t)).rate i * (C (biteSR a ρ ρinf t)).wt i *
    engX a κ γ ρ ρinf μ₀ C t

/-- The parameter sum with the tail factor `1/(1 - ȳ)`. -/
def parSumR {k : ℕ} (a κ γ ρ ρinf μ₀ ybar : ℝ) (C : ℝ → StageConsts k) (kpre : ℕ)
    (Ctail : StageConsts k) : ℝ :=
  (∑ s ∈ Finset.range kpre, (C (biteSR a ρ ρinf s)).Cp * engMu a κ γ ρ ρinf μ₀ C s) +
    Ctail.Cp * engMu a κ γ ρ ρinf μ₀ C kpre / (1 - ybar)

section Converge

variable {n k : ℕ} {α : Type*}

/-- `converge_ratio` with the parameter limit: `S.par` of the iterates converges to `pinf` with
`|pinf - par x₀| ≤ parSumR …`, and the iterates are admissible with the explicit ball and caps
(`engBeta`, `engMu`, `engCap`). Extra hypotheses: `hκ : 0 ≤ κ + 1` and nonnegativity of `Cp`. -/
theorem StageScheme.converge_ratio_par {n k : ℕ} {α : Type*} {S : StageScheme n k α}
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
    (hCp0 : ∀ δ, 0 < δ → δ ≤ bite0R a ρ ρinf → 0 ≤ (C δ).Cp)
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
        stageBallR a κ γ ρ ρinf μ₀ ybar C kpre Ctail) ∧
      Tendsto (fun s => S.par (stageIterR S a ρ ρinf x₀ s)) atTop (𝓝 pinf) ∧
      |pinf - S.par x₀| ≤ parSumR a κ γ ρ ρinf μ₀ ybar C kpre Ctail ∧
      (∀ s, S.Adm (stripSR a ρ ρinf s)
          (engBeta a κ γ ρ ρinf β₀ μ₀ C s) (engMu a κ γ ρ ρinf μ₀ C s)
          (engCap a κ γ ρ ρinf m₀ μ₀ C s) (stageIterR S a ρ ρinf x₀ s) ∧
        β₀ - stageBallR a κ γ ρ ρinf μ₀ ybar C kpre Ctail ≤ engBeta a κ γ ρ ρinf β₀ μ₀ C s ∧
        ρinf < stripSR a ρ ρinf s ∧ (∀ i, engCap a κ γ ρ ρinf m₀ μ₀ C s i ≤ σ i)) := by
  classical
  have ha0 : 0 < a := by linarith
  have hδ0 := bite0R_pos ha hρ
  have hΓ : (0 : ℝ) < γ * bite0R a ρ ρinf ^ (κ + 1) := mul_pos hγ (Real.rpow_pos_of_pos hδ0 _)
  have hX0 : 0 ≤ μ₀ / (γ * bite0R a ρ ρinf ^ (κ + 1)) := div_nonneg (hS.regular hx₀).1 hΓ.le
  have hbs : ∀ s, kpre ≤ s → biteSR a ρ ρinf s ≤ bite0R a ρ ρinf / a ^ kpre := fun s hs =>
    div_le_div_of_nonneg_left hδ0.le (by positivity) (pow_le_pow_right₀ ha.le hs)
  have hbs' : ∀ s, kpre ≤ s → biteSR a ρ ρinf s ≤ biteSR a ρ ρinf kpre := fun s hs =>
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
  -- the parameter limit
  have hCpnn : ∀ t, 0 ≤ (C (biteSR a ρ ρinf t)).Cp := fun t =>
    hCp0 _ (biteSR_pos ha hρ t) (biteSR_le ha hρ t)
  have hCpt : 0 ≤ Ctail.Cp :=
    (hCpnn kpre).trans (htail _ (biteSR_pos ha hρ kpre) le_rfl).2.2.2.1
  obtain ⟨aP, haP⟩ : ∃ aP : ℕ → ℝ, ∀ s,
      aP s = (C (biteSR a ρ ρinf s)).Cp * (γ * biteSR a ρ ρinf s ^ (κ + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hg0 : ∀ t, 0 ≤ γ * biteSR a ρ ρinf t ^ (κ + 1) := fun t =>
    mul_nonneg hγ.le (Real.rpow_nonneg (biteSR_pos ha hρ t).le _)
  have haP0 : ∀ t, 0 ≤ aP t := fun t => by rw [haP]; exact mul_nonneg (hCpnn t) (hg0 t)
  have haPA : ∀ t, kpre ≤ t → aP t ≤ Ctail.Cp * (γ * biteSR a ρ ρinf kpre ^ (κ + 1)) :=
    fun t ht => by
      rw [haP]
      refine mul_le_mul (htail _ (biteSR_pos ha hρ t) (hbs t ht)).2.2.2.1 ?_ (hg0 t) hCpt
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (biteSR_pos ha hρ t).le (hbs' t ht) hκ) hγ.le
  have hparstep : ∀ s, |S.par (stageIterR S a ρ ρinf x₀ (s + 1)) -
      S.par (stageIterR S a ρ ρinf x₀ s)| ≤ aP s * X s := by
    intro s
    have hδ := biteSR_pos ha hρ s
    have h3 : 3 * biteSR a ρ ρinf s < stripSR a ρ ρinf s := by
      have := stripSR_succ ha (ρ := ρ) (ρinf := ρinf) s
      have := stripSR_gt ha hρ (s + 1)
      linarith
    obtain ⟨-, -, h⟩ := hS.step (hAdm s) hδ (biteSR_le ha hρ s) h3 (hcond s) (hballc s) (hcap s)
    refine h.trans (le_of_eq ?_)
    rw [haP, hμ]; ring
  have hasum : Summable fun s => aP s * X s :=
    summable_mul_decayR hy0.le hy1 haP0 hXnn hXd haPA
  have hdsumP : Summable fun s => S.par (stageIterR S a ρ ρinf x₀ (s + 1)) -
      S.par (stageIterR S a ρ ρinf x₀ s) :=
    Summable.of_norm_bounded hasum (fun s => by rw [Real.norm_eq_abs]; exact hparstep s)
  obtain ⟨pinf, hpartend⟩ : ∃ pinf, Tendsto (fun s => S.par (stageIterR S a ρ ρinf x₀ s))
      atTop (𝓝 pinf) := by
    refine ⟨S.par x₀ + ∑' s, (S.par (stageIterR S a ρ ρinf x₀ (s + 1)) -
      S.par (stageIterR S a ρ ρinf x₀ s)), ?_⟩
    have h := (hdsumP.hasSum.tendsto_sum_nat).const_add (S.par x₀)
    refine h.congr fun N => ?_
    rw [Finset.sum_range_sub (fun s => S.par (stageIterR S a ρ ρinf x₀ s))]
    simp [stageIterR]
  have hparN : ∀ N, |S.par (stageIterR S a ρ ρinf x₀ N) - S.par x₀| ≤
      parSumR a κ γ ρ ρinf μ₀ ybar C kpre Ctail := by
    intro N
    have h1 : S.par (stageIterR S a ρ ρinf x₀ N) - S.par x₀ = ∑ s ∈ Finset.range N,
        (S.par (stageIterR S a ρ ρinf x₀ (s + 1)) - S.par (stageIterR S a ρ ρinf x₀ s)) := by
      rw [Finset.sum_range_sub (fun s => S.par (stageIterR S a ρ ρinf x₀ s))]
      simp [stageIterR]
    rw [h1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun s _ => hparstep s).trans
      ((partial_sum_leR N hy0.le hy1 haP0 hXnn hXd haPA).trans (le_of_eq ?_)))
    simp only [parSumR, engMu, hXdef, haP]
    congr 1
    · exact Finset.sum_congr rfl fun t _ => by ring
    · ring
  have hparbd : |pinf - S.par x₀| ≤ parSumR a κ γ ρ ρinf μ₀ ybar C kpre Ctail :=
    le_of_tendsto ((hpartend.sub_const _).abs) (Filter.Eventually.of_forall hparN)
  refine ⟨L, pinf, hholo, hprim, hreal, fun s => ?_, hconv, fun θ hθ => ?_,
    hpartend, hparbd, fun s => ⟨?_, ?_, stripSR_gt ha hρ s, fun i => ?_⟩⟩
  · exact ⟨stripSR a ρ ρinf s, β s, μ s, m s, hAdm s, stripSR_gt ha hρ s, fun i => by
      rw [hm]; exact hcapTot i s⟩
  · have h1 := KAM.Apost.lim_close (Ks := fun s => S.tor (stageIterR S a ρ ρinf x₀ s)) (L := L)
      hdsum hdiff hLG θ hθ
    exact h1.trans (Real.tsum_le_of_sum_range_le (fun t => mul_nonneg (haB0 t) (hXnn t)) hballLe)
  · have e : engMu a κ γ ρ ρinf μ₀ C s = μ s := by rw [hμ]; simp only [engMu, hXdef]
    have e1 : engBeta a κ γ ρ ρinf β₀ μ₀ C s = β s := by
      rw [hβ]; simp only [engBeta, hXdef, haB]
    have e2 : engCap a κ γ ρ ρinf m₀ μ₀ C s = m s := by
      funext i; rw [hm]; simp only [engCap, hXdef, haC]
    rw [e, e1, e2]; exact hAdm s
  · have e1 : engBeta a κ γ ρ ρinf β₀ μ₀ C s = β s := by
      rw [hβ]; simp only [engBeta, hXdef, haB]
    rw [e1, hβ]
    have := hballLe s
    linarith
  · have e2 : engCap a κ γ ρ ρinf m₀ μ₀ C s = m s := by
      funext i; rw [hm]; simp only [engCap, hXdef, haC]
    rw [e2, hm]; exact hcapTot i s

end Converge

end KAM.Sharp2

end
