/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.IterLemma
public import KAM.Wave.Iteration.Params
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the iteration (`bpW:w6:convergence`, step `c-ind`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:convergence` (milestone W6), step `c-ind`.

* `W6State`: the data `(Π_ν, ω_ν, Ω_ν, P_ν, X_{P_ν})` of a stage; `W6State.next d ν` applies
  Lemma `bpW:w6:iter-lemma` (W5's step) when the hypotheses of stage `ν` hold, and is the identity
  otherwise; `w6Seq d S₀ ν` is the iteration started at `S₀`; `W6State.phi d ν S` is `Φ_{ν+1}`.
* `W6ConvHyp`: the hypotheses of Proposition `bpW:w6:convergence` on `Π_{-1}`; `w6Start` is the
  stage-`0` state, with `Π_0 = Π_{-1} ∖ ⋃_{(k,l) ∈ Z, k ≠ 0} R^0_{kl}`.
* `w6Seq_stage`: the hypotheses of stage `ν` hold for every `ν` (step `c-ind`: the iterative
  lemma with Lemma `bpW:w6:k0`); conditional helper `w6Seq_stage_of_stepReal` (hypothesis
  `W6StepReal`, discharged by `w6StepReal_holds`).
* `w6Seq_Pi_antitone`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- The data of a stage of the iteration: `(Π, ω, Ω, P, X_P)` (`Ω` in W5's index). -/
structure W6State where
  /-- `Π_ν` -/
  Pi : Set (Fin 2 → ℝ)
  /-- `ω_ν` -/
  om : (Fin 2 → ℝ) → Fin 2 → ℝ
  /-- `Ω_ν` (W5 index) -/
  Om : (Fin 2 → ℝ) → ℕ+ → ℝ
  /-- `P_ν` -/
  P : (Fin 2 → ℝ) → KamPhase → ℂ
  /-- `X_{P_ν}` -/
  X : (Fin 2 → ℝ) → KamPhase → KamPhase

namespace W6State

variable {d : W6SeqData}

/-- The hypotheses of `bpW:w6:iter-lemma` at stage `ν` for the state `S`. -/
def w6Stage (d : W6SeqData) (ν : ℕ) (S : W6State) : Prop := W6Stage d ν S.Pi S.om S.Om S.P S.X

/-- The standing conditions on the data `d`: `Valid` and `ε₀ ≤ γ₀ α₀ σ₀^t`. -/
def Std (d : W6SeqData) : Prop := d.SeqValid ∧ d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T

/-- One step of the iteration: the outputs of Lemma `bpW:w6:iter-lemma` at stage `ν`. -/
def next (d : W6SeqData) (ν : ℕ) (S : W6State) : W6State :=
  open Classical in
  if h : Std d ∧ S.w6Stage d ν then
    ⟨W6Stage.PiN h.1.1 h.1.2 h.2, W6Stage.omN h.1.1 h.1.2 h.2, W6Stage.OmN h.1.1 h.1.2 h.2,
      W6Stage.PN h.1.1 h.1.2 h.2, W6Stage.XN h.1.1 h.1.2 h.2⟩
  else S

/-- `Φ_{ν+1}` (the identity if the hypotheses of stage `ν` fail). -/
def phi (d : W6SeqData) (ν : ℕ) (S : W6State) (ξ : Fin 2 → ℝ) :
    StepPhase (d.rNu ν) → StepPhase (d.rNu ν) :=
  open Classical in
  if h : Std d ∧ S.w6Stage d ν then W6Stage.PhiN h.1.1 h.1.2 h.2 ξ else id

theorem w6next_eq {S : W6State} {ν : ℕ} (hd : d.SeqValid)
    (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T) (h : S.w6Stage d ν) :
    S.next d ν = ⟨W6Stage.PiN hd hsmall h, W6Stage.omN hd hsmall h, W6Stage.OmN hd hsmall h,
      W6Stage.PN hd hsmall h, W6Stage.XN hd hsmall h⟩ := by
  unfold next
  rw [dite_eq_left ⟨⟨hd, hsmall⟩, h⟩]

theorem phi_eq {S : W6State} {ν : ℕ} (hd : d.SeqValid)
    (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T) (h : S.w6Stage d ν) :
    S.phi d ν = W6Stage.PhiN hd hsmall h := by
  funext ξ
  unfold phi
  rw [dite_eq_left ⟨⟨hd, hsmall⟩, h⟩]

theorem next_Pi_subset (S : W6State) (ν : ℕ) : (S.next d ν).Pi ⊆ S.Pi := by
  unfold next
  split_ifs with h
  · exact W6Stage.PiN_subset h.1.1 h.1.2 h.2
  · exact subset_rfl

end W6State

/-- The iteration started at `S₀`: `S_0 = S₀`, `S_{ν+1} = next ν S_ν`. -/
def w6Seq (d : W6SeqData) (S0 : W6State) : ℕ → W6State
  | 0 => S0
  | ν + 1 => (w6Seq d S0 ν).next d ν

theorem w6Seq_succ (d : W6SeqData) (S0 : W6State) (ν : ℕ) :
    w6Seq d S0 (ν + 1) = (w6Seq d S0 ν).next d ν := rfl

theorem w6Seq_Pi_antitone (d : W6SeqData) (S0 : W6State) :
    Antitone fun ν => (w6Seq d S0 ν).Pi :=
  antitone_nat_of_succ_le fun ν => W6State.next_Pi_subset _ ν

/-- The hypotheses of Proposition `bpW:w6:convergence`, on the set `Π_{-1} = Pm`: the data `d` of
Definition `bpW:w6:sequences` with `ε₀ ≤ γ₀ α₀ σ₀^t`; frequencies `(ω₀, Ω₀)` satisfying
`(bpW:w5:freq)` with `M_ω + M_Ω ≤ M₀`; the `k = 0` bound `|⟨l, Ω₀⟩| ≥ 2β₀⟨l⟩` (`l ∈ Λ`) with
`β₀ ≥ α₀`, `8ε₀ ≤ β₀`; a real periodic `P₀ ∈ 𝒮_{p_+}(D_0)` with `|X_{P₀}|^{λ_0}_{r_0, D_0} ≤ ε₀`. -/
structure W6ConvHyp (d : W6SeqData) (Pm : Set (Fin 2 → ℝ)) (ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ) (P0 : (Fin 2 → ℝ) → KamPhase → ℂ)
    (X0 : (Fin 2 → ℝ) → KamPhase → KamPhase) (β₀ : ℝ) : Prop where
  valid : d.SeqValid
  small : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T
  freq : ∃ T Mω MΩ : ℝ, HomFreqHyp Pm ω0 Ω0 T Mω MΩ ∧ Mω + MΩ ≤ d.M0
  beta_ge : d.al0 ≤ β₀
  eight_le : 8 * d.eps0 ≤ β₀
  k0 : ∀ ξ ∈ Pm, ∀ l : ℕ →₀ ℤ, IsLam l → 2 * β₀ * japL l ≤ |linF l (w6Om7 (Ω0 ξ))|
  smooth : ∀ ξ ∈ Pm, IsSmoothing (a := 1) (p := 1) (pb := 3 / 2) zero_le_one (by norm_num)
    (d.domNu 0) (P0 ξ) (X0 ξ)
  per : ∀ ξ ∈ Pm, ∀ i, ∀ w ∈ d.domNu 0, P0 ξ (w + stepTau i) = P0 ξ w
  real : ∀ ξ ∈ Pm, ∀ w ∈ d.domNu 0, StepReal w → (P0 ξ w).im = 0
  bound : FamBound Pm (d.domNu 0) (d.rNu 0) (d.lam 0) (d.eps 0) X0

/-- `Π_0 = Π_{-1} ∖ ⋃_{(k,l) ∈ Z, k ≠ 0} R^0_{kl}` (zones of `(ω₀, Ω₀)` at level `α₀`), i.e. the
removal of W6-PREP's `w6Removed` at index `0` (`K_{-1} = 0`). -/
def w6Pi0 (d : W6SeqData) (Pm : Set (Fin 2 → ℝ)) (ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ) : Set (Fin 2 → ℝ) :=
  Pm \ w6Removed (fun _ => ω0) (fun _ ξ => w6Om7 (Ω0 ξ)) d.alpha d.KprevNu Pm 0

/-- The stage-`0` state `(Π_0, ω₀, Ω₀, P₀, X₀)`. -/
def w6Start (d : W6SeqData) (Pm : Set (Fin 2 → ℝ)) (ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ) (P0 : (Fin 2 → ℝ) → KamPhase → ℂ)
    (X0 : (Fin 2 → ℝ) → KamPhase → KamPhase) : W6State :=
  ⟨w6Pi0 d Pm ω0 Ω0, ω0, Ω0, P0, X0⟩

section conv

variable {d : W6SeqData} {Pm : Set (Fin 2 → ℝ)} {ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ}
  {Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ} {P0 : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X0 : (Fin 2 → ℝ) → KamPhase → KamPhase} {β₀ : ℝ}

theorem w6Pi0_subset : w6Pi0 d Pm ω0 Ω0 ⊆ Pm := Set.sdiff_subset

theorem w6Seq_Pi_subset (S0 : W6State) (ν : ℕ) : (w6Seq d S0 ν).Pi ⊆ S0.Pi :=
  w6Seq_Pi_antitone d S0 (Nat.zero_le ν)

/-- The `k = 0` conditions at stage `ν` along the iteration, from Lemma `bpW:w6:k0`, given the
hypotheses of the stages `μ < ν`. -/
theorem w6Seq_k0 (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) (ν : ℕ)
    (hst : ∀ μ < ν, (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) μ).w6Stage d μ) :
    W6Mel0 (d.alpha ν) (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Pi
      (fun ξ => w6Om7 ((w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).Om ξ)) := by
  set S := w6Seq d (w6Start d Pm ω0 Ω0 P0 X0)
  have hinc : ∀ μ < ν, ∀ ξ ∈ (S μ).Pi, ∀ j : ℕ, normLab j ^ (1 / 2 : ℝ) *
      |w6Om7 ((S (μ + 1)).Om ξ) j - w6Om7 ((S μ).Om ξ) j| ≤ 3 * d.eps μ := by
    intro μ hμ ξ hξ j
    have hs := hst μ hμ
    have e : S (μ + 1) = _ := (w6Seq_succ d _ μ).trans (W6State.w6next_eq hC.valid hC.small hs)
    obtain ⟨c₀, c₁, h0, h1, hcs, hcb, -⟩ := W6Stage.OmN_inc hC.valid hC.small hs
    rw [e]
    have := hcb ξ hξ j
    have : 0 ≤ d.lam μ * c₁ := mul_nonneg (W6SeqData.lam_pos hC.valid μ).le h1
    dsimp only
    linarith
  have h0 : ∀ ξ ∈ (S 0).Pi, ∀ l : ℕ →₀ ℤ, IsLam l →
      2 * β₀ * japL l ≤ |linF l (w6Om7 ((S 0).Om ξ))| :=
    fun ξ hξ l hl => hC.k0 ξ (w6Pi0_subset hξ) l hl
  have := (W6SeqData.w6K0_of_increments hC.valid hC.small hC.beta_ge hC.eight_le
    (fun n => (S n).Pi) (w6Seq_Pi_antitone d _) (fun n ξ => w6Om7 ((S n).Om ξ)) h0 ν hinc).2.2
  exact this

/-- **Stage `0`** (step `c-ind` at `ν = 0`): the hypotheses of `bpW:w6:iter-lemma` hold for
`w6Start` (for `k ≠ 0` by the removal, for `k = 0` by Lemma `bpW:w6:k0`). -/
theorem w6Start_stage (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) :
    (w6Start d Pm ω0 Ω0 P0 X0).w6Stage d 0 := by
  have hsub : w6Pi0 d Pm ω0 Ω0 ⊆ Pm := w6Pi0_subset
  have hk0 := w6Seq_k0 hC 0 (fun μ hμ => absurd hμ (Nat.not_lt_zero μ))
  refine ⟨⟨?_, ?_, fun ξ hξ => hC.smooth ξ (hsub hξ), fun ξ hξ => hC.per ξ (hsub hξ), ?_⟩,
    fun ξ hξ => hC.real ξ (hsub hξ)⟩
  · obtain ⟨T, Mω, MΩ, hf, hle⟩ := hC.freq
    exact ⟨T, Mω, MΩ, hf.w6mono hsub le_rfl, by rw [W6SeqData.M_zero]; exact hle⟩
  · intro ξ hξ k l hkl
    by_cases hk : k = 0
    · subst hk
      have hl : IsLam l := by
        obtain ⟨h1, h2⟩ := hkl
        rcases h1 with h1 | h1
        · exfalso
          rcases h2 with h2 | h2
          · exact h2 rfl
          · exact h2 h1
        · exact h1
      have e : ∑ i, (((0 : Fin 2 → ℤ) i : ℤ) : ℝ) * (w6Start d Pm ω0 Ω0 P0 X0).om ξ i = 0 := by
        simp
      rw [e, zero_add]
      exact hk0 ξ hξ l hl
    · have hkpos : d.KprevNu 0 < kAbs k := by
        show (0 : ℝ) < kAbs k
        linarith [one_le_kAbs hk]
      have hn := hξ.2
      simp only [w6Removed, Set.mem_iUnion, not_exists] at hn
      by_contra hlt
      push Not at hlt
      exact hn k l ⟨hkl, hkpos⟩ ⟨hξ.1, hlt⟩
  · have e : d.domNu 0 = d.domNu 0 := rfl
    exact hC.bound.mono_lam hsub subset_rfl le_rfl le_rfl

/-- **Induction** (step `c-ind`; conditional helper, not the label): if W5's reality clause
`W6StepReal` holds, the hypotheses of `bpW:w6:iter-lemma` hold at every stage of the iteration. -/
theorem w6Seq_stage_of_stepReal (hR : W6StepReal) (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) (ν : ℕ) :
    (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).w6Stage d ν := by
  suffices H : ∀ ν, ∀ μ ≤ ν, (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) μ).w6Stage d μ from H ν ν le_rfl
  intro ν
  induction ν with
  | zero =>
    intro μ hμ
    rw [Nat.le_zero.1 hμ]
    exact w6Start_stage hC
  | succ ν ih =>
    intro μ hμ
    rcases Nat.lt_or_eq_of_le hμ with hlt | heq
    · exact ih μ (Nat.lt_succ_iff.1 hlt)
    · subst heq
      have hs := ih ν le_rfl
      have hk0 := w6Seq_k0 hC (ν + 1) fun μ hμ => ih μ (Nat.lt_succ_iff.1 hμ)
      have e := (w6Seq_succ d (w6Start d Pm ω0 Ω0 P0 X0) ν).trans
        (W6State.w6next_eq hC.valid hC.small hs)
      rw [e] at hk0 ⊢
      exact W6Stage.next_stage_of_stepReal hC.valid hC.small hs hR hk0

/-- **Induction** (step `c-ind` of `bpW:w6:convergence`): the hypotheses of `bpW:w6:iter-lemma`
hold at every stage of the iteration (W5's reality clause discharged, `w6StepReal_holds`). -/
theorem w6Seq_stage (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) (ν : ℕ) :
    (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) ν).w6Stage d ν :=
  w6Seq_stage_of_stepReal w6StepReal_holds hC ν

end conv

end KAM.Wave
