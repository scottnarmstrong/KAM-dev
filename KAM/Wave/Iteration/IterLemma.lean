/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Stage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# W6: the iterative lemma (`bpW:w6:iter-lemma`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:iter-lemma` (milestone W6).

For the data `d` of Definition `bpW:w6:sequences` with `ε₀ ≤ γ₀ α₀ σ₀^t` and the hypotheses
`W6Stage d ν Π ω Ω P X` at stage `ν`, W5's step (`stepTheorem`, unmodified case) applies with
`s_ν, σ_ν, η_ν, r_ν, α_ν, λ_ν` (`W6Stage.stageStepHyp`) and yields `Φ_{ν+1}`, `ω_{ν+1}`, `Ω_{ν+1}`,
`P_{ν+1}` (`W6Stage.PhiN`, `omN`, `OmN`, `PN`, `XN`) and `Π_{ν+1}` (`W6Stage.PiN`). `w6IterLemma`:

* `q_ν ≤ γ₀ 2^{-ν}`, `q_{ν+1} ≤ q_ν/4`;
* `Φ_{ν+1}` maps `D_{ν+1}` into `D(s_ν - 4σ_ν, 2η_ν r_ν) ⊆ D_ν`;
* given the conditions with `k = 0` at stage `ν+1` on `Π_{ν+1}` (`W6Mel0`, supplied by `bpW:w6:k0`),
  all hypotheses of stage `ν+1` hold (`W6Stage`; `W6StageCore` without the reality of `P_{ν+1}`);
* `Φ_{ν+1} = id + ι Ψ_{ν+1}`, `|Φ_{ν+1} - id|^{λ_ν}_{p_+} = |Ψ_{ν+1}|^{λ_ν} ≤ 2 M_{F,ν}`,
  `|DΦ_{ν+1} - I|^{λ_ν}_{p→p_+} = |DΨ_{ν+1}|^{λ_ν} ≤ 16 M_{F,ν}/σ_ν ≤ 2^{-ν-2}` (W5's smoothing
  displacement `Ψ_{ν+1}`, `W6Stage.PsiN`);
* `|ω_{ν+1} - ω_ν| + λ_ν |ω_{ν+1} - ω_ν|^ℒ ≤ 6πε_ν`,
  `sup_j (j+2)^{1/2} (|Ω_{ν+1,j} - Ω_{ν,j}| + λ_ν |·|^ℒ) ≤ 3ε_ν` (W7 index, `normLab j = j + 3`).

The reality of `P_{ν+1}` is W5's clause `bpW:w5:step` (ii) (reality). `W6StepReal` is that clause
for the data used here; it holds (`w6StepReal_holds`, from `stepTheorem_reality_of_eps0_pos`), and
`next_stage` gives the full stage `ν+1` (the conditional helper `next_stage_of_stepReal` takes
`W6StepReal` as a hypothesis).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- The conditions `(bpW:w6:melnikov)` with `k = 0` at level `a` on `Par` (W7 index). -/
def W6Mel0 (a : ℝ) (Par : Set (Fin 2 → ℝ)) (Ω : (Fin 2 → ℝ) → ℕ → ℝ) : Prop :=
  ∀ ξ ∈ Par, ∀ l : ℕ →₀ ℤ, IsLam l → a * japL l / kAk 0 ≤ |linF l (Ω ξ)|

/-- W5's reality clause for `P_+` (blueprint `bpW:w5:step` (ii)), for `a = p = 1`, `p_+ = 3/2`,
`τ = 24`, `γ_G = w6GamG`; it holds, `w6StepReal_holds`. -/
def W6StepReal : Prop :=
  ∀ (s r σ η α lam ε ε₀ ε₁ M0 Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) (P : (Fin 2 → ℝ) → KamPhase → ℂ)
    (X : (Fin 2 → ℝ) → KamPhase → KamPhase)
    (H : WaveStepHyp 1 1 (3 / 2) s r σ η w6Tau α lam ε ε₀ ε₁ w6GamG M0 Mω MΩ Par ω Ω P X)
    [Fact (0 < r)],
    ∀ ξ ∈ Par, ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), StepReal (StepPhase.toK w) →
      (H.core.Pplus ξ w).im = 0

/-- `W6StepReal` holds: it is the `P_+` part of W5's reality clause
(`stepTheorem_reality_of_eps0_pos`, which is stated for `WaveStepHyp`, as `W6StepReal` is). -/
theorem w6StepReal_holds : W6StepReal :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ => (stepTheorem_reality_of_eps0_pos H).2

/-- The divisor estimate of step `il-div`: a Melnikov bound at level `a` survives perturbations
`|ω' - ω| ≤ 6πε`, `|Ω'_j - Ω_j| ≤ 3ε` at level `a'` for `|k| ≤ K` if `24π K^{τ+1} ε ≤ a - a'`. -/
theorem w6_mel_perturb {a a' ε K : ℝ} {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hl : l = 0 ∨ IsLam l)
    {ω ω' : Fin 2 → ℝ} {Ω Ω' : ℕ → ℝ} (hK : 1 ≤ K) (hk : kAbs k ≤ K) (hε : 0 ≤ ε)
    (hω : ‖ω' - ω‖ ≤ 6 * π * ε) (hΩ : ∀ n, |Ω' n - Ω n| ≤ 3 * ε)
    (hdiv : 6 * π * (4 * K ^ (w6Tau + 1)) * ε ≤ a - a')
    (h : a * japL l / kAk k ≤ |∑ i, (k i : ℝ) * ω i + linF l Ω|) :
    a' * japL l / kAk k ≤ |∑ i, (k i : ℝ) * ω' i + linF l Ω'| := by
  have hpi := Real.pi_gt_three
  have hK0 : 0 ≤ K := by linarith
  -- the perturbation of the `k` part
  have hkω : |∑ i, (k i : ℝ) * ω' i - ∑ i, (k i : ℝ) * ω i| ≤ K * (6 * π * ε) := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ i, ((k i : ℝ) * ω' i - (k i : ℝ) * ω i)|
        ≤ ∑ i, |(k i : ℝ) * ω' i - (k i : ℝ) * ω i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |(k i : ℝ)| * (6 * π * ε) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← mul_sub, abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have : |ω' i - ω i| ≤ ‖ω' - ω‖ := by
            have := norm_le_pi_norm (ω' - ω) i
            rwa [Real.norm_eq_abs, Pi.sub_apply] at this
          linarith
      _ = kAbs k * (6 * π * ε) := by rw [← Finset.sum_mul]; rfl
      _ ≤ K * (6 * π * ε) := by gcongr
  -- the perturbation of the `l` part
  have hlΩ : |linF l Ω' - linF l Ω| ≤ 6 * ε := by
    have h1 := abs_linF_le_l1Norm_mul l (fun n => Ω' n - Ω n) hΩ
    rw [linF_sub'] at h1
    have hl2 : (l1Norm l : ℝ) ≤ 2 := by
      rcases hl with h0 | h0
      · subst h0; simp [l1Norm]
      · exact_mod_cast h0.2
    have : (l1Norm l : ℝ) * (3 * ε) ≤ 2 * (3 * ε) := mul_le_mul_of_nonneg_right hl2 (by linarith)
    linarith
  -- the size of the divisor margin
  have hA1 : 1 ≤ kAk k := by unfold kAk; have := pow_nonneg (kAbs_nonneg k) 24; linarith
  have hA0 : 0 < kAk k := by linarith
  have hAK : kAk k ≤ 1 + K ^ w6Tau := by
    unfold kAk
    rw [w6Tau_eq, show (24 : ℝ) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    gcongr
    exact kAbs_nonneg k
  have h4 := W6SeqData.one_add_mul_one_add_rpow_le hK
  have hKτ : 0 ≤ K ^ w6Tau := Real.rpow_nonneg hK0 _
  have hmargin : 6 * π * (1 + K) * ε * kAk k ≤ a - a' := by
    have : 6 * π * (1 + K) * ε * kAk k ≤ 6 * π * ((1 + K) * (1 + K ^ w6Tau)) * ε := by
      have : 0 ≤ 6 * π * (1 + K) * ε := by positivity
      nlinarith
    have : 6 * π * ((1 + K) * (1 + K ^ w6Tau)) * ε ≤ 6 * π * (4 * K ^ (w6Tau + 1)) * ε := by
      gcongr
    linarith
  have hJ := japL_ge_one l
  have haa : 0 ≤ a - a' := le_trans (by positivity) hdiv
  -- `(a - a') ⟨l⟩/A_k ≥ 6π(1+K)ε ≥ pert`
  have hpert : K * (6 * π * ε) + 6 * ε ≤ (a - a') * japL l / kAk k := by
    rw [le_div_iff₀ hA0]
    have h1 : (K * (6 * π * ε) + 6 * ε) * kAk k ≤ 6 * π * (1 + K) * ε * kAk k := by
      have : K * (6 * π * ε) + 6 * ε ≤ 6 * π * (1 + K) * ε := by nlinarith
      exact mul_le_mul_of_nonneg_right this hA0.le
    have h2 : a - a' ≤ (a - a') * japL l := le_mul_of_one_le_right haa hJ
    linarith
  have htri : |∑ i, (k i : ℝ) * ω i + linF l Ω| ≤ |∑ i, (k i : ℝ) * ω' i + linF l Ω'| +
      (|∑ i, (k i : ℝ) * ω' i - ∑ i, (k i : ℝ) * ω i| + |linF l Ω' - linF l Ω|) := by
    have := abs_sub_abs_le_abs_sub (∑ i, (k i : ℝ) * ω i + linF l Ω)
      (∑ i, (k i : ℝ) * ω' i + linF l Ω')
    have h2 := abs_add_le (∑ i, (k i : ℝ) * ω' i - ∑ i, (k i : ℝ) * ω i) (linF l Ω' - linF l Ω)
    have e : ∑ i, (k i : ℝ) * ω i + linF l Ω - (∑ i, (k i : ℝ) * ω' i + linF l Ω') =
        -((∑ i, (k i : ℝ) * ω' i - ∑ i, (k i : ℝ) * ω i) + (linF l Ω' - linF l Ω)) := by ring
    rw [e, abs_neg] at this
    linarith
  have esplit : a * japL l / kAk k = a' * japL l / kAk k + (a - a') * japL l / kAk k := by ring
  linarith

namespace W6Stage

variable {d : W6SeqData} {ν : ℕ} {Pi : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
  {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {P : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  (hd : d.SeqValid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
  (h : W6Stage d ν Pi ω Ω P X)


theorem w6_iter_one_le_three_halves : (1 : ℝ) ≤ 3 / 2 := by norm_num

/-- `ε²/(α σ^t η²) = ε η` for `η = (ε/(α σ^t))^{1/3}` (step `il-err`). -/
theorem w6_newerror_eq (hd : d.SeqValid) (ν : ℕ) :
    d.eps ν ^ 2 / (d.alpha ν * d.sigma ν ^ w6T * d.etaNu ν ^ 2) = d.etaNu ν * d.eps ν := by
  have hq := W6SeqData.qNu_pos hd ν
  have hη3 : d.etaNu ν ^ 3 = d.qNu ν := by
    rw [W6SeqData.eta_eq_q, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]; norm_num
  have hA := W6SeqData.alpha_sigma_pos hd ν
  have hη := W6SeqData.eta_pos hd ν
  rw [W6SeqData.eps_eq_q hd ν, ← hη3]
  field_simp

/-- **Step `il-small`, `(i)`**: `Φ_{ν+1}` maps `D_{ν+1}` into `D(s_ν - 4σ_ν, 2η_ν r_ν) ⊆ D_ν`. -/
theorem phiN_mapsTo :
    ∀ ξ ∈ Pi, ∀ w ∈ stepDomain (d.rNu ν) (d.s (ν + 1)) (d.rNu (ν + 1)),
      StepPhase.toK (h.PhiN hd hsmall ξ w) ∈ kamDomain (d.s ν - 4 * d.sigma ν)
        (2 * d.etaNu ν * d.rNu ν) ∧
      StepPhase.toK (h.PhiN hd hsmall ξ w) ∈ d.domNu ν := by
  have := factRPos hd ν
  intro ξ hξ w hw
  have h1 := (stepTheorem_clauses (h.stageStepHyp hd hsmall)).1 ξ hξ w hw
  refine ⟨h1, kamDomain_mono ?_ ?_ ?_ h1⟩
  · linarith [W6SeqData.sigmaNu_pos hd ν]
  · have := W6SeqData.eta_pos hd ν; have := W6SeqData.w6r_pos hd ν; positivity
  · have := W6SeqData.eta_le hd hsmall ν; have := W6SeqData.w6r_pos hd ν; nlinarith

/-- **Frequencies, `ω`** (`bpW:w6:iter-lemma`, `bpW:w5:step` (iii)):
`|ω_{ν+1} - ω_ν| + λ_ν |ω_{ν+1} - ω_ν|^ℒ ≤ 6π ε_ν` on `Π_ν`. -/
theorem omN_inc :
    ∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ b₀ + d.lam ν * b₁ ≤ 6 * π * d.eps ν ∧
      (∀ ξ ∈ Pi, ‖h.omN hd hsmall ξ - ω ξ‖ ≤ b₀) ∧
      ∀ ξ ∈ Pi, ∀ ζ ∈ Pi,
        ‖(h.omN hd hsmall ξ - ω ξ) - (h.omN hd hsmall ζ - ω ζ)‖ ≤ b₁ * ‖ξ - ζ‖ := by
  have := factRPos hd ν
  exact (stepTheorem_clauses (h.stageStepHyp hd hsmall)).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normLab_eq_succPNat (n : ℕ) : normLab n = ((n.succPNat : ℕ+) : ℝ) + 2 := by
  unfold normLab
  rw [show ((n.succPNat : ℕ+) : ℝ) = ((n.succPNat : ℕ) : ℝ) from rfl, Nat.succPNat_coe]
  push_cast; ring

/-- **Frequencies, `Ω`** (`bpW:w6:iter-lemma`, `bpW:w5:step` (iii)), W7 index:
`sup_j (j+2)^{1/2} (|Ω_{ν+1,j} - Ω_{ν,j}| + λ_ν |·|^ℒ) ≤ 3 ε_ν` on `Π_ν`. -/
theorem OmN_inc :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + d.lam ν * c₁ ≤ 3 * d.eps ν ∧
      (∀ ξ ∈ Pi, ∀ n : ℕ,
        normLab n ^ (1 / 2 : ℝ) * |w6Om7 (h.OmN hd hsmall ξ) n - w6Om7 (Ω ξ) n| ≤ c₀) ∧
      ∀ ξ ∈ Pi, ∀ ζ ∈ Pi, ∀ n : ℕ, normLab n ^ (1 / 2 : ℝ) *
        |(w6Om7 (h.OmN hd hsmall ξ) n - w6Om7 (Ω ξ) n) -
          (w6Om7 (h.OmN hd hsmall ζ) n - w6Om7 (Ω ζ) n)| ≤ c₁ * ‖ξ - ζ‖ := by
  have := factRPos hd ν
  obtain ⟨c₀, c₁, h0, h1, hs, hb, hl⟩ :=
    (stepTheorem_clauses (h.stageStepHyp hd hsmall)).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have e : ((3 / 2 : ℝ) - 1) = 1 / 2 := by norm_num
  refine ⟨c₀, c₁, h0, h1, hs, fun ξ hξ n => ?_, fun ξ hξ ζ hζ n => ?_⟩
  · have := hb ξ hξ n.succPNat
    rw [e, ← normLab_eq_succPNat] at this
    exact this
  · have := hl ξ hξ ζ hζ n.succPNat
    rw [e, ← normLab_eq_succPNat] at this
    exact this

/-- `|Ω_{ν+1,j} - Ω_{ν,j}| ≤ 3 ε_ν` (W7 index) on `Π_ν`. -/
theorem OmN_inc_abs : ∀ ξ ∈ Pi, ∀ n : ℕ,
    |w6Om7 (h.OmN hd hsmall ξ) n - w6Om7 (Ω ξ) n| ≤ 3 * d.eps ν := by
  obtain ⟨c₀, c₁, h0, h1, hs, hb, -⟩ := h.OmN_inc hd hsmall
  intro ξ hξ n
  have h2 := hb ξ hξ n
  have hw := one_le_normLab_rpow_half n
  have hl := (W6SeqData.lam_pos hd ν).le
  have : 0 ≤ d.lam ν * c₁ := mul_nonneg hl h1
  have ha := abs_nonneg (w6Om7 (h.OmN hd hsmall ξ) n - w6Om7 (Ω ξ) n)
  nlinarith

/-- `Ψ_{ν+1}` (on `Π_ν`): W5's smoothing displacement of `Φ_{ν+1}` (`StepCore.Psi`), with values
in the `p_+`-representatives (`p_+ = 3/2`): `Φ_{ν+1} = id + ι Ψ_{ν+1}` on `D_{ν+1}`. -/
def PsiN (ξ : Fin 2 → ℝ) : StepPhase (d.rNu ν) → StepPhase (d.rNu ν) :=
  haveI := factRPos hd ν
  (h.stageStepHyp hd hsmall).hyp.core.Psi ξ

/-- **Transformations** (step `il-tr`; `bpW:w5:step` (v) in the `p_+` norms, W5-STEP-B-FIX):
with `M_{F,ν} = c_F q_ν σ_ν`, on `D_{ν+1}`, `ξ, ζ ∈ Π_ν`: `Φ_{ν+1} = id + ι Ψ_{ν+1}`,
`DΦ_{ν+1} = I + ι ∘ DΨ_{ν+1}` (`ι = 𝒫^{p_+} → 𝒫`), and
`|Φ_{ν+1} - id|^{λ_ν}_{p_+,r_ν} = |Ψ_{ν+1}|^{λ_ν}_{r_ν} ≤ 2M_{F,ν}`,
`|DΦ_{ν+1} - I|^{λ_ν}_{p→p_+,r_ν} = |DΨ_{ν+1}|^{λ_ν} ≤ 16 M_{F,ν}/σ_ν ≤ 2^{-ν-2}`, each `λ`-norm as
a sup bound plus `λ_ν` times a parameter-Lipschitz bound (norms of `StepPhase r_ν` on the
`p_+`-representatives, operator norm `p → p_+`). -/
theorem phiN_bounds :
    ∃ A₀ A₁ B₀ B₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      A₀ + d.lam ν * A₁ ≤ 2 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) ∧
      B₀ + d.lam ν * B₁ ≤ 16 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) / d.sigma ν ∧
      16 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) / d.sigma ν ≤ 1 / 2 ^ (ν + 2) ∧
      ∀ ξ ∈ Pi, ∀ ζ ∈ Pi, ∀ w ∈ stepDomain (d.rNu ν) (d.s (ν + 1)) (d.rNu (ν + 1)),
        have := factRPos hd ν
        h.PhiN hd hsmall ξ w =
          w + stepEmbedCLM 1 1 (3 / 2) w6_iter_one_le_three_halves (d.rNu ν)
            (h.PsiN hd hsmall ξ w) ∧
        fderiv ℂ (h.PhiN hd hsmall ξ) w = ContinuousLinearMap.id ℂ _ +
          (stepEmbedCLM 1 1 (3 / 2) w6_iter_one_le_three_halves (d.rNu ν)).comp
            (fderiv ℂ (h.PsiN hd hsmall ξ) w) ∧
        ‖h.PsiN hd hsmall ξ w‖ ≤ A₀ ∧
        ‖h.PsiN hd hsmall ξ w - h.PsiN hd hsmall ζ w‖ ≤ A₁ * ‖ξ - ζ‖ ∧
        ‖fderiv ℂ (h.PsiN hd hsmall ξ) w‖ ≤ B₀ ∧
        ‖fderiv ℂ (h.PsiN hd hsmall ξ) w - fderiv ℂ (h.PsiN hd hsmall ζ) w‖ ≤ B₁ * ‖ξ - ζ‖ := by
  have := factRPos hd ν
  set G := (h.stageStepHyp hd hsmall).hyp.core
  obtain ⟨A₀, A₁, B₀, B₁, a0, a1, b0, b1, ha, hb, hall⟩ := G.smooth_clause_v
  exact ⟨A₀, A₁, B₀, B₁, a0, a1, b0, b1, ha, hb, W6SeqData.transf_arith hd hsmall ν,
    fun ξ hξ ζ hζ w hw => ⟨G.phi_eq_add_Psi hξ hw, G.fderiv_phi_eq hξ hw, hall ξ hξ ζ hζ w hw⟩⟩

/-- **Stage `ν+1`** (`bpW:w6:iter-lemma`): given the conditions with `k = 0` at stage `ν+1` on
`Π_{ν+1}` (supplied by `bpW:w6:k0`), all hypotheses of the lemma hold at stage `ν+1`, except the
reality of `P_{ν+1}` (W5's reality clause, see `next_stage_of_stepReal`). -/
theorem next_core
    (hk0 : W6Mel0 (d.alpha (ν + 1)) (h.PiN hd hsmall) (fun ξ => w6Om7 (h.OmN hd hsmall ξ))) :
    W6StageCore d (ν + 1) (h.PiN hd hsmall) (h.omN hd hsmall) (h.OmN hd hsmall)
      (h.PN hd hsmall) (h.XN hd hsmall) := by
  have := factRPos hd ν
  obtain ⟨-, -, -, -, -, -, -, -, c6, c7, -, c8, -, -, c11, -, -⟩ :=
    stepTheorem_clauses (h.stageStepHyp hd hsmall)
  have hsub := h.PiN_subset hd hsmall
  have hlam := W6SeqData.lam_pos hd ν
  have hε := W6SeqData.epsNu_pos hd ν
  refine ⟨?_, ?_, fun ξ hξ => c6 ξ (hsub hξ), fun ξ hξ i w hw => c7 ξ (hsub hξ) i w hw, ?_⟩
  · -- `(bpW:w5:freq)` with `M_ω + M_Ω ≤ M_{ν+1}` (step `il-lip`)
    refine ⟨h.w6StageTail + 3 * d.eps ν, d.Mnu ν - h.MO + 6 * π * d.eps ν / d.lam ν,
      h.MO + 3 * d.eps ν / d.lam ν, (c11 hlam).w6mono hsub le_rfl, ?_⟩
    have h1 := W6SeqData.lip_growth_le hd hsmall ν
    have h2 := W6SeqData.M_growth_le hd ν
    have e : d.Mnu ν - h.MO + 6 * π * d.eps ν / d.lam ν + (h.MO + 3 * d.eps ν / d.lam ν) =
        d.Mnu ν + (6 * π + 3) * d.eps ν / d.lam ν := by ring
    have e2 : d.Mnu ν * (1 + 1 / 2 ^ (ν + 2)) = d.Mnu ν + d.Mnu ν / 2 ^ (ν + 2) := by ring
    rw [e]
    linarith
  · -- `(bpW:w6:melnikov)` at level `α_{ν+1}` on `Π_{ν+1}` (step `il-div`)
    intro ξ hξ k l hkl
    have hξP : ξ ∈ Pi := hsub hξ
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
      have e : ∑ i, (((0 : Fin 2 → ℤ) i : ℤ) : ℝ) * h.omN hd hsmall ξ i = 0 := by simp
      rw [e, zero_add]
      exact hk0 ξ hξ l hl
    · by_cases hK : kAbs k ≤ d.K ν
      · obtain ⟨b₀, b₁, hb0, hb1, hbs, hbb, -⟩ := h.omN_inc hd hsmall
        have hK1 : 1 ≤ d.K ν :=
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans (W6SeqData.two_pow_le_K hd ν)
        have hω : ‖h.omN hd hsmall ξ - ω ξ‖ ≤ 6 * π * d.eps ν := by
          have := hbb ξ hξP
          have : 0 ≤ d.lam ν * b₁ := mul_nonneg hlam.le hb1
          linarith
        exact w6_mel_perturb hkl.1 hK1 hK hε.le hω (h.OmN_inc_abs hd hsmall ξ hξP)
          (W6SeqData.div_arith hd hsmall ν) (h.mel ξ hξP k l hkl)
      · -- `|k| > K_ν`: by construction of `Π_{ν+1}`
        push Not at hK
        have hn := hξ.2
        simp only [Set.mem_iUnion, not_exists] at hn
        by_contra hlt
        push Not at hlt
        exact hn k l ⟨hkl, hK⟩ ⟨hξP, hlt⟩
  · -- `|X_{P_{ν+1}}|^{λ_{ν+1}}_{r_{ν+1}, D_{ν+1}} ≤ ε_{ν+1}` (step `il-err`)
    have e : d.eps ν ^ 2 / (d.alpha ν * d.sigma ν ^ stepExpT w6Tau * d.etaNu ν ^ 2) =
        d.etaNu ν * d.eps ν := w6_newerror_eq hd ν
    have hb : stepC2 w6Tau * (d.eps ν ^ 2 / (d.alpha ν * d.sigma ν ^ stepExpT w6Tau *
        d.etaNu ν ^ 2) + d.etaNu ν * d.eps ν) = d.eps (ν + 1) := by
      rw [W6SeqData.eps_succ, e]
      unfold w6C2
      ring
    exact c8.mono_lam hsub subset_rfl (W6SeqData.lam_succ_le hd ν) hb.le

/-- **Stage `ν+1`, with reality** (conditional helper; not the label): if W5's reality clause
`W6StepReal` holds, all hypotheses of `bpW:w6:iter-lemma` hold at stage `ν+1`. -/
theorem next_stage_of_stepReal (hR : W6StepReal)
    (hk0 : W6Mel0 (d.alpha (ν + 1)) (h.PiN hd hsmall) (fun ξ => w6Om7 (h.OmN hd hsmall ξ))) :
    W6Stage d (ν + 1) (h.PiN hd hsmall) (h.omN hd hsmall) (h.OmN hd hsmall)
      (h.PN hd hsmall) (h.XN hd hsmall) := by
  have := factRPos hd ν
  refine ⟨h.next_core hd hsmall hk0, fun ξ hξ w hw hwr => ?_⟩
  exact hR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.stageStepHyp hd hsmall).hyp ξ
    (h.PiN_subset hd hsmall hξ) (StepPhase.ofK w) hw hwr

/-- **Stage `ν+1`** (`bpW:w6:iter-lemma`): given the conditions with `k = 0` at stage `ν+1` on
`Π_{ν+1}` (supplied by `bpW:w6:k0`), all hypotheses of the lemma hold at stage `ν+1`, including the
reality of `P_{ν+1}` (W5's reality clause, `w6StepReal_holds`). -/
theorem next_stage
    (hk0 : W6Mel0 (d.alpha (ν + 1)) (h.PiN hd hsmall) (fun ξ => w6Om7 (h.OmN hd hsmall ξ))) :
    W6Stage d (ν + 1) (h.PiN hd hsmall) (h.omN hd hsmall) (h.OmN hd hsmall)
      (h.PN hd hsmall) (h.XN hd hsmall) :=
  h.next_stage_of_stepReal hd hsmall w6StepReal_holds hk0

/-- **Iterative lemma** (blueprint `bpW:w6:iter-lemma`). At stage `ν`, with `ε₀ ≤ γ₀ α₀ σ₀^t`:
`q_ν ≤ γ₀ 2^{-ν}`, `q_{ν+1} ≤ q_ν/4`; W5's step applies (`W6Stage.stageStepHyp`) and gives
`Φ_{ν+1} : D_{ν+1} → D_ν`; given the conditions with `k = 0` at stage `ν+1`, all hypotheses hold at
stage `ν+1` (`W6Stage`, including the reality of `P_{ν+1}`); and the bounds on
`Φ_{ν+1} - id`, `DΦ_{ν+1} - I`, `ω_{ν+1} - ω_ν`, `Ω_{ν+1} - Ω_ν`. -/
theorem w6IterLemma :
    (d.qNu ν ≤ w6Gamma0 / 2 ^ ν ∧ d.qNu (ν + 1) ≤ d.qNu ν / 4) ∧
    (∀ ξ ∈ Pi, ∀ w ∈ stepDomain (d.rNu ν) (d.s (ν + 1)) (d.rNu (ν + 1)),
      StepPhase.toK (h.PhiN hd hsmall ξ w) ∈ kamDomain (d.s ν - 4 * d.sigma ν)
        (2 * d.etaNu ν * d.rNu ν) ∧
      StepPhase.toK (h.PhiN hd hsmall ξ w) ∈ d.domNu ν) ∧
    (W6Mel0 (d.alpha (ν + 1)) (h.PiN hd hsmall) (fun ξ => w6Om7 (h.OmN hd hsmall ξ)) →
      W6Stage d (ν + 1) (h.PiN hd hsmall) (h.omN hd hsmall) (h.OmN hd hsmall)
        (h.PN hd hsmall) (h.XN hd hsmall)) ∧
    (∃ A₀ A₁ B₀ B₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      A₀ + d.lam ν * A₁ ≤ 2 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) ∧
      B₀ + d.lam ν * B₁ ≤ 16 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) / d.sigma ν ∧
      16 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) / d.sigma ν ≤ 1 / 2 ^ (ν + 2) ∧
      ∀ ξ ∈ Pi, ∀ ζ ∈ Pi, ∀ w ∈ stepDomain (d.rNu ν) (d.s (ν + 1)) (d.rNu (ν + 1)),
        haveI := factRPos hd ν
        h.PhiN hd hsmall ξ w =
          w + stepEmbedCLM 1 1 (3 / 2) w6_iter_one_le_three_halves (d.rNu ν)
            (h.PsiN hd hsmall ξ w) ∧
        fderiv ℂ (h.PhiN hd hsmall ξ) w = ContinuousLinearMap.id ℂ _ +
          (stepEmbedCLM 1 1 (3 / 2) w6_iter_one_le_three_halves (d.rNu ν)).comp
            (fderiv ℂ (h.PsiN hd hsmall ξ) w) ∧
        ‖h.PsiN hd hsmall ξ w‖ ≤ A₀ ∧
        ‖h.PsiN hd hsmall ξ w - h.PsiN hd hsmall ζ w‖ ≤ A₁ * ‖ξ - ζ‖ ∧
        ‖fderiv ℂ (h.PsiN hd hsmall ξ) w‖ ≤ B₀ ∧
        ‖fderiv ℂ (h.PsiN hd hsmall ξ) w - fderiv ℂ (h.PsiN hd hsmall ζ) w‖ ≤ B₁ * ‖ξ - ζ‖) ∧
    (∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧ b₀ + d.lam ν * b₁ ≤ 6 * π * d.eps ν ∧
      (∀ ξ ∈ Pi, ‖h.omN hd hsmall ξ - ω ξ‖ ≤ b₀) ∧
      ∀ ξ ∈ Pi, ∀ ζ ∈ Pi,
        ‖(h.omN hd hsmall ξ - ω ξ) - (h.omN hd hsmall ζ - ω ζ)‖ ≤ b₁ * ‖ξ - ζ‖) ∧
    (∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ c₀ + d.lam ν * c₁ ≤ 3 * d.eps ν ∧
      (∀ ξ ∈ Pi, ∀ n : ℕ,
        normLab n ^ (1 / 2 : ℝ) * |w6Om7 (h.OmN hd hsmall ξ) n - w6Om7 (Ω ξ) n| ≤ c₀) ∧
      ∀ ξ ∈ Pi, ∀ ζ ∈ Pi, ∀ n : ℕ, normLab n ^ (1 / 2 : ℝ) *
        |(w6Om7 (h.OmN hd hsmall ξ) n - w6Om7 (Ω ξ) n) -
          (w6Om7 (h.OmN hd hsmall ζ) n - w6Om7 (Ω ζ) n)| ≤ c₁ * ‖ξ - ζ‖) :=
  ⟨W6SeqData.w6Iter_q_bounds hd hsmall ν, h.phiN_mapsTo hd hsmall, h.next_stage hd hsmall,
    h.phiN_bounds hd hsmall, h.omN_inc hd hsmall, h.OmN_inc hd hsmall⟩

end W6Stage

end KAM.Wave
