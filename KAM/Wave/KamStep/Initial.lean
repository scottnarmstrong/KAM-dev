/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.InitialBound
public import KAM.Wave.KamStep.TaylorEst
public import KAM.Wave.Analytic.Cauchy
public import KAM.Wave.Measure.Coords
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The initial perturbation (blueprint-W `bpW:w5:initial`)

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:initial` (KP96 §7, Step 3), steps `i-par`, `i-freq`.

* `differentiableAt_aaXP_param`: for fixed `w`, `ζ ↦ X_{P_ζ}(w)` is holomorphic where `𝒜_ζ(w)` is
  defined and in `B_{ρ₁}` (step `i-par`: `X_{Q̃}` does not depend on `ζ`; the explicit formula).
* `aaXP_lipschitz`: the Lipschitz constant `4ε_in/ρ_ξ` (Cauchy estimate `lipschitz_of_margin` on
  the `ρ_ξ`-polydisc for `|ξ - ξ'| < ρ_ξ/2`, the trivial bound `2ε_in` otherwise).
* **`initialPerturbation`**: the proposition (`a = p = 1`): `P_ξ ∈ 𝒮_{p+1}(D(s,r))` is a real periodic
  family on `Π`, `|X_P|^λ_{r,D(s,r)} ≤ ε_in(1 + 4λ/ρ_ξ)` for every `λ ≥ 0` (as `FamBound`), the
  frequencies `ω⁰, Ω⁰_{j+2}` satisfy `bpW:w4:freq` with the constants of `bpW:w4:wave`, and
  `|ω⁰(ξ) - ω⁰(ξ')| ≤ N_A |ξ - ξ'|`.

Hypotheses: those of the blueprint (`0 < s ≤ 1/8`, `0 < r ≤ 1`, `t > 0`, `ρ_ξ > 0`, the
`ρ_ξ`-neighbourhood condition on `Π`, `c_A(t+r²) < ρ₁²`); the premises `0 < s` and `r ≤ 1` are not
needed by the proof and are omitted (the statement is the stronger one).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex Metric

/-- The complexification `ξ ↦ (ξ_i : ℂ)` of a real parameter. -/
abbrev aaOfReal (ξ : Fin 2 → ℝ) : Fin 2 → ℂ := fun i => (ξ i : ℂ)

theorem norm_aaOfReal_sub (ξ ξ' : Fin 2 → ℝ) : ‖aaOfReal ξ - aaOfReal ξ'‖ = ‖ξ - ξ'‖ := by
  have h : ∀ i, ‖(aaOfReal ξ - aaOfReal ξ') i‖ = ‖(ξ - ξ') i‖ := fun i => by
    simp [aaOfReal, ← Complex.ofReal_sub, Complex.norm_real]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [h]; exact norm_le_pi_norm _ i
  · rw [← h]; exact norm_le_pi_norm _ i

/-! ### Holomorphy in the parameter -/

theorem differentiableAt_aaS_param {ζ : Fin 2 → ℂ} {w : KamPhase} {i : Fin 2}
    (h : 0 < (ζ i + w.2.1 i).re) : DifferentiableAt ℂ (fun ζ : Fin 2 → ℂ => aaS ζ w i) ζ :=
  differentiableAt_aaSqrt_comp (g := fun ζ : Fin 2 → ℂ => ζ i + w.2.1 i) (by fun_prop) h

theorem differentiableAt_aaMap_param (a p : ℝ) {ζ : Fin 2 → ℂ} {w : KamPhase}
    (h : ∀ i, 0 < (ζ i + w.2.1 i).re) :
    DifferentiableAt ℂ (fun ζ : Fin 2 → ℂ => aaMap a p ζ w) ζ := by
  have hJ := (aaMap_differentiableOn a p (ζ, w) h).differentiableAt
    (isOpen_aaDomJ.mem_nhds h)
  have hpair : DifferentiableAt ℂ (fun ζ : Fin 2 → ℂ => (ζ, w)) ζ :=
    differentiableAt_id.prodMk (differentiableAt_const w)
  exact (hJ.comp ζ hpair :)

/-- `ζ ↦ D𝒜_ζ(w)⁻¹ F(ζ)` is holomorphic where `F` is. -/
theorem differentiableAt_aaDerInv_param (a q : ℝ) {ζ : Fin 2 → ℂ} {w : KamPhase}
    (hw : ∀ i, 0 < (ζ i + w.2.1 i).re) {F : (Fin 2 → ℂ) → BirkSpace}
    (hF : DifferentiableAt ℂ F ζ) :
    DifferentiableAt ℂ (fun ζ => aaDerInv a q ζ w (F ζ)) ζ := by
  simp_rw [aaDerInv_eq]
  have hev : ∀ l : BirkIdx, DifferentiableAt ℂ (fun ζ => F ζ l) ζ := fun l =>
    (aaEv l).differentiableAt.comp ζ hF
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  refine DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk ?_ ?_))
  · refine differentiableAt_pi.2 fun i => ?_
    have hs := differentiableAt_aaS_param (hw i)
    have hs0 := aaS_ne_zero (hw i)
    have h1 := hev (false, modeIdx i)
    have h2 := hev (true, modeIdx i)
    have hω : (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a q (modeIdx i))
    have hden : 4 * (Real.pi : ℂ) * I * aaS ζ w i * (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi)
        Complex.I_ne_zero) hs0) hω
    fun_prop (disch := assumption)
  · refine differentiableAt_pi.2 fun i => ?_
    have hs := differentiableAt_aaS_param (hw i)
    have h1 := hev (false, modeIdx i)
    have h2 := hev (true, modeIdx i)
    have hω : (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a q (modeIdx i))
    fun_prop (disch := assumption)
  · exact (aaUnshift.comp ((ContinuousLinearMap.fst ℂ _ _).comp birkZinv)).differentiableAt.comp
      ζ hF
  · exact (aaUnshift.comp ((ContinuousLinearMap.snd ℂ _ _).comp birkZinv)).differentiableAt.comp
      ζ hF

/-- **Step `i-par`**: for fixed `w`, `ζ ↦ X_{P_ζ}(w)` is holomorphic at `ζ` when `𝒜_ζ(w)` is defined
and lies in `B_{ρ₁}`. -/
theorem differentiableAt_aaXP_param (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)
    {ζ : Fin 2 → ℂ} {w : KamPhase} (hw : ∀ i, 0 < (ζ i + w.2.1 i).re)
    (hB : aaMap a p ζ w ∈ birkBall1 m p) :
    DifferentiableAt ℂ (fun ζ => aaXP m hm ha hp ζ w) ζ := by
  unfold aaXP
  refine (differentiableAt_const _).add (differentiableAt_aaDerInv_param a (p + 1) hw ?_)
  have hmap := differentiableAt_aaMap_param a p hw
  have h1 : DifferentiableAt ℂ (fun ζ => birkHamNorX m hm ha hp (aaMap a p ζ w)) ζ :=
    ((birkHamNor_classA ha hp).analytic_field _ trivial).differentiableAt.comp ζ hmap
  have hK : AnalyticAt ℂ (aaXKext m hm ha hp) (aaMap a p ζ w) :=
    aaXKext_analyticOnNhd (m := m) (hm := hm) ha hp (aaMap a p ζ w) hB
  have h2 : DifferentiableAt ℂ (fun ζ => aaXKext m hm ha hp (aaMap a p ζ w)) ζ :=
    DifferentiableAt.comp (g := aaXKext m hm ha hp) (f := fun ζ => aaMap a p ζ w) ζ
      hK.differentiableAt hmap
  exact h1.add h2

/-! ### The parameter Lipschitz bound -/

theorem aa_kamNorm_sub_le {r : ℝ} (hr : 0 < r) (W W' : KamPhase) :
    kamNorm r (W - W') ≤ kamNorm r W + kamNorm r W' := by
  have h := kamNorm_add_le hr W (-W')
  have e : kamNorm r (-W') = kamNorm r W' := by unfold kamNorm; simp
  rw [sub_eq_add_neg]
  linarith

theorem aaEpsIn_nonneg (m : ℝ) (hm : 0 < m) {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ aaEpsIn m r t := by
  unfold aaEpsIn
  have hC := waveCubicConst_pos (p := 1) (by norm_num)
  have hCF := birkCF_pos m hm (by norm_num : (1 : ℝ) / 2 ≤ 1)
  have h5 : 0 ≤ (aaCA * (t + r ^ 2)) ^ ((5 : ℝ) / 2) :=
    Real.rpow_nonneg (by unfold aaCA; positivity) _
  have h3 : 0 ≤ 3 / r + 2 * Real.sqrt (t + r ^ 2) / r ^ 2 := by positivity
  have h1 : 0 ≤ (1 + 2 * waveCubicConst 1) * r ^ 2 := mul_nonneg (by linarith) (sq_nonneg r)
  have h2 : 0 ≤ 66 * waveCubicConst 1 * birkCF m 1 :=
    (mul_pos (mul_pos (by norm_num) hC) hCF).le
  exact add_nonneg h1 (mul_nonneg (mul_nonneg h2 h5) h3)

section Lip

variable (m : ℝ) (hm : 0 < m) {s r t ρξ : ℝ} (hs : s ≤ 1 / 8) (hr : 0 < r) (ht : 0 < t)
  (hρξ : 0 < ρξ) {Par : Set (Fin 2 → ℝ)}
  (hPar : ∀ ζ : Fin 2 → ℂ, (∃ ξ ∈ Par, ‖ζ - aaOfReal ξ‖ < ρξ) →
    (∀ i, 2 * r ^ 2 ≤ (ζ i).re) ∧ ‖ζ‖ ≤ t)
  (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2)
include hs hr ht hρξ hPar hρ₁

omit hρξ in
theorem aaXP_bound_nbhd {ζ : Fin 2 → ℂ} (hζ : ∃ ξ ∈ Par, ‖ζ - aaOfReal ξ‖ < ρξ) {w : KamPhase}
    (hw : w ∈ kamDomain s r) :
    kamNorm r (aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) ζ w) ≤ aaEpsIn m r t :=
  kamNorm_aaXP_le m hm hs hr ht hρ₁ ζ (hPar ζ hζ).2 (hPar ζ hζ).1 hw


/-- **Step `i-par`**: `|X_{P_ξ}(w) - X_{P_ξ'}(w)|_{2,r} ≤ (4 ε_in/ρ_ξ) |ξ - ξ'|` on `Π`. -/
theorem aaXP_lipschitz {ξ ξ' : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hξ' : ξ' ∈ Par) {w : KamPhase}
    (hw : w ∈ kamDomain s r) :
    kamNorm r (aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ) w -
        aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ') w) ≤
      4 * aaEpsIn m r t / ρξ * ‖ξ - ξ'‖ := by
  have hε := aaEpsIn_nonneg m hm hr ht.le
  by_cases hd : ρξ / 2 ≤ ‖ξ - ξ'‖
  · have h1 := aaXP_bound_nbhd m hm hs hr ht hPar hρ₁ (ζ := aaOfReal ξ)
      ⟨ξ, hξ, by simpa using hρξ⟩ hw
    have h2 := aaXP_bound_nbhd m hm hs hr ht hPar hρ₁ (ζ := aaOfReal ξ')
      ⟨ξ', hξ', by simpa using hρξ⟩ hw
    refine (aa_kamNorm_sub_le hr _ _).trans ?_
    have : 2 * aaEpsIn m r t ≤ 4 * aaEpsIn m r t / ρξ * ‖ξ - ξ'‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρξ]
      nlinarith
    linarith
  · push Not at hd
    have : Fact (0 < r) := ⟨hr⟩
    set f : (Fin 2 → ℂ) → StepPhase r := fun ζ => kamToStep r
      (aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) ζ w) with hf
    have hV : ∀ z ∈ ball (aaOfReal ξ) ρξ, ∃ ξ₀ ∈ Par, ‖z - aaOfReal ξ₀‖ < ρξ := fun z hz =>
      ⟨ξ, hξ, by rwa [mem_ball, dist_eq_norm] at hz⟩
    have hdiff : DifferentiableOn ℂ f (ball (aaOfReal ξ) ρξ) := fun z hz => by
      obtain ⟨hre, hzt⟩ := hPar z (hV z hz)
      obtain ⟨hpos, -⟩ := aaMap_domain hs hr ht z hzt hre hw
      have hB := aaMap_mem_birkBall1 m hm hs hr ht hρ₁ z hzt hre hw
      exact ((kamToStep r).differentiableAt.comp z (differentiableAt_aaXP_param m hm
        (zero_le_one' ℝ) (by norm_num) (fun i => lt_trans (by positivity) (hpos i))
        hB)).differentiableWithinAt
    have hbd : ∀ z ∈ ball (aaOfReal ξ) ρξ, ‖f z‖ ≤ aaEpsIn m r t := fun z hz => by
      rw [stepPhase_norm_eq]
      exact aaXP_bound_nbhd m hm hs hr ht hPar hρ₁ (hV z hz) hw
    have hlip := lipschitz_of_margin (by positivity : (0 : ℝ) < ρξ / 2) hε isOpen_ball hdiff hbd
      (convex_ball (aaOfReal ξ) (ρξ / 2)) (fun z hz => by
        intro y hy
        rw [mem_ball, dist_eq_norm] at hy hz ⊢
        have := norm_add_le (y - z) (z - aaOfReal ξ)
        simp only [sub_add_sub_cancel] at this
        linarith) (aaOfReal ξ) (mem_ball_self (by positivity)) (aaOfReal ξ')
      (by rw [mem_ball, dist_eq_norm, norm_sub_rev, norm_aaOfReal_sub]; exact hd)
    rw [norm_aaOfReal_sub] at hlip
    have e : ‖f (aaOfReal ξ) - f (aaOfReal ξ')‖ =
        kamNorm r (aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ) w -
          aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ') w) := by
      rw [hf, ← map_sub, stepPhase_norm_eq]; rfl
    rw [e] at hlip
    refine hlip.trans ?_
    have : aaEpsIn m r t / (ρξ / 2) ≤ 4 * aaEpsIn m r t / ρξ := by
      rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hρξ]; linarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

end Lip

/-! ### The proposition -/

/-- **The initial perturbation** (`bpW:w5:initial`, `a = p = 1`, KP96 §7 Step 3): under the
hypotheses of the blueprint, `P_ξ ∈ 𝒮_{p+1}(D(s,r))` (field `X_{P_ξ}`) is a real, periodic family on
`Π`, `|X_P|^λ_{r,D(s,r)} ≤ ε_in (1 + 4λ/ρ_ξ)` for every `λ ≥ 0`, the frequencies `ω⁰, Ω⁰_{j+2}`
(`= waveFreqTan`, `waveFreqNor`, Definition `bpW:w7:omega0`) satisfy `bpW:w4:freq` with the
constants of `bpW:w4:wave` (for any bound `B` of `|⟨b,ξ⟩|` on `Π`), and
`|ω⁰(ξ) - ω⁰(ξ')| ≤ N_A |ξ - ξ'|`. -/
theorem initialPerturbation (m : ℝ) (hm : 0 < m) {s r t ρξ : ℝ} (hs : s ≤ 1 / 8) (hr : 0 < r)
    (ht : 0 < t) (hρξ : 0 < ρξ) (Par : Set (Fin 2 → ℝ))
    (hPar : ∀ ζ : Fin 2 → ℂ, (∃ ξ ∈ Par, ‖ζ - aaOfReal ξ‖ < ρξ) →
      (∀ i, 2 * r ^ 2 ≤ (ζ i).re) ∧ ‖ζ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) :
    (∀ ξ ∈ Par, IsSmoothing (p := 1) (pb := 1 + 1) (zero_le_one' ℝ) (by norm_num) (kamDomain s r)
      (aaPfun m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ))
      (aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ))) ∧
    (∀ ξ ∈ Par, ∀ k : Fin 2, ∀ w ∈ kamDomain s r,
      aaPfun m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ) (w + stepTau k) =
        aaPfun m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ) w) ∧
    (∀ ξ ∈ Par, ∀ w ∈ kamDomain s r, StepReal w →
      (aaPfun m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ) w).im = 0) ∧
    (∀ lam : ℝ, 0 ≤ lam → FamBound Par (kamDomain s r) r lam
      (aaEpsIn m r t * (1 + 4 * lam / ρξ))
      (fun ξ => aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ))) ∧
    (∀ B : ℝ, 0 ≤ B → (∀ ξ ∈ Par, |waveB m hm ξ| ≤ B) →
      HomFreqHyp1 Par (waveFreqTan m hm) (waveFreqNor m hm) (m / 2 + 3 / (2 * Real.pi) * B)
        (waveMomega m hm) (waveMOmega m hm)) ∧
    (∀ ξ ξ' : Fin 2 → ℝ, dist (waveFreqTan m hm ξ) (waveFreqTan m hm ξ') ≤
      measNA m hm * dist ξ ξ') := by
  have hmem : ∀ ξ ∈ Par, (∀ i, 2 * r ^ 2 ≤ (aaOfReal ξ i).re) ∧ ‖aaOfReal ξ‖ ≤ t := fun ξ hξ =>
    hPar _ ⟨ξ, hξ, by simpa using hρξ⟩
  refine ⟨fun ξ hξ => aaP_isSmoothing hs hr ht hρ₁ _ (hmem ξ hξ).2 (hmem ξ hξ).1,
    fun ξ _ k w _ => aaPfun_add_tau _ _ _ _ k, fun ξ hξ w hw hreal => ?_, fun lam hlam => ?_,
    fun B hB0 hB => homFreqHyp1_wave m hm Par hB0 hB, fun ξ ξ' => measNA_dist_le m hm ξ ξ'⟩
  · obtain ⟨hpos, -⟩ := aaMap_domain hs hr ht _ (hmem ξ hξ).2 (hmem ξ hξ).1 hw
    have hB := aaMap_mem_birkBall1 m hm hs hr ht hρ₁ _ (hmem ξ hξ).2 (hmem ξ hξ).1 hw
    exact aaPfun_real _ _ ξ w hreal (fun i => by
      have := hpos i
      simp only [aaOfReal, Complex.add_re, Complex.ofReal_re] at this
      exact lt_trans (by positivity) this) hB
  · have hε : 0 ≤ aaEpsIn m r t := aaEpsIn_nonneg m hm hr ht.le
    refine ⟨aaEpsIn m r t, 4 * aaEpsIn m r t / ρξ, hε, by positivity, le_of_eq (by ring),
      fun ξ hξ w hw => aaXP_bound_nbhd m hm hs hr ht hPar hρ₁ ⟨ξ, hξ, by simpa using hρξ⟩ hw,
      fun ξ hξ ζ hζ w hw => aaXP_lipschitz m hm hs hr ht hρξ hPar hρ₁ hξ hζ hw⟩

end KAM.Wave

end
