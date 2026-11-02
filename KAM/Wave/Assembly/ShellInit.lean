/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellData
public import KAM.Wave.Assembly.UpstreamW6
public import KAM.Wave.Iteration.PrepStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: shell data for the initial perturbation and the preparatory step
(blueprint `bpW:w8:shell-data` (iii), (iv))

Blueprint label `bpW:w8:shell-data` (milestone W8), parts (iii), (iv).

The W8 constants are evaluated at the W5–W6 constants `w8Upstream m hm` (`γ = w6Gamma m hm`,
`γ₁ = w6Gamma1 m hm`, `c_F`, `c^♮_F`); `w8T0W m hm` is the resulting `t₀`.

* (iii) `w8_shellData_init`: the hypotheses of Proposition `bpW:w5:initial` hold for shell `n`
  (`s = 1/8`, `r = r_n`, `t = t_n`, `ρ_ξ = α_n/2`, `Π = Π_n`): `0 < r_n ≤ 1`, `t_n > 0`, `ρ_ξ > 0`,
  every `ζ ∈ ℂ²` within `ρ_ξ` of a point of `Π_n` has `Re ζ_i ≥ 2r_n²` and `|ζ| ≤ t_n`,
  `c_A (t_n + r_n²) < ρ₁²`; and `ε_in (1 + 4λ/ρ_ξ) = ε_in (1 + 8/M) ≤ ε^♯_n` for `λ = α_n/M`
  (`ε_in = w8EpsIn`, the formula of `bpW:w5:initial`). The last sentence of (iii) (the
  bound on `X_P`) consumes the conclusion of `bpW:w5:initial`; it is the conditional helper
  `w8_famBound_sharp_of_initial` (any family bounded by `ε_in(1 + 4λ/ρ_ξ)` is bounded by `ε^♯_n`).
* (iv) `w8_shellData_prep`: the hypotheses of Lemma `bpW:w6:prep-step` that concern the shell
  data (`Π_n` Borel in `{|ξ| ≤ 1/2}`, `0 < α_n ≤ α₀`, `r_n > 0`, `0 < ε^♯_n ≤ γ α_n`) and
  `c_A(t_n + r_n²) < ρ₁²` (Remark `bpW:w6:to-w8`). The bundle `W6PrepHyp` for shell `n`
  (`W8ShellPrep`) is assembled from the properties of the perturbation `P` supplied by
  `bpW:w5:initial` by the conditional helper `w8ShellPrep_of_initial`.

Interface (W5-AA, `KAM/Wave/KamStep/Initial.lean`, not in this base): `w8EpsIn m r t` is the
formula of `aaEpsIn m r t` (`w8CKp m = 66 C_* C_F`, `w8cA = aaCA = 2200`), `w8Rho1 m = birkRho1 m 1`
(both `1/(2√(40 C_F))`, definitionally), and the `ζ`-condition of (iii) is the hypothesis `hPar` of
`initialPerturbation` with `aaOfReal ξ = fun i => (ξ i : ℂ)`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

/-- `t₀` of `bpW:w8:const` for the W5–W6 constants `w8Upstream m hm`. -/
abbrev w8T0W (m : ℝ) (hm : 0 < m) : ℝ := w8T0 m hm (w8Upstream m hm)

/-- `ε_in = (1 + 2C_*) r² + C'_K (c_A(t + r²))^{5/2} (3/r + 2√(t + r²)/r²)` of Proposition
`bpW:w5:initial`. -/
def w8EpsIn (m r t : ℝ) : ℝ :=
  (1 + 2 * w8CStar) * r ^ 2 + w8CKp m * (w8cA * (t + r ^ 2)) ^ (5 / 2 : ℝ) *
    (3 / r + 2 * Real.sqrt (t + r ^ 2) / r ^ 2)

/-- The hypotheses of Lemma `bpW:w6:prep-step` for shell `n` (`Π = Π_n`, `α = α_n`, `r = r_n`,
`ε = ε^♯_n`), for a perturbation `P` with field `X`. -/
abbrev W8ShellPrep (m : ℝ) (hm : 0 < m) (n : ℕ) (P : (Fin 2 → ℝ) → KamPhase → ℂ)
    (X : (Fin 2 → ℝ) → KamPhase → KamPhase) : Prop :=
  W6PrepHyp m hm (w8Pi (w8T0W m hm) n) (w8alpha (w8T0W m hm) n) (w8rn (w8T0W m hm) n)
    (w8epsSharp m hm (w8T0W m hm) n) P X

/-- Step `stepW:w8:sd-init` in the variable `x = t^{1/4}`: `ε_in(r = x³, t = x⁴) ≤ E₁ x⁶`
for `0 < x ≤ 1`. -/
theorem w8EpsIn_le_pow {m x : ℝ} (hm : 0 < m) (hx : 0 < x) (hx1 : x ≤ 1) :
    w8EpsIn m (x ^ 3) (x ^ 4) ≤ w8E1 m * x ^ 6 := by
  have hcA : (0 : ℝ) < w8cA := by unfold w8cA; norm_num
  have hCs : 0 ≤ w8CStar := waveCubicConst_nonneg 1
  have hCK : 0 ≤ w8CKp m := by
    have := w8CF_pos hm; unfold w8CKp; positivity
  have e2 : (x ^ 3) ^ 2 = x ^ 6 := by ring
  have hsum : x ^ 4 + x ^ 6 ≤ 2 * x ^ 4 := by
    have : x ^ 6 ≤ x ^ 4 := pow_le_pow_of_le_one hx.le hx1 (by norm_num)
    linarith
  -- `(c_A (t + r²))^{5/2} ≤ (2c_A)^{5/2} x^{10}`
  have hA : (w8cA * (x ^ 4 + x ^ 6)) ^ (5 / 2 : ℝ) ≤ (2 * w8cA) ^ (5 / 2 : ℝ) * x ^ 10 := by
    have h10 : (x ^ 4) ^ (5 / 2 : ℝ) = x ^ 10 := by
      rw [← Real.rpow_natCast_mul hx.le]; norm_num
    calc (w8cA * (x ^ 4 + x ^ 6)) ^ (5 / 2 : ℝ) ≤ (2 * w8cA * x ^ 4) ^ (5 / 2 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num); nlinarith
      _ = (2 * w8cA) ^ (5 / 2 : ℝ) * x ^ 10 := by
          rw [Real.mul_rpow (by positivity) (by positivity), h10]
  -- `√(t + r²) ≤ √2 x²`
  have hS : Real.sqrt (x ^ 4 + x ^ 6) ≤ Real.sqrt 2 * x ^ 2 := by
    calc Real.sqrt (x ^ 4 + x ^ 6) ≤ Real.sqrt (2 * (x ^ 2) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = Real.sqrt 2 * x ^ 2 := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hB : 3 / x ^ 3 + 2 * Real.sqrt (x ^ 4 + (x ^ 3) ^ 2) / (x ^ 3) ^ 2 ≤
      3 / x ^ 3 + 2 * Real.sqrt 2 / x ^ 4 := by
    rw [e2]
    have : 2 * Real.sqrt (x ^ 4 + x ^ 6) / x ^ 6 ≤ 2 * (Real.sqrt 2 * x ^ 2) / x ^ 6 := by gcongr
    have e : 2 * (Real.sqrt 2 * x ^ 2) / x ^ 6 = 2 * Real.sqrt 2 / x ^ 4 := by
      field_simp
    linarith
  have hB0 : 0 ≤ 3 / x ^ 3 + 2 * Real.sqrt (x ^ 4 + (x ^ 3) ^ 2) / (x ^ 3) ^ 2 := by positivity
  have hprod : (2 * w8cA) ^ (5 / 2 : ℝ) * x ^ 10 * (3 / x ^ 3 + 2 * Real.sqrt 2 / x ^ 4) ≤
      (2 * w8cA) ^ (5 / 2 : ℝ) * (6 * x ^ 6) := by
    have e : x ^ 10 * (3 / x ^ 3 + 2 * Real.sqrt 2 / x ^ 4) =
        3 * x ^ 7 + 2 * Real.sqrt 2 * x ^ 6 := by
      field_simp
    have h7 : x ^ 7 ≤ x ^ 6 := pow_le_pow_of_le_one hx.le hx1 (by norm_num)
    have hc : (0 : ℝ) ≤ (2 * w8cA) ^ (5 / 2 : ℝ) := by positivity
    rw [mul_assoc, e]
    apply mul_le_mul_of_nonneg_left _ hc
    nlinarith [pow_pos hx 6]
  unfold w8EpsIn
  rw [e2]
  have hA0 : 0 ≤ (w8cA * (x ^ 4 + x ^ 6)) ^ (5 / 2 : ℝ) := by positivity
  have hBB : 0 ≤ 3 / x ^ 3 + 2 * Real.sqrt 2 / x ^ 4 := by positivity
  have key : w8CKp m * (w8cA * (x ^ 4 + x ^ 6)) ^ (5 / 2 : ℝ) *
      (3 / x ^ 3 + 2 * Real.sqrt (x ^ 4 + x ^ 6) / x ^ 6) ≤
      w8CKp m * ((2 * w8cA) ^ (5 / 2 : ℝ) * (6 * x ^ 6)) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCK
    rw [e2] at hB hB0
    calc (w8cA * (x ^ 4 + x ^ 6)) ^ (5 / 2 : ℝ) *
          (3 / x ^ 3 + 2 * Real.sqrt (x ^ 4 + x ^ 6) / x ^ 6)
        ≤ (2 * w8cA) ^ (5 / 2 : ℝ) * x ^ 10 * (3 / x ^ 3 + 2 * Real.sqrt 2 / x ^ 4) :=
          mul_le_mul hA hB hB0 (by positivity)
      _ ≤ _ := hprod
  have : w8E1 m * x ^ 6 = (1 + 2 * w8CStar) * x ^ 6 +
      w8CKp m * ((2 * w8cA) ^ (5 / 2 : ℝ) * (6 * x ^ 6)) := by
    unfold w8E1; ring
  linarith

variable {m : ℝ} (hm : 0 < m)

/-- `t_n = x⁴`, `r_n = x³`, `t_n^{3/2} = x⁶` for `x = t_n^{1/4}`. -/
theorem w8tn_quarter_pow {t : ℝ} (ht : 0 < t) :
    t = (t ^ (1 / 4 : ℝ)) ^ 4 ∧ t ^ (3 / 4 : ℝ) = (t ^ (1 / 4 : ℝ)) ^ 3 ∧
      t ^ (3 / 2 : ℝ) = (t ^ (1 / 4 : ℝ)) ^ 6 := by
  have h : ∀ k : ℕ, (t ^ (1 / 4 : ℝ)) ^ k = t ^ ((1 / 4 : ℝ) * k) := fun k => by
    rw [Real.rpow_mul ht.le, Real.rpow_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rw [h]; norm_num
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- Step `stepW:w8:sd-init`: `ε_in(r_n, t_n) ≤ E₁ t_n^{3/2}` for `t₀ = w8T0W m hm`. -/
theorem w8EpsIn_shell_le (n : ℕ) :
    w8EpsIn m (w8rn (w8T0W m hm) n) (w8tn (w8T0W m hm) n) ≤
      w8E1 m * w8tn (w8T0W m hm) n ^ (3 / 2 : ℝ) := by
  obtain ⟨h1, -, -, h4, -⟩ := w8tn_facts hm (w8Upstream m hm) n
  set t := w8tn (w8T0W m hm) n
  obtain ⟨e4, e3, e6⟩ := w8tn_quarter_pow h1
  have hx : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos h1 _
  have hx1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one h1.le h4 (by norm_num)
  have := w8EpsIn_le_pow hm hx hx1
  rw [← e4] at this
  unfold w8rn
  rw [e3, e6]
  exact this

/-- `4λ/ρ_ξ = 8/M` for `λ = α_n/M`, `ρ_ξ = α_n/2`. -/
theorem w8lam_div_rhoXi (n : ℕ) :
    4 * (w8alpha (w8T0W m hm) n / w8M m hm) / w8rhoXi (w8T0W m hm) n = 8 / w8M m hm := by
  have hα := w8alpha_pos (w8T0_pos hm (w8Upstream m hm)) n
  have hM := w8M_pos hm
  unfold w8rhoXi
  field_simp
  ring

/-- `ε_in (1 + 4λ/ρ_ξ) ≤ ε^♯_n` (blueprint `bpW:w8:shell-data` (iii), Step `stepW:w8:sd-init`). -/
theorem w8EpsIn_shell_sharp (n : ℕ) :
    w8EpsIn m (w8rn (w8T0W m hm) n) (w8tn (w8T0W m hm) n) *
        (1 + 4 * (w8alpha (w8T0W m hm) n / w8M m hm) / w8rhoXi (w8T0W m hm) n) ≤
      w8epsSharp m hm (w8T0W m hm) n := by
  rw [w8lam_div_rhoXi hm n]
  have hM := w8M_pos hm
  have h := w8EpsIn_shell_le hm n
  have hp : 0 ≤ 1 + 8 / w8M m hm := by positivity
  calc _ ≤ w8E1 m * w8tn (w8T0W m hm) n ^ (3 / 2 : ℝ) * (1 + 8 / w8M m hm) :=
        mul_le_mul_of_nonneg_right h hp
    _ = _ := by unfold w8epsSharp w8E3; ring

/-- **Shell data (iii)** (blueprint `bpW:w8:shell-data` (iii), Step `stepW:w8:sd-init`): the
hypotheses of Proposition `bpW:w5:initial` hold with `s = 1/8`, `r = r_n`, `t = t_n`,
`ρ_ξ = α_n/2`, `Π = Π_n`, and `ε_in (1 + 4λ/ρ_ξ) ≤ ε^♯_n` for `λ = α_n/M`. -/
theorem w8_shellData_init (n : ℕ) :
    (w6S ≤ 1 / 8 ∧ 0 < w8rn (w8T0W m hm) n ∧ w8rn (w8T0W m hm) n ≤ 1) ∧
      0 < w8tn (w8T0W m hm) n ∧ 0 < w8rhoXi (w8T0W m hm) n ∧
      (∀ ζ : Fin 2 → ℂ, (∃ ξ ∈ w8Pi (w8T0W m hm) n,
          ‖ζ - (fun i => (ξ i : ℂ))‖ < w8rhoXi (w8T0W m hm) n) →
        (∀ i, 2 * w8rn (w8T0W m hm) n ^ 2 ≤ (ζ i).re) ∧ ‖ζ‖ ≤ w8tn (w8T0W m hm) n) ∧
      w8cA * (w8tn (w8T0W m hm) n + w8rn (w8T0W m hm) n ^ 2) < w8Rho1 m ^ 2 ∧
      w8EpsIn m (w8rn (w8T0W m hm) n) (w8tn (w8T0W m hm) n) *
          (1 + 4 * (w8alpha (w8T0W m hm) n / w8M m hm) / w8rhoXi (w8T0W m hm) n) ≤
        w8epsSharp m hm (w8T0W m hm) n := by
  set u := w8Upstream m hm
  have hT := w8T0_pos hm u
  obtain ⟨⟨h1, -, -⟩, -, hr1, hr2, -, -, hρa, hρb⟩ := w8_shellData_sizes hm u n
  have hα := w8alpha_pos hT n
  have hrn : 0 < w8rn (w8T0W m hm) n := Real.rpow_pos_of_pos h1 _
  have hcA : (0 : ℝ) < w8cA := by unfold w8cA; norm_num
  refine ⟨⟨by unfold w6S; norm_num, hrn, hr1⟩, h1, by unfold w8rhoXi; positivity, ?_, ?_,
    w8EpsIn_shell_sharp hm n⟩
  · rintro ζ ⟨ξ, hξ, hd⟩
    have hco := fun i => w8Pi_coord hξ i
    have hdi : ∀ i, ‖ζ i - (ξ i : ℂ)‖ < w8alpha (w8T0W m hm) n / 2 := fun i =>
      lt_of_le_of_lt (norm_le_pi_norm (ζ - fun i => (ξ i : ℂ)) i) hd
    refine ⟨fun i => ?_, ?_⟩
    · have h := Complex.abs_re_le_norm (ζ i - (ξ i : ℂ))
      have e : (ζ i - (ξ i : ℂ)).re = (ζ i).re - ξ i := by simp
      rw [e] at h
      have := (abs_le.1 h).1
      have := hdi i
      have := (hco i).1
      linarith
    · refine (pi_norm_le_iff_of_nonneg h1.le).2 fun i => ?_
      have h := norm_sub_norm_le (ζ i) (ξ i : ℂ)
      have e : ‖(ξ i : ℂ)‖ = ξ i := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hα.trans (hco i).1)]
      have := hdi i
      have := (hco i).2
      linarith
  · have h2 : w8rn (w8T0W m hm) n ^ 2 ≤ w8tn (w8T0W m hm) n := by
      have := (w8alpha_le hm u n).2; linarith
    have : w8cA * (w8tn (w8T0W m hm) n + w8rn (w8T0W m hm) n ^ 2) ≤
        2 * w8cA * w8tn (w8T0W m hm) n := by nlinarith
    have : 0 < w8Rho1 m ^ 2 := by have := w8Rho1_pos hm; positivity
    linarith

/-- (`bpW:w8:shell-data` (iii), last sentence; conditional helper on the conclusion of
`bpW:w5:initial`) A family whose fields satisfy `|X|^λ ≤ ε_in(1 + 4λ/ρ_ξ)` for every `λ ≥ 0`
satisfies `|X|^{α_n/M}_{r_n, V} ≤ ε^♯_n`. -/
theorem w8_famBound_sharp_of_initial {Par : Set (Fin 2 → ℝ)} {V : Set KamPhase}
    {X : (Fin 2 → ℝ) → KamPhase → KamPhase} (n : ℕ)
    (hX : ∀ lam : ℝ, 0 ≤ lam → FamBound Par V (w8rn (w8T0W m hm) n) lam
      (w8EpsIn m (w8rn (w8T0W m hm) n) (w8tn (w8T0W m hm) n) *
        (1 + 4 * lam / w8rhoXi (w8T0W m hm) n)) X) :
    FamBound Par V (w8rn (w8T0W m hm) n) (w8alpha (w8T0W m hm) n / w8M m hm)
      (w8epsSharp m hm (w8T0W m hm) n) X := by
  have hα := w8alpha_pos (w8T0_pos hm (w8Upstream m hm)) n
  have hM := w8M_pos hm
  have h := hX (w8alpha (w8T0W m hm) n / w8M m hm) (by positivity)
  exact h.famMono subset_rfl (w8EpsIn_shell_sharp hm n)

/-- **Shell data (iv)** (blueprint `bpW:w8:shell-data` (iv), Step `stepW:w8:sd-prep`): the
hypotheses of Lemma `bpW:w6:prep-step` on the shell data hold for shell `n` (`Π_n` Borel in
`{|ξ| ≤ 1/2}`, `0 < α_n ≤ α₀`, `r_n > 0`, `0 < ε^♯_n ≤ γ α_n`), and `c_A(t_n + r_n²) < ρ₁²`
(Remark `bpW:w6:to-w8`). -/
theorem w8_shellData_prep (n : ℕ) :
    MeasurableSet (w8Pi (w8T0W m hm) n) ∧ (∀ ξ ∈ w8Pi (w8T0W m hm) n, ‖ξ‖ ≤ 1 / 2) ∧
      0 < w8alpha (w8T0W m hm) n ∧ w8alpha (w8T0W m hm) n ≤ measAlpha0 m hm ∧
      0 < w8rn (w8T0W m hm) n ∧ 0 < w8epsSharp m hm (w8T0W m hm) n ∧
      w8epsSharp m hm (w8T0W m hm) n ≤ w6Gamma m hm * w8alpha (w8T0W m hm) n ∧
      w8cA * (w8tn (w8T0W m hm) n + w8rn (w8T0W m hm) n ^ 2) < w8Rho1 m ^ 2 := by
  set u := w8Upstream m hm
  have hT := w8T0_pos hm u
  obtain ⟨⟨h1, -, h3⟩, ⟨ha0, -⟩, -, -, -, heps, -, -⟩ := w8_shellData_sizes hm u n
  obtain ⟨-, -, -, -, hρ, -⟩ := w8_shellData_init hm n
  have ht2 : w8T0W m hm ≤ 1 / 2 := h3.trans (by norm_num)
  have hE := w8E3_pos hm
  refine ⟨w8Pi_measurableSet hT n, fun ξ hξ => w8Pi_subset_ball hT ht2 n hξ, w8alpha_pos hT n,
    ha0, Real.rpow_pos_of_pos h1 _, ?_, heps, hρ⟩
  unfold w8epsSharp
  exact mul_pos hE (Real.rpow_pos_of_pos h1 _)

/-- (`bpW:w8:shell-data` (iv); conditional helper on the conclusion of `bpW:w5:initial`) The
hypotheses of Lemma `bpW:w6:prep-step` for shell `n`, given a perturbation `P` with field `X` that
is a smoothing, periodic, real family on `Π_n` with `|X|^λ_{r_n, D(s, r_n)} ≤ ε_in(1 + 4λ/ρ_ξ)`
(the conclusion of `bpW:w5:initial` for the data of (iii)). -/
theorem w8ShellPrep_of_initial {P : (Fin 2 → ℝ) → KamPhase → ℂ}
    {X : (Fin 2 → ℝ) → KamPhase → KamPhase} (n : ℕ)
    (hsm : ∀ ξ ∈ w8Pi (w8T0W m hm) n, IsSmoothing (a := 1) (p := 1) (pb := 1 + 1) zero_le_one
      (by norm_num) (kamDomain w6S (w8rn (w8T0W m hm) n)) (P ξ) (X ξ))
    (hper : ∀ ξ ∈ w8Pi (w8T0W m hm) n, ∀ i, ∀ w ∈ kamDomain w6S (w8rn (w8T0W m hm) n),
      P ξ (w + stepTau i) = P ξ w)
    (hreal : ∀ ξ ∈ w8Pi (w8T0W m hm) n, ∀ w ∈ kamDomain w6S (w8rn (w8T0W m hm) n),
      StepReal w → (P ξ w).im = 0)
    (hX : ∀ lam : ℝ, 0 ≤ lam → FamBound (w8Pi (w8T0W m hm) n)
      (kamDomain w6S (w8rn (w8T0W m hm) n)) (w8rn (w8T0W m hm) n) lam
      (w8EpsIn m (w8rn (w8T0W m hm) n) (w8tn (w8T0W m hm) n) *
        (1 + 4 * lam / w8rhoXi (w8T0W m hm) n)) X) :
    W8ShellPrep m hm n P X := by
  obtain ⟨hmeas, hsub, hα, hα0, hr, hε, hεγ, -⟩ := w8_shellData_prep hm n
  have hb := w8_famBound_sharp_of_initial hm n hX
  exact
  { meas := hmeas
    sub := hsub
    hα := hα
    hα0 := hα0
    hr := hr
    smooth := fun ξ hξ => hsm ξ hξ.1
    per := fun ξ hξ => hper ξ hξ.1
    real := fun ξ hξ => hreal ξ hξ.1
    hε := hε
    hεγ := hεγ
    bound := by
      rw [← w8M_eq_w6 m hm]
      exact hb.mono_lam Set.sdiff_subset subset_rfl le_rfl le_rfl }

end KAM.Wave

end
