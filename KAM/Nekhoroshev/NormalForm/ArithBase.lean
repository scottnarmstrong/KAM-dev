/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.IterativeMap
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: numerics, Step 0 and the schedule (`bpN:p6:normal-form`, `nf-first`, `nf-case`, `nf-N`)

The step schedule (`nfRho`, `nfSig`, `nfR`, `nfS`), the carried bound sequence `nfB` and the displayed
inequalities of the proof as standalone real lemmas: Step 0 (`iterU_first`, Case A (6.1), Case B), the
number of steps `N` and (6.2), the induction constant `128/127 · 0.1915 < 1/4`, the conclusions (a),
(b) and the displacement constants (1.17, `8 + 32/(36 ln 2) ≤ 10`). No `nlinarith`. Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8.
-/

@[expose] public noncomputable section

namespace KAM.NormalForm

/-! ### The step schedule and the bound sequence -/

/-- The losses `ρᵢ`: `r/8` for the first step, `r/(8N)` afterwards. -/
def nfRho (r : ℝ) (N i : ℕ) : ℝ := if i = 0 then r / 8 else r / (8 * N)

/-- The losses `σᵢ`: `s/6` for the first step, `s/(4N)` afterwards. -/
def nfSig (s : ℝ) (N i : ℕ) : ℝ := if i = 0 then s / 6 else s / (4 * N)

/-- The radii `rᵢ` (`r₀ = r`, `rᵢ₊₁ = rᵢ - 2ρᵢ`). -/
def nfR (r : ℝ) (N : ℕ) : ℕ → ℝ
  | 0 => r
  | i + 1 => nfR r N i - 2 * nfRho r N i

/-- The widths `sᵢ` (`s₀ = s`, `sᵢ₊₁ = sᵢ - 2σᵢ`). -/
def nfS (s : ℝ) (N : ℕ) : ℕ → ℝ
  | 0 => s
  | i + 1 => nfS s N i - 2 * nfSig s N i

/-- The bound `ε₁ = 2⁷ q ε² / (ᾱ r s)` of Case A (6.1). -/
def nfEps1 (α p r s ε : ℝ) : ℝ := 2 ^ 7 * conjExp p * ε ^ 2 / (2 * Real.pi * α * r * s)

/-- The carried bounds: `B₀ = ε`, `Bᵢ = 4^{1-i} ε₁` for `i ≥ 1`. -/
def nfB (ε₁ ε : ℝ) : ℕ → ℝ
  | 0 => ε
  | i + 1 => ε₁ / 4 ^ i

/-- The bound of `iterative_direct_d` for the decomposition norm `S` and the loss pair `(ρ, σ)`. -/
def nfBound (α p K ρ σ δ S : ℝ) : ℝ :=
  (1 - 2 * iterU α p δ ρ σ)⁻¹ *
      (2 * conjExp p / (Real.exp 1 * (2 * Real.pi * α) * ρ * σ) * (S + δ) +
        Real.exp (-(2 * Real.pi * K * σ))) * δ

section Numerics

variable {α p K r s ε : ℝ}

theorem conjExp_pos' (hp : 1 < p) : 0 < conjExp p := by
  unfold conjExp
  exact div_pos (by linarith) (by linarith)

theorem exp_one_gt : (2 : ℝ) < Real.exp 1 := by
  have := Real.exp_one_gt_d9
  linarith

/-- `2/e < 1`, in the form used for `2q/(e ᾱ ρ σ) · δ = (2/e) u`. -/
theorem two_div_exp_lt : 2 / Real.exp 1 < 1 := by
  rw [div_lt_one (Real.exp_pos 1)]
  exact exp_one_gt

theorem log_two_gt : (2 : ℝ) / 3 < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- The coefficient identity `2q/(e ᾱ ρ σ) · δ = (2/e) · u`. -/
theorem coef_mul_eq {ρ σ p δ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) (hσ : 0 < σ) :
    2 * conjExp p / (Real.exp 1 * (2 * Real.pi * α) * ρ * σ) * δ = 2 / Real.exp 1 * iterU α p δ ρ σ := by
  have := Real.pi_pos
  have := Real.exp_pos 1
  unfold iterU
  field_simp

/-- `δ ≤ ᾱρσ/(4q) ↔ u ≤ 1/4`. -/
theorem small_iff_iterU (hp : 1 < p) (hα : 0 < α) {ρ σ δ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) :
    δ ≤ 2 * Real.pi * α * ρ * σ / (4 * conjExp p) ↔ iterU α p δ ρ σ ≤ 1 / 4 := by
  have hq := conjExp_pos' hp
  have := Real.pi_pos
  have hpos : 0 < 2 * Real.pi * α * ρ * σ := by positivity
  unfold iterU
  rw [div_le_iff₀ hpos, le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- `u ≤ 1/16` for Step 0 (`nf-first`). -/
theorem iterU_first (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r) (hs : 0 < s)
    (hε0 : 0 ≤ ε) (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K))
    (hii : 6 ≤ 2 * Real.pi * K * s) : iterU α p ε (r / 8) (s / 6) ≤ 1 / 16 := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have h1 : conjExp p * ε * 2 ^ 7 * K ≤ α * r := by
    have := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 ^ 7 * conjExp p * K)
    rw [show 2 ^ 7 * conjExp p * K * (1 / (2 ^ 7 * conjExp p) * (α * r / K)) = α * r by
      field_simp] at this
    calc conjExp p * ε * 2 ^ 7 * K = 2 ^ 7 * conjExp p * K * ε := by ring
      _ ≤ _ := this
  have e1 : conjExp p * ε * 2 ^ 7 * 3 ≤ conjExp p * ε * 2 ^ 7 * (K * Real.pi * s) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : conjExp p * ε * 2 ^ 7 * K * (Real.pi * s) ≤ α * r * (Real.pi * s) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  unfold iterU
  rw [div_le_iff₀ (by positivity)]
  linarith [e1, e2]

/-- `u'` for the doubled losses is a quarter of `u`. -/
theorem iterU_double (hα : 0 < α) (hr : 0 < r) (hs : 0 < s) :
    iterU α p ε (r / 4) (s / 3) = iterU α p ε (r / 8) (s / 6) / 4 := by
  have := Real.pi_pos
  unfold iterU
  field_simp
  ring

theorem inv_one_sub_le {t c : ℝ} (ht : t ≤ c) (hc : c < 1) : (1 - t)⁻¹ ≤ (1 - c)⁻¹ :=
  inv_anti₀ (by linarith) (by linarith)

/-- `q ε 2⁷ K ≤ α r`: hypothesis (i) of the Normal Form Lemma, cleared of denominators. -/
theorem hi_mul (hp : 1 < p) (hK : 0 < K)
    (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)) : conjExp p * ε * 2 ^ 7 * K ≤ α * r := by
  have hq := conjExp_pos' hp
  have := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 ^ 7 * conjExp p * K)
  rw [show 2 ^ 7 * conjExp p * K * (1 / (2 ^ 7 * conjExp p) * (α * r / K)) = α * r by
    field_simp] at this
  calc conjExp p * ε * 2 ^ 7 * K = 2 ^ 7 * conjExp p * K * ε := by ring
    _ ≤ _ := this

theorem iterU_nonneg (hp : 1 < p) (hα : 0 < α) {ρ σ δ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hδ : 0 ≤ δ) : 0 ≤ iterU α p δ ρ σ := by
  have := conjExp_pos' hp
  have := Real.pi_pos
  unfold iterU
  positivity

/-- `u ε = 48 q ε² / (ᾱ r s)` for Step 0. -/
private theorem iterU_first_mul (hα : 0 < α) (hr : 0 < r) (hs : 0 < s) :
    iterU α p ε (r / 8) (s / 6) * ε = 48 * (conjExp p * ε ^ 2 / (2 * Real.pi * α * r * s)) := by
  have := Real.pi_pos
  unfold iterU
  field_simp
  ring

private theorem nfEps1_eq :
    nfEps1 α p r s ε = 2 ^ 7 * (conjExp p * ε ^ 2 / (2 * Real.pi * α * r * s)) := by
  unfold nfEps1
  ring

theorem nfEps1_nonneg (hp : 1 < p) (hα : 0 < α) (hr : 0 < r) (hs : 0 < s) :
    0 ≤ nfEps1 α p r s ε := by
  have := conjExp_pos' hp
  have := Real.pi_pos
  unfold nfEps1
  positivity

/-- Case A (6.1), first half: `|f₁| ≤ (16/7) u ε ≤ ε₁` when `e^{-κ/6} ≤ u`. -/
theorem nfBound_caseA (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r) (hs : 0 < s)
    (hε0 : 0 ≤ ε) (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K))
    (hii : 6 ≤ 2 * Real.pi * K * s)
    (hA : Real.exp (-(2 * Real.pi * K * s) / 6) ≤ iterU α p ε (r / 8) (s / 6)) :
    nfBound α p K (r / 8) (s / 6) ε 0 ≤ nfEps1 α p r s ε := by
  have hu := iterU_first hp hα hK hr hs hε0 hi hii
  have hu0 := iterU_nonneg hp hα (by positivity : 0 < r / 8) (by positivity : 0 < s / 6) hε0
  have hX : 0 ≤ conjExp p * ε ^ 2 / (2 * Real.pi * α * r * s) := by
    have := conjExp_pos' hp
    have := Real.pi_pos
    positivity
  have hexp : Real.exp (-(2 * Real.pi * K * (s / 6))) = Real.exp (-(2 * Real.pi * K * s) / 6) := by
    congr 1; ring
  unfold nfBound
  rw [zero_add, coef_mul_eq hα (by positivity) (by positivity), hexp]
  have h1 : (1 - 2 * iterU α p ε (r / 8) (s / 6))⁻¹ ≤ 8 / 7 := by
    have := inv_one_sub_le (t := 2 * iterU α p ε (r / 8) (s / 6)) (c := 1 / 8) (by linarith)
      (by norm_num)
    norm_num at this
    exact this
  have h2 : 2 / Real.exp 1 * iterU α p ε (r / 8) (s / 6) ≤ iterU α p ε (r / 8) (s / 6) :=
    mul_le_of_le_one_left hu0 two_div_exp_lt.le
  have h3 : (1 - 2 * iterU α p ε (r / 8) (s / 6))⁻¹ *
      (2 / Real.exp 1 * iterU α p ε (r / 8) (s / 6) + Real.exp (-(2 * Real.pi * K * s) / 6)) ≤
        8 / 7 * (2 * iterU α p ε (r / 8) (s / 6)) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  have h4 := mul_le_mul_of_nonneg_right h3 hε0
  have h5 := iterU_first_mul (p := p) (ε := ε) hα hr hs
  rw [nfEps1_eq]
  linarith [h4, h5, hX]

/-- Case B: the doubled losses give `|f₁| ≤ e^{-κ/6} ε`. -/
theorem nfBound_caseB (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r) (hs : 0 < s)
    (hε0 : 0 ≤ ε) (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K))
    (hii : 6 ≤ 2 * Real.pi * K * s)
    (hB : iterU α p ε (r / 8) (s / 6) < Real.exp (-(2 * Real.pi * K * s) / 6)) :
    nfBound α p K (r / 4) (s / 3) ε 0 ≤ Real.exp (-(2 * Real.pi * K * s) / 6) * ε := by
  have hu := iterU_first hp hα hK hr hs hε0 hi hii
  have hu0 := iterU_nonneg hp hα (by positivity : 0 < r / 8) (by positivity : 0 < s / 6) hε0
  set E := Real.exp (-(2 * Real.pi * K * s) / 6) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 / 2 := by
    have h1 : E ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg] at h1
    have : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      norm_num
      exact exp_one_gt.le
    linarith
  have hexp : Real.exp (-(2 * Real.pi * K * (s / 3))) = E * E := by
    rw [hE, ← Real.exp_add]; congr 1; ring
  have hd := iterU_double (p := p) (ε := ε) hα hr hs
  have hu'0 := iterU_nonneg hp hα (by positivity : 0 < r / 4) (by positivity : 0 < s / 3) hε0
  unfold nfBound
  rw [zero_add, coef_mul_eq hα (by positivity) (by positivity), hexp]
  have h1 : (1 - 2 * iterU α p ε (r / 4) (s / 3))⁻¹ ≤ 32 / 31 := by
    have := inv_one_sub_le (t := 2 * iterU α p ε (r / 4) (s / 3)) (c := 1 / 32) (by linarith)
      (by norm_num)
    norm_num at this
    exact this
  have h2 : 2 / Real.exp 1 * iterU α p ε (r / 4) (s / 3) ≤ iterU α p ε (r / 4) (s / 3) :=
    mul_le_of_le_one_left hu'0 two_div_exp_lt.le
  have hEE : E * E ≤ E / 2 := by
    have := mul_le_mul_of_nonneg_left hE1 hE0.le
    linarith
  have h3 : (1 - 2 * iterU α p ε (r / 4) (s / 3))⁻¹ *
      (2 / Real.exp 1 * iterU α p ε (r / 4) (s / 3) + E * E) ≤ 32 / 31 * (3 / 4 * E) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  have h4 := mul_le_mul_of_nonneg_right h3 hε0
  have h5 := mul_nonneg hE0.le hε0
  linarith [h4, h5]

/-- `N = 0`: `κ < 12 ln 2` gives `1/4 < e^{-κ/6}`. -/
theorem quarter_lt_exp {κ : ℝ} (h : κ < 12 * Real.log 2) : 1 / 4 < Real.exp (-κ / 6) := by
  have e : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
    rw [Real.exp_neg, show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add,
      Real.exp_log two_pos]
    norm_num
  exact lt_of_eq_of_lt e.symm (Real.exp_lt_exp.mpr (by linarith))

/-- `N = ⌊κ/(12 ln 2)⌋`: `N · 12 ln 2 ≤ κ < (N+1) · 12 ln 2` and `8N ≤ κ`. -/
theorem floor_facts {N : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (hN : N = ⌊κ / (12 * Real.log 2)⌋₊) :
    (N : ℝ) * (12 * Real.log 2) ≤ κ ∧ κ < ((N : ℝ) + 1) * (12 * Real.log 2) ∧
      8 * (N : ℝ) ≤ κ := by
  have hl := log_two_gt
  have hpos : 0 < 12 * Real.log 2 := by linarith
  have h1 : (N : ℝ) ≤ κ / (12 * Real.log 2) := by
    rw [hN]; exact Nat.floor_le (div_nonneg hκ hpos.le)
  have h2 : κ / (12 * Real.log 2) < (N : ℝ) + 1 := by
    rw [hN]; exact Nat.lt_floor_add_one _
  rw [le_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  refine ⟨h1, h2, ?_⟩
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left (by linarith : (8 : ℝ) ≤ 12 * Real.log 2) h0
  linarith

/-- (b): `B_{N+1} = 4^{-N} ε₁ ≤ e^{-κ/6} ε` for `ε₁ ≤ ε/4` and `κ < (N+1) · 12 ln 2`. -/
theorem final_b {N : ℕ} {κ ε ε₁ : ℝ} (hε0 : 0 ≤ ε) (hε₁ : ε₁ ≤ ε / 4)
    (hκ : κ < ((N : ℝ) + 1) * (12 * Real.log 2)) :
    nfB ε₁ ε (N + 1) ≤ Real.exp (-κ / 6) * ε := by
  have e : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
    rw [Real.exp_neg, show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add,
      Real.exp_log two_pos]
    norm_num
  have h1 : (1 / 4 : ℝ) ^ (N + 1) ≤ Real.exp (-κ / 6) := by
    have : Real.exp (-(((N + 1 : ℕ) : ℝ) * (2 * Real.log 2))) = (1 / 4 : ℝ) ^ (N + 1) := by
      rw [show -(((N + 1 : ℕ) : ℝ) * (2 * Real.log 2)) =
          ((N + 1 : ℕ) : ℝ) * (-(2 * Real.log 2)) by ring, Real.exp_nat_mul, e]
    rw [← this]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    linarith
  have h2 : nfB ε₁ ε (N + 1) ≤ (1 / 4 : ℝ) ^ (N + 1) * ε := by
    show ε₁ / 4 ^ N ≤ (1 / 4 : ℝ) ^ (N + 1) * ε
    rw [div_le_iff₀ (by positivity), one_div, inv_pow, pow_succ]
    have h4 : (0 : ℝ) < 4 ^ N := by positivity
    rw [show ((4 : ℝ) ^ N * 4)⁻¹ * ε * 4 ^ N = ε / 4 by field_simp]
    exact hε₁
  exact h2.trans (mul_le_mul_of_nonneg_right h1 hε0)

end Numerics

end KAM.NormalForm

end
