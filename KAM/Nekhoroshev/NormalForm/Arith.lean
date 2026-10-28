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
# The Normal Form Lemma: numerics (`bpN:p6:normal-form`, Steps `nf-first` .. `nf-concl`, `nf-disp`)

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

private theorem conjExp_pos' (hp : 1 < p) : 0 < conjExp p := by
  unfold conjExp
  exact div_pos (by linarith) (by linarith)

private theorem exp_one_gt : (2 : ℝ) < Real.exp 1 := by
  have := Real.exp_one_gt_d9
  linarith

/-- `2/e < 1`, in the form used for `2q/(e ᾱ ρ σ) · δ = (2/e) u`. -/
private theorem two_div_exp_lt : 2 / Real.exp 1 < 1 := by
  rw [div_lt_one (Real.exp_pos 1)]
  exact exp_one_gt

private theorem log_two_gt : (2 : ℝ) / 3 < Real.log 2 := by
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

private theorem inv_one_sub_le {t c : ℝ} (ht : t ≤ c) (hc : c < 1) : (1 - t)⁻¹ ≤ (1 - c)⁻¹ :=
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

/-! ### (6.1), (6.2) and the induction constant -/

/-- (6.1): `ε₁ ≤ ε/κ`. -/
theorem eps1_le_div (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r) (hs : 0 < s)
    (hε0 : 0 ≤ ε) (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)) :
    nfEps1 α p r s ε ≤ ε / (2 * Real.pi * K * s) := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have h1 := hi_mul hp hK hi
  unfold nfEps1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ε * (2 * Real.pi * s))
  calc 2 ^ 7 * conjExp p * ε ^ 2 * (2 * Real.pi * K * s)
      = conjExp p * ε * 2 ^ 7 * K * (ε * (2 * Real.pi * s)) := by ring
    _ ≤ α * r * (ε * (2 * Real.pi * s)) := h2
    _ = ε * (2 * Real.pi * α * r * s) := by ring

/-- (6.1): `ε₁ ≤ ε/4` (as `κ ≥ 6`). -/
theorem eps1_le_quarter (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r) (hs : 0 < s)
    (hε0 : 0 ≤ ε) (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K))
    (hii : 6 ≤ 2 * Real.pi * K * s) : nfEps1 α p r s ε ≤ ε / 4 := by
  refine (eps1_le_div hp hα hK hr hs hε0 hi).trans ?_
  have hpos : 0 < 2 * Real.pi * K * s := by linarith
  rw [div_le_div_iff₀ hpos (by norm_num)]
  exact mul_le_mul_of_nonneg_left (by linarith) hε0

/-- (6.2), first half: `ε ≤ ᾱ r s / (2¹⁰ q N)` for `1 ≤ N`, `8N ≤ κ`. -/
theorem eps_le_sixtwo {N : ℕ} (hp : 1 < p) (_hα : 0 < α) (hK : 0 < K) (_hr : 0 < r) (hs : 0 < s)
    (hε0 : 0 ≤ ε) (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)) (hN : 1 ≤ N)
    (h8 : 8 * (N : ℝ) ≤ 2 * Real.pi * K * s) :
    ε ≤ 2 * Real.pi * α * r * s / (2 ^ 10 * conjExp p * N) := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := hi_mul hp hK hi
  rw [le_div_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 2 * Real.pi * s)
  have h3 : conjExp p * ε * 2 ^ 10 * (N : ℝ) ≤ conjExp p * ε * 2 ^ 10 * (Real.pi * K * s / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc ε * (2 ^ 10 * conjExp p * N) = conjExp p * ε * 2 ^ 10 * (N : ℝ) := by ring
    _ ≤ conjExp p * ε * 2 ^ 10 * (Real.pi * K * s / 4) := h3
    _ = conjExp p * ε * 2 ^ 7 * K * (2 * Real.pi * s) := by ring
    _ ≤ α * r * (2 * Real.pi * s) := h2
    _ = 2 * Real.pi * α * r * s := by ring

/-- (6.2): `ε₁ ≤ ᾱ ρ σ / 2⁸q` for `ρ = r/(8N)`, `σ = s/(4N)`. -/
theorem eps1_sixtwo {N : ℕ} (hp : 1 < p) (hα : 0 < α) (hr : 0 < r) (hs : 0 < s)
    (hε0 : 0 ≤ ε) (hN : 1 ≤ N)
    (hε : ε ≤ 2 * Real.pi * α * r * s / (2 ^ 10 * conjExp p * N)) :
    iterU α p (nfEps1 α p r s ε) (r / (8 * N)) (s / (4 * N)) ≤ 1 / 2 ^ 8 := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set P := 2 * Real.pi * α * r * s with hP
  have hP0 : 0 < P := by positivity
  have h1 : ε ^ 2 ≤ (P / (2 ^ 10 * conjExp p * N)) ^ 2 := pow_le_pow_left₀ hε0 hε 2
  have h2 : nfEps1 α p r s ε ≤ 2 ^ 7 * conjExp p * (P / (2 ^ 10 * conjExp p * N)) ^ 2 / P := by
    unfold nfEps1
    rw [← hP]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hP0.le
  have h3 : iterU α p (nfEps1 α p r s ε) (r / (8 * N)) (s / (4 * N)) ≤
      iterU α p (2 ^ 7 * conjExp p * (P / (2 ^ 10 * conjExp p * N)) ^ 2 / P) (r / (8 * N))
        (s / (4 * N)) := by
    unfold iterU
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hq.le) (by positivity)
  refine h3.trans_eq ?_
  unfold iterU
  rw [hP]
  field_simp
  ring

/-- The induction constant: `u_i ≤ 2⁻⁸`, `|g|_* ≤ ᾱρσ/(2⁴q)`, `e^{-2πKσ} ≤ 1/8` give
`|f₊| ≤ (128/127) · 0.1915 · δ ≤ δ/4`. -/
theorem induct_step (hp : 1 < p) (hα : 0 < α) {ρ σ δ S K : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hδ0 : 0 ≤ δ) (hS0 : 0 ≤ S) (hδ : iterU α p δ ρ σ ≤ 1 / 2 ^ 8)
    (hS : iterU α p S ρ σ ≤ 1 / 2 ^ 4) (hexp : Real.exp (-(2 * Real.pi * K * σ)) ≤ 1 / 8) :
    nfBound α p K ρ σ δ S ≤ δ / 4 := by
  have ha0 := iterU_nonneg hp hα hρ hσ hδ0
  have hb0 := iterU_nonneg hp hα hρ hσ hS0
  have hadd : iterU α p (S + δ) ρ σ = iterU α p S ρ σ + iterU α p δ ρ σ := by
    unfold iterU
    ring
  unfold nfBound
  rw [coef_mul_eq hα hρ hσ, hadd]
  have h1 : (1 - 2 * iterU α p δ ρ σ)⁻¹ ≤ 128 / 127 := by
    have := inv_one_sub_le (t := 2 * iterU α p δ ρ σ) (c := 1 / 2 ^ 7) (by linarith)
      (by norm_num)
    norm_num at this
    exact this
  have h2 : 2 / Real.exp 1 * (iterU α p S ρ σ + iterU α p δ ρ σ) ≤
      iterU α p S ρ σ + iterU α p δ ρ σ :=
    mul_le_of_le_one_left (by linarith) two_div_exp_lt.le
  have h3 : (1 - 2 * iterU α p δ ρ σ)⁻¹ *
      (2 / Real.exp 1 * (iterU α p S ρ σ + iterU α p δ ρ σ) + Real.exp (-(2 * Real.pi * K * σ))) ≤
        128 / 127 * (1 / 2 ^ 4 + 1 / 2 ^ 8 + 1 / 8) :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  have h4 := mul_le_mul_of_nonneg_right h3 hδ0
  have h5 : 128 / 127 * (1 / 2 ^ 4 + 1 / 2 ^ 8 + 1 / 8) * δ ≤ δ / 4 := by
    have : (128 / 127 * (1 / 2 ^ 4 + 1 / 2 ^ 8 + 1 / 8) : ℝ) ≤ 1 / 4 := by norm_num
    have := mul_le_mul_of_nonneg_right this hδ0
    linarith
  linarith

/-! ### The decomposition norm, (a) and the geometric sums -/

theorem iterU_mono (hp : 1 < p) (hα : 0 < α) {ρ σ x y : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hxy : x ≤ y) : iterU α p x ρ σ ≤ iterU α p y ρ σ := by
  have := conjExp_pos' hp
  have := Real.pi_pos
  unfold iterU
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (by positivity)) (by positivity)

theorem iterU_lin {ρ σ x y a b : ℝ} :
    iterU α p (a * x + b * y) ρ σ = a * iterU α p x ρ σ + b * iterU α p y ρ σ := by
  unfold iterU
  ring

theorem sum_inv4_le (m : ℕ) : ∑ i ∈ Finset.range m, (1 : ℝ) / 4 ^ i ≤ 4 / 3 := by
  have h := geom_sum_eq (x := (1 / 4 : ℝ)) (by norm_num) m
  have e : ∑ i ∈ Finset.range m, (1 : ℝ) / 4 ^ i = ∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ i :=
    Finset.sum_congr rfl fun i _ => by rw [one_div, one_div, inv_pow]
  rw [e, h]
  have : (0 : ℝ) ≤ (1 / 4) ^ m := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

/-- The decomposition norm: weights `w₀ ≤ c` and `wⱼ ≤ 1` against the bounds `Bⱼ` sum to at most
`c ε + (4/3) ε₁`. -/
theorem star_sum_le {ε ε₁ c : ℝ} (hε0 : 0 ≤ ε) (hε₁ : 0 ≤ ε₁) (hc : 0 ≤ c) (i : ℕ) (w : ℕ → ℝ)
    (hw0 : w 0 ≤ c) (hw : ∀ j, 1 ≤ j → w j ≤ 1) (_hwn : ∀ j, 0 ≤ w j) :
    ∑ j ∈ Finset.range i, w j * nfB ε₁ ε j ≤ c * ε + 4 / 3 * ε₁ := by
  cases i with
  | zero => simp; positivity
  | succ i =>
    rw [Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range i, w (j + 1) * nfB ε₁ ε (j + 1) ≤ ε₁ * (4 / 3) := by
      calc ∑ j ∈ Finset.range i, w (j + 1) * nfB ε₁ ε (j + 1)
          ≤ ∑ j ∈ Finset.range i, ε₁ * (1 / 4 ^ j) := by
            refine Finset.sum_le_sum fun j _ => ?_
            show w (j + 1) * (ε₁ / 4 ^ j) ≤ ε₁ * (1 / 4 ^ j)
            have h4 : 0 ≤ ε₁ / 4 ^ j := by positivity
            calc w (j + 1) * (ε₁ / 4 ^ j) ≤ 1 * (ε₁ / 4 ^ j) :=
                  mul_le_mul_of_nonneg_right (hw _ (by omega)) h4
              _ = ε₁ * (1 / 4 ^ j) := by ring
        _ = ε₁ * ∑ j ∈ Finset.range i, (1 : ℝ) / 4 ^ j := by rw [Finset.mul_sum]
        _ ≤ ε₁ * (4 / 3) := mul_le_mul_of_nonneg_left (sum_inv4_le i) hε₁
    have h2 : w 0 * nfB ε₁ ε 0 ≤ c * ε := mul_le_mul hw0 le_rfl hε0 hc
    linarith

/-- The part-0 weight `½(ρ/(r-R+ρ) + σ/(s-S+σ)) ≤ 5/(8N)` for `R ≤ 3r/4`, `S ≤ 2s/3`. -/
theorem w0_le {N : ℕ} {r s R S : ℝ} (hN : 1 ≤ N) (hr : 0 < r) (hs : 0 < s) (hR : R ≤ 3 * r / 4)
    (hS : S ≤ 2 * s / 3) :
    1 / 2 * ((r / (8 * N)) / (r - R + r / (8 * N)) + (s / (4 * N)) / (s - S + s / (4 * N))) ≤
      5 / (8 * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (r / (8 * N)) / (r - R + r / (8 * N)) ≤ (r / (8 * N)) / (r / 4) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by
      have : 0 ≤ r / (8 * N) := by positivity
      linarith)
  have h2 : (s / (4 * N)) / (s - S + s / (4 * N)) ≤ (s / (4 * N)) / (s / 3) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by
      have : 0 ≤ s / (4 * N) := by positivity
      linarith)
  have e1 : (r / (8 * N)) / (r / 4) = 1 / (2 * N) := by field_simp; ring
  have e2 : (s / (4 * N)) / (s / 3) = 3 / (4 * N) := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  have e3 : 1 / 2 * (1 / (2 * (N : ℝ)) + 3 / (4 * N)) = 5 / (8 * N) := by field_simp; ring
  linarith

/-- `|g_{i-1}|_*` is small: `u(S) ≤ 1/2⁴` once `S ≤ (5/(8N)) ε + (4/3) ε₁`. -/
theorem star_small {N : ℕ} {S : ℝ} (hp : 1 < p) (hα : 0 < α) (hr : 0 < r) (hs : 0 < s)
    (_hε0 : 0 ≤ ε) (hN : 1 ≤ N) (hε : ε ≤ 2 * Real.pi * α * r * s / (2 ^ 10 * conjExp p * N))
    (hε₁ : iterU α p (nfEps1 α p r s ε) (r / (8 * N)) (s / (4 * N)) ≤ 1 / 2 ^ 8)
    (hS : S ≤ 5 / (8 * N) * ε + 4 / 3 * nfEps1 α p r s ε) :
    iterU α p S (r / (8 * N)) (s / (4 * N)) ≤ 1 / 2 ^ 4 := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 < r / (8 * (N : ℝ)) := by positivity
  have hσ : 0 < s / (4 * (N : ℝ)) := by positivity
  have h1 : iterU α p ε (r / (8 * N)) (s / (4 * N)) ≤ N / 32 := by
    refine (iterU_mono hp hα hρ hσ hε).trans_eq ?_
    unfold iterU
    field_simp
    ring
  have h2 := iterU_mono hp hα hρ hσ hS
  rw [iterU_lin] at h2
  refine h2.trans ?_
  have h3 : 5 / (8 * (N : ℝ)) * iterU α p ε (r / (8 * N)) (s / (4 * N)) ≤ 5 / 256 := by
    calc 5 / (8 * (N : ℝ)) * iterU α p ε (r / (8 * N)) (s / (4 * N))
        ≤ 5 / (8 * (N : ℝ)) * (N / 32) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 5 / 256 := by field_simp; ring
  have h4 : 4 / 3 * iterU α p (nfEps1 α p r s ε) (r / (8 * N)) (s / (4 * N)) ≤ 4 / 3 * (1 / 2 ^ 8) :=
    mul_le_mul_of_nonneg_left hε₁ (by norm_num)
  have h5 : (5 / 256 : ℝ) + 4 / 3 * (1 / 2 ^ 8) ≤ 1 / 2 ^ 4 := by norm_num
  linarith

/-- (a): `Σ_{i=1}^N B_i ≤ (4/3) ε₁ ≤ 16 c ε²` for `κ ≥ 8`, `c = 2qK/(αr)`. -/
theorem concl_a (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r) (hs : 0 < s)
    (h8 : 8 ≤ 2 * Real.pi * K * s) :
    4 / 3 * nfEps1 α p r s ε ≤ 16 * (2 * conjExp p * K / (α * r)) * ε ^ 2 := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  set Y := conjExp p * ε ^ 2 / (α * r) with hY
  have hY0 : 0 ≤ Y := by positivity
  have e1 : nfEps1 α p r s ε = 2 ^ 6 / (Real.pi * s) * Y := by
    unfold nfEps1
    rw [hY]
    field_simp
  have e2 : 16 * (2 * conjExp p * K / (α * r)) * ε ^ 2 = 32 * K * Y := by
    rw [hY]
    field_simp
    ring
  rw [e1, e2]
  have h1 : 4 / 3 * (2 ^ 6 / (Real.pi * s)) ≤ 32 * K := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  calc 4 / 3 * (2 ^ 6 / (Real.pi * s) * Y) = 4 / 3 * (2 ^ 6 / (Real.pi * s)) * Y := by ring
    _ ≤ 32 * K * Y := mul_le_mul_of_nonneg_right h1 hY0

/-! ### Displacement (`nf-disp`) -/

/-- (c), action direction, Case A: `∑ᵢ q Bᵢ/(e ᾱ σᵢ) ≤ qKε/α`. -/
theorem disp_I {N : ℕ} (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hs : 0 < s) (hε0 : 0 ≤ ε)
    {ε₁ : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε / 4) (hii : 6 ≤ 2 * Real.pi * K * s)
    (h8 : 8 * (N : ℝ) ≤ 2 * Real.pi * K * s) :
    ∑ i ∈ Finset.range (N + 1),
        conjExp p * nfB ε₁ ε i / (Real.exp 1 * (2 * Real.pi * α) * nfSig s N i) ≤
      conjExp p * K * ε / α := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have he := Real.exp_pos 1
  have he2 := exp_one_gt
  set W := conjExp p * ε / (Real.exp 1 * α) with hW
  have hW0 : 0 ≤ W := by positivity
  have hT0 : conjExp p * nfB ε₁ ε 0 / (Real.exp 1 * (2 * Real.pi * α) * nfSig s N 0) ≤ K * W := by
    have e : conjExp p * nfB ε₁ ε 0 / (Real.exp 1 * (2 * Real.pi * α) * nfSig s N 0) =
        6 / (2 * Real.pi * s) * W := by
      simp only [nfB, nfSig, ite_true, hW]
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hW0
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hKW : 0 ≤ K * W := by positivity
  have hfin : 2 * (K * W) ≤ conjExp p * K * ε / α := by
    have : conjExp p * K * ε / α = K * W * Real.exp 1 := by
      rw [hW]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left he2.le hKW |>.trans_eq' (by ring)
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [zero_add, Finset.sum_range_one]
    linarith
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Finset.sum_range_succ']
    set C := conjExp p * ε₁ / (Real.exp 1 * (2 * Real.pi * α) * (s / (4 * N))) with hC
    have hC0 : 0 ≤ C := by positivity
    have hterm : ∀ i ∈ Finset.range N,
        conjExp p * nfB ε₁ ε (i + 1) / (Real.exp 1 * (2 * Real.pi * α) * nfSig s N (i + 1)) =
          C * (1 / 4 ^ i) := by
      intro i _
      simp only [nfB, nfSig, hC, Nat.succ_ne_zero, ite_false]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsum := mul_le_mul_of_nonneg_left (sum_inv4_le N) hC0
    have hC1 : C * (4 / 3) ≤ K * W / 6 := by
      have e : C = 4 * N * conjExp p * ε₁ / (Real.exp 1 * (2 * Real.pi * α) * s) := by
        rw [hC]; field_simp
      have h1 : C ≤ N * conjExp p * ε / (Real.exp 1 * (2 * Real.pi * α) * s) := by
        rw [e]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ (N : ℝ) * conjExp p)
        linarith
      have h2 : N * conjExp p * ε / (Real.exp 1 * (2 * Real.pi * α) * s) ≤ K * W / 8 := by
        rw [div_le_iff₀ (by positivity)]
        have e2 : K * W / 8 * (Real.exp 1 * (2 * Real.pi * α) * s) =
            conjExp p * ε * (2 * Real.pi * K * s) / 8 := by
          rw [hW]; field_simp
        rw [e2]
        have := mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ conjExp p * ε)
        linarith
      have := mul_le_mul_of_nonneg_right (h1.trans h2) (by norm_num : (0 : ℝ) ≤ 4 / 3)
      linarith
    linarith

/-- (c), angle direction, Case A: `∑ᵢ q Bᵢ/(ᾱ ρᵢ) ≤ 10 q ε/(ᾱ r)`. -/
theorem disp_theta {N : ℕ} (hp : 1 < p) (hα : 0 < α) (_hK : 0 < K) (hr : 0 < r) (_hs : 0 < s)
    (hε0 : 0 ≤ ε) {ε₁ : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε / (2 * Real.pi * K * s))
    (hii : 6 ≤ 2 * Real.pi * K * s) (h8 : 8 * (N : ℝ) ≤ 2 * Real.pi * K * s) :
    ∑ i ∈ Finset.range (N + 1),
        conjExp p * nfB ε₁ ε i / (2 * Real.pi * α * nfRho r N i) ≤
      10 * conjExp p * ε / (2 * Real.pi * α * r) := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have hκ : 0 < 2 * Real.pi * K * s := by linarith
  set V := conjExp p * ε / (2 * Real.pi * α * r) with hV
  have hV0 : 0 ≤ V := by positivity
  have hfin : 10 * conjExp p * ε / (2 * Real.pi * α * r) = 10 * V := by rw [hV]; ring
  have hT0 : conjExp p * nfB ε₁ ε 0 / (2 * Real.pi * α * nfRho r N 0) = 8 * V := by
    simp only [nfB, nfRho, ite_true, hV]
    field_simp
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [zero_add, Finset.sum_range_one]
    rw [hT0, hfin]
    linarith
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Finset.sum_range_succ']
    set C := conjExp p * ε₁ / (2 * Real.pi * α * (r / (8 * N))) with hC
    have hC0 : 0 ≤ C := by positivity
    have hterm : ∀ i ∈ Finset.range N,
        conjExp p * nfB ε₁ ε (i + 1) / (2 * Real.pi * α * nfRho r N (i + 1)) =
          C * (1 / 4 ^ i) := by
      intro i _
      simp only [nfB, nfRho, hC, Nat.succ_ne_zero, ite_false]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsum := mul_le_mul_of_nonneg_left (sum_inv4_le N) hC0
    have hC1 : C ≤ V := by
      have e : C = 8 * N * conjExp p * ε₁ / (2 * Real.pi * α * r) := by
        rw [hC]; field_simp
      rw [e]
      have h1 : 8 * N * conjExp p * ε₁ ≤ 8 * N * conjExp p * (ε / (2 * Real.pi * K * s)) :=
        mul_le_mul_of_nonneg_left hε₁ (by positivity)
      have h2 : 8 * N * conjExp p * (ε / (2 * Real.pi * K * s)) ≤ conjExp p * ε := by
        have e3 : 8 * N * conjExp p * (ε / (2 * Real.pi * K * s)) =
            conjExp p * ε * (8 * N / (2 * Real.pi * K * s)) := by ring
        rw [e3]
        have : 8 * (N : ℝ) / (2 * Real.pi * K * s) ≤ 1 := by
          rw [div_le_one hκ]; exact h8
        calc conjExp p * ε * (8 * N / (2 * Real.pi * K * s)) ≤ conjExp p * ε * 1 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = conjExp p * ε := mul_one _
      rw [hV]
      exact div_le_div_of_nonneg_right (h1.trans h2) (by positivity)
    rw [hT0, hfin]
    have := mul_le_mul_of_nonneg_right hC1 (by norm_num : (0 : ℝ) ≤ 4 / 3)
    linarith

/-- Case B displacement: `qε/(e ᾱ (s/3)) ≤ qKε/α` and `qε/(ᾱ r/4) ≤ 10 qε/(ᾱ r)`. -/
theorem disp_B (hp : 1 < p) (hα : 0 < α) (hK : 0 < K) (hr : 0 < r) (hs : 0 < s) (hε0 : 0 ≤ ε)
    (hii : 6 ≤ 2 * Real.pi * K * s) :
    conjExp p * ε / (Real.exp 1 * (2 * Real.pi * α) * (s / 3)) ≤ conjExp p * K * ε / α ∧
      conjExp p * ε / (2 * Real.pi * α * (r / 4)) ≤ 10 * conjExp p * ε / (2 * Real.pi * α * r) := by
  have hq := conjExp_pos' hp
  have hπ := Real.pi_pos
  have he := Real.exp_pos 1
  have he2 := exp_one_gt
  constructor
  · have e : conjExp p * ε / (Real.exp 1 * (2 * Real.pi * α) * (s / 3)) =
        3 / (2 * Real.pi * s) * (conjExp p * ε / (Real.exp 1 * α)) := by
      field_simp
    rw [e]
    have h1 : 3 / (2 * Real.pi * s) ≤ K := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h2 : conjExp p * ε / (Real.exp 1 * α) ≤ conjExp p * ε / α := by
      refine div_le_div_of_nonneg_left (by positivity) hα ?_
      have := mul_le_mul_of_nonneg_right he2.le hα.le
      linarith
    calc 3 / (2 * Real.pi * s) * (conjExp p * ε / (Real.exp 1 * α))
        ≤ K * (conjExp p * ε / α) :=
          mul_le_mul h1 h2 (by positivity) hK.le
      _ = conjExp p * K * ε / α := by ring
  · have e : conjExp p * ε / (2 * Real.pi * α * (r / 4)) =
        4 * (conjExp p * ε / (2 * Real.pi * α * r)) := by
      field_simp
    rw [e]
    have : 0 ≤ conjExp p * ε / (2 * Real.pi * α * r) := by positivity
    have e2 : 10 * conjExp p * ε / (2 * Real.pi * α * r) =
        10 * (conjExp p * ε / (2 * Real.pi * α * r)) := by ring
    rw [e2]
    linarith

/-! ### The radii -/

theorem nfR_succ_closed (r : ℝ) (N j : ℕ) :
    nfR r N (j + 1) = 3 * r / 4 - 2 * j * (r / (8 * N)) := by
  induction j with
  | zero => simp [nfR, nfRho]; ring
  | succ j ih =>
    rw [nfR, ih]
    simp only [nfRho, Nat.succ_ne_zero, ite_false]
    push_cast
    ring

theorem nfS_succ_closed (s : ℝ) (N j : ℕ) :
    nfS s N (j + 1) = 2 * s / 3 - 2 * j * (s / (4 * N)) := by
  induction j with
  | zero => simp [nfS, nfSig]; ring
  | succ j ih =>
    rw [nfS, ih]
    simp only [nfSig, Nat.succ_ne_zero, ite_false]
    push_cast
    ring

/-- `r_{N+1} = r/2`. -/
theorem nfR_final {N : ℕ} (hN : 1 ≤ N) (r : ℝ) : nfR r N (N + 1) = r / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [nfR_succ_closed]
  field_simp
  ring

/-- `s_{N+1} = s/6`. -/
theorem nfS_final {N : ℕ} (hN : 1 ≤ N) (s : ℝ) : nfS s N (N + 1) = s / 6 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [nfS_succ_closed]
  field_simp
  ring

end Numerics

end KAM.NormalForm

end
