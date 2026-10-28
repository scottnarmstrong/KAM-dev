/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.ArithBase
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Normal Form Lemma: numerics, (6.1), (6.2), the induction constant and (a)

`nf-case` (6.1), `nf-N` (6.2), `nf-induct` (`128/127 · 0.1915 < 1/4`), the decomposition norm and
`nf-concl` (a). Design `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-8.
-/

@[expose] public noncomputable section

namespace KAM.NormalForm

section Numerics

variable {α p K r s ε : ℝ}


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
    (hw0 : 0 < i → w 0 ≤ c) (hw : ∀ j, 1 ≤ j → j < i → w j ≤ 1) :
    ∑ j ∈ Finset.range i, w j * nfB ε₁ ε j ≤ c * ε + 4 / 3 * ε₁ := by
  cases i with
  | zero => simp; positivity
  | succ i =>
    rw [Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range i, w (j + 1) * nfB ε₁ ε (j + 1) ≤ ε₁ * (4 / 3) := by
      calc ∑ j ∈ Finset.range i, w (j + 1) * nfB ε₁ ε (j + 1)
          ≤ ∑ j ∈ Finset.range i, ε₁ * (1 / 4 ^ j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            show w (j + 1) * (ε₁ / 4 ^ j) ≤ ε₁ * (1 / 4 ^ j)
            have h4 : 0 ≤ ε₁ / 4 ^ j := by positivity
            calc w (j + 1) * (ε₁ / 4 ^ j) ≤ 1 * (ε₁ / 4 ^ j) :=
                  mul_le_mul_of_nonneg_right
                    (hw _ (by omega) (by have := Finset.mem_range.mp hj; omega)) h4
              _ = ε₁ * (1 / 4 ^ j) := by ring
        _ = ε₁ * ∑ j ∈ Finset.range i, (1 : ℝ) / 4 ^ j := by rw [Finset.mul_sum]
        _ ≤ ε₁ * (4 / 3) := mul_le_mul_of_nonneg_left (sum_inv4_le i) hε₁
    have h2 : w 0 * nfB ε₁ ε 0 ≤ c * ε := mul_le_mul (hw0 (by omega)) le_rfl hε0 hc
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
  have h4 : 4 / 3 * iterU α p (nfEps1 α p r s ε) (r / (8 * N)) (s / (4 * N)) ≤
      4 / 3 * (1 / 2 ^ 8) :=
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


end Numerics

end KAM.NormalForm

end
