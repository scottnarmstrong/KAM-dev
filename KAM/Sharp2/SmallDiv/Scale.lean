/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Instances

/-!
# Scaling of small-divisor constants (v2)

`SDConst.of_le_gamma` (`bp:p2s2sd:gamma-mono`): a certificate at the scale `γ` serves every smaller
scale. `SDConst.of_le_const`: a larger constant serves. `cohConstC_mono`, `sdConst_classical_of_le`
(`bp:p2s2sd:avg-tail`): the classical constant at the full bite `b'` serves every bite `b ≤ b'`.
`fullBite_ratio_mono`: the ratio `x / min (ρ + c x) 1` is increasing in `x`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM.Torus KAM.Apost

theorem zero_mem_complexStrip {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (0 : Fin n → ℂ) ∈ KAM.complexStrip n r := fun i => by simpa using hr

/-- A bound `‖X‖ ≤ K H` with `K > 0` forces `0 ≤ H`. -/
private theorem nonneg_of_bound {K H x : ℝ} (hK : 0 < K) (h : x ≤ K * H) (hx : 0 ≤ x) :
    0 ≤ H := by
  by_contra hH
  push Not at hH
  nlinarith [mul_neg_of_pos_of_neg hK hH]

/-- The constants enter only through `c γ⁻¹`: a larger coefficient serves. -/
theorem SDConst.of_coef {n : ℕ} {κ γ γ' δ c c' : ℝ} {Ω : Set (Fin n → ℝ)}
    (hc : SDConst n κ γ δ c Ω) (hγ : 0 < γ) (hc' : 0 < c') (hcc : c * γ⁻¹ ≤ c' * γ'⁻¹) :
    SDConst n κ γ' δ c' Ω := by
  have hd := hc.delta_pos
  have hc0 := hc.c_pos
  have hP : 0 < δ ^ (-κ) := by positivity
  have hm : ∀ H : ℝ, 0 ≤ H → c * γ⁻¹ * δ ^ (-κ) * H ≤ c' * γ'⁻¹ * δ ^ (-κ) * H := fun H hH => by
    have h1 : c * γ⁻¹ * δ ^ (-κ) ≤ c' * γ'⁻¹ * δ ^ (-κ) := mul_le_mul_of_nonneg_right hcc hP.le
    exact mul_le_mul_of_nonneg_right h1 hH
  have hK : 0 < c * γ⁻¹ * δ ^ (-κ) := by positivity
  have hH0 : ∀ {x H : ℝ}, 0 ≤ x → x ≤ c * γ⁻¹ * δ ^ (-κ) * H → 0 ≤ H := fun {x H} hx h =>
    nonneg_of_bound hK h hx
  refine ⟨hc', hd, ?_, ?_, ?_⟩
  · intro ω hω r hr p g H hd' hp hb ha θ hθ
    have hr0 : 0 < r := hd.trans hr
    have hH : 0 ≤ H := (norm_nonneg _).trans (hb 0 (zero_mem_complexStrip hr0))
    exact (hc.sol ω hω hr g H hd' hp hb ha θ hθ).trans (hm H hH)
  · intro ω hω r hr p q u H hd' hp ha hb θ hθ
    have h1 := hc.apriori ω hω hr u H hd' hp ha hb θ hθ
    have hr' : 0 < r - δ := by linarith
    have hH : 0 ≤ H :=
      hH0 (norm_nonneg _) (hc.apriori ω hω hr u H hd' hp ha hb 0 (zero_mem_complexStrip hr'))
    exact h1.trans (hm H hH)
  · intro ω hω r hr p g H hd' hp hb ha θ
    have h1 := hc.real ω hω hr g H hd' hp hb ha θ
    have hH : 0 ≤ H := hH0 (norm_nonneg _) (hc.real ω hω hr g H hd' hp hb ha 0)
    exact h1.trans (hm H hH)

/-- `bp:p2s2sd:gamma-mono` (audit iso F1): a certificate at the scale `γ` serves every smaller
scale. -/
theorem SDConst.of_le_gamma {n : ℕ} {κ γ γ' δ c : ℝ} {Ω : Set (Fin n → ℝ)}
    (hc : SDConst n κ γ δ c Ω) (hγ' : 0 < γ') (hγγ' : γ' ≤ γ) : SDConst n κ γ' δ c Ω :=
  hc.of_coef (hγ'.trans_le hγγ') hc.c_pos
    (mul_le_mul_of_nonneg_left (inv_anti₀ hγ' hγγ') hc.c_pos.le)

/-- A larger constant serves. -/
theorem SDConst.of_le_const {n : ℕ} {κ γ δ c c' : ℝ} {Ω : Set (Fin n → ℝ)}
    (hc : SDConst n κ γ δ c Ω) (hγ : 0 < γ) (hcc : c ≤ c') : SDConst n κ γ δ c' Ω :=
  hc.of_coef hγ (hc.c_pos.trans_le hcc)
    (mul_le_mul_of_nonneg_right hcc (inv_nonneg.mpr hγ.le))

/-- `bp:p2s2sd:avg-tail` (audit F9): the classical constant at the full bite `b'` serves every
full bite `b ≤ b'`. -/
theorem sdConst_classical_of_le {n : ℕ} (hn : 1 ≤ n) {τ γ b b' : ℝ} (hτ : 1 ≤ τ) (hγ : 0 < γ)
    (hb : 0 < b) (hbb' : b ≤ b') (hb'1 : b' ≤ 1) :
    SDConst n τ γ b (cohConstC n τ b') {ω | IsDiophantine γ τ ω} :=
  (sdConst_classical hn hτ hγ hb (hbb'.trans hb'1)).of_le_const hγ
    (cohConstC_mono hτ hb.le hbb')

/-- The full-bite ratio along the geometric schedule is increasing in the bite:
`δ_j/r_j ≤ δ_k/r_k` for `j ≥ k`. -/
theorem fullBite_ratio_mono {ρinf c x y : ℝ} (hρinf : 0 < ρinf) (hc : 0 < c) (hx : 0 < x)
    (hxy : x ≤ y) : x / min (ρinf + c * x) 1 ≤ y / min (ρinf + c * y) 1 := by
  have hy : 0 < y := hx.trans_le hxy
  have h1 : 0 < min (ρinf + c * x) 1 := lt_min (by positivity) one_pos
  have h2 : 0 < min (ρinf + c * y) 1 := lt_min (by positivity) one_pos
  have hm : min (ρinf + c * x) 1 ≤ min (ρinf + c * y) 1 := min_le_min (by nlinarith) le_rfl
  rw [div_le_div_iff₀ h1 h2]
  rcases le_total (ρinf + c * y) 1 with hy1 | hy1
  · have hx1 : ρinf + c * x ≤ 1 := by nlinarith
    rw [min_eq_left hy1, min_eq_left hx1]
    nlinarith
  · rw [min_eq_right hy1]
    rcases le_total (ρinf + c * x) 1 with hx1 | hx1
    · rw [min_eq_left hx1]
      rcases le_total 1 (c * y) with hcy | hcy
      · nlinarith
      · nlinarith [mul_nonneg (sub_nonneg.mpr hcy) (sub_nonneg.mpr hxy)]
    · rw [min_eq_right hx1]; nlinarith

end KAM.Sharp2

end
