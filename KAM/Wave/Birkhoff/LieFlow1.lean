/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieLeibniz

/-!
# The flow `Γ_t = Σ t^k φ_k`: convergence and estimates (blueprint-W `bpW:w3:flow` (i), (iii))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

For a symmetric continuous trilinear `T` on `E` with `‖T v‖ ≤ C ∏‖v_i‖` and `q = 2|t|C‖w‖² ≤ 1/10`:
`norm_lieTerm_le` (`‖t^kφ_k(w)‖ ≤ q^k‖w‖`), `summable_lieTerm`, `norm_lieGamma_le`
(`‖Γ_t(w)‖ ≤ (10/9)‖w‖`),
`norm_lieGamma_sub_le` (`‖Γ_t(w) - w‖ ≤ 3|t|C‖w‖³`), `norm_lieGammaD_sub_le`
(`‖DΓ_t(w) - I‖ ≤ 10|t|C‖w‖²`).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ContinuousMultilinearMap ℂ
  (fun _ : Fin 3 => E) E)

/-- `Γ_t(w) = Σ t^k φ_k(w)`. -/
def lieGamma (t : ℝ) (w : E) : E := ∑' k, (t ^ k) • lieSeq T w k

/-- `DΓ_t(w) = Σ t^k Dφ_k(w)`. -/
def lieGammaD (t : ℝ) (w : E) : E →L[ℂ] E := ∑' k, (t ^ k) • lieDer T w k

section Bounds

variable {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
theorem norm_lieTerm_le (t : ℝ) (w : E) (k : ℕ) :
    ‖(t ^ k) • lieSeq T w k‖ ≤ (2 * |t| * C * ‖w‖ ^ 2) ^ k * ‖w‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  refine (mul_le_mul_of_nonneg_left (norm_lieSeq_le T hC hT w k) (by positivity)).trans ?_
  have hm := birkLieM_le_pow k
  have h0 := birkLieM_nonneg k
  calc |t| ^ k * (birkLieM k * C ^ k * ‖w‖ ^ (2 * k + 1))
      ≤ |t| ^ k * (2 ^ k * C ^ k * ‖w‖ ^ (2 * k + 1)) := by gcongr
    _ = (2 * |t| * C * ‖w‖ ^ 2) ^ k * ‖w‖ := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring

include hC hT in
theorem norm_lieDTerm_le (t : ℝ) (w : E) (k : ℕ) :
    ‖(t ^ k) • lieDer T w k‖ ≤ (2 * k + 1) * (2 * |t| * C * ‖w‖ ^ 2) ^ k := by
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  refine (mul_le_mul_of_nonneg_left (norm_lieDer_le T hC hT w k) (by positivity)).trans ?_
  have hm := birkLieM_le_pow k
  have h0 := birkLieM_nonneg k
  calc |t| ^ k * ((2 * k + 1) * birkLieM k * C ^ k * ‖w‖ ^ (2 * k))
      ≤ |t| ^ k * ((2 * k + 1) * 2 ^ k * C ^ k * ‖w‖ ^ (2 * k)) := by gcongr
    _ = (2 * k + 1) * (2 * |t| * C * ‖w‖ ^ 2) ^ k := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring

theorem geom_sums (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1 / 10) :
    (∑' k : ℕ, q ^ k) ≤ 10 / 9 ∧ (∑' k : ℕ, q ^ (k + 1)) ≤ 10 / 9 * q ∧
      (∑' k : ℕ, (2 * ((k + 1 : ℕ) : ℝ) + 1) * q ^ (k + 1)) ≤ 5 * q := by
  have hq : q < 1 := by linarith
  have hg : ∑' k : ℕ, q ^ k = (1 - q)⁻¹ := tsum_geometric_of_lt_one h0 hq
  have hg' : ∑' k : ℕ, q ^ (k + 1) = q * (1 - q)⁻¹ := by
    simp only [pow_succ, tsum_mul_right, hg]; ring
  have hs : ∑' k : ℕ, ((k : ℝ)) * q ^ k = q / (1 - q) ^ 2 := by
    simpa using tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := q)
      (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact hq)
  have h1q : 0 < 1 - q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hg, inv_eq_one_div, div_le_iff₀ h1q]; linarith
  · rw [hg', ← div_eq_mul_inv, div_le_iff₀ h1q]; nlinarith
  · have hsum1 : Summable fun k : ℕ => ((k : ℝ)) * q ^ k := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
        (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact hq)
    have hsum0 : Summable fun k : ℕ => q ^ k := summable_geometric_of_lt_one h0 hq
    have e : ∀ k : ℕ, (2 * ((k + 1 : ℕ) : ℝ) + 1) * q ^ (k + 1) =
        2 * (((k + 1 : ℕ) : ℝ) * q ^ (k + 1)) + q ^ (k + 1) := fun k => by ring
    simp only [e]
    have s1 : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * q ^ (k + 1) :=
      (summable_nat_add_iff 1).2 hsum1
    have s2 : Summable fun k : ℕ => q ^ (k + 1) := (summable_nat_add_iff 1).2 hsum0
    rw [(s1.mul_left 2).tsum_add s2, tsum_mul_left, hg']
    have shift : ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * q ^ (k + 1) = q / (1 - q) ^ 2 := by
      have := hsum1.tsum_eq_zero_add
      rw [hs] at this
      simpa using this.symm
    rw [shift]
    have h3 : (1 - q)⁻¹ ≤ 10 / 9 := by rw [inv_eq_one_div, div_le_iff₀ h1q]; linarith
    have h4 : (1 - q) ^ 2 ≥ 81 / 100 := by nlinarith
    have h5 : q / (1 - q) ^ 2 ≤ q * (100 / 81) := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith

variable [CompleteSpace E]

include hC hT in
theorem summable_norm_lieTerm (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    Summable fun k => ‖(t ^ k) • lieSeq T w k‖ := by
  have h0 : 0 ≤ 2 * |t| * C * ‖w‖ ^ 2 := by positivity
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_lieTerm_le T hC hT t w)
    ((summable_geometric_of_lt_one h0 (by linarith)).mul_right ‖w‖)

include hC hT in
theorem summable_norm_lieDTerm (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    Summable fun k => ‖(t ^ k) • lieDer T w k‖ := by
  have h0 : 0 ≤ 2 * |t| * C * ‖w‖ ^ 2 := by positivity
  have hs : Summable fun k : ℕ => ((k : ℝ)) * (2 * |t| * C * ‖w‖ ^ 2) ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := 2 * |t| * C * ‖w‖ ^ 2) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; linarith)
  have hg : Summable fun k : ℕ => (2 * |t| * C * ‖w‖ ^ 2) ^ k :=
    summable_geometric_of_lt_one h0 (by linarith)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => ?_) ((hs.mul_left 2).add hg)
  refine (norm_lieDTerm_le T hC hT t w k).trans (le_of_eq ?_)
  ring

include hC hT in
theorem summable_lieTerm (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    Summable fun k => (t ^ k) • lieSeq T w k := (summable_norm_lieTerm T hC hT t w hq).of_norm

include hC hT in
theorem summable_lieDTerm (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    Summable fun k => (t ^ k) • lieDer T w k := (summable_norm_lieDTerm T hC hT t w hq).of_norm

include hC hT in
/-- `‖Γ_t(w)‖ ≤ (10/9)‖w‖`. -/
theorem norm_lieGamma_le (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    ‖lieGamma T t w‖ ≤ 10 / 9 * ‖w‖ := by
  have h0 : 0 ≤ 2 * |t| * C * ‖w‖ ^ 2 := by positivity
  have hsn := summable_norm_lieTerm T hC hT t w hq
  have hs := summable_lieTerm T hC hT t w hq
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine (Summable.tsum_le_tsum (norm_lieTerm_le T hC hT t w) hsn
    ((summable_geometric_of_lt_one h0 (by linarith)).mul_right ‖w‖)).trans ?_
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (geom_sums _ h0 hq).1 (norm_nonneg _) |>.trans (by linarith)

include hC hT in
/-- `‖Γ_t(w) - w‖ ≤ 3 |t| C ‖w‖³`. -/
theorem norm_lieGamma_sub_le (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    ‖lieGamma T t w - w‖ ≤ 3 * |t| * C * ‖w‖ ^ 3 := by
  have h0 : 0 ≤ 2 * |t| * C * ‖w‖ ^ 2 := by positivity
  have hsn := summable_norm_lieTerm T hC hT t w hq
  have hs := summable_lieTerm T hC hT t w hq
  have hsplit : lieGamma T t w - w = ∑' k, (t ^ (k + 1)) • lieSeq T w (k + 1) := by
    unfold lieGamma
    rw [hs.tsum_eq_zero_add]
    simp only [pow_zero, one_smul, lieSeq_zero, add_sub_cancel_left]
  rw [hsplit]
  have hs1n : Summable fun k => ‖(t ^ (k + 1)) • lieSeq T w (k + 1)‖ :=
    (summable_nat_add_iff (f := fun k => ‖(t ^ k) • lieSeq T w k‖) 1).2 hsn
  have hg := summable_geometric_of_lt_one h0 (by linarith)
  have hg1 : Summable fun k : ℕ => (2 * |t| * C * ‖w‖ ^ 2) ^ (k + 1) * ‖w‖ :=
    ((summable_nat_add_iff (f := fun k : ℕ => (2 * |t| * C * ‖w‖ ^ 2) ^ k) 1).2 hg).mul_right _
  refine (norm_tsum_le_tsum_norm hs1n).trans ?_
  refine (Summable.tsum_le_tsum (fun k => norm_lieTerm_le T hC hT t w (k + 1)) hs1n hg1).trans ?_
  rw [tsum_mul_right]
  have := (geom_sums _ h0 hq).2.1
  have hw := norm_nonneg w
  calc (∑' k : ℕ, (2 * |t| * C * ‖w‖ ^ 2) ^ (k + 1)) * ‖w‖
      ≤ 10 / 9 * (2 * |t| * C * ‖w‖ ^ 2) * ‖w‖ := mul_le_mul_of_nonneg_right this hw
    _ ≤ 3 * |t| * C * ‖w‖ ^ 3 := by
      have : 0 ≤ |t| * C * ‖w‖ ^ 3 := by positivity
      nlinarith

include hC hT in
/-- `‖DΓ_t(w) - I‖ ≤ 10 |t| C ‖w‖²`. -/
theorem norm_lieGammaD_sub_le (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    ‖lieGammaD T t w - ContinuousLinearMap.id ℂ E‖ ≤ 10 * |t| * C * ‖w‖ ^ 2 := by
  have h0 : 0 ≤ 2 * |t| * C * ‖w‖ ^ 2 := by positivity
  have hsn := summable_norm_lieDTerm T hC hT t w hq
  have hs := summable_lieDTerm T hC hT t w hq
  have hsplit : lieGammaD T t w - ContinuousLinearMap.id ℂ E =
      ∑' k, (t ^ (k + 1)) • lieDer T w (k + 1) := by
    unfold lieGammaD
    rw [hs.tsum_eq_zero_add]
    simp only [pow_zero, one_smul, lieDer_zero, add_sub_cancel_left]
  rw [hsplit]
  have hs1 : Summable fun k => (t ^ (k + 1)) • lieDer T w (k + 1) :=
    (summable_nat_add_iff 1).2 hs
  have hb : ∀ k : ℕ, ‖(t ^ (k + 1)) • lieDer T w (k + 1)‖ ≤
      (2 * ((k + 1 : ℕ) : ℝ) + 1) * (2 * |t| * C * ‖w‖ ^ 2) ^ (k + 1) := fun k => by
    have := norm_lieDTerm_le T hC hT t w (k + 1)
    push_cast at this ⊢
    exact this
  have hs1n : Summable fun k => ‖(t ^ (k + 1)) • lieDer T w (k + 1)‖ :=
    (summable_nat_add_iff (f := fun k => ‖(t ^ k) • lieDer T w k‖) 1).2 hsn
  have hsum : Summable fun k : ℕ => (2 * ((k + 1 : ℕ) : ℝ) + 1) *
      (2 * |t| * C * ‖w‖ ^ 2) ^ (k + 1) := by
    have hq1 : 2 * |t| * C * ‖w‖ ^ 2 < 1 := by linarith
    have hs : Summable fun k : ℕ => ((k : ℝ)) * (2 * |t| * C * ‖w‖ ^ 2) ^ k := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1
        (r := 2 * |t| * C * ‖w‖ ^ 2) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact hq1)
    have hg : Summable fun k : ℕ => (2 * |t| * C * ‖w‖ ^ 2) ^ k :=
      summable_geometric_of_lt_one h0 hq1
    have := ((hs.mul_left 2).add hg)
    have h' := (summable_nat_add_iff 1).2 this
    refine h'.congr fun k => ?_
    push_cast; ring
  refine (norm_tsum_le_tsum_norm hs1n).trans ?_
  refine (Summable.tsum_le_tsum hb hs1n hsum).trans ?_
  refine ((geom_sums _ h0 hq).2.2).trans ?_
  nlinarith

end Bounds

end KAM.Wave

end
