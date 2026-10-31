/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Taylor
public import KAM.Wave.Homological.Extract
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Component bounds, part A: test points and the zeroth/first order bounds
(blueprint-W `bpW:w4:components` (i), steps *Test points* and *Zeroth and first order*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

Hypothesis `hX`: `|X_R|_r ≤ ε` on `D(s,r)`. Conclusions at every `θ ∈ T_s`:
`|b| ≤ 2πε`, `‖c^±‖ ≤ rε/√2`, `‖2P‖, ‖Q‖, ‖Q^T‖, ‖2P'‖ ≤ ε` (norms of the weighted matrices).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem homUV_le (z zb : HomL2) :
    ‖homU z zb‖ + ‖homV z zb‖ ≤ Real.sqrt 2 * (‖z‖ + ‖zb‖) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hn : ‖homSqrt2⁻¹‖ = (Real.sqrt 2)⁻¹ := by rw [norm_inv, norm_homSqrt2]
  have h1 : ‖homU z zb‖ ≤ (Real.sqrt 2)⁻¹ * (‖z‖ + ‖zb‖) := by
    unfold homU
    rw [norm_smul, hn]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
  have h2 : ‖homV z zb‖ ≤ (Real.sqrt 2)⁻¹ * (‖z‖ + ‖zb‖) := by
    unfold homV
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, hn]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
  have : (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by field_simp; linarith
  nlinarith [norm_nonneg z, norm_nonneg zb]

theorem homDomain_y {r : ℝ} {θ y : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) (hr : 0 < r)
    (hy : ‖y‖ < r ^ 2) : HomDomain s r θ y 0 0 := by
  refine ⟨hθ, hy, ?_⟩
  have := homUV_le (0 : HomL2) 0
  simp only [norm_zero, add_zero, mul_zero] at this
  linarith

theorem homDomain_z {r : ℝ} {θ : Fin 2 → ℂ} {z : HomL2} (hθ : θ ∈ complexStrip 2 s)
    (hr : 0 < r) (hz : ‖z‖ < r / Real.sqrt 2) : HomDomain s r θ 0 z 0 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨hθ, by simpa using pow_pos hr 2, ?_⟩
  have := homUV_le z 0
  simp only [norm_zero, add_zero] at this
  have h2 : Real.sqrt 2 * ‖z‖ < r := by
    rwa [lt_div_iff₀ hs, mul_comm] at hz
  linarith

theorem homDomain_zb {r : ℝ} {θ : Fin 2 → ℂ} {zb : HomL2} (hθ : θ ∈ complexStrip 2 s)
    (hr : 0 < r) (hz : ‖zb‖ < r / Real.sqrt 2) : HomDomain s r θ 0 0 zb := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨hθ, by simpa using pow_pos hr 2, ?_⟩
  have := homUV_le 0 zb
  simp only [norm_zero, zero_add] at this
  have h2 : Real.sqrt 2 * ‖zb‖ < r := by
    rwa [lt_div_iff₀ hs, mul_comm] at hz
  linarith

theorem homDomain_zzb {r : ℝ} {θ : Fin 2 → ℂ} {z zb : HomL2} (hθ : θ ∈ complexStrip 2 s)
    (hr : 0 < r) (hz : ‖z‖ < r / (2 * Real.sqrt 2)) (hzb : ‖zb‖ < r / (2 * Real.sqrt 2)) :
    HomDomain s r θ 0 z zb := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨hθ, by simpa using pow_pos hr 2, ?_⟩
  have := homUV_le z zb
  have h2 : Real.sqrt 2 * ‖z‖ < r / 2 := by
    have : ‖z‖ * (2 * Real.sqrt 2) < r := by rwa [lt_div_iff₀ (by positivity)] at hz
    linarith
  have h3 : Real.sqrt 2 * ‖zb‖ < r / 2 := by
    have : ‖zb‖ * (2 * Real.sqrt 2) < r := by rwa [lt_div_iff₀ (by positivity)] at hzb
    linarith
  nlinarith

/-- **Affine extraction**: if `‖v₀ + ζ L x‖ ≤ K` for `‖ζ‖ < ρ`, `‖x‖ ≤ 1`, then `‖L‖ ≤ K/ρ`. -/
theorem homAffine_bound {E E1 : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E1] [NormedSpace ℂ E1] {ρ K : ℝ} (hρ : 0 < ρ) (v0 : E) (L : E1 →L[ℂ] E)
    (hK : ∀ x : E1, ‖x‖ ≤ 1 → ∀ ζ : ℂ, ‖ζ‖ < ρ → ‖v0 + ζ • L x‖ ≤ K) : ‖L‖ ≤ K / ρ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simp) 0 (by simpa using hρ))
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hK0 hρ.le) fun x hx => ?_
  have h := polyExtract_one (![v0, L x, 0] : Fin 3 → E) hρ (K := K) (fun ζ hζ => by
    have : ∑ p : Fin 3, ζ ^ (p : ℕ) • (![v0, L x, 0] : Fin 3 → E) p = v0 + ζ • L x := by
      simp [Fin.sum_univ_three]
    rw [this]
    exact hK x hx.le ζ hζ) 1
  simpa using h

/-- `‖R_z‖, ‖R_{\bar z}‖ ≤ rε/√2` and the three parts of the norm at a domain point. -/
theorem homXnorm_parts_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0
    < r)
    (T : HomTaylor_gen a p pb s) {θ y : Fin 2 → ℂ} {z zb : HomL2}
    (h : homXnorm_gen ha hp hpb r T θ y z zb ≤ ε) :
    ‖homRy_gen T θ‖ ≤ 2 * Real.pi * ε ∧
      ‖fun i => homRtheta_gen ha hp hpb T i θ y z zb‖ ≤ 2 * Real.pi * r ^ 2 * ε ∧
      ‖homRu_gen T θ z zb‖ + ‖homRv_gen T θ z zb‖ ≤ r * ε ∧
      ‖homRz_gen T θ z zb‖ ≤ r * ε / Real.sqrt 2 ∧ ‖homRzb_gen T θ z zb‖ ≤ r * ε / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hπ := Real.pi_pos
  unfold homXnorm_gen at h
  have t1 : 0 ≤ (2 * Real.pi)⁻¹ * ‖homRy_gen T θ‖ := by positivity
  have t2 : 0 ≤ (2 * Real.pi * r ^ 2)⁻¹ * ‖fun i => homRtheta_gen ha hp hpb T i θ y z zb‖ := by
      positivity
  have t3 : 0 ≤ r⁻¹ * (‖homRu_gen T θ z zb‖ + ‖homRv_gen T θ z zb‖) := by positivity
  have e1 : ‖homRy_gen T θ‖ ≤ 2 * Real.pi * ε := by
    have : (2 * Real.pi)⁻¹ * ‖homRy_gen T θ‖ ≤ ε := by linarith
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)] at this
    linarith
  have e2 : ‖fun i => homRtheta_gen ha hp hpb T i θ y z zb‖ ≤ 2 * Real.pi * r ^ 2 * ε := by
    have : (2 * Real.pi * r ^ 2)⁻¹ * ‖fun i => homRtheta_gen ha hp hpb T i θ y z zb‖ ≤ ε := by
        linarith
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)] at this
    linarith
  have e3 : ‖homRu_gen T θ z zb‖ + ‖homRv_gen T θ z zb‖ ≤ r * ε := by
    have : r⁻¹ * (‖homRu_gen T θ z zb‖ + ‖homRv_gen T θ z zb‖) ≤ ε := by linarith
    rw [← div_eq_inv_mul, div_le_iff₀ hr] at this
    linarith
  have hn : ‖homSqrt2⁻¹‖ = (Real.sqrt 2)⁻¹ := by rw [norm_inv, norm_homSqrt2]
  refine ⟨e1, e2, e3, ?_, ?_⟩
  · rw [homRz_eq_gen, norm_smul, hn]
    refine le_trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)) ?_
    rw [norm_smul, Complex.norm_I, one_mul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left e3 (by positivity)
  · rw [homRzb_eq_gen, norm_smul, hn]
    refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)) ?_
    rw [norm_smul, Complex.norm_I, one_mul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left e3 (by positivity)

end KAM.Wave
