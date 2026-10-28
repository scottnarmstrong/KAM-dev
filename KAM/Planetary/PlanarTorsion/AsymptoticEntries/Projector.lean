/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Inputs

/-!
# Planar quartic torsion: the spectral projector at hierarchical axes (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, step `stepP:p11b:as-pi`): with `Δ_Q = Q₁₁ - Q₂₂ < 0`
and `R = √(Δ_Q² + 4 Q₁₂²) ≥ |Δ_Q|`, the projector satisfies `π₁₂ = -Q₁₂ / R`,
`π₂₂ = (Δ_Q + R) / (2 R)`, hence `|π₁₂| ≤ |Q₁₂| / |Δ_Q| = O(α ^ (5/4))`,
`0 ≤ π₂₂ ≤ Q₁₂² / Δ_Q² = O(α ^ (5/2))` and `π₁₁ = 1 - π₂₂`.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

/-- The entries of the projector in terms of `Q`, valid when `Δ_Q ≠ 0`. -/
theorem p11cAe_proj_exact (p : PlanarData) {α : ℝ}
    (hΔ : p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1 < 0) :
    p11c_projector p ![α, 1] 0 1 = -p11c_Q p ![α, 1] 0 1 /
        √((p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) ^ 2 + 4 * p11c_Q p ![α, 1] 0 1 ^ 2) ∧
    p11c_projector p ![α, 1] 1 1 =
      ((p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) +
        √((p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) ^ 2 + 4 * p11c_Q p ![α, 1] 0 1 ^ 2)) /
      (2 * √((p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) ^ 2 +
        4 * p11c_Q p ![α, 1] 0 1 ^ 2)) := by
  set Δ := p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1 with hΔdef
  set q := p11c_Q p ![α, 1] 0 1 with hq
  set R := √(Δ ^ 2 + 4 * q ^ 2) with hR
  have hRpos : 0 < R := Real.sqrt_pos.2 (by nlinarith [sq_nonneg q, sq_pos_of_neg hΔ])
  have hσ : p11c_sigma p ![α, 1] 0 - p11c_sigma p ![α, 1] 1 = -R := by
    simp only [p11c_sigma, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hR, hΔdef, hq]
    ring
  have hs1 : p11c_sigma p ![α, 1] 1 = (p11c_Q p ![α, 1] 0 0 + p11c_Q p ![α, 1] 1 1 + R) / 2 := by
    simp only [p11c_sigma, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
    rw [hR, hΔdef, hq]
  have e01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by simp
  constructor
  · simp only [p11c_projector, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, e01]
    rw [hσ, ← hq]
    field_simp
    ring
  · simp only [p11c_projector, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq,
      smul_eq_mul]
    rw [hσ, hs1]
    field_simp
    ring

/-- `-Δ_Q ≥ k α ^ (3/2)` for small `α`, from `as_in`. -/
theorem p11cAe_delta_lower (p : PlanarData) (hp : p.Valid) :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ α : ℝ in 𝓝[>] 0,
      k * α ^ (3 / 2 : ℝ) ≤ -(p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) := by
  obtain ⟨P1, P2, -, -, -⟩ := as_in p hp
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hsk : 0 < √p.kappa := Real.sqrt_pos.2 hk
  have hk1 : 0 < 3 * p.G * p.m 1 / (8 * √p.kappa) := by
    have := hp.2.2 1; have := hp.1; positivity
  have hQ11 : (fun α => p11c_Q p ![α, 1] 1 1) =O[𝓝[>] 0] fun α : ℝ => α ^ (2 : ℝ) :=
    p11cAe_lead_isBigO' (c := 3 * p.G * p.m 0 / (8 * √p.kappa)) (by norm_num) P2
  have P1' : (fun α => (p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) +
      3 * p.G * p.m 1 / (8 * √p.kappa) * α ^ (3 / 2 : ℝ)) =O[𝓝[>] 0] fun α : ℝ => α ^ (2 : ℝ) :=
    ((P1.trans (p11cAe_rpow_isBigO (by norm_num : (2 : ℝ) ≤ 7 / 2))).sub hQ11).congr_left
      fun a => by ring
  exact ⟨_, half_pos hk1, p11cAe_lower hk1 (by norm_num : (3 / 2 : ℝ) < 2) P1'⟩

/-- `bpP:p11b:asymptotics`, step `as-pi`: bounds on the projector entries at `a = ![α, 1]`. -/
theorem as_pi (p : PlanarData) (hp : p.Valid) :
    (∀ᶠ α : ℝ in 𝓝[>] 0,
      |p11c_projector p ![α, 1] 0 1| ≤
          |p11c_Q p ![α, 1] 0 1| / |p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1| ∧
      0 ≤ p11c_projector p ![α, 1] 1 1 ∧
      p11c_projector p ![α, 1] 1 1 ≤
          p11c_Q p ![α, 1] 0 1 ^ 2 / (p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) ^ 2 ∧
      p11c_projector p ![α, 1] 0 0 = 1 - p11c_projector p ![α, 1] 1 1) ∧
    (fun α => p11c_projector p ![α, 1] 0 1) =O[𝓝[>] 0] (fun α : ℝ => α ^ (5 / 4 : ℝ)) ∧
    (fun α => p11c_projector p ![α, 1] 1 1) =O[𝓝[>] 0] (fun α : ℝ => α ^ (5 / 2 : ℝ)) := by
  obtain ⟨-, -, hQ01, hneg, -⟩ := as_in p hp
  obtain ⟨k, hk, hlow⟩ := p11cAe_delta_lower p hp
  have hD : (fun a : ℝ => a ^ (3 / 2 : ℝ)) =O[𝓝[>] 0]
      fun a => p11c_Q p ![a, 1] 0 0 - p11c_Q p ![a, 1] 1 1 :=
    p11cAe_rpow_isBigO_of_lower hk hlow
  have hinv := hD.inv_rev (by
    filter_upwards [p11cAe_pos] with a h0 h
    exact absurd h (Real.rpow_pos_of_pos h0 _).ne')
  have hinv' : (fun a => (p11c_Q p ![a, 1] 0 0 - p11c_Q p ![a, 1] 1 1)⁻¹) =O[𝓝[>] 0]
      fun a : ℝ => a ^ (-(3 / 2) : ℝ) :=
    hinv.congr' EventuallyEq.rfl (p11cAe_pos.mono fun a ha => (Real.rpow_neg ha.le _).symm)
  have hw := p11cAe_congr_exp (s := 5 / 4) (by norm_num) (p11cAe_mul hQ01 hinv')
  have hww := p11cAe_congr_exp (s := 5 / 2) (by norm_num) (p11cAe_mul hw hw)
  have key : ∀ᶠ α : ℝ in 𝓝[>] 0,
      |p11c_projector p ![α, 1] 0 1| ≤
          |p11c_Q p ![α, 1] 0 1| / |p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1| ∧
      0 ≤ p11c_projector p ![α, 1] 1 1 ∧
      p11c_projector p ![α, 1] 1 1 ≤
          p11c_Q p ![α, 1] 0 1 ^ 2 / (p11c_Q p ![α, 1] 0 0 - p11c_Q p ![α, 1] 1 1) ^ 2 ∧
      p11c_projector p ![α, 1] 0 0 = 1 - p11c_projector p ![α, 1] 1 1 := by
    filter_upwards [hneg, p11cAe_pos, p11cAe_lt_one] with a hΔ h0 h1
    obtain ⟨e01, e11⟩ := p11cAe_proj_exact p hΔ
    have htr := p11c_projector_trace p hp (a := ![a, 1]) ⟨by simpa using h0, by simpa using h1⟩
    set Δ := p11c_Q p ![a, 1] 0 0 - p11c_Q p ![a, 1] 1 1 with hΔdef
    set q := p11c_Q p ![a, 1] 0 1 with hq
    set R := √(Δ ^ 2 + 4 * q ^ 2) with hR
    have hR2 : R ^ 2 = Δ ^ 2 + 4 * q ^ 2 := Real.sq_sqrt (by positivity)
    have hRd : -Δ ≤ R := by
      have := Real.abs_le_sqrt (x := Δ) (y := Δ ^ 2 + 4 * q ^ 2) (by nlinarith [sq_nonneg q])
      rw [← hR] at this
      exact (neg_le_abs Δ).trans this
    have hRpos : 0 < R := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e01, abs_div, abs_neg, abs_of_pos hRpos]
      exact div_le_div_of_nonneg_left (abs_nonneg q) (abs_pos.2 hΔ.ne) (by
        rw [abs_of_neg hΔ]; exact hRd)
    · rw [e11]; exact div_nonneg (by linarith) (by positivity)
    · rw [e11, div_le_div_iff₀ (by linarith) (sq_pos_of_neg hΔ)]
      have h1 : 0 ≤ R + Δ := by linarith
      have h2 : 0 ≤ R * (R - Δ) / 2 - Δ ^ 2 := by
        nlinarith [mul_nonneg h1 (show 0 ≤ R - 2 * Δ by linarith)]
      nlinarith [mul_nonneg h1 h2]
    · linarith
  refine ⟨key, ?_, ?_⟩
  · refine (IsBigO.of_bound 1 (key.mono fun a ha => ?_)).trans hw
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_inv, one_mul, ← div_eq_mul_inv]
    exact ha.1
  · refine (IsBigO.of_bound 1 (key.mono fun a ha => ?_)).trans hww
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha.2.1,
      abs_of_nonneg (mul_self_nonneg _), one_mul]
    refine ha.2.2.1.trans (le_of_eq ?_)
    generalize p11c_Q p ![a, 1] 0 0 - p11c_Q p ![a, 1] 1 1 = D
    generalize p11c_Q p ![a, 1] 0 1 = q
    ring

end KAM.Planetary

end
