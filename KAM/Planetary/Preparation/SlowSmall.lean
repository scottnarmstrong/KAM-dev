/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Fast
public import KAM.Planetary.Preparation.SlowData
public import KAM.Planetary.Preparation.LogBounds
public import KAM.Planetary.Preparation.SlowRates

/-!
# Slow averaging: polynomial-in-`log` bounds of the radii (P11A-P7c, `stepP:p11:as-nr`, `as-b2`)

`s₁ ≥ c / (log 1/ε)^{τ+1}` and `s₂ ≥ c' / (log 1/ε)^{τ+1}`, and the eventual inequalities
`ε ℓ^m ≤ δ` obtained from `e4`.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

section Small

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

theorem min_div_le_min {A B P : ℝ} (hA : 0 < A) (hP : 1 ≤ P) :
    min A B / P ≤ min A (B / P) := by
  have hP0 : 0 < P := by linarith
  refine le_min ?_ ?_
  · calc min A B / P ≤ A / P := div_le_div_of_nonneg_right (min_le_left _ _) hP0.le
      _ ≤ A := div_le_self hA.le hP
  · exact div_le_div_of_nonneg_right (min_le_right _ _) hP0.le

/-- Eventually `ε ℓ^m ≤ δ`. -/
theorem eventually_eps_log_le {m δ : ℝ} (hm : 0 ≤ m) (hδ : 0 < δ) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), eps * Real.log (1 / eps) ^ m ≤ δ := by
  have he := e4 (a := (1 : ℝ)) (b := m) one_pos hm
  have := he.eventually (gt_mem_nhds hδ)
  filter_upwards [this] with eps h
  rw [Real.rpow_one] at h
  exact h.le

/-- Lower bound of `s₁`: `s₁ ≥ c / ℓ^{τ+1}`. -/
theorem p11s1_log_lower (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    min C.rC (C.gamma / (4 * C.L)) / ((6 / (Real.pi * C.sigma)) ^ (C.tau + 1) *
      Real.log (1 / eps) ^ (C.tau + 1)) ≤ p11s1 C eps := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  have hεM0 : 0 < eps * C.MF := mul_pos heps hM0
  have hK1 := p11K1_ge_one hC heps hεM
  have hℓΛ : Real.log (1 / (eps * C.MF)) ≤ Real.log (1 / eps) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul heps.ne' hM0.ne']
    have := Real.log_nonneg hMF
    linarith
  have hc30 : 0 < 6 / (Real.pi * C.sigma) := by positivity
  have hKΛ : p11K1 C eps ≤ 6 / (Real.pi * C.sigma) * Real.log (1 / eps) :=
    mul_le_mul_of_nonneg_left hℓΛ hc30.le
  have hP1 : 1 ≤ p11K1 C eps ^ (C.tau + 1) := Real.one_le_rpow hK1 (by linarith)
  have hL0 : 0 < C.L := by linarith
  have hA : 0 < min C.rC (C.gamma / (4 * C.L)) := lt_min hrC0 (by positivity)
  have h1 : min C.rC (C.gamma / (4 * C.L)) / p11K1 C eps ^ (C.tau + 1) ≤ p11s1 C eps := by
    have := min_div_le_min (B := C.gamma / (4 * C.L)) hrC0 hP1
    unfold p11s1
    rw [div_div] at this
    exact (div_le_div_of_nonneg_right (min_le_min_left _ (le_refl _)) (by linarith)).trans this
  refine le_trans ?_ h1
  have hl0 : 0 < Real.log (1 / eps) := by
    have := log_inv_ge_one heps (le_trans (by nlinarith) hεM)
    linarith
  rw [← Real.mul_rpow hc30.le hl0.le]
  exact div_le_div_of_nonneg_left hA.le (by positivity)
    (Real.rpow_le_rpow (by linarith) hKΛ (by linarith))

/-- Lower bound of `s₂`: `s₂ ≥ c / ℓ^{τ+1}`. -/
theorem p11s2_log_lower (hC : P11SecularSpec D C) {nu eps : ℝ} (hnu : 0 < nu) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)))
      (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1))) /
      Real.log (1 / eps) ^ (C.tau + 1) ≤ p11s2 C nu eps := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  have hl0 : 0 < Real.log (1 / eps) := by
    have := log_inv_ge_one heps (le_trans (by nlinarith) hεM)
    linarith
  have hL0 : 0 < C.L := by linarith
  have hc30 : 0 < 6 / (Real.pi * C.sigma) := by positivity
  have ha : 0 < 3 * nu / (Real.pi * (C.sigma / 12)) := by positivity
  have hq : 0 < Real.log (1 / eps) ^ (C.tau + 1) := Real.rpow_pos_of_pos hl0 _
  have hs1 := p11s1_log_lower hC heps hεM
  unfold p11s2
  have hK : p11K2 C nu eps = 3 * nu / (Real.pi * (C.sigma / 12)) * Real.log (1 / eps) := rfl
  have hX : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) := Real.rpow_pos_of_pos hc30 _
  have hY : 0 < (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1) := Real.rpow_pos_of_pos ha _
  refine le_min ?_ ?_
  · refine le_trans ?_ (div_le_div_of_nonneg_right hs1 (by norm_num : (0 : ℝ) ≤ 4))
    calc _ ≤ min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^ (C.tau + 1)) /
          Real.log (1 / eps) ^ (C.tau + 1) :=
          div_le_div_of_nonneg_right (min_le_left _ _) hq.le
      _ = _ := by field_simp
  · rw [hK, Real.mul_rpow ha.le hl0.le]
    calc _ ≤ C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1)) /
          Real.log (1 / eps) ^ (C.tau + 1) :=
          div_le_div_of_nonneg_right (min_le_right _ _) hq.le
      _ = _ := by field_simp

/-- Atoms of the divisor smallness `K c (ε + η₁) ≤ γ K^{-τ}/8`. -/
theorem small_arith_cz {t l a u γ eps c ce η : ℝ} (ht : 1 ≤ t) (hl : 1 ≤ l) (ha : 0 < a)
    (hu : 0 < u) (hγ : 0 < γ) (heps : 0 < eps) (hc : 0 ≤ c) (hce : 0 ≤ ce)
    (hη : η ≤ ce * eps * (t ^ 2 * l))
    (hsm : 8 * u * a * (c * (1 + ce) + 1) * (eps * (t ^ 3 * l ^ 2)) ≤ γ) :
    a * l * (c * (eps + η)) ≤ γ * (u * t)⁻¹ / 8 := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < l := by linarith
  have h1 : 1 ≤ t ^ 2 * l := by nlinarith [pow_le_pow_left₀ zero_le_one ht 2, one_le_pow₀ ht (n := 2)]
  have h2 : eps ≤ eps * (t ^ 2 * l) := by nlinarith
  have h3 : eps + η ≤ (1 + ce) * (eps * (t ^ 2 * l)) := by nlinarith
  have h4 : a * l * (c * (eps + η)) ≤ a * l * (c * ((1 + ce) * (eps * (t ^ 2 * l)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hc) (by positivity)
  refine h4.trans ?_
  rw [div_eq_mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
  have hut : 0 < u * t := by positivity
  have : a * l * (c * ((1 + ce) * (eps * (t ^ 2 * l)))) * 8 * (u * t) =
      8 * u * a * (c * (1 + ce)) * (eps * (t ^ 3 * l ^ 2)) := by ring
  have hpos : 0 ≤ 8 * u * a * (c * (1 + ce)) * (eps * (t ^ 3 * l ^ 2)) := by positivity
  calc a * l * (c * ((1 + ce) * (eps * (t ^ 2 * l)))) * 8
      = a * l * (c * ((1 + ce) * (eps * (t ^ 2 * l)))) * 8 * (u * t) * (u * t)⁻¹ := by
        field_simp
    _ ≤ γ * (u * t)⁻¹ := by
        rw [this]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 8 * u * a)
          (by positivity : 0 ≤ eps * (t ^ 3 * l ^ 2))) (by norm_num : (0:ℝ) ≤ 1)]

/-- Atoms of the Cauchy smallness `ε K M ≤ (γ K^{-τ}/2) R`. -/
theorem small_arith_R {t l a u γ eps MW cR R : ℝ} (ht : 1 ≤ t) (hl : 1 ≤ l) (ha : 0 < a)
    (hu : 0 < u) (hγ : 0 < γ) (heps : 0 < eps) (hMW : 0 ≤ MW) (hcR : 0 < cR)
    (hR : cR * (t * l)⁻¹ ≤ R)
    (hsm : 2 * u * a * (MW + 1) * (eps * (t ^ 2 * l ^ 2)) ≤ γ * cR) :
    eps * (a * l) * MW ≤ γ * (u * t)⁻¹ / 2 * R := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < l := by linarith
  have hγ' : 0 ≤ γ * (u * t)⁻¹ / 2 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hR hγ')
  have e : γ * (u * t)⁻¹ / 2 * (cR * (t * l)⁻¹) = γ * cR / (2 * u * t ^ 2 * l) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  have : eps * (a * l) * MW * (2 * u * t ^ 2 * l) =
      2 * u * a * MW * (eps * (t ^ 2 * l ^ 2)) := by ring
  rw [this]
  have hp : 0 ≤ 2 * u * a * (eps * (t ^ 2 * l ^ 2)) := by positivity
  nlinarith

/-- `ℓ = log (1/ε) ≥ 1` for `ε M ≤ e⁻¹`. -/
theorem slow_log_ge_one (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) : 1 ≤ Real.log (1 / eps) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hMF⟩ := fast_consts hC
  exact log_inv_ge_one heps (le_trans (by nlinarith) hεM)

/-- `K₂ = a ℓ`, the radii `s₁, s₂` are positive. -/
theorem slow_pos (hC : P11SecularSpec D C) {nu eps : ℝ} (hnu : 1 ≤ nu) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    0 < p11K2 C nu eps ∧ 0 < p11s1 C eps ∧ 0 < p11s2 C nu eps := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hl := slow_log_ge_one hC heps hεM
  have hπ := Real.pi_pos
  have hs1 := p11s1_log_lower hC heps hεM
  have hs2 := p11s2_log_lower hC (nu := nu) (by linarith) heps hεM
  have hl0 : 0 < Real.log (1 / eps) := by linarith
  have hL0 : 0 < C.L := by linarith
  have hq : 0 < Real.log (1 / eps) ^ (C.tau + 1) := Real.rpow_pos_of_pos hl0 _
  refine ⟨by unfold p11K2; positivity, lt_of_lt_of_le ?_ hs1, lt_of_lt_of_le ?_ hs2⟩
  · have : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact div_pos (lt_min hrC0 (by positivity)) (by positivity)
  · have h1 : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    have h2 : 0 < (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact div_pos (lt_min (div_pos (lt_min hrC0 (by positivity)) (by positivity))
      (by positivity)) hq

/-- `π ε ≤ s₂` for small `ε`. -/
theorem slow_pe_eventually (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), 0 < eps → eps * C.MF ≤ Real.exp (-1) →
      Real.pi * eps ≤ p11s2 C nu eps := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hπ := Real.pi_pos
  have hL0 : 0 < C.L := by linarith
  have hs1c0 : 0 < min C.rC (C.gamma / (4 * C.L)) := lt_min hrC0 (by positivity)
  have hc3p : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hap : 0 < (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by have : 0 < nu := by linarith
                             positivity) _
  have hcs20 : 0 < min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^
      (C.tau + 1))) (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^
      (C.tau + 1))) := lt_min (by positivity) (by positivity)
  filter_upwards [eventually_eps_log_le (m := C.tau + 1) (by linarith) (div_pos hcs20 hπ)]
    with eps h1 heps hεM
  have hs2 := p11s2_log_lower hC (nu := nu) (by linarith) heps hεM
  have hq : 0 < Real.log (1 / eps) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by have := slow_log_ge_one hC heps hεM; linarith) _
  refine le_trans ?_ hs2
  rw [le_div_iff₀ hq]
  rw [le_div_iff₀ hπ] at h1
  linarith

end Small

end KAM.Planetary

end
