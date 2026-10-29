/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedJets

/-!
# The polar average `Ĝ₀`: the normalized jet bound (P11A-P8b, `stepP:p11:pr-in` (i))

* `p11_prin_MF_eta1_le`: `M_F + η₁(ε) ≤ K M_F` with `K` fixed before `ε`, on the whole range
  `ε M_F ≤ e⁻¹` (no further shrinking is needed, since `ε ℓ^p ≤ (2p)^p` for `ε ≤ 1`).
* `p11_prin_G0_jet_MF`, `p11_prin_G0_jet_log`: `|∂_J^β Ĝ₀| ≤ K M_F β! (4/s₁)^{|β|}
  ≤ c ℓ^{(τ₀+1)|β|}` for the actual `Ĝ₀ = p11PolarAverage Fast.G`.

The suppressed constant `c` of the source may depend on `n`, `τ`, the fixed data and the
derivative orders, fixed before `ε`; the explicit order factors are therefore acceptable.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section PrInG0

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- `ε ℓ^p ≤ (2p)^p` for `0 < ε ≤ 1`, `ℓ = log (1/ε)`. -/
theorem p11_prin_eps_log_le {p eps : ℝ} (hp : 0 < p) (heps : 0 < eps) (h1 : eps ≤ 1) :
    eps * Real.log (1 / eps) ^ p ≤ (2 * p) ^ p := by
  have hx : 1 ≤ 1 / eps := by rw [le_div_iff₀ heps]; linarith
  have hl0 : 0 ≤ Real.log (1 / eps) := Real.log_nonneg hx
  have hε : 0 < 1 / (2 * p) := by positivity
  have hlog := Real.log_le_rpow_div (by linarith : (0:ℝ) ≤ 1 / eps) hε
  have hpow : Real.log (1 / eps) ^ p ≤ ((1 / eps) ^ (1 / (2 * p)) / (1 / (2 * p))) ^ p :=
    Real.rpow_le_rpow hl0 hlog hp.le
  have e : ((1 / eps) ^ (1 / (2 * p)) / (1 / (2 * p))) ^ p =
      (1 / eps) ^ (1 / (2 : ℝ)) * (2 * p) ^ p := by
    rw [Real.div_rpow (by positivity) hε.le, ← Real.rpow_mul (by linarith)]
    have : 1 / (2 * p) * p = 1 / 2 := by field_simp
    have e2 : (1 / (2 * p))⁻¹ = 2 * p := by field_simp
    rw [this, div_eq_mul_inv, ← Real.inv_rpow hε.le, e2]
  have h2 : (1 / eps) ^ (1 / (2 : ℝ)) ≤ 1 / eps := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hq : 0 ≤ (2 * p) ^ p := Real.rpow_nonneg (by positivity) _
  calc eps * Real.log (1 / eps) ^ p ≤ eps * ((1 / eps) ^ (1 / (2 : ℝ)) * (2 * p) ^ p) := by
        gcongr; exact hpow.trans e.le
    _ ≤ eps * (1 / eps * (2 * p) ^ p) := by gcongr
    _ = _ := by field_simp

/-- `M_F + η₁(ε) ≤ K M_F`, with `K ≥ 1` fixed before `ε`.  (The suppressed constant of the
source may depend on `n`, `τ`, the data and the derivative orders, fixed before `ε`.) -/
theorem p11_prin_MF_eta1_le (hC : P11SecularSpec D C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {eps : ℝ}, 0 < eps → eps * C.MF ≤ Real.exp (-1) →
      C.MF + p11eta1 C eps ≤ K * C.MF := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨k, hk, hη⟩ := p11_prin_eta1_le hC
  have hp : 0 < 2 * C.tau + 1 := by linarith
  have hq : 0 ≤ (2 * (2 * C.tau + 1)) ^ (2 * C.tau + 1) := Real.rpow_nonneg (by positivity) _
  refine ⟨1 + k * (2 * (2 * C.tau + 1)) ^ (2 * C.tau + 1), by nlinarith, ?_⟩
  intro eps heps hεM
  have hε1 : eps ≤ 1 := by
    have h : eps * 1 ≤ eps * C.MF := mul_le_mul_of_nonneg_left hMF heps.le
    have := Real.exp_le_one_iff.2 (by norm_num : (-1 : ℝ) ≤ 0)
    linarith
  have h1 := hη heps hεM
  have h2 := p11_prin_eps_log_le hp heps hε1
  have h3 : p11eta1 C eps ≤ k * (2 * (2 * C.tau + 1)) ^ (2 * C.tau + 1) := by
    calc _ ≤ k * eps * Real.log (1 / eps) ^ (2 * C.tau + 1) := h1
      _ = k * (eps * Real.log (1 / eps) ^ (2 * C.tau + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hk.le
  have h4 : k * (2 * (2 * C.tau + 1)) ^ (2 * C.tau + 1) ≤
      k * (2 * (2 * C.tau + 1)) ^ (2 * C.tau + 1) * C.MF :=
    le_mul_of_one_le_right (by positivity) hMF
  nlinarith

/-- Step pr-in (i), `M_F` form: `|∂_J^β Ĝ₀| ≤ K M_F β! (4/s₁)^{|β|}` for the actual
`Ĝ₀ = p11PolarAverage Fast.G`, with `K` fixed before `ε`.  The suppressed constant of the
source may depend on `n`, `τ`, the data and the derivative orders. -/
theorem p11_prin_G0_jet_MF (hC : P11SecularSpec D C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {Fast : P11FastData n} {eps : ℝ}, 0 < eps →
      eps * C.MF ≤ Real.exp (-1) → P11FastSpec C eps Fast →
      ∀ (β : Fin n → ℕ) (J ρ : P11CVec n),
        ‖J - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4 →
        ‖ρ‖ < Real.pi * (C.rz / 2) ^ 2 →
        ‖p11PartialVec β (fun (J : P11CVec n) (_ : Fin 1) => p11PolarAverage Fast.G (J, ρ)) J‖ ≤
          K * C.MF * (∏ i, ((β i).factorial : ℝ)) * (4 / p11s1 C eps) ^ (∑ i, β i) := by
  obtain ⟨K, hK, hKb⟩ := p11_prin_MF_eta1_le hC
  refine ⟨K, hK, ?_⟩
  intro Fast eps heps hεM hF β J ρ hJ hρ
  have h := p11_prin_G0_jet hC heps hεM hF β J ρ hJ hρ
  have hb := hKb heps hεM
  have hP : 0 ≤ ∏ i, ((β i).factorial : ℝ) := by positivity
  have e : (∏ i, ((β i).factorial : ℝ)) * (C.MF + p11eta1 C eps) /
      (p11s1 C eps / 4) ^ (∑ i, β i) =
      (∏ i, ((β i).factorial : ℝ)) * (C.MF + p11eta1 C eps) *
        (4 / p11s1 C eps) ^ (∑ i, β i) := by
    rw [div_eq_mul_inv, ← inv_pow, inv_div]
  rw [e] at h
  refine h.trans ?_
  have hs := (slow_pos hC (nu := 1) le_rfl heps hεM).2.1
  have hpos : 0 ≤ (4 / p11s1 C eps) ^ (∑ i, β i) := by positivity
  calc _ ≤ (∏ i, ((β i).factorial : ℝ)) * (K * C.MF) * (4 / p11s1 C eps) ^ (∑ i, β i) := by
        gcongr
    _ = _ := by ring

/-- Step pr-in (i), logarithmic form: `|∂_J^β Ĝ₀| ≤ c ℓ^{(τ₀+1)|β|}` for `Ĝ₀ =
p11PolarAverage Fast.G`, with `c` fixed before `ε` (depending on `n`, `τ`, the data and
`β`, as in the source's suppressed constant).  `c = K M_F β! (4 k)^{|β|}`. -/
theorem p11_prin_G0_jet_log (hC : P11SecularSpec D C) (β : Fin n → ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Fast : P11FastData n} {eps : ℝ}, 0 < eps →
      eps * C.MF ≤ Real.exp (-1) → P11FastSpec C eps Fast →
      ∀ (J ρ : P11CVec n),
        ‖J - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4 →
        ‖ρ‖ < Real.pi * (C.rz / 2) ^ 2 →
        ‖p11PartialVec β (fun (J : P11CVec n) (_ : Fin 1) => p11PolarAverage Fast.G (J, ρ)) J‖ ≤
          c * Real.log (1 / eps) ^ ((C.tau + 1) * ((∑ i, β i : ℕ) : ℝ)) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, -, hrz0, -, hMF⟩ := fast_consts hC
  obtain ⟨K, hK, hG⟩ := p11_prin_G0_jet_MF hC (D := D)
  obtain ⟨k, hk, hs⟩ := p11_prin_s1_inv hC
  have hP : 0 ≤ ∏ i, ((β i).factorial : ℝ) := by positivity
  refine ⟨K * C.MF * (∏ i, ((β i).factorial : ℝ)) * (4 * k) ^ (∑ i, β i), by positivity, ?_⟩
  intro Fast eps heps hεM hF J ρ hJ hρ
  have h := hG heps hεM hF β J ρ hJ hρ
  refine h.trans ?_
  have hl0 : 0 < Real.log (1 / eps) := by linarith [slow_log_ge_one hC heps hεM]
  have hs0 := (slow_pos hC (nu := 1) le_rfl heps hεM).2.1
  have h4 : 4 / p11s1 C eps ≤ 4 * k * Real.log (1 / eps) ^ (C.tau + 1) := by
    calc 4 / p11s1 C eps = 4 * (p11s1 C eps)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 4 * (k * Real.log (1 / eps) ^ (C.tau + 1)) :=
          mul_le_mul_of_nonneg_left (hs heps hεM) (by norm_num)
      _ = _ := by ring
  have hq : Real.log (1 / eps) ^ ((C.tau + 1) * ((∑ i, β i : ℕ) : ℝ)) =
      (Real.log (1 / eps) ^ (C.tau + 1)) ^ (∑ i, β i) := by
    rw [Real.rpow_mul hl0.le, Real.rpow_natCast]
  rw [hq]
  have h5 := pow_le_pow_left₀ (by positivity) h4 (∑ i, β i)
  have h6 : (4 / p11s1 C eps) ^ (∑ i, β i) ≤
      (4 * k) ^ (∑ i, β i) * (Real.log (1 / eps) ^ (C.tau + 1)) ^ (∑ i, β i) := by
    rw [← mul_pow]; exact h5
  have hX : 0 ≤ K * C.MF * ∏ i, ((β i).factorial : ℝ) := by positivity
  calc _ ≤ K * C.MF * (∏ i, ((β i).factorial : ℝ)) *
        ((4 * k) ^ (∑ i, β i) * (Real.log (1 / eps) ^ (C.tau + 1)) ^ (∑ i, β i)) := by
        gcongr
    _ = _ := by ring

end PrInG0

end KAM.Planetary

end
