/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.Modal
public import KAM.EffectiveStability.Tube.Poly.HTilde
public import KAM.EffectiveStability.Tube.Chart.Polar
public import KAM.EffectiveStability.Tube.Chart.Shift

/-!
# `SJSU18-O2` in tube coordinates (T2-CONF, N5a)

`sjsuHTilde B (u, φ) = Σ_n T_n(φ) Π_j (B_j(φ) + u_j)^{n_j/2}` over the rows of `H_w`
(`hTildeOf`), and **N2's chart hypothesis**
`sjsu18O2 (rotMap V′ (polar (I, θ))) = sjsuHTilde B (shiftChart B (I, θ))` for all `I > 0`, `θ` and
every `B` (`sjsu18O2_rotMap_polar`). The shift cancels: `B_j + (I_j - B_j) = I_j`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube Complex

/-- **The Hamiltonian in tube coordinates** `(u, φ)`, for a shift `B`. -/
def sjsuHTilde (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  hTildeOf sjsuE sjsuN sjsuHwAll B p

theorem omegaOf_polar (act θ : Fin 3 → ℝ) :
    omegaOf (polar (act, θ)) = fun k => (((sjsuN : ℝ)⁻¹ : ℝ) : ℂ) * polarW act θ k := by
  funext k
  have h2 : √(2 * act k) = √2 * √(act k) := Real.sqrt_mul (by norm_num) _
  have hs2 : (√2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [omegaOf, polar, polarW, h2]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  field_simp
  ring_nf

theorem polarAmp_eq_binomProd (act : Fin 3 → ℝ) (hact : ∀ j, 0 ≤ act j) (e : (Mon × Mon) × ℤ)
    (Bφ : Fin 3 → ℝ) :
    polarAmp act e.1 = binomProd (halfExp (rowExp e)) Bφ (fun j => act j - Bφ j) := by
  have key : ∀ (x : ℝ) (n : ℕ), 0 ≤ x → √x ^ n = x ^ ((n : ℝ) / 2) := by
    intro x n hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
    ring_nf
  simp only [polarAmp, binomProd, Fin.prod_univ_three, halfExp, rowExp, add_sub_cancel]
  simp [key _ _ (hact 0), key _ _ (hact 1), key _ _ (hact 2)]

/-- **N2's chart hypothesis for `SJSU18-O2`.** For all positive actions, all angles and every
shift `B`: `H (Rinv (polar (I, θ))) = h̃ (I - B(φ), φ)` with `φ = phiOf θ`. -/
theorem sjsu18O2_rotMap_polar (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (y : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    (hy : ∀ j, 0 ≤ y.1 j) :
    sjsu18O2 (rotMap sjsuV (polar y)) = sjsuHTilde B (shiftChart B y) := by
  obtain ⟨act, θ⟩ := y
  rw [sjsu18O2_rotMap, omegaOf_polar act θ]
  have hstar : (fun k => star ((((sjsuN : ℝ)⁻¹ : ℝ) : ℂ) * polarW act θ k)) =
      fun k => (((sjsuN : ℝ)⁻¹ : ℝ) : ℂ) * star (polarW act θ k) := by
    funext k
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [hstar, show ((10 : ℂ) ^ sjsuE)⁻¹ = (((10 : ℝ) ^ sjsuE)⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.re_sum]
  simp only [re_bevalAt_polarW]
  rw [sjsuHTilde, hTildeOf_eq_rows]
  simp only [shiftChart]
  have hterm : ∀ e ∈ sjsuHwAll,
      ((10 : ℝ) ^ sjsuE)⁻¹ * ((e.2 : ℝ) * ((sjsuN : ℝ)⁻¹) ^ (Mon.deg e.1.1 + Mon.deg e.1.2) *
        polarAmp act e.1 * Real.cos (polarAngle θ e.1)) =
      rowTrig sjsuE sjsuN e (phiOf θ) *
        binomProd (halfExp (rowExp e)) (B (phiOf θ)) (act - B (phiOf θ)) := by
    intro e he
    rw [polarAmp_eq_binomProd act hy e (B (phiOf θ)), polarAngle_of_charge θ e.1 (sjsuHw_charge he)]
    have hb : binomProd (halfExp (rowExp e)) (B (phiOf θ)) (fun j => act j - B (phiOf θ) j) =
        binomProd (halfExp (rowExp e)) (B (phiOf θ)) (act - B (phiOf θ)) := rfl
    rw [hb]
    simp only [rowTrig, rowCoef, rowMode, phiOf_apply_zero, phiOf_apply_one]
    push_cast
    field_simp
    rw [one_div, inv_pow, div_eq_mul_inv]
    ring
  rw [List.map_congr_left (fun e he => (hterm e he).symm), List.sum_map_mul_left]
  congr 1
  simp only [sjsuHwAll, Finset.sum_range_succ, Finset.sum_range_zero, List.map_append,
    List.sum_append, zero_add]

end KAM.EffectiveStability.SJSU

end
