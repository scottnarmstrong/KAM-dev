/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Frame
public import KAM.Planetary.PlanarTorsion.Beta
public import KAM.Planetary.PlanarTorsion.Homological

/-!
# Planar quartic torsion: the rotated quartic family (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-nf`, `stepP:p11b:bf-gram`).  The rotated physical quartic
`z ↦ p11c_quartic (p11c_coeffs p (p.axes I)) (p11c_rotateSlow (p11c_frame p (p.axes I)) z)` is a
`QuarticFamily` over every open set of actions inside the frame domain: the Gram form of the rotated
quartic is again a combination `p11c_quartic c'` of the six basic quartics with coefficients that
are polynomial in the frame entries, and `quartic_extract` expands each basic quartic in the
monomials.  The nonresonance `p11c_NR4` of the frequency `2σ` follows from `p11c_phi4 ≠ 0`.
-/

@[expose] public noncomputable section

open Set Metric Real Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.Planetary.PlanarCharacters

/-- Coefficients of the rotated quartic in the six basic quartics. -/
def p11cB_rotC (c : Fin 6 → ℝ) (g s : ℝ) : Fin 6 → ℝ :=
  ![c 0 * g ^ 4 + c 1 * s ^ 4 + c 2 * g ^ 2 * s ^ 2 + c 3 * g ^ 2 * s ^ 2 + c 4 * g ^ 3 * s +
      c 5 * g * s ^ 3,
    c 0 * s ^ 4 + c 1 * g ^ 4 + c 2 * g ^ 2 * s ^ 2 + c 3 * g ^ 2 * s ^ 2 - c 4 * g * s ^ 3 -
      c 5 * g ^ 3 * s,
    2 * c 0 * g ^ 2 * s ^ 2 + 2 * c 1 * g ^ 2 * s ^ 2 + c 2 * g ^ 4 + c 2 * s ^ 4 -
      2 * c 3 * g ^ 2 * s ^ 2 - c 4 * g ^ 3 * s + c 4 * g * s ^ 3 + c 5 * g ^ 3 * s -
      c 5 * g * s ^ 3,
    4 * c 0 * g ^ 2 * s ^ 2 + 4 * c 1 * g ^ 2 * s ^ 2 - 4 * c 2 * g ^ 2 * s ^ 2 + c 3 * g ^ 4 -
      2 * c 3 * g ^ 2 * s ^ 2 + c 3 * s ^ 4 - 2 * c 4 * g ^ 3 * s + 2 * c 4 * g * s ^ 3 +
      2 * c 5 * g ^ 3 * s - 2 * c 5 * g * s ^ 3,
    -4 * c 0 * g ^ 3 * s + 4 * c 1 * g * s ^ 3 + 2 * c 2 * g ^ 3 * s - 2 * c 2 * g * s ^ 3 +
      2 * c 3 * g ^ 3 * s - 2 * c 3 * g * s ^ 3 + c 4 * g ^ 4 - 3 * c 4 * g ^ 2 * s ^ 2 +
      3 * c 5 * g ^ 2 * s ^ 2 - c 5 * s ^ 4,
    -4 * c 0 * g * s ^ 3 + 4 * c 1 * g ^ 3 * s - 2 * c 2 * g ^ 3 * s + 2 * c 2 * g * s ^ 3 -
      2 * c 3 * g ^ 3 * s + 2 * c 3 * g * s ^ 3 + 3 * c 4 * g ^ 2 * s ^ 2 - c 4 * s ^ 4 +
      c 5 * g ^ 4 - 3 * c 5 * g ^ 2 * s ^ 2]

theorem p11cB_quartic_rot (c : Fin 6 → ℝ) (g s : ℝ) (w : Phase 2) :
    p11c_quartic c (p11c_rotateSlow !![g, -s; s, g] w) = p11c_quartic (p11cB_rotC c g s) w := by
  simp only [p11c_quartic, p11c_pairDot, p11c_rotateSlow, p11cB_rotC, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The basic quartics are real combinations of the monomials. -/
theorem p11cB_basic_extract (k : Fin 6) :
    ∃ γ : (Fin 4 → Fin 5) → ℝ, ∀ z : Phase 2, p11c_quartic (Pi.single k 1) z =
      ∑ a ∈ charIdx, γ a * p11c_monomial (fun i => (a i).val) z := by
  let P : Fin 6 → MvPolynomial (Fin 4) ℂ := fun k =>
    open MvPolynomial in
    match k with
    | 0 => (X 0 ^ 2 + X 1 ^ 2) ^ 2
    | 1 => (X 2 ^ 2 + X 3 ^ 2) ^ 2
    | 2 => (X 0 ^ 2 + X 1 ^ 2) * (X 2 ^ 2 + X 3 ^ 2)
    | 3 => (X 0 * X 2 + X 1 * X 3) ^ 2
    | 4 => (X 0 ^ 2 + X 1 ^ 2) * (X 0 * X 2 + X 1 * X 3)
    | 5 => (X 2 ^ 2 + X 3 ^ 2) * (X 0 * X 2 + X 1 * X 3)
  have hP : ∀ z : Phase 2, (p11c_quartic (Pi.single k 1) z : ℂ) =
      MvPolynomial.eval (quarticVec z) (P k) := by
    intro z
    fin_cases k <;>
      simp [P, p11c_quartic, p11c_pairDot, quarticVec] <;> ring
  have hh : ∀ (z : Phase 2) (t : ℝ), (p11c_quartic (Pi.single k 1) (t • z) : ℂ) =
      (t : ℂ) ^ 4 * (p11c_quartic (Pi.single k 1) z : ℂ) := by
    intro z t
    fin_cases k <;>
      simp [p11c_quartic, p11c_pairDot] <;> push_cast <;> ring
  obtain ⟨c, hc⟩ := quartic_extract (fun z => (p11c_quartic (Pi.single k 1) z : ℂ)) (P k) hP hh
  refine ⟨fun a => (c a).re, fun z => ?_⟩
  have := congrArg Complex.re (hc z)
  simp only [Complex.ofReal_re, Complex.re_sum] at this
  rw [this]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.ofReal_re (p11c_monomial (fun i => (a i).val) z)]
  rw [Complex.re_mul_ofReal]
  simp

/-- A quartic with analytic coefficients in the six basic quartics is a `QuarticFamily`. -/
theorem p11cB_family_of_coeffs {O : Set (Fin 2 → ℝ)} (c : (Fin 2 → ℝ) → Fin 6 → ℝ)
    (hc : ∀ k, AnalyticOnNhd ℝ (fun I => c I k) O) :
    ∃ F : QuarticFamily O, ∀ I z, F.eval I z = p11c_quartic (c I) z := by
  choose γ hγ using p11cB_basic_extract
  obtain ⟨F, hF⟩ := quartic_of_coeffs (O := O) (fun b I => ∑ k, c I k * γ k b) (fun b => by
    exact Finset.analyticOnNhd_fun_sum _ fun k _ => (hc k).mul (fun _ _ => analyticAt_const))
  refine ⟨F, fun I z => ?_⟩
  rw [hF]
  simp_rw [Finset.sum_mul, Finset.sum_comm (s := charIdx) (t := (Finset.univ : Finset (Fin 6)))]
  have hq : p11c_quartic (c I) z = ∑ k, c I k * p11c_quartic (Pi.single k 1) z := by
    simp only [p11c_quartic, Fin.sum_univ_six, Pi.single_apply]
    simp
    ring
  rw [hq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hγ k z, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end KAM.Planetary

end
