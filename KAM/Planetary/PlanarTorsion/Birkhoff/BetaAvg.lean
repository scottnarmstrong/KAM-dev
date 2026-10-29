/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Beta
public import KAM.Planetary.PlanarTorsion.Frame
public import KAM.Planetary.PlanarTorsion.Birkhoff.Jets

/-!
# Planar quartic torsion: the average of the rotated quartic is the `β` form (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-nf`, `bpP:p11b:beta-formula`).  For the global frame
`U = p11c_frame p a` (`U = [[g, -s], [s, g]]`, `g² + s² = 1`) the spectral projector of `p11c_Q` is
`[[g², g s], [g s, s²]]` (`p11c_projector_eq_frame`), so `beta_formula` gives the torus average of
the rotated physical quartic as `½ ∑ β_ij R_i R_j` with `β = p11c_beta p a`.
-/

@[expose] public noncomputable section

open Set Metric Real Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler

theorem p11cB_frame_eq (p : PlanarData) (a : Fin 2 → ℝ) :
    p11c_frame p a = !![p11c_frame p a 0 0, -p11c_frame p a 1 0;
      p11c_frame p a 1 0, p11c_frame p a 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [p11c_frame]

theorem p11cB_average_beta (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) (z : Phase 2) :
    p11c_average (fun _ w => p11c_quartic (p11c_coeffs p a)
        (p11c_rotateSlow (p11c_frame p a) w)) 0 z =
      (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p a i j * oscillatorAction z.2 z.1 i *
        oscillatorAction z.2 z.1 j := by
  have hF := (global_planar_frame p hp).2 a ha
  set U := p11c_frame p a with hU
  set g := U 0 0 with hg
  set s := U 1 0 with hs
  have hUe : U = !![g, -s; s, g] := p11cB_frame_eq p a
  have hgs : g ^ 2 + s ^ 2 = 1 := by
    have := congrFun (congrFun hF.1 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    nlinarith [this]
  have hUU : U * U.transpose = 1 := mul_eq_one_comm.1 hF.1
  have hQ : p11c_Q p a = U * Matrix.diagonal (p11c_sigma p a) * U.transpose := by
    rw [← hF.2.2]
    calc p11c_Q p a = (U * U.transpose) * p11c_Q p a * (U * U.transpose) := by rw [hUU]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hso : SecularSpectrum.isSO U := ⟨hF.1, hF.2.1⟩
  have hmono : StrictMono (p11c_sigma p a) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (lt_irrefl _)
    · exact p11c_sigma_lt p hp ha
    · exact absurd hij (by decide)
    · exact absurd hij (lt_irrefl _)
  have hproj := (p11c_projector_eq_frame p hp ha hso hmono hQ).2
  have hP : p11c_projector p a = !![g ^ 2, g * s; g * s, s ^ 2] := by
    ext i j
    rw [hproj i j]
    fin_cases i <;> fin_cases j <;> simp [hg, hs] <;> ring
  have hbf := beta_formula (p11c_coeffs p a) g s hgs z
  simp only [← hUe] at hbf
  rw [hbf]
  unfold p11c_beta
  rw [hP]

end KAM.Planetary

end
