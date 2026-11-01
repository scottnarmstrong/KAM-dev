/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Rotation46

/-!
# Rotation (46): the rotation vector of a varying tilt

Package LP-SP-CHART, `LP:MAIN L17 (562–569)`, track LP, non-frozen. Pure algebra for the
symplecticity computation. Since the tilt `t = (a, b, 0)` of (46) has no third component,
`R = rot3 a b c` is an explicit `3 × 3` matrix, `c² + a² + b² = 1`. For a variation
`(da, db, dc)` with `a da + b db + c dc = 0`,

* `rot3Deriv` is the derivative of `R`;
* `Rᵀ dR = [ω]ₓ` with `ω = rot3Omega` (so `dR = R [ω]ₓ`, an infinitesimal rotation);
* `rot3_form_identity`: the identity
  `ω_k3 dG_h − ω_h3 dG_k − G (ω_h × ω_k)_3 = du_h dv_k − dv_h du_k` for
  `(u, v, G) = (2 s a, −2 s b, s²)`.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

open Matrix

namespace KAM.Planetary.Spatial

/-- `incRotation` with the tilt `(a, b, 0)` and cosine `c`, as an explicit matrix. -/
def rot3 (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - 2 * b ^ 2, 2 * a * b, 2 * c * b;
    2 * a * b, 1 - 2 * a ^ 2, -(2 * c * a);
    -(2 * c * b), 2 * c * a, 1 - 2 * (a ^ 2 + b ^ 2)]

/-- The derivative of `rot3` in the direction `(da, db, dc)`. -/
def rot3Deriv (a b c da db dc : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(4 * b * db), 2 * (a * db + b * da), 2 * (dc * b + c * db);
    2 * (a * db + b * da), -(4 * a * da), -(2 * (dc * a + c * da));
    -(2 * (dc * b + c * db)), 2 * (dc * a + c * da), -(4 * (a * da + b * db))]

/-- The rotation vector `ω` with `(rot3 a b c)ᵀ * rot3Deriv a b c da db dc = [ω]ₓ`. -/
def rot3Omega (a b c da db dc : ℝ) : Fin 3 → ℝ :=
  ![2 * (c * da - a * dc), 2 * (c * db - b * dc), 2 * (b * da - a * db)]

lemma incRotation_eq_rot3 (u v G : ℝ) :
    incRotation u v G =
      rot3 (incTilt u v G 0) (incTilt u v G 1) (incCos u v G) := by
  rw [incRotation_eq_tiltRotation, tiltRotation_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot3, incTilt_apply_two]

/-- `Rᵀ dR = [ω]ₓ`. -/
theorem rot3_transpose_mul_deriv {a b c da db dc : ℝ} (hc : c ^ 2 + a ^ 2 + b ^ 2 = 1)
    (hd : a * da + b * db + c * dc = 0) :
    (rot3 a b c)ᵀ * rot3Deriv a b c da db dc = skewMatrix (rot3Omega a b c da db dc) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot3, rot3Deriv, rot3Omega, skewMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (4 * b * db) * (hc) + (4 * b ^ 2) * hd
  · linear_combination (-4 * b * da) * (hc) + (-4 * a * b) * hd
  · linear_combination (-4 * b * dc) * (hc) + (4 * b * c) * hd
  · linear_combination (-4 * a * db) * (hc) + (-4 * a * b) * hd
  · linear_combination (4 * a * da) * (hc) + (4 * a ^ 2) * hd
  · linear_combination (4 * a * dc) * (hc) + (-4 * a * c) * hd
  · linear_combination (4 * b * dc) * (hc) + (-4 * b * c) * hd
  · linear_combination (-4 * a * dc) * (hc) + (4 * a * c) * hd
  · linear_combination (4 * a * da + 4 * b * db) * (hc) + (4 * (a ^ 2 + b ^ 2)) * hd

/-- `dR = R [ω]ₓ`, with `R Rᵀ = 1`. -/
theorem rot3_deriv_eq {a b c da db dc : ℝ} (hc : c ^ 2 + a ^ 2 + b ^ 2 = 1)
    (hd : a * da + b * db + c * dc = 0) :
    rot3Deriv a b c da db dc = rot3 a b c * skewMatrix (rot3Omega a b c da db dc) := by
  have hT : (rot3 a b c)ᵀ * rot3 a b c = 1 := by
    have h := tiltRotation_transpose_mul ![a, b, 0] c (by
      simp [dotProduct, Fin.sum_univ_three]; linarith)
    have e : tiltRotation ![a, b, 0] c = rot3 a b c := by
      rw [tiltRotation_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rot3]
    rwa [e] at h
  have hO : rot3 a b c * (rot3 a b c)ᵀ = 1 := mul_eq_one_comm.1 hT
  rw [← rot3_transpose_mul_deriv hc hd, ← Matrix.mul_assoc, hO, Matrix.one_mul]

/-- The key identity for the `(u, v)`-part of the pullback of `dp ∧ dq`. -/
theorem rot3_form_identity {a b c s da db dc ds da' db' dc' ds' : ℝ}
    (hc : c ^ 2 + a ^ 2 + b ^ 2 = 1)
    (hd : a * da + b * db + c * dc = 0) (hd' : a * da' + b * db' + c * dc' = 0) :
    rot3Omega a b c da' db' dc' 2 * (2 * s * ds) - rot3Omega a b c da db dc 2 * (2 * s * ds') -
        s ^ 2 * (rot3Omega a b c da db dc 0 * rot3Omega a b c da' db' dc' 1 -
          rot3Omega a b c da db dc 1 * rot3Omega a b c da' db' dc' 0) =
      (2 * s * da + 2 * a * ds) * (-(2 * s * db') - 2 * b * ds') -
        (-(2 * s * db) - 2 * b * ds) * (2 * s * da' + 2 * a * ds') := by
  simp only [rot3Omega, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (4 * s ^ 2 * (da' * db - da * db')) * hc +
    (4 * s ^ 2 * (a * db' - b * da')) * hd - (4 * s ^ 2 * (a * db - b * da)) * hd'

end KAM.Planetary.Spatial
