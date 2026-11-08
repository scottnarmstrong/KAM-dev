/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Data.Matrix.Mul
public import KAM.Frozen.Defs.SymplecticForm

/-!
# The symplectic matrix identity of the cotangent-lift chart (track B, B5-CHART)

Pure linear algebra behind `DΨᵀ Ω₀ DΨ = Ω₀`: given `Bᵀ A = 1`, the differentiated relations
`dBᵀ A + Bᵀ dA = 0`, the symmetry of the second derivative of the base map, and the
Lagrangian symmetry, the form of two tangent vectors is preserved.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Matrix

variable {n : ℕ}

/-- The frozen form as a difference of dot products. -/
theorem symplecticForm_eq_dot (s t : (Fin n → ℝ) × (Fin n → ℝ)) :
    KAM.symplecticForm s t = s.2 ⬝ᵥ t.1 - s.1 ⬝ᵥ t.2 := by
  simp [KAM.symplecticForm, dotProduct, Finset.sum_sub_distrib]

/-- The algebraic core of symplecticity of the cotangent-lift chart. -/
theorem torusChart_symplectic_algebra (A B dBa dBb dAa dAb : Matrix (Fin n) (Fin n) ℝ)
    (a1 a2 b1 b2 dv1 dv2 J : Fin n → ℝ)
    (hBA : Bᵀ * A = 1) (hda : dBaᵀ * A + Bᵀ * dAa = 0) (hdb : dBbᵀ * A + Bᵀ * dAb = 0)
    (hsym2 : dAa *ᵥ b1 = dAb *ᵥ a1) (hsymV : (A *ᵥ a1) ⬝ᵥ dv2 = (A *ᵥ b1) ⬝ᵥ dv1) :
    (dv1 + B *ᵥ a2 + dBa *ᵥ J) ⬝ᵥ (A *ᵥ b1) - (A *ᵥ a1) ⬝ᵥ (dv2 + B *ᵥ b2 + dBb *ᵥ J) =
      a2 ⬝ᵥ b1 - a1 ⬝ᵥ b2 := by
  have g1 : ∀ x y : Fin n → ℝ, (B *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := fun x y => by
    rw [← Matrix.vecMul_transpose B x, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    rw [hBA, Matrix.one_mulVec]
  have g3 : ∀ (dB dA : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ),
      dBᵀ * A + Bᵀ * dA = 0 → (dB *ᵥ J) ⬝ᵥ (A *ᵥ y) = - (J ⬝ᵥ (Bᵀ *ᵥ (dA *ᵥ y))) := by
    intro dB dA y hd
    have e : dBᵀ *ᵥ (A *ᵥ y) = - (Bᵀ *ᵥ (dA *ᵥ y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        eq_neg_iff_add_eq_zero, ← Matrix.add_mulVec, hd, Matrix.zero_mulVec]
    rw [← Matrix.vecMul_transpose dB J, ← Matrix.dotProduct_mulVec, e, dotProduct_neg]
  have f3 := g3 dBa dAa b1 hda
  have f4 := g3 dBb dAb a1 hdb
  rw [← hsym2] at f4
  have f1 := g1 a2 b1
  have f2 := g1 b2 a1
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (A *ᵥ a1) (B *ᵥ b2), dotProduct_comm (A *ᵥ a1) (dBb *ᵥ J)]
  rw [dotProduct_comm dv1 (A *ᵥ b1)]
  rw [dotProduct_comm b2 a1] at f2
  rw [f1, f2, f3, f4, hsymV]
  ring

end KAM.EffectiveStability
