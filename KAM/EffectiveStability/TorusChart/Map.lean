/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChart.Matrix
public import KAM.ODE.Basic

/-!
# The cotangent-lift chart of a Lagrangian graph torus: definitions and algebra (track B, B5-CHART)

`torusChartMap u v (φ, J) = (x φ, v φ + (Dx φ)^{-T} J)` and
`torusChartInvMap u v (y, p) = (x⁻¹ y, (Dx (x⁻¹ y))ᵀ (p - v (x⁻¹ y)))`, with `x = id + u`.
Proved here: `C²` regularity, lattice equivariance, `Ψ (φ, 0) = (x φ, v φ)`, and that the two
maps are mutually inverse everywhere.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Matrix

variable {n : ℕ}

/-- The chart `Ψ(φ, J) = (x φ, v φ + (Dx φ)^{-T} J)`. -/
def torusChartMap (u v : (Fin n → ℝ) → (Fin n → ℝ)) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (torusChartX u w.1, v w.1 + torusChartInvT u w.1 *ᵥ w.2)

/-- The inverse `Ψinv(y, p) = (x⁻¹ y, (Dx (x⁻¹ y))ᵀ (p - v (x⁻¹ y)))`. -/
def torusChartInvMap (u v : (Fin n → ℝ) → (Fin n → ℝ)) (q : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (torusChartXinv u q.1,
    (torusChartJac u (torusChartXinv u q.1))ᵀ *ᵥ (q.2 - v (torusChartXinv u q.1)))

/-- All hypotheses on the Lagrangian graph `φ ↦ (φ + u φ, v φ)`: periodic `u, v`, `u` of class
`C³`, `v` of class `C²`, `‖Du‖ ≤ κ < 1`, and the Lagrangian condition `(Dx)ᵀ Dv` symmetric. -/
structure TorusChartData (u v : (Fin n → ℝ) → (Fin n → ℝ)) (κ : ℝ) : Prop
    extends TorusBaseData u κ where
  uPeriodic : TorusPeriodic u
  vPeriodic : ∀ (φ : Fin n → ℝ) (k : Fin n → ℤ), v (φ + fun i => (k i : ℝ)) = v φ
  vSmooth : ContDiff ℝ 2 v
  lagrangian : ∀ (φ : Fin n → ℝ) (i j : Fin n),
    ∑ l, (fderiv ℝ (torusChartX u) φ (Pi.single i 1)) l * (fderiv ℝ v φ (Pi.single j 1)) l =
    ∑ l, (fderiv ℝ (torusChartX u) φ (Pi.single j 1)) l * (fderiv ℝ v φ (Pi.single i 1)) l

variable {u v : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}

theorem torusChartMap_contDiff (h : TorusChartData u v κ) : ContDiff ℝ 2 (torusChartMap u v) := by
  have hx : ContDiff ℝ 2 (torusChartX u) :=
    (torusChartX_contDiff h.toTorusBaseData).of_le (by norm_num)
  refine (hx.comp contDiff_fst).prodMk (contDiff_pi' fun i => ?_)
  have hB : ∀ k, ContDiff ℝ 2 fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
      torusChartInvT u w.1 i k * w.2 k := fun k =>
    ((torusChartInvT_contDiff h.toTorusBaseData i k).comp contDiff_fst).mul
      ((contDiff_pi.mp contDiff_snd) k)
  have hv : ContDiff ℝ 2 fun w : (Fin n → ℝ) × (Fin n → ℝ) => v w.1 i :=
    (contDiff_pi.mp (h.vSmooth.comp contDiff_fst)) i
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  exact hv.add (ContDiff.sum fun k _ => hB k)

theorem torusChartMap_zero (φ : Fin n → ℝ) :
    torusChartMap u v (φ, 0) = (torusChartX u φ, v φ) := by
  simp [torusChartMap]

theorem torusChartJac_shift (h : TorusChartData u v κ) (φ : Fin n → ℝ) (k : Fin n → ℤ) :
    torusChartJac u (φ + fun i => (k i : ℝ)) = torusChartJac u φ := by
  have : fderiv ℝ (torusChartX u) (φ + fun i => (k i : ℝ)) = fderiv ℝ (torusChartX u) φ := by
    rw [← fderiv_comp_add_right (f := torusChartX u) (x := φ) (fun i => (k i : ℝ))]
    have hfun : (fun z => torusChartX u (z + fun i => (k i : ℝ))) =
        fun z => torusChartX u z + fun i => (k i : ℝ) := funext fun z =>
      torusChartX_shift h.uPeriodic z k
    rw [hfun, fderiv_add_const]
  unfold torusChartJac
  rw [this]

theorem torusChartInvT_shift (h : TorusChartData u v κ) (φ : Fin n → ℝ) (k : Fin n → ℤ) :
    torusChartInvT u (φ + fun i => (k i : ℝ)) = torusChartInvT u φ := by
  unfold torusChartInvT; rw [torusChartJac_shift h]

/-- Lattice equivariance of the chart. -/
theorem torusChartMap_shift (h : TorusChartData u v κ) (w : (Fin n → ℝ) × (Fin n → ℝ))
    (k : Fin n → ℤ) :
    torusChartMap u v (w + KAM.ODE.angleShift k) =
      torusChartMap u v w + KAM.ODE.angleShift k := by
  obtain ⟨φ, J⟩ := w
  simp only [KAM.ODE.angleShift, Prod.mk_add_mk, add_zero, torusChartMap,
    torusChartX_shift h.uPeriodic, h.vPeriodic, torusChartInvT_shift h]

theorem torusChartInvMap_map (h : TorusChartData u v κ) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    torusChartInvMap u v (torusChartMap u v w) = w := by
  obtain ⟨φ, J⟩ := w
  simp only [torusChartInvMap, torusChartMap, torusChartXinv_left h.toTorusBaseData,
    add_sub_cancel_left]
  rw [torusChartJacT_invT_mulVec h.toTorusBaseData]

theorem torusChartMap_invMap (h : TorusChartData u v κ) (q : (Fin n → ℝ) × (Fin n → ℝ)) :
    torusChartMap u v (torusChartInvMap u v q) = q := by
  obtain ⟨y, p⟩ := q
  simp only [torusChartInvMap, torusChartMap, torusChartXinv_right h.toTorusBaseData,
    torusChartInvT_jacT_mulVec h.toTorusBaseData, add_sub_cancel]

end KAM.EffectiveStability
