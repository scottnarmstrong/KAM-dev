/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.AnalyticRegularity

/-!
# Secular form: the complexified perturbation restricts to the real one

Blueprint P, Part 8, Proposition `bpP:p8:perturbation-analytic` (`pa-hol`): at real points the
complex chart coordinates are the complexification of the real chart, the bilinear square is the
real squared separation, the principal root is `1 / planeLength`, and the complexified
perturbation is the real `perturbation`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ} (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ} (hr : r < rho D a)

theorem planetBlock_assemble (x : Slow n) (t : Vec n) (i : Fin n) :
    planetBlock (assemble x.2.1 t x.2.2 x.1) i = (![t i, x.1 i], ![x.2.1 i, x.2.2 i]) := by
  simp [planetBlock, assemble, fast, slow, Fin.append_left]

include ha hr in
theorem planetC_inclusion {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) (i : Fin n) :
    planetC D t (inclusion x) i =
      phaseToC (poincare (D.m i) (D.G * D.m0) (planetBlock (assemble x.2.1 t x.2.2 x.1) i)) := by
  have hΛ := action_pos D ha i
  have h := (poincare_holomorphic (m := D.m i) (κ := D.G * D.m0) (Λo := action D a i)
    (D.hm i) (mul_pos D.hG D.hm0) hΛ).2.2.2.2
  have hb : blockC t (inclusion x) i = phaseToC (planetBlock (assemble x.2.1 t x.2.2 x.1) i) := by
    rw [planetBlock_assemble]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
      simp [blockC, inclusion, phaseToC]
  have hmem := blockC_mem_nbhd D ha hr (t := t) hx i
  rw [hb] at hmem
  rw [planetC_eq, hb]
  exact (h _ hmem).2

include ha hr in
theorem planetC_inclusion_fst {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) (i : Fin n)
    (c : Fin 2) : (planetC D t (inclusion x) i).1 c =
      ((bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i c : ℝ) : ℂ) := by
  have h := (Prod.ext_iff.1 (poincareProd_block D.m (D.G * D.m0)
    (assemble x.2.1 t x.2.2 x.1) i)).1
  rw [planetC_inclusion D ha hr hx]
  exact (congrArg (fun v : Fin 2 → ℝ => ((v c : ℝ) : ℂ)) h).symm

include ha hr in
theorem planetC_inclusion_snd {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) (i : Fin n)
    (c : Fin 2) : (planetC D t (inclusion x) i).2 c =
      ((bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).2 i c : ℝ) : ℂ) := by
  have h := (Prod.ext_iff.1 (poincareProd_block D.m (D.G * D.m0)
    (assemble x.2.1 t x.2.2 x.1) i)).2
  rw [planetC_inclusion D ha hr hx]
  exact (congrArg (fun v : Fin 2 → ℝ => ((v c : ℝ) : ℂ)) h).symm

include ha hr in
theorem separationC_inclusion {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) (i j : Fin n) :
    separationC D t (inclusion x) i j =
      ((planeSq (bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i -
        bodyVector (poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1)).1 j) : ℝ) : ℂ) := by
  unfold separationC planeSq
  simp only [planetC_inclusion_fst D ha hr hx]
  push_cast
  simp

theorem cpow_planeSq (v : Fin 2 → ℝ) :
    ((planeSq v : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = (((planeLength v)⁻¹ : ℝ) : ℂ) := by
  have h0 : 0 ≤ planeSq v := Finset.sum_nonneg fun k _ => sq_nonneg _
  have := Complex.ofReal_cpow h0 (-1 / 2)
  rw [show ((-1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) by push_cast; rfl] at this
  rw [← this]
  congr 1
  unfold planeLength
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul h0]
  norm_num

include ha hr in
theorem perturbationC_inclusion (b : Bool) {x : Slow n} (hx : x ∈ realDisc D a r) (t : Vec n) :
    perturbationC D b t (inclusion x) =
      (perturbation D b (assemble x.2.1 t x.2.2 x.1) : ℂ) := by
  set z := poincareProd D.m (D.G * D.m0) (assemble x.2.1 t x.2.2 x.1) with hz
  have hpair : (-(D.G : ℂ) * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
      (D.m i : ℂ) * D.m j * separationC D t (inclusion x) i j ^ (-1/2 : ℂ)) =
      ((-pairPotential D.G D.m z.1 : ℝ) : ℂ) := by
    unfold pairPotential
    simp only [separationC_inclusion D ha hr hx, cpow_planeSq]
    push_cast
    rw [Finset.mul_sum]
    simp only [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [div_eq_mul_inv]; ring
  unfold perturbationC perturbation
  rw [hpair]
  cases b
  · simp [fFix, hz]
  · simp only [ite_true, fMov]
    have hm : (∑ c : Fin 2, (∑ i, (planetC D t (inclusion x) i).2 c) ^ 2) / (2 * (D.m0 : ℂ)) =
        ((planeSq (∑ i, bodyVector z.2 i) / (2 * D.m0) : ℝ) : ℂ) := by
      simp only [planetC_inclusion_snd D ha hr hx]
      unfold planeSq
      push_cast
      simp [Finset.sum_apply, hz]
    rw [hm]; push_cast; ring

end SecularForm
end KAM.Planetary
end
