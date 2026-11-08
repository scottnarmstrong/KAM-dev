/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# A second-order Taylor bound along a segment (track B, B5-NF)

For a real function `G` of class `C³` on an open set, a segment `x + t d` (`t ∈ [0, 1]`) inside
the set, and a direction `e`: if `DG x e = 0` and `D²G x d e = 0`, then
`|DG (x + d) e| ≤ M ‖d‖² ‖e‖ / 2` where `|D³G y a b c| ≤ M ‖a‖ ‖b‖ ‖c‖` on the set
(the operator-norm bound, in evaluated form).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- One-dimensional comparison: if `|f'| ≤ φ'` on `[0, 1]` and `f 0 = φ 0 = 0`, then `|f| ≤ φ`. -/
theorem abs_le_of_abs_deriv_le_nfT {f f' φ φ' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hφ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' t) t)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |f' t| ≤ φ' t) (h0 : f 0 = 0) (hφ0 : φ 0 = 0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : |f t| ≤ φ t := by
  have h0m : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hcf : ContinuousOn f (Icc 0 1) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hcφ : ContinuousOn φ (Icc 0 1) := fun s hs => (hφ s hs).continuousAt.continuousWithinAt
  have hint : ∀ s ∈ interior (Icc (0 : ℝ) 1), s ∈ Icc (0 : ℝ) 1 := fun s hs =>
    interior_subset hs
  have m1 : MonotoneOn (fun s => φ s - f s) (Icc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (hcφ.sub hcf)
      (fun s hs => ((hφ s (hint s hs)).sub (hf s (hint s hs))).differentiableAt
        |>.differentiableWithinAt)
      (fun s hs => by
        rw [((hφ s (hint s hs)).fun_sub (hf s (hint s hs))).deriv]
        linarith [(abs_le.1 (h s (hint s hs))).2])
  have m2 : MonotoneOn (fun s => φ s + f s) (Icc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (hcφ.add hcf)
      (fun s hs => ((hφ s (hint s hs)).add (hf s (hint s hs))).differentiableAt
        |>.differentiableWithinAt)
      (fun s hs => by
        rw [((hφ s (hint s hs)).fun_add (hf s (hint s hs))).deriv]
        linarith [(abs_le.1 (h s (hint s hs))).1])
  have a1 := m1 h0m ht ht.1
  have a2 := m2 h0m ht ht.1
  simp only [h0, hφ0] at a1 a2
  exact abs_le.2 ⟨by linarith, by linarith⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivative along a segment of a continuous-linear-map valued function applied to `e`. -/
theorem hasDerivAt_clm_path_nfT {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : E → E →L[ℝ] F} {x d : E} {t : ℝ} (hΦ : DifferentiableAt ℝ Φ (x + t • d)) (e : E) :
    HasDerivAt (fun s : ℝ => Φ (x + s • d) e) (fderiv ℝ Φ (x + t • d) d e) t := by
  have hγ : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h1 := hΦ.hasFDerivAt.comp_hasDerivAt t hγ
  have h2 := (ContinuousLinearMap.apply ℝ F e).hasFDerivAt.comp_hasDerivAt t h1
  exact h2

/-- **Second-order Taylor bound** along a segment, with the sharp constant `1/2`. -/
theorem fderiv_taylor_bound_nfT {G : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hG : ContDiffOn ℝ 3 G s) {x d e : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ s)
    (h0 : fderiv ℝ G x e = 0) (h1 : fderiv ℝ (fderiv ℝ G) x d e = 0) {M : ℝ}
    (hM : ∀ y ∈ s, ∀ a b c : E,
      |fderiv ℝ (fderiv ℝ (fderiv ℝ G)) y a b c| ≤ M * ‖a‖ * ‖b‖ * ‖c‖) :
    |fderiv ℝ G (x + d) e| ≤ M * ‖d‖ ^ 2 * ‖e‖ / 2 := by
  have d1 : ContDiffOn ℝ 2 (fderiv ℝ G) s := hG.fderiv_of_isOpen hs (by norm_num)
  have d2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ G)) s := d1.fderiv_of_isOpen hs (by norm_num)
  have dd1 : ∀ y ∈ s, DifferentiableAt ℝ (fderiv ℝ G) y := fun y hy =>
    (d1.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hy)
  have dd2 : ∀ y ∈ s, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ G)) y := fun y hy =>
    (d2.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hy)
  set m : ℝ := M * ‖d‖ ^ 2 * ‖e‖ with hm
  have hstep1 : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => fderiv ℝ (fderiv ℝ G) (x + r • d) d e)
        (fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (x + t • d) d d e) t := fun t ht => by
    have h := hasDerivAt_clm_path_nfT (Φ := fderiv ℝ (fderiv ℝ G)) (x := x) (d := d) (t := t)
      (dd2 _ (hseg t ht)) d
    exact (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt t h
  have hstep0 : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => fderiv ℝ G (x + r • d) e)
        (fderiv ℝ (fderiv ℝ G) (x + t • d) d e) t := fun t ht =>
    hasDerivAt_clm_path_nfT (dd1 _ (hseg t ht)) e
  have hb2 : ∀ t ∈ Icc (0 : ℝ) 1,
      |fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (x + t • d) d d e| ≤ m := fun t ht => by
    have := hM _ (hseg t ht) d d e
    calc _ ≤ M * ‖d‖ * ‖d‖ * ‖e‖ := this
      _ = m := by rw [hm]; ring
  have hs1 : ∀ t ∈ Icc (0 : ℝ) 1, |fderiv ℝ (fderiv ℝ G) (x + t • d) d e| ≤ m * t := fun t ht => by
    have := abs_le_of_abs_deriv_le_nfT (f := fun r : ℝ => fderiv ℝ (fderiv ℝ G) (x + r • d) d e)
      (φ := fun r => m * r) (φ' := fun _ => m) hstep1
      (fun r _ => by simpa using (hasDerivAt_id r).const_mul m) hb2 (by simpa using h1)
      (by simp) ht
    simpa using this
  have hs0 := abs_le_of_abs_deriv_le_nfT (f := fun r : ℝ => fderiv ℝ G (x + r • d) e)
    (φ := fun r => m * (id r * id r) / 2) (φ' := fun r => m * r) hstep0
    (fun r _ => by
      simpa using (((hasDerivAt_id r).mul (hasDerivAt_id r)).const_mul m).div_const 2 |>.congr_deriv
        (by simp; ring))
    hs1 (by simpa using h0) (by simp) (t := 1) ⟨zero_le_one, le_rfl⟩
  simpa using hs0

end KAM.EffectiveStability

end
