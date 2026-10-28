/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.GlobalRealFlow

/-!
# The real-flow Lipschitz estimate (P11A-C7)

`bpP:p11a:real-lipschitz` (`real_lipschitz`): the time-`t` flow of a periodic bounded `C²` field
with bounded derivative satisfies the displacement bound, the periodicity and the Gronwall bound
`‖D Θ^t - 1‖ ≤ e^L - 1` for `|t| ≤ 1` (`stepP:p11a:rl-global`, `rl-deriv`, `rl-const`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ} {v : P11Vec n → P11Vec n}

/-- Gronwall for the linear equation `Y' = A Y`, `Y 0 = 1`, `‖A‖ ≤ L`, forward in time. -/
private theorem p11_gronwall_lin {L : ℝ} (hL : 0 ≤ L) {Y A : ℝ → (P11Vec n →L[ℝ] P11Vec n)}
    (hY : ∀ s, HasDerivAt Y ((A s).comp (Y s)) s) (hA : ∀ s, ‖A s‖ ≤ L)
    (h0 : Y 0 = ContinuousLinearMap.id ℝ _) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖Y t - ContinuousLinearMap.id ℝ _‖ ≤ Real.exp L - 1 := by
  have hW : ∀ s, HasDerivAt (fun s => Y s - ContinuousLinearMap.id ℝ _) ((A s).comp (Y s)) s :=
    fun s => (hY s).sub_const _
  have key := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun s => Y s - ContinuousLinearMap.id ℝ (P11Vec n))
    (f' := fun s => (A s).comp (Y s)) (δ := 0) (K := L) (ε := L) (a := 0) (b := 1)
    (fun s _ => (hW s).continuousAt.continuousWithinAt)
    (fun s _ => (hW s).hasDerivWithinAt) (by simp [h0])
    (fun s _ => by
      have h1 : ‖(A s).comp (Y s)‖ ≤ L * ‖Y s‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hA s) (norm_nonneg _))
      have h2 : ‖Y s‖ ≤ ‖Y s - ContinuousLinearMap.id ℝ (P11Vec n)‖ + 1 := by
        calc ‖Y s‖ = ‖(Y s - ContinuousLinearMap.id ℝ (P11Vec n)) +
              ContinuousLinearMap.id ℝ (P11Vec n)‖ := by rw [sub_add_cancel]
          _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right
              (ContinuousLinearMap.norm_id_le) _)
      nlinarith) t ht
  refine key.trans ?_
  rw [sub_zero]
  by_cases hL0 : L = 0
  · subst hL0
    simp [gronwallBound]
  · rw [gronwallBound_of_K_ne_0 hL0, div_self hL0]
    have : Real.exp (L * t) ≤ Real.exp L :=
      Real.exp_le_exp.2 (by nlinarith [ht.2])
    linarith

/-- The analytic real-flow estimate is proved with a real field from the start. -/
theorem real_lipschitz {n : ℕ} {v : P11Vec n → P11Vec n}
    (hv : ContDiff ℝ 2 v) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ x, ‖v x‖ ≤ M) (hD : ∀ x, ‖fderiv ℝ v x‖ ≤ L)
    (hp : ∀ x, ∀ k : Fin n → ℤ, v (x+fun i => (k i : ℝ))=v x) :
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x,
      ‖fderiv ℝ (p11RealFlow v t) x-ContinuousLinearMap.id ℝ _‖ ≤ Real.exp L-1 ∧
      ‖p11RealFlow v t x-x‖ ≤ M ∧
      ∀ k : Fin n → ℤ, p11RealFlow v t (x+fun i => (k i : ℝ))=
        p11RealFlow v t x+fun i => (k i : ℝ) := by
  intro t ht x
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  obtain ⟨-, hvar, hzero⟩ := p11_global_variational hv hM hL hb hD
  obtain ⟨hs0, hsd⟩ := p11RealFlow_spec hv1 hM hb x
  refine ⟨?_, ?_, fun k => ?_⟩
  · have hY : ∀ s, HasDerivAt (fun s => fderiv ℝ (p11RealFlow v s) x)
        ((fderiv ℝ v (p11RealFlow v s x)).comp (fderiv ℝ (p11RealFlow v s) x)) s :=
      fun s => hvar x s
    have h0 := hzero x
    rcases le_total 0 t with h | h
    · exact p11_gronwall_lin hL hY (fun s => hD _) h0 ⟨h, ht.2⟩
    · have := p11_gronwall_lin (n := n) hL
        (Y := fun s => fderiv ℝ (p11RealFlow v (-s)) x)
        (A := fun s => -fderiv ℝ v (p11RealFlow v (-s) x))
        (fun s => ((hY (-s)).scomp s (hasDerivAt_neg s)).congr_deriv (by ext w; simp))
        (fun s => by simpa using hD _) (by simpa using h0) (t := -t)
        ⟨by linarith, by linarith [ht.1]⟩
      simpa using this
  · have h := p11_norm_sub_le_of_sol hb (u := fun s => p11RealFlow v s x) (a := 0) (b := t)
      (fun s _ => hsd s)
    rw [hs0, Real.norm_eq_abs, sub_zero] at h
    have : |t| ≤ 1 := abs_le.2 ht
    calc _ ≤ M * |t| := h
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left this hM
      _ = M := mul_one M
  · have hu : ∀ s, HasDerivAt (fun s => p11RealFlow v s x + fun i => (k i : ℝ))
        (v (p11RealFlow v s x + fun i => (k i : ℝ))) s := fun s =>
      ((hsd s).add_const _).congr_deriv (hp _ k).symm
    exact (p11RealFlow_eq hv1 hM hb (x := x + fun i => (k i : ℝ)) (by simp [hs0]) hu t).symm

end KAM.Planetary

end
