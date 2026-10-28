/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.HigherCauchy
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Planetary.MaximalStep.Basic

/-!
# Parameter Cauchy estimates (P11A-C3, `bpP:p11a:param-cauchy`)

Iterated Cauchy estimates for a holomorphic map on the complex collar `E + t`: the `j`-th Fréchet
derivative at a point of the inner collar `E + t'` is bounded by `j^j M / (t - t')^j`. The proof
iterates the first-order closed-ball estimate `j` times on balls of radius `(t - t') / j`
(`stepP:p11a:pc-iter`); no polydisc parametrisation is needed since the nested closed balls lie in
the collar (`stepP:p11a:pc-poly`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
universe u
namespace KAM.Planetary

/-- The collar `E + t` is open. -/
theorem p11_isOpen_actionNbhd {n : ℕ} (E : Set (P11Vec n)) (t : ℝ) :
    IsOpen (KAM.actionNbhd E t) := by
  have h : KAM.actionNbhd E t =
      ⋃ J ∈ E, ball (fun i => (J i : ℂ)) t := by
    ext I
    simp [KAM.actionNbhd, mem_ball, dist_eq_norm]
  rw [h]
  exact isOpen_biUnion fun _ _ => isOpen_ball

/-- Iterated Cauchy estimate on nested closed balls: a bound `A` on `closedBall z (k δ)` gives
`‖D^k f (z)‖ ≤ A / δ^k`. -/
theorem p11_norm_iteratedFDeriv_le_of_closedBall {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ (k : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
      [CompleteSpace F] [SecondCountableTopology F] {f : E → F} {A : ℝ} {z : E},
      DifferentiableOn ℂ f U →
      closedBall z (k * δ) ⊆ U → (∀ w ∈ closedBall z (k * δ), ‖f w‖ ≤ A) →
      ‖iteratedFDeriv ℂ k f z‖ ≤ A / δ ^ k := by
  intro k
  induction k with
  | zero =>
    intro F _ _ _ _ f A z _ _ hA
    simpa using hA z (by simp)
  | succ k ih =>
    intro F _ _ _ _ f A z hf hz hA
    have hz' : closedBall z (k * δ) ⊆ U :=
      (closedBall_subset_closedBall (by push_cast; nlinarith)).trans hz
    have key : ∀ w ∈ closedBall z (k * δ), ‖fderiv ℂ f w‖ ≤ A / δ := by
      intro w hw
      have hsub : closedBall w δ ⊆ closedBall z ((k + 1 : ℕ) * δ) :=
        closedBall_subset_closedBall' (by
          have := mem_closedBall.mp hw
          push_cast
          nlinarith)
      exact KAM.norm_fderiv_le_of_closedBall_bound hU hf hδ (hsub.trans hz)
        (fun u hu => hA u (hsub hu))
    have := ih (differentiableOn_fderiv_of_isOpen hU hf) hz' key
    rw [norm_iteratedFDeriv_fderiv] at this
    rw [pow_succ]
    convert this using 1
    field_simp

/-- `bpP:p11a:param-cauchy`: the `j`-th derivative of a holomorphic map on `E + t`, bounded by
`M`, is at most `j^j M / (t - t')^j` on `E + t'`. -/
theorem param_cauchy {n q : ℕ} {E : Set (P11Vec n)} {t tp M : ℝ}
    (htp : 0 < tp) (ht : tp < t) (hM : 0 ≤ M)
    {u : P11CVec n → P11CVec q} (hu : DifferentiableOn ℂ u (KAM.actionNbhd E t))
    (hb : p11Bound (KAM.actionNbhd E t) u M) {j : ℕ} (hj : 1 ≤ j) :
    ∀ b ∈ KAM.actionNbhd E tp, ‖iteratedFDeriv ℂ j u b‖ ≤
      (j : ℝ)^j*M/(t-tp)^j := by
  intro b hb'
  obtain ⟨J, hJ, hbJ⟩ := hb'
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hδ : 0 < (t - tp) / j := div_pos (by linarith) hjpos
  have hball : closedBall b (j * ((t - tp) / j)) ⊆ KAM.actionNbhd E t := by
    intro w hw
    refine ⟨J, hJ, ?_⟩
    have hw' := mem_closedBall_iff_norm.mp hw
    rw [mul_div_cancel₀ _ hjpos.ne'] at hw'
    calc ‖w - fun i => (J i : ℂ)‖ = ‖(w - b) + (b - fun i => (J i : ℂ))‖ := by
          congr 1; abel
      _ ≤ ‖w - b‖ + ‖b - fun i => (J i : ℂ)‖ := norm_add_le _ _
      _ < t := by linarith
  have := p11_norm_iteratedFDeriv_le_of_closedBall (p11_isOpen_actionNbhd E t) hδ j hu hball
    (fun w hw => hb w (hball hw))
  convert this using 1
  rw [div_pow, div_div_eq_mul_div]
  ring

end KAM.Planetary
