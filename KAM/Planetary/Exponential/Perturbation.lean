/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Defs.IsPartialPerturbation
public import KAM.Planetary.Exponential.Setting
public import KAM.Planetary.Exponential.RealDomain
public import KAM.Planetary.Exponential.ComplexTube
public import KAM.Planetary.Poincare.Product

/-!
# P14 package E7: the normalized perturbation

Blueprint P, Part 14 (`bpP:p14:perturbation`, steps `pt-input`, `pt-rho`, `pt-def`, `pt-p12`,
`pt-p3`, `pt-p4`, `pt-neg`).

* `chart_perturbation_analytic`: the moving perturbation `fMov 1 1 m ∘ poincareProd m 1` is real
  analytic on the collision-free chart domain `chartSafe m` (the inherited pc-share gap).
* `perturbation`: `pt-input` — the compact core `perturbationCore` (one fundamental cell of the
  periodic orbit set of the enlarged cylinder) lies in `chartSafe`, and `tube` extends the chart
  perturbation to a shift-periodic holomorphic `fc` on a complex tube; `pt-rho` — `ρ = min κ (r/2)`
  and the bound `B₀` come from compactness of a thickening of the core; `pt-def` — `P = fc / B₀`
  on the tube and `0` elsewhere; `pt-p12`, `pt-p3`, `pt-p4` — the four clauses of
  `IsPartialPerturbation`; `pt-neg` — the same for `-P` (`isPartialPerturbation_neg_of`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Planetary

variable {n : ℕ}

/-- Inherited pc-share/ho-hol gap: analytic regularity, not merely smoothness. -/
theorem chart_perturbation_analytic (m : Fin n → ℝ) (hm : ∀ i, 0 < m i) :
    AnalyticOnNhd ℝ (fun w => fMov 1 1 m (poincareProd m 1 w)) (chartSafe m) := by
  have h := analyticOnNhd_fMov_poincareProd (G := 1) (m0 := 1) hm (by norm_num)
  simp only [mul_one] at h
  exact h

/-- `pt-input`: the fundamental cell `K_*` of the enlarged cylinder (fast angles in `[0, 2π]`). -/
def perturbationCore (B : AMDBox n) (kappa A : ℝ) : Set (Phase (n + n)) :=
  {w | (∀ i, 0 ≤ fast w.1 i ∧ fast w.1 i ≤ 2 * Real.pi) ∧ w ∈ enlargedCylinder B kappa A}

theorem perturbationCore_subset (B : AMDBox n) (kappa A : ℝ) :
    perturbationCore B kappa A ⊆ enlargedCylinder B kappa A := fun _ hw => hw.2

theorem isClosed_perturbationCore (B : AMDBox n) (kappa A : ℝ) :
    IsClosed (perturbationCore B kappa A) := by
  have h1 : IsClosed {w : Phase (n + n) | ∀ i : Fin n, 0 ≤ fast w.1 i ∧ fast w.1 i ≤ 2 * Real.pi} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => ?_
    have : Continuous fun w : Phase (n + n) => fast w.1 i :=
      (continuous_apply _).comp continuous_fst
    exact (isClosed_le continuous_const this).inter (isClosed_le this continuous_const)
  have h2 : IsClosed {w : Phase (n + n) | ∀ i : Fin n, B.lower i - 2 * kappa ≤ fast w.2 i ∧
      fast w.2 i ≤ B.upper i + 2 * kappa} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => ?_
    have : Continuous fun w : Phase (n + n) => fast w.2 i :=
      (continuous_apply _).comp continuous_snd
    exact (isClosed_le continuous_const this).inter (isClosed_le this continuous_const)
  have h3 : IsClosed {w : Phase (n + n) | chartAMD w ≤ A} := by
    refine isClosed_le ?_ continuous_const
    unfold chartAMD
    refine continuous_finsetSum _ fun i _ => ?_
    have a : Continuous fun w : Phase (n + n) => slow w.1 i :=
      (continuous_apply _).comp continuous_fst
    have b : Continuous fun w : Phase (n + n) => slow w.2 i :=
      (continuous_apply _).comp continuous_snd
    exact ((a.pow 2).add (b.pow 2)).div_const _
  have := h1.inter (h2.inter h3)
  convert this using 1
  ext w
  simp only [perturbationCore, enlargedCylinder, mem_ofPred_eq, mem_inter_iff]

theorem isCompact_perturbationCore (B : AMDBox n) (kappa A : ℝ) :
    IsCompact (perturbationCore B kappa A) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_perturbationCore B kappa A) ?_
  set c : ℝ := ∑ i, (|B.lower i - 2 * kappa| + |B.upper i + 2 * kappa|) with hcdef
  have hc0 : ∀ i, |B.lower i - 2 * kappa| + |B.upper i + 2 * kappa| ≤ c := fun i =>
    Finset.single_le_sum (f := fun j => |B.lower j - 2 * kappa| + |B.upper j + 2 * kappa|)
      (fun j _ => by positivity) (Finset.mem_univ i)
  refine (Metric.isBounded_closedBall (x := (0 : Phase (n + n)))
    (r := 2 * Real.pi + c + 1 + 2 * A)).subset fun w hw => ?_
  obtain ⟨h1, h2, hA⟩ := hw
  have hpi := Real.pi_pos
  have hcnn : 0 ≤ c := Finset.sum_nonneg fun j _ => by positivity
  have hsl : ∀ i, (slow w.1 i) ^ 2 + (slow w.2 i) ^ 2 ≤ 2 * A := fun i => by
    have := Finset.single_le_sum (f := fun j => ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
    unfold chartAMD at hA
    linarith
  have habs : ∀ x : ℝ, x ^ 2 ≤ 2 * A → |x| ≤ 1 + 2 * A := fun x hx => by
    by_contra h
    push Not at h
    nlinarith [sq_abs x, abs_nonneg x]
  have hA0 : 0 ≤ A := by
    by_cases hn : n = 0
    · subst hn
      unfold chartAMD at hA
      simp at hA
      exact hA
    · have := hsl ⟨0, Nat.pos_of_ne_zero hn⟩
      nlinarith [sq_nonneg (slow w.1 ⟨0, Nat.pos_of_ne_zero hn⟩),
        sq_nonneg (slow w.2 ⟨0, Nat.pos_of_ne_zero hn⟩)]
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := h1 i
      rw [Real.norm_eq_abs, abs_le]
      simp only [fast] at this
      constructor <;> linarith [this.1, this.2]
    · have := habs _ ((le_add_of_nonneg_right (sq_nonneg _)).trans (hsl i))
      rw [Real.norm_eq_abs]
      simp only [slow] at this
      linarith
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := h2 i
      have := hc0 i
      rw [Real.norm_eq_abs, abs_le]
      have h4 := neg_abs_le (B.lower i - 2 * kappa)
      have h5 := le_abs_self (B.upper i + 2 * kappa)
      have h6 := neg_abs_le (B.upper i + 2 * kappa)
      have h7 := abs_nonneg (B.lower i - 2 * kappa)
      have h8 := abs_nonneg (B.upper i + 2 * kappa)
      have h2i := h2 i
      simp only [fast] at h2i
      constructor <;> linarith [h2i.1, h2i.2]
    · have := habs _ ((le_add_of_nonneg_left (sq_nonneg _)).trans (hsl i))
      rw [Real.norm_eq_abs]
      simp only [slow] at this
      linarith

end KAM.Planetary

end
