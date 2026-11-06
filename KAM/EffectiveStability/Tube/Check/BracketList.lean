/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.BTerm
public import KAM.EffectiveStability.Tube.Obs.ListObs
public import KAM.EffectiveStability.Tube.Chart.Shift

/-!
# The reduced bracket of two list observables, term by term (T2-CONF, N9 (A))

For `f = Σ_{i ∈ Fl} u^{μ_i} g_i(φ)` and `h = Σ_{e ∈ Hl} u^{ν_e} k_e(φ)` (N8's `listObs`), N2's
`reducedBracket f h (u, φ)` is the sum over N7's bracket terms `b ∈ bterms Fl Hl` of
`coef b · u^{mon b} · val b φ` (`reducedBracket_listObs`). The identity is pure algebra: the
`u`-partials are `∂_{u_x} u^m = m_x u^{m - e_x}`, and `m_x u^{m - e_x} u^n = m_x u^{m + n - e_x}`
(natural subtraction; both sides vanish when `m_x = 0`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

/-- `m_x u^{m - e_x} u^n = m_x u^{m + n - e_x}`. -/
theorem natCast_mul_umon_sub_mul_umon (m n : Fin 3 → ℕ) (x : Fin 3) (u : Fin 3 → ℝ) :
    (m x : ℝ) * umon (m - Pi.single x 1) u * umon n u =
      (m x : ℝ) * umon (m + n - Pi.single x 1) u := by
  by_cases h : m x = 0
  · simp [h]
  · have e : m + n - Pi.single x 1 = (m - Pi.single x 1) + n := by
      ext y
      by_cases hy : y = x
      · subst hy; simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]; omega
      · simp [hy]
    rw [e, umon_add, mul_assoc]

/-- `n_x u^m u^{n - e_x} = n_x u^{m + n - e_x}`. -/
theorem natCast_mul_umon_mul_umon_sub (m n : Fin 3 → ℕ) (x : Fin 3) (u : Fin 3 → ℝ) :
    (n x : ℝ) * (umon m u * umon (n - Pi.single x 1) u) =
      (n x : ℝ) * umon (m + n - Pi.single x 1) u := by
  have h := natCast_mul_umon_sub_mul_umon n m x u
  rw [add_comm m n, ← h]
  ring

/-- Sum over a `flatMap`. -/
theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (F : β → ℝ) :
    ((l.flatMap f).map F).sum = (l.map fun a => ((f a).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- Distributing a product of list sums. -/
theorem list_sum_mul_list_sum {ι κ : Type*} (Fl : List ι) (Hl : List κ) (A : ι → ℝ)
    (C : κ → ℝ) :
    (Fl.map A).sum * (Hl.map C).sum = (Fl.map fun i => (Hl.map fun e => A i * C e).sum).sum := by
  rw [← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [← List.sum_map_mul_left]

theorem list_sum_sub {ι : Type*} (Fl : List ι) (A B : ι → ℝ) :
    (Fl.map A).sum - (Fl.map B).sum = (Fl.map fun i => A i - B i).sum := by
  induction Fl with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

theorem list_sum_add {ι : Type*} (Fl : List ι) (A B : ι → ℝ) :
    (Fl.map A).sum + (Fl.map B).sum = (Fl.map fun i => A i + B i).sum := by
  induction Fl with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

/-- **(A) The bracket of two list observables, term by term.** -/
theorem reducedBracket_listObs {ι κ : Type*} (Fl : List ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (Hl : List κ) (ν : κ → Fin 3 → ℕ) (k : κ → (Fin 2 → ℝ) → ℝ)
    (hg : ∀ i ∈ Fl, Differentiable ℝ (g i)) (hk : ∀ e ∈ Hl, Differentiable ℝ (k e))
    (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) :
    reducedBracket (listObs Fl μ g) (listObs Hl ν k) (u, φ) =
      ((bterms Fl Hl).map fun b => (b.coef μ ν : ℝ) * umon (b.mon μ ν) u * b.val g k φ).sum := by
  -- the per-`(a, i, e)` contribution
  set T : Fin 2 → ι → κ → ℝ := fun a i e =>
    (μ i a.castSucc : ℝ) * umon (μ i + ν e - Pi.single a.castSucc 1) u *
        (g i φ * pderiv (k e) φ a) -
      (μ i 2 : ℝ) * umon (μ i + ν e - Pi.single 2 1) u * (g i φ * pderiv (k e) φ a) -
      (ν e a.castSucc : ℝ) * umon (μ i + ν e - Pi.single a.castSucc 1) u *
        (pderiv (g i) φ a * k e φ) +
      (ν e 2 : ℝ) * umon (μ i + ν e - Pi.single 2 1) u * (pderiv (g i) φ a * k e φ) with hT
  -- the right side
  have hR : ((bterms Fl Hl).map fun b =>
      (b.coef μ ν : ℝ) * umon (b.mon μ ν) u * b.val g k φ).sum =
      ∑ a : Fin 2, (Fl.map fun i => (Hl.map fun e => T a i e).sum).sum := by
    rw [bterms, sum_map_flatMap, Fin.sum_univ_two]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 1 <;>
    · rw [sum_map_flatMap]
      refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
      rw [sum_map_flatMap]
      refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
      simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        List.append_nil, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil,
        BT.coef, BT.mon, BT.val, BT.axis, hT]
      push_cast
      ring
  rw [hR, reducedBracket, Fin.sum_univ_two]
  have hpt : ∀ a : Fin 2,
      (fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single a.castSucc 1, 0) -
          fderiv ℝ (listObs Fl μ g) (u, φ) (Pi.single 2 1, 0)) *
          fderiv ℝ (listObs Hl ν k) (u, φ) (0, Pi.single a 1) -
        fderiv ℝ (listObs Fl μ g) (u, φ) (0, Pi.single a 1) *
          (fderiv ℝ (listObs Hl ν k) (u, φ) (Pi.single a.castSucc 1, 0) -
            fderiv ℝ (listObs Hl ν k) (u, φ) (Pi.single 2 1, 0)) =
        (Fl.map fun i => (Hl.map fun e => T a i e).sum).sum := by
    intro a
    rw [fderiv_listObs_u Fl μ hg, fderiv_listObs_u Fl μ hg, fderiv_listObs_φ Hl ν hk,
      fderiv_listObs_φ Fl μ hg, fderiv_listObs_u Hl ν hk, fderiv_listObs_u Hl ν hk,
      list_sum_sub, list_sum_sub, list_sum_mul_list_sum, list_sum_mul_list_sum, list_sum_sub]
    refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
    rw [list_sum_sub]
    refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
    have h1 := natCast_mul_umon_sub_mul_umon (μ i) (ν e) a.castSucc u
    have h2 := natCast_mul_umon_sub_mul_umon (μ i) (ν e) 2 u
    have h3 := natCast_mul_umon_mul_umon_sub (μ i) (ν e) a.castSucc u
    have h4 := natCast_mul_umon_mul_umon_sub (μ i) (ν e) 2 u
    simp only [hT, pderiv]
    linear_combination (g i φ * fderiv ℝ (k e) φ (Pi.single a 1)) * h1 -
      (g i φ * fderiv ℝ (k e) φ (Pi.single a 1)) * h2 -
      (fderiv ℝ (g i) φ (Pi.single a 1) * k e φ) * h3 +
      (fderiv ℝ (g i) φ (Pi.single a 1) * k e φ) * h4
  rw [hpt 0, hpt 1, Fin.sum_univ_two]

end KAM.EffectiveStability.Tube

end
