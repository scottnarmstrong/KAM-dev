/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Deriv
public import KAM.EffectiveStability.Tube.Engine.Sparse

/-!
# Derivative operands (T2-CONF, N7)

The angle derivative `∂_a` of an operand as an operand of the opposite parity:

* `colsOk_dlist`, `symOk_dlist`, `mx_dlist`: `dlist` keeps the padding zero, flips the symmetry
  parity and multiplies the slot bound by `C`; `symOk_of_getD` (the converse of `symOk_spec`);
* `LitD.dopd P a d`: the derivative of a literal, packed by `derivZ` (`LitD.dwf`, `LitD.dmx`,
  `LitD.dsym`, `LitD.dopd_eval`);
* `SpD.deriv a d`: the derivative of a sparse model, again a sparse model (`SpD.ok_deriv`,
  `SpD.list_deriv`, `SpD.deriv_eval`);
* `l1_le_of_mx`: `l1 d ≤ |d| m` from a slot bound `m`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

theorem colsOk_dlist {C S : ℕ} {d : List ℤ} (h : colsOk C S d = true) (κ : ℕ → ℤ × ℤ) (a : Fin 2)
    (p : Bool) : colsOk C S (dlist κ a p d) = true := by
  apply colsOk_of_getD
  intro i hi
  simp only [zero_add]
  rw [getD_dlist] at hi
  by_contra hc
  push Not at hc
  exact hi (by rw [getD_eq_zero_of_colsOk h hc, mul_zero])

/-- The converse of `symOk_spec`. -/
theorem symOk_of_getD {q : Bool} {d : List ℤ}
    (h : ∀ i < d.length, d.getD (d.length - 1 - i) 0 = psgn q * d.getD i 0) :
    symOk q d = true := by
  unfold symOk
  rw [beq_iff_eq]
  apply List.ext_getElem
  · cases q <;> simp
  · intro i h1 _
    rw [List.getElem_reverse]
    have hi : i < d.length := by simpa using h1
    have := h i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [this]
    cases q <;> simp [psgn]

theorem kc_neg (k : ℤ × ℤ) (a : Fin 2) : kc (-k) a = -kc k a := by
  unfold kc; split_ifs <;> rfl

/-- **The derivative flips the symmetry parity.** -/
theorem symOk_dlist {C S : ℕ} (hS : 2 * C < S) {p : Bool} {d : List ℤ} (hs : symOk p d = true)
    (hc : colsOk C S d = true) (hl : d.length = Layout.len C S) (a : Fin 2) :
    symOk (!p) (dlist (Layout.key C S) a p d) = true := by
  apply symOk_of_getD
  intro i hi
  rw [length_dlist, hl] at hi ⊢
  rw [getD_dlist, getD_dlist]
  have hsd := symOk_spec hs (i := i) (by rw [hl]; exact hi)
  rw [hl] at hsd
  rw [hsd]
  by_cases hcol : i % S ≤ 2 * C
  · rw [Layout.key_reflect hS hi hcol, kc_neg]
    cases p <;> simp [psgn] <;> ring
  · push Not at hcol
    rw [getD_eq_zero_of_colsOk hc hcol]
    simp

/-- The slot bound of a derivative list. -/
theorem mx_dlist {C S : ℕ} (hS : 2 * C < S) {d : List ℤ} (hc : colsOk C S d = true)
    (hl : d.length ≤ Layout.len C S) {m : ℤ} (hm : ∀ x ∈ d, |x| ≤ m) (a : Fin 2) (p : Bool) :
    ∀ y ∈ dlist (Layout.key C S) a p d, |y| ≤ C * m := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hi' : i < d.length := by rwa [length_dlist] at hi
  have hg : (dlist (Layout.key C S) a p d)[i] = (dlist (Layout.key C S) a p d).getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hdi : d.getD i 0 = d[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm _ (List.getElem_mem hi'))
  rw [hg, getD_dlist, abs_mul, abs_mul]
  by_cases hcol : i % S ≤ 2 * C
  · have hk := abs_kc_key_le hS hcol (by omega) a
    have hx : |d.getD i 0| ≤ m := by rw [hdi]; exact hm _ (List.getElem_mem hi')
    have hp : |psgn p| = 1 := by cases p <;> simp [psgn]
    rw [hp, one_mul]
    exact mul_le_mul hk hx (abs_nonneg _) (by positivity)
  · push Not at hcol
    rw [getD_eq_zero_of_colsOk hc hcol]
    simp only [abs_zero, mul_zero]
    positivity

/-- `l1 d ≤ |d| m` from a slot bound. -/
theorem l1_le_of_mx {d : List ℤ} {m : ℤ} (hm : ∀ x ∈ d, |x| ≤ m) : l1 d ≤ d.length * m := by
  rw [l1_eq]
  calc ∑ i ∈ range d.length, |d.getD i 0| ≤ ∑ _i ∈ range d.length, m := by
        refine sum_le_sum fun i hi => ?_
        have hi' := mem_range.mp hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
        exact hm _ (List.getElem_mem hi')
    _ = d.length * m := by simp

/-! ### Literals -/

/-- The packed derivative of a literal (kernel). -/
def LitD.dZ (P : Prm) (a : Fin 2) (d : LitD) : ℤ := derivZ P.w P.S d.C (P.b - 1) a d.par (d.Z P)

/-- The derivative operand of a literal. -/
def LitD.dopd (P : Prm) (a : Fin 2) (d : LitD) : Opd :=
  ⟨d.C, !d.par, d.q, dlist (Layout.key d.C P.S) a d.par (litList d.C P.S P.b d.X), d.dZ P a⟩

theorem LitD.dwf {P : Prm} {d : LitD} (h : d.ok P = true) (hb : 1 ≤ P.b) (a : Fin 2) :
    (d.dopd P a).WF P.w P.S := by
  have hwf := LitD.wf h
  simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, hbw⟩, hKS⟩, -⟩, -⟩ := h
  refine ⟨?_, colsOk_dlist hwf.cols _ _ _, ?_⟩
  · exact (packSum_dlist hKS (by omega) hwf.pack hwf.cols hwf.len (abs_litList_lt hb) a d.par).symm
  · simp only [LitD.dopd, length_dlist]; exact hwf.len

theorem LitD.dmx {P : Prm} {d : LitD} (h : d.ok P = true) (hb : 1 ≤ P.b) (a : Fin 2) :
    (d.dopd P a).Mx (d.C * 2 ^ (P.b - 1)) := by
  have hwf := LitD.wf h
  simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, hKS⟩, -⟩, -⟩ := h
  intro y hy
  have := mx_dlist (C := d.C) (by omega) hwf.cols hwf.len (LitD.mx (d := d) hb) a d.par y hy
  push_cast
  exact this

theorem LitD.dsym {P : Prm} {d : LitD} (h : d.ok P = true) (hb : 1 ≤ P.b)
    (hs : symDigOk d.par d.C P.b d.X = true) (a : Fin 2) :
    symOk (d.dopd P a).par (d.dopd P a).l = true ∧
      (d.dopd P a).l.length = Layout.len (d.dopd P a).C P.S := by
  have hwf := LitD.wf h
  simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, hKS⟩, -⟩, -⟩ := h
  obtain ⟨hs', hl⟩ := LitD.sym hb hKS hs
  exact ⟨symOk_dlist (C := d.C) (by omega) hs' hwf.cols hl a, by
    simp only [LitD.dopd, length_dlist]; exact hl⟩

theorem LitD.dopd_eval (P : Prm) (a : Fin 2) (d : LitD) (φ : Fin 2 → ℝ) :
    (d.dopd P a).eval P.S φ = pderiv ((d.opd P).eval P.S) φ a := by
  rw [show (d.opd P).eval P.S = fun φ => (d.q : ℝ) *
      evalK (Layout.key d.C P.S) d.par (litList d.C P.S P.b d.X) φ from rfl,
    C1Close.pderiv_const_mul (differentiable_evalK _ _ _), pderiv_evalK]
  rfl

/-! ### Sparse models -/

/-- The derivative of a sparse model. -/
def SpD.deriv (a : Fin 2) (d : SpD) : SpD :=
  ⟨d.C, !d.par, d.q, d.es.map fun e =>
    (e.1, psgn d.par * kc (((e.1.1 : ℕ) : ℤ) - d.C, ((e.1.2 : ℕ) : ℤ) - d.C) a * e.2)⟩

theorem SpD.ok_deriv (S : ℕ) (a : Fin 2) (d : SpD) : (d.deriv a).ok S = d.ok S := by
  cases d
  unfold SpD.ok SpD.deriv
  rw [List.all_map]
  rfl

theorem SpD.list_deriv {S : ℕ} {d : SpD} (h : d.ok S = true) (a : Fin 2) :
    (d.deriv a).list S = dlist (Layout.key d.C S) a d.par (d.list S) := by
  apply List.ext_getElem
  · rw [length_dlist, SpD.length_list, SpD.length_list]; rfl
  · intro i h1 h2
    have hg1 : ((d.deriv a).list S)[i] = ((d.deriv a).list S).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
    have hg2 : (dlist (Layout.key d.C S) a d.par (d.list S))[i] =
        (dlist (Layout.key d.C S) a d.par (d.list S)).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    rw [hg1, hg2, getD_dlist, SpD.getD_list, SpD.getD_list]
    have hC : (d.deriv a).C = d.C := rfl
    simp only [hC]
    by_cases hi : i < Layout.len d.C S
    · simp only [hi, if_true]
      have hfil : List.filter (fun e => SpD.idx S e == i) (d.deriv a).es =
          (List.filter (fun e => SpD.idx S e == i) d.es).map fun e =>
            (e.1, psgn d.par * kc (((e.1.1 : ℕ) : ℤ) - d.C, ((e.1.2 : ℕ) : ℤ) - d.C) a * e.2) := by
        rw [SpD.deriv, List.filter_map]; rfl
      rw [hfil, List.map_map, ← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun e he => ?_)
      have hef := List.mem_filter.mp he
      have hidx : SpD.idx S e = i := by simpa using hef.2
      have hok := h
      simp only [SpD.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
      have he' := hok.2 e hef.1
      have e1 := mod_div_of_lt (S := S) (c := e.1.1) (r := e.1.2) (by omega)
      have hkey : Layout.key d.C S i = (((e.1.1 : ℕ) : ℤ) - d.C, ((e.1.2 : ℕ) : ℤ) - d.C) := by
        rw [← hidx]; simp only [Layout.key, SpD.idx, e1.1, e1.2]
      simp only [Function.comp_apply, hkey]
    · simp [hi]

theorem SpD.deriv_eval {w S : ℕ} {d : SpD} (h : d.ok S = true) (a : Fin 2) (w' : ℕ)
    (φ : Fin 2 → ℝ) : ((d.deriv a).opd w S).eval S φ = pderiv ((d.opd w' S).eval S) φ a := by
  rw [show (d.opd w' S).eval S = fun φ => (d.q : ℝ) *
      evalK (Layout.key d.C S) d.par (d.list S) φ from rfl,
    C1Close.pderiv_const_mul (differentiable_evalK _ _ _), pderiv_evalK, ← SpD.list_deriv h]
  rfl

end KAM.EffectiveStability.Tube

end
