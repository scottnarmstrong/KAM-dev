/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Bracket

/-!
# The dropped part of the bracket (T2-CONF, N10)

The bracket of a literal observable `f = Σ_{i ∈ Fl} u^{s_i} g_i` and a literal model
`h = Σ_{t ∈ Hl} u^t k_t` is a sum over the bracket terms `bterms Fl Hl` (`BTerm.lean`). The kept
part (`u`-degree `≤ L`) is bounded per monomial by `brCheck` (`Bracket.lean`); this module bounds
the dropped part, the terms of `u`-degree `> L`, on the box `|u| ≤ r`:

* `dropT`: the bound of one term, `|coef| r^{d - 1} (|q| Σ|m|)_F (|q| n)_H` (`n` the `ℓ¹` claim of
  `H_t`, times `C` for its derivative), when the total degree `d = |s_i| + |t|` is at least `L + 2`,
  else `0`;
* `dropSum`: factored nested sums equal to `Σ dropT` over `bterms` (`dropSum_eq`);
* `dropCheck` and **`dropCheck_sound`**: `dropSum ≤ D` bounds the dropped part by `D`.

For a term with a nonzero coefficient, the monomial has degree `d - 1` (`mdeg_mon_eq`), so it is
dropped only when `L + 2 ≤ d`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- The bound of one bracket term if it is dropped (`u`-degree `> L`), else `0`. -/
def dropT (_Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ) (b : BrT) : ℚ :=
  let d := b.i.1.1 + b.i.1.2.1 + b.i.1.2.2 + (b.e.1 + b.e.2.1 + b.e.2.2)
  if L + 2 ≤ d then |(b.coef muF monOf : ℚ)| * r ^ (d - 1) * (|(brSp b).q| * (brSp b).l1E) *
    (|(HL b.e).q| * (if b.kind then nH b.e else (HL b.e).C * nH b.e)) else 0

/-- The `F`-side factor `|q| Σ|m|` of `brSp` (it depends on the axis, the entry and the kind
only). -/
def dropF (a : Fin 2) (i : (ℕ × ℕ × ℕ) × SpD) (kind : Bool) : ℚ :=
  |(if kind then i.2.deriv a else i.2).q| * (if kind then i.2.deriv a else i.2).l1E

/-- The `H`-side factor `|q| n` (`|q| C n` for the derivative of `H_t`). -/
def dropH (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (e : ℕ × ℕ × ℕ) (kind : Bool) : ℚ :=
  |(HL e).q| * (if kind then nH e else (HL e).C * nH e)

/-- The degree factor `|coef| r^{d - 1}` of a dropped term, else `0`. -/
def dropC (r : ℚ) (L : ℕ) (b : BrT) : ℚ :=
  let d := b.i.1.1 + b.i.1.2.1 + b.i.1.2.2 + (b.e.1 + b.e.2.1 + b.e.2.2)
  if L + 2 ≤ d then |(b.coef muF monOf : ℚ)| * r ^ (d - 1) else 0

/-- `Σ dropT` over the bracket terms as nested sums, with the `F`- and `H`-side factors computed
once per axis, entry and kind (`dropSum_eq`); never one flat list. -/
def dropSum (_Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ)
    (Fl : List ((ℕ × ℕ × ℕ) × SpD)) (Hl : List (ℕ × ℕ × ℕ)) : ℚ :=
  (([0, 1] : List (Fin 2)).map fun a => (Fl.map fun i =>
    (([false, true] : List Bool).map fun kind => dropF a i kind *
      (Hl.map fun e => dropH HL nH e kind *
        (([false, true] : List Bool).map fun sh =>
          dropC r L ⟨a, i, e, kind, sh⟩).sum).sum).sum).sum).sum

/-- The dropped-part check. -/
def dropCheck (Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ)
    (Fl : List ((ℕ × ℕ × ℕ) × SpD)) (Hl : List (ℕ × ℕ × ℕ)) (D : ℚ) : Bool :=
  decide (0 ≤ r) && decide (dropSum Pb HL nH r L Fl Hl ≤ D)

/-! ### Sums -/

theorem sum_map_flatMapQ {α β : Type*} (l : List α) (f : α → List β) (F : β → ℚ) :
    ((l.flatMap f).map F).sum = (l.map fun x => ((f x).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem cast_sum_mapQ {β : Type*} (l : List β) (F : β → ℚ) :
    (((l.map F).sum : ℚ) : ℝ) = (l.map fun x => (F x : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem dropT_eq (Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ) (b : BrT) :
    dropT Pb HL nH r L b = dropF b.a b.i b.kind * (dropH HL nH b.e b.kind * dropC r L b) := by
  simp only [dropT, dropF, dropH, dropC, brSp]
  split_ifs <;> ring

theorem sum_map_commQ {α β : Type*} (l : List α) (m : List β) (f : α → β → ℚ) :
    (l.map fun x => (m.map fun y => f x y).sum).sum =
      (m.map fun y => (l.map fun x => f x y).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, ← List.sum_map_add]

theorem dropSum_eq (Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ)
    (Fl : List ((ℕ × ℕ × ℕ) × SpD)) (Hl : List (ℕ × ℕ × ℕ)) :
    dropSum Pb HL nH r L Fl Hl = ((bterms Fl Hl).map (dropT Pb HL nH r L)).sum := by
  simp only [bterms, sum_map_flatMapQ, List.map_map, Function.comp_def, dropT_eq]
  unfold dropSum
  congr 1; refine List.map_congr_left fun a _ => ?_
  congr 1; refine List.map_congr_left fun i _ => ?_
  rw [sum_map_commQ Hl]
  congr 1; refine List.map_congr_left fun kind _ => ?_
  rw [← List.sum_map_mul_left]
  congr 1; refine List.map_congr_left fun e _ => ?_
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]

/-! ### One term -/

/-- The total degree `|s_i| + |t|` of a term. -/
def dropDeg (b : BrT) : ℕ := b.i.1.1 + b.i.1.2.1 + b.i.1.2.2 + (b.e.1 + b.e.2.1 + b.e.2.2)

/-- For a nonzero coefficient, the monomial of a term has degree `|s_i| + |t| - 1`. -/
theorem mdeg_mon_eq (b : BrT) (h : b.coef muF monOf ≠ 0) :
    mdeg (b.mon muF monOf) = dropDeg b - 1 := by
  have h1 := one_le_of_coef_ne_zero muF b h
  obtain ⟨a, ⟨⟨x, y, z⟩, d⟩, ⟨p, q, s⟩, kind, sh⟩ := b
  simp only [BT.mon, BT.axis, muF, mdeg, dropDeg, Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply,
    single_eq_dl, monOf, dl] at h1 ⊢
  cases sh <;> fin_cases a <;> simp at h1 ⊢ <;> omega

theorem dropT_nonneg {Pb : Prm} {HL : ℕ×ℕ×ℕ → LitD} {nH : ℕ×ℕ×ℕ → ℕ} {r : ℚ} (hr : 0 ≤ r)
    (L : ℕ) (b : BrT) : 0 ≤ dropT Pb HL nH r L b := by
  simp only [dropT]
  split_ifs <;> first
    | exact le_rfl
    | exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hr _))
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

/-- The value bound `|val| ≤ (|q| Σ|m|)_F (|q| n)_H` (times `C` for the derivative of `H_t`). -/
theorem abs_val_le {Pb P0 : Prm} {HL : ℕ×ℕ×ℕ → LitD} {nH : ℕ×ℕ×ℕ → ℕ}
    (w₀ : ℕ) (hS0 : P0.S = Pb.S) (hb0 : P0.b = Pb.b) (b : BrT) (hF : b.i.2.ok Pb.S = true)
    (hH : (HL b.e).ok Pb = true ∧ (HL b.e).l1Check Pb (nH b.e) = true) (φ : Fin 2 → ℝ) :
    |b.val (fun i => (i.2.opd w₀ Pb.S).eval Pb.S) (fun t => ((HL t).opd P0).eval P0.S) φ| ≤
      (|(brSp b).q| * (brSp b).l1E : ℚ) *
        (|(HL b.e).q| * (if b.kind then nH b.e else (HL b.e).C * nH b.e) : ℚ) := by
  have hk : ((HL b.e).opd P0).eval P0.S = ((HL b.e).opd Pb).eval Pb.S :=
    LitD.opd_eval_congr hS0 hb0 (HL b.e)
  have hl := LitD.l1_le hH.2
  have hwf := LitD.wf hH.1
  have hok := hH.1
  simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hS : 2 * ((HL b.e).opd Pb).C < Pb.S := by
    show 2 * (HL b.e).C < Pb.S; omega
  have hK : ∀ φ, |((HL b.e).opd Pb).eval Pb.S φ| ≤ |((HL b.e).q : ℝ)| * nH b.e :=
    fun φ => Opd.abs_eval_le (w := Pb.w) hl φ
  have hdK : ∀ φ a, |pderiv (((HL b.e).opd Pb).eval Pb.S) φ a| ≤
      |((HL b.e).q : ℝ)| * ((HL b.e).C * nH b.e) :=
    fun φ a => Opd.abs_pderiv_eval_le hS hwf hl φ a
  unfold BT.val
  dsimp only
  rw [hk]
  cases hkind : b.kind
  · -- `g · ∂_a k`
    have hsp : brSp b = b.i.2 := by simp [brSp, hkind]
    have hg : |(b.i.2.opd w₀ Pb.S).eval Pb.S φ| ≤ |(b.i.2.q : ℝ)| * b.i.2.l1E :=
      Opd.abs_eval_le (w := w₀) (SpD.l1_list_le hF) φ
    simp only [ite_false, Bool.false_eq_true, hsp]
    rw [abs_mul]
    push_cast
    exact mul_le_mul hg (hdK φ b.a) (abs_nonneg _) (by positivity)
  · -- `∂_a g · k`
    have hsp : brSp b = b.i.2.deriv b.a := by simp [brSp, hkind]
    have hd : pderiv ((b.i.2.opd w₀ Pb.S).eval Pb.S) φ b.a =
        ((b.i.2.deriv b.a).opd w₀ Pb.S).eval Pb.S φ := (SpD.deriv_eval hF b.a w₀ φ).symm
    have hok' : (b.i.2.deriv b.a).ok Pb.S = true := by rw [SpD.ok_deriv]; exact hF
    have hg : |((b.i.2.deriv b.a).opd w₀ Pb.S).eval Pb.S φ| ≤
        |((b.i.2.deriv b.a).q : ℝ)| * (b.i.2.deriv b.a).l1E :=
      Opd.abs_eval_le (w := w₀) (SpD.l1_list_le hok') φ
    simp only [ite_true, hsp, hd]
    rw [abs_mul]
    push_cast
    exact mul_le_mul hg (hK φ) (abs_nonneg _) (by positivity)

/-- One dropped term is bounded by `dropT`. -/
theorem abs_dropTerm_le {Pb P0 : Prm} {HL : ℕ×ℕ×ℕ → LitD} {nH : ℕ×ℕ×ℕ → ℕ} {r : ℚ} (hr : 0 ≤ r)
    (L : ℕ) (w₀ : ℕ) (hS0 : P0.S = Pb.S) (hb0 : P0.b = Pb.b) (b : BrT)
    (hF : b.i.2.ok Pb.S = true) (hH : (HL b.e).ok Pb = true ∧ (HL b.e).l1Check Pb (nH b.e) = true)
    {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ (r : ℝ)) (φ : Fin 2 → ℝ) :
    |if decide (L < mdeg (b.mon muF monOf)) = true then (b.coef muF monOf : ℝ) *
      umon (b.mon muF monOf) u *
      b.val (fun i => (i.2.opd w₀ Pb.S).eval Pb.S) (fun t => ((HL t).opd P0).eval P0.S) φ
      else 0| ≤ (dropT Pb HL nH r L b : ℝ) := by
  have h0 : (0 : ℝ) ≤ (dropT Pb HL nH r L b : ℝ) := by exact_mod_cast dropT_nonneg hr L b
  by_cases hc : b.coef muF monOf = 0
  · split_ifs <;> simp [hc, h0]
  split_ifs with hL
  · have hm := mdeg_mon_eq b hc
    have hL' : L + 2 ≤ dropDeg b := by
      simp only [decide_eq_true_eq] at hL; omega
    have hT : dropT Pb HL nH r L b = |(b.coef muF monOf : ℚ)| * r ^ (dropDeg b - 1) *
        (|(brSp b).q| * (brSp b).l1E) *
        (|(HL b.e).q| * (if b.kind then nH b.e else (HL b.e).C * nH b.e)) := by
      have hL'' : L + 2 ≤ b.i.1.1 + b.i.1.2.1 + b.i.1.2.2 + (b.e.1 + b.e.2.1 + b.e.2.2) := hL'
      simp only [dropT, dropDeg, hL'', ite_true]
    rw [hT]
    have hU := abs_umon_le (r := (r : ℝ)) hu (b.mon muF monOf)
    rw [hm] at hU
    have hV := abs_val_le w₀ hS0 hb0 b hF hH φ
    rw [abs_mul, abs_mul]
    push_cast at hV ⊢
    have h1 : 0 ≤ |((b.coef muF monOf : ℤ) : ℝ)| := abs_nonneg _
    calc |((b.coef muF monOf : ℤ) : ℝ)| * |umon (b.mon muF monOf) u| *
          |b.val (fun i => (i.2.opd w₀ Pb.S).eval Pb.S) (fun t => ((HL t).opd P0).eval P0.S) φ|
        ≤ |((b.coef muF monOf : ℤ) : ℝ)| * (r : ℝ) ^ (dropDeg b - 1) * (|((brSp b).q : ℝ)| *
          ((brSp b).l1E : ℝ) * (|((HL b.e).q : ℝ)| *
            ((if b.kind then (nH b.e : ℕ) else (HL b.e).C * nH b.e : ℕ) : ℝ))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hU h1) ?_ (abs_nonneg _) ?_
          · convert hV using 3; split_ifs <;> push_cast <;> ring
          · exact mul_nonneg h1 (le_trans (abs_nonneg _) hU)
      _ = _ := by split_ifs <;> push_cast <;> ring
  · simpa using h0

/-! ### Soundness -/

theorem dropCheck_sound {Pb : Prm} {HL : ℕ×ℕ×ℕ → LitD} {nH : ℕ×ℕ×ℕ → ℕ} {r : ℚ} {L : ℕ}
    {Fl : List ((ℕ × ℕ × ℕ) × SpD)} {Hl : List (ℕ × ℕ × ℕ)} {D : ℚ}
    (hchk : dropCheck Pb HL nH r L Fl Hl D = true) (_hb : 1 ≤ Pb.b)
    (hF : ∀ i ∈ Fl, i.2.ok Pb.S = true)
    (hH : ∀ t ∈ Hl, (HL t).ok Pb = true ∧ (HL t).l1Check Pb (nH t) = true) (w₀ : ℕ) {P0 : Prm}
    (hS0 : P0.S = Pb.S) (hb0 : P0.b = Pb.b) {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ (r : ℝ))
    (φ : Fin 2 → ℝ) :
    |((bterms Fl Hl).filter fun b => decide (L < mdeg (b.mon muF monOf))).map (fun b =>
      (b.coef muF monOf : ℝ) * umon (b.mon muF monOf) u *
      b.val (fun i => (i.2.opd w₀ Pb.S).eval Pb.S) (fun t => ((HL t).opd P0).eval P0.S) φ) |>.sum| ≤
      D := by
  simp only [dropCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hr, hD⟩ := hchk
  rw [sum_map_filter_ite]
  have hmem : ∀ b ∈ bterms Fl Hl, b.i ∈ Fl ∧ b.e ∈ Hl := by
    intro b hb'
    simp only [bterms, List.mem_flatMap, List.mem_map] at hb'
    obtain ⟨a, -, i, hi, e, he, kind, -, sh, -, rfl⟩ := hb'
    exact ⟨hi, he⟩
  refine (abs_list_sum_le _ _ (fun b => (dropT Pb HL nH r L b : ℝ)) fun b hb' =>
    abs_dropTerm_le hr L w₀ hS0 hb0 b (hF _ (hmem b hb').1) (hH _ (hmem b hb').2) hu φ).trans ?_
  rw [← cast_sum_mapQ, ← dropSum_eq]
  exact_mod_cast hD

end KAM.EffectiveStability.Tube

end
