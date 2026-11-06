/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.Tube.Engine.Input

/-!
# Sparse literal models (T2-CONF, N7)

A sparse model (`SpD`): half-width `C`, parity, scale `q` and a short list of entries
`((c, r), m)` (box coordinates `c, r ≤ 2C`, integer mantissa `m`; mode `(c - C, r - C)`). Used for
the pruned literal observables, whose `u`-coefficients have a few dozen modes each.

* `SpD.list`: the dense slot list on the square layout (duplicates add); `SpD.Z`: its packed value
  in the kernel (one shift and one addition per entry); `SpD.opd`.
* `SpD.wf` (well formed, from `SpD.ok`: every entry in the box), `SpD.l1_le` (`ℓ¹ ≤ Σ |m|`),
  `SpD.mx` (slots bounded by `Σ |m|`).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

namespace SpD

/-- The slot index of a box position on the layout of stride `S`. -/
def idx (S : ℕ) (e : (ℕ × ℕ) × ℤ) : ℕ := e.1.1 + S * e.1.2

/-- The dense slot list. -/
def list (S : ℕ) (d : SpD) : List ℤ :=
  (List.range (Layout.len d.C S)).map fun i => ((d.es.filter fun e => idx S e == i).map (·.2)).sum

/-- The packed value (kernel). -/
def Z (w S : ℕ) (d : SpD) : ℤ := (d.es.map fun e => e.2 * 2 ^ (w * idx S e)).sum

/-- The operand. -/
def opd (w S : ℕ) (d : SpD) : Opd := ⟨d.C, d.par, d.q, d.list S, d.Z w S⟩

/-- Every entry lies in the box (decidable). -/
def ok (S : ℕ) (d : SpD) : Bool :=
  decide (2 * d.C + 1 ≤ S) && d.es.all fun e => decide (e.1.1 ≤ 2 * d.C) && decide (e.1.2 ≤ 2 * d.C)

/-- `Σ |m|`. -/
def l1E (d : SpD) : ℕ := (d.es.map fun e => e.2.natAbs).sum

theorem getD_list (S : ℕ) (d : SpD) (i : ℕ) :
    (d.list S).getD i 0 =
      if i < Layout.len d.C S then ((d.es.filter fun e => idx S e == i).map (·.2)).sum else 0 := by
  unfold list
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]; rfl

theorem idx_lt {S : ℕ} {d : SpD} (h : d.ok S = true) {e : (ℕ × ℕ) × ℤ} (he : e ∈ d.es) :
    idx S e < Layout.len d.C S ∧ (idx S e) % S = e.1.1 := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have he' := h.2 e he
  have hS := h.1
  refine ⟨?_, (mod_div_of_lt (by omega)).1⟩
  unfold idx Layout.len
  have : S * e.1.2 ≤ S * (2 * d.C) := Nat.mul_le_mul_left S he'.2
  nlinarith

/-- Fiber sums: summing per slot, then over slots, is summing over the entries. -/
theorem fiber_sum {M : Type*} [AddCommMonoid M] {S n : ℕ} (g : (ℕ × ℕ) × ℤ → M) (h : ℕ → M → M)
    (hadd : ∀ i x y, h i (x + y) = h i x + h i y) (h0 : ∀ i, h i 0 = 0) :
    ∀ es : List ((ℕ × ℕ) × ℤ), (∀ e ∈ es, idx S e < n) →
      ∑ i ∈ range n, h i ((es.filter fun e => idx S e == i).map g).sum =
        (es.map fun e => h (idx S e) (g e)).sum
  | [], _ => by simp [h0]
  | e :: es, he => by
    have ih := fiber_sum g h hadd h0 es fun x hx => he x (by simp [hx])
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    rw [← ih, ← sum_erase_add _ _ (mem_range.mpr (he e (by simp))),
      ← sum_erase_add _ _ (mem_range.mpr (he e (by simp)))]
    have hrest : ∀ i ∈ (range n).erase (idx S e),
        h i ((if (idx S e == i) = true then e :: es.filter (fun e => idx S e == i)
          else es.filter (fun e => idx S e == i)).map g).sum =
        h i ((es.filter fun e => idx S e == i).map g).sum := fun i hi => by
      rw [ite_eq_right (by simpa using (Finset.ne_of_mem_erase hi).symm)]
    rw [sum_congr rfl hrest, ite_eq_left (by simp), List.map_cons, List.sum_cons, hadd]
    abel

theorem length_list (S : ℕ) (d : SpD) : (d.list S).length = Layout.len d.C S := by simp [list]

theorem packSum_list {w S : ℕ} {d : SpD} (h : d.ok S = true) : packSum w (d.list S) = d.Z w S := by
  rw [packSum_eq_sum, length_list,
    sum_congr rfl (fun i hi => by rw [getD_list, ite_eq_left (mem_range.mp hi)]),
    fiber_sum (S := S) (n := Layout.len d.C S) (fun e => e.2)
      (fun i x => x * (2 ^ w) ^ i) (fun i x y => add_mul _ _ _) (fun i => zero_mul _) d.es
      (fun e he => (idx_lt h he).1), Z]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  rw [← pow_mul]

theorem colsOk_list {S : ℕ} {d : SpD} (h : d.ok S = true) : colsOk d.C S (d.list S) = true := by
  apply colsOk_of_getD
  intro i hi
  simp only [zero_add]
  rw [getD_list] at hi
  split_ifs at hi with hl
  · obtain ⟨x, hx⟩ : ∃ x ∈ d.es.filter fun e => idx S e == i, True := by
      by_contra hn
      push Not at hn
      apply hi
      rw [List.eq_nil_iff_forall_not_mem.mpr fun x hx => hn x hx]; rfl
    have hm := List.mem_filter.mp hx.1
    have hi' := (beq_iff_eq.mp hm.2).symm
    rw [hi', (idx_lt h hm.1).2]
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact (h.2 x hm.1).1
  · exact absurd rfl hi

theorem abs_listSum_le' (l : List ℤ) : |l.sum| ≤ (l.map fun x => |x|).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.map_cons]; exact (abs_add_le _ _).trans (by linarith)

theorem l1_list_le {S : ℕ} {d : SpD} (h : d.ok S = true) : l1 (d.list S) ≤ d.l1E := by
  rw [l1_eq, length_list]
  calc ∑ i ∈ range (Layout.len d.C S), |(d.list S).getD i 0|
      ≤ ∑ i ∈ range (Layout.len d.C S), ((d.es.filter fun e => idx S e == i).map
          fun e => (e.2.natAbs : ℤ)).sum := by
        refine sum_le_sum fun i hi => ?_
        rw [getD_list, ite_eq_left (mem_range.mp hi)]
        refine (abs_listSum_le' _).trans (le_of_eq ?_)
        rw [List.map_map]
        refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
        simp only [Function.comp_apply, Int.natCast_natAbs]
    _ = (d.es.map fun e => (e.2.natAbs : ℤ)).sum := by
        have := fiber_sum (S := S) (n := Layout.len d.C S) (fun e => (e.2.natAbs : ℤ))
          (fun _ x => x) (fun _ _ _ => rfl) (fun _ => rfl) d.es (fun e he => (idx_lt h he).1)
        exact this
    _ = d.l1E := by rw [l1E, Nat.cast_list_sum, List.map_map]; rfl

theorem wf {w S : ℕ} {d : SpD} (h : d.ok S = true) : (d.opd w S).WF w S :=
  ⟨packSum_list h, colsOk_list h, (length_list S d).le⟩

/-- **The value of a sparse model** is the sum over its entries. -/
theorem eval_eq {w S : ℕ} {d : SpD} (h : d.ok S = true) (φ : Fin 2 → ℝ) :
    (d.opd w S).eval S φ = (d.q : ℝ) * (d.es.map fun e =>
      (e.2 : ℝ) * trig d.par (kdot (((e.1.1 : ℕ) : ℤ) - d.C, ((e.1.2 : ℕ) : ℤ) - d.C) φ)).sum := by
  simp only [Opd.eval, opd]
  congr 1
  rw [evalK, length_list,
    sum_congr rfl (fun i hi => by rw [getD_list, ite_eq_left (mem_range.mp hi), Int.cast_list_sum,
      List.map_map])]
  simp only [Function.comp_def]
  rw [fiber_sum (S := S) (n := Layout.len d.C S) (fun e => (e.2 : ℝ))
    (fun i x => x * trig d.par (kdot (Layout.key d.C S i) φ)) (fun i x y => add_mul _ _ _)
    (fun i => zero_mul _) d.es (fun e he => (idx_lt h he).1)]
  · refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    have hok := h
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
    have he' := hok.2 e he
    have hS := hok.1
    have e1 := mod_div_of_lt (S := S) (c := e.1.1) (r := e.1.2) (by omega)
    simp only [Layout.key, idx, e1.1, e1.2]

end SpD

end KAM.EffectiveStability.Tube

end
