/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Bracket

/-!
# A kept coefficient in chunks (T2-CONF, N7)

The kernel's memory grows with the number of operands of one declaration, so a kept coefficient
with many terms is checked in chunks of `m` consecutive terms of `brList` (`brCheckC`, one
declaration each); each chunk is an exact sum, and the coefficient is bounded by the sum of the
chunk bounds (`brChunks_sound`, `brChunksAll_sound`). Splitting into chunks of about 100 terms
loses a factor 2–3 of the cancellation only.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- Chunk `k` (of length `m`) of a list. -/
def chunk {α : Type*} (l : List α) (m k : ℕ) : List α := (l.drop (m * k)).take m

theorem chunk_succ {α : Type*} (l : List α) (m k : ℕ) :
    chunk l m (k + 1) = chunk (l.drop m) m k := by
  unfold chunk
  rw [List.drop_drop, Nat.mul_succ, Nat.add_comm]

theorem sum_chunks {α : Type*} (f : α → ℝ) (m : ℕ) :
    ∀ (n : ℕ) (l : List α), l.length ≤ m * n →
      (l.map f).sum = ((List.range n).map fun k => ((chunk l m k).map f).sum).sum
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; simp
  | n + 1, l, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have hc0 : chunk l m 0 = l.take m := by simp [chunk]
    rw [hc0]
    conv_lhs => rw [← List.take_append_drop m l]
    rw [List.map_append, List.sum_append,
      sum_chunks f m n (l.drop m) (by simp only [List.length_drop]; rw [Nat.mul_succ] at h; omega)]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
    simp only [Function.comp_apply, chunk_succ]

theorem abs_list_sum_le_map {α : Type*} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map fun x => |f x|).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem mem_of_mem_chunk {α : Type*} {l : List α} {m k : ℕ} {x : α} (h : x ∈ chunk l m k) : x ∈ l :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- **The kernel check of a chunk of a kept coefficient.** -/
def brCheckC (D : BrD) (Ca Cb : ℕ) (pp : Bool) (Fl : List ((ℕ × ℕ × ℕ) × SpD))
    (inH : ℕ × ℕ × ℕ → Bool) (p : ℕ × ℕ × ℕ) (m k : ℕ) (G : ℚ) : Bool :=
  brCheckL D Ca Cb pp (chunk (brList Fl muF inH p) m k) G

/-- **A kept coefficient from its chunks.** -/
theorem brChunks_sound {D : BrD} {Ca Cb : ℕ} {pp : Bool} {Fl : List ((ℕ × ℕ × ℕ) × SpD)}
    {Hl : List (ℕ × ℕ × ℕ)} {inH : ℕ × ℕ × ℕ → Bool} {P0 : Prm} {p : ℕ × ℕ × ℕ} {m n : ℕ}
    {G : ℕ → ℚ} (hlen : (brList Fl muF inH p).length ≤ m * n)
    (hall : ∀ k < n, brCheckC D Ca Cb pp Fl inH p m k (G k) = true)
    (hnd : Hl.Nodup) (hin : ∀ t, inH t = true ↔ t ∈ Hl) (hD : D.Ok Fl Hl)
    (w₀ : ℕ) (hS0 : P0.S = D.Pb.S) (hb0 : P0.b = D.Pb.b) (φ : Fin 2 → ℝ) :
    |(((bterms Fl Hl).filter fun b => decide (b.mon muF monOf = monOf p)).map
      (fun b => (b.coef muF monOf : ℝ) * b.val (fun i => (i.2.opd w₀ D.Pb.S).eval D.Pb.S)
        (fun t => ((D.HL t).opd P0).eval P0.S) φ)).sum| ≤
      (((List.range n).map G).sum : ℚ) := by
  rw [sum_filter_mon Fl muF hnd hin _ (fun b hb => by rw [hb]; simp),
    sum_chunks _ m n _ hlen, Rat.cast_list_sum, List.map_map]
  refine (abs_list_sum_le_map _ _).trans (List.sum_le_sum fun k hk => ?_)
  have hk' := List.mem_range.mp hk
  exact brl_sound (hall k hk') (fun b hb => ⟨(mem_brList (mem_of_mem_chunk hb)).1,
    (hin _).1 (mem_brList (mem_of_mem_chunk hb)).2⟩) hD w₀ hS0 hb0 φ

/-- The checks of one kept coefficient in `n` chunks of `m` terms against the chunk claims `Gc` and
the total `G`. -/
def BrPOk (D : BrD) (Ca Cb : ℕ) (pp : Bool) (Fl : List ((ℕ × ℕ × ℕ) × SpD))
    (inH : ℕ × ℕ × ℕ → Bool) (m n : ℕ) (Gc : ℕ → ℚ) (G : ℚ) (p : ℕ × ℕ × ℕ) : Prop :=
  (brList Fl muF inH p).length ≤ m * n ∧ (∀ k < n, brCheckC D Ca Cb pp Fl inH p m k (Gc k) = true) ∧
    ((List.range n).map Gc).sum ≤ G

/-- **All kept coefficients** from their chunk checks. -/
theorem brAllC_sound {D : BrD} {Ca Cb : ℕ} {pp : Bool} {Fl : List ((ℕ × ℕ × ℕ) × SpD)}
    {Hl : List (ℕ × ℕ × ℕ)} {inH : ℕ × ℕ × ℕ → Bool} {P0 : Prm} {L m : ℕ}
    {nOf : ℕ × ℕ × ℕ → ℕ} {Gc : ℕ × ℕ × ℕ → ℕ → ℚ} {G : ℕ × ℕ × ℕ → ℚ}
    (hall : ∀ t ∈ monsUpTo L, BrPOk D Ca Cb pp Fl inH m (nOf t) (Gc t) (G t) t)
    (hnd : Hl.Nodup) (hin : ∀ t, inH t = true ↔ t ∈ Hl) (hD : D.Ok Fl Hl)
    (w₀ : ℕ) (hS0 : P0.S = D.Pb.S) (hb0 : P0.b = D.Pb.b) (p : Fin 3 → ℕ) (hp : mdeg p ≤ L)
    (φ : Fin 2 → ℝ) :
    |(((bterms Fl Hl).filter fun b => decide (b.mon muF monOf = p)).map
      (fun b => (b.coef muF monOf : ℝ) * b.val (fun i => (i.2.opd w₀ D.Pb.S).eval D.Pb.S)
        (fun t => ((D.HL t).opd P0).eval P0.S) φ)).sum| ≤ G (p 0, p 1, p 2) := by
  have hmem : (p 0, p 1, p 2) ∈ monsUpTo L := by
    rw [mem_monsUpTo]
    simpa [mdeg, Fin.sum_univ_three] using hp
  obtain ⟨hlen, hk, hG⟩ := hall _ hmem
  have h := brChunks_sound hlen hk hnd hin hD w₀ hS0 hb0 φ
  rw [monOf_triple] at h
  exact h.trans (by exact_mod_cast hG)

end KAM.EffectiveStability.Tube

end
