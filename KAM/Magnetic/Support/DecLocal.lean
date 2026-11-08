/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.Support.DecSplit

/-!
# Decoding a packed product in local slot pieces (MAG-SEAL)

`pieceAt adv.targetEntry adv.combined a b` (`DecSplit.lean`) reads the slots `[a, b)` of the whole
overlap-added target `adv.combined`; evaluated in the kernel it walks the overlap-add of every
window before `a`, so for a product of `135 000` slots even a short final piece exceeds the
per-theorem memory budget. This module rewrites a piece through the windows that reach it:

* `drop_packAddZ`, `take_packAddZ`, `packAddZ_assoc`: zero-extended slotwise addition commutes
  with `drop` and `take` and is associative;
* `drop_packOverlapAdd`: past the block `s`, the overlap-add is the tail of window `s` added to
  the overlap-add of the later windows (every window at most two blocks long);
* `take_packOverlapAdd_take`: the first `m ≤ k · L` slots need only the first `k` windows;
* `localPiece adv s t a b`: the piece `[a, b)` from the windows `s - 1, …, t - 1` (for
  `s · L ≤ a ≤ b ≤ t · L`), and `pieceAt_eq_localPiece`: it equals `pieceAt`;
* `dyadicTerms_pieceAt_of_local`, `dyadicTerms_pieceAt_map_of_local`: a piece's decode from the
  decode of its local form (what the generated decode pieces prove in the kernel).

Nothing here is assumed about the data: the window lengths are a hypothesis.
-/

@[expose] public section

namespace KAM.Magnetic.Data

open KAM.Certificate CertArith

theorem packAddZ_nil_right : ∀ a : List ℤ, packAddZ a [] = a
  | [] => rfl
  | _ :: _ => rfl

theorem drop_packAddZ : ∀ (k : ℕ) (a b : List ℤ),
    (packAddZ a b).drop k = packAddZ (a.drop k) (b.drop k)
  | 0, _, _ => rfl
  | k + 1, [], b => by simp [packAddZ]
  | k + 1, _ :: _, [] => by simp [packAddZ, packAddZ_nil_right]
  | k + 1, _ :: xs, _ :: ys => by simp [packAddZ, drop_packAddZ k xs ys]

theorem take_packAddZ : ∀ (k : ℕ) (a b : List ℤ),
    (packAddZ a b).take k = packAddZ (a.take k) (b.take k)
  | 0, _, _ => rfl
  | k + 1, [], b => by simp [packAddZ]
  | k + 1, _ :: _, [] => by simp [packAddZ, packAddZ_nil_right]
  | k + 1, _ :: xs, _ :: ys => by simp [packAddZ, take_packAddZ k xs ys]

theorem packAddZ_assoc : ∀ a b c : List ℤ,
    packAddZ (packAddZ a b) c = packAddZ a (packAddZ b c)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => by simp [packAddZ, packAddZ_nil_right]
  | x :: xs, y :: ys, z :: zs => by simp [packAddZ, packAddZ_assoc xs ys zs, add_assoc]

theorem drop_packOverlapAdd_cons (L : ℕ) (x : List ℤ) (xs : List (List ℤ)) :
    (packOverlapAdd L (x :: xs)).drop L = packAddZ (x.drop L) (packOverlapAdd L xs) := by
  rw [packOverlapAdd, drop_packAddZ, List.drop_left' (List.length_replicate ..)]

/-- Past block `s` (offset `(s + 1) · L`), the overlap-add is the tail of window `s` plus the
overlap-add of the windows after it, when every window has at most `2 L` slots. -/
theorem drop_packOverlapAdd (L : ℕ) : ∀ (ws : List (List ℤ)) (s : ℕ),
    (∀ w ∈ ws, w.length ≤ 2 * L) →
    (packOverlapAdd L ws).drop ((s + 1) * L) =
      packAddZ ((ws.getD s []).drop L) (packOverlapAdd L (ws.drop (s + 1)))
  | [], s, _ => by simp [packOverlapAdd, packAddZ]
  | x :: xs, s, hw => by
    rw [show (s + 1) * L = L + s * L by ring, ← List.drop_drop, drop_packOverlapAdd_cons]
    cases s with
    | zero => simp
    | succ s =>
      have hx : (x.drop L).drop ((s + 1) * L) = [] := by
        apply List.drop_eq_nil_of_le
        have := hw x (List.mem_cons_self ..)
        simp only [List.length_drop]
        rw [Nat.succ_mul]
        omega
      rw [drop_packAddZ, hx,
        drop_packOverlapAdd L xs s fun w hw' => hw w (List.mem_cons_of_mem _ hw')]
      simp [packAddZ]

/-- The first `m ≤ k · L` slots of an overlap-add need only its first `k` windows. -/
theorem take_packOverlapAdd_take (L : ℕ) : ∀ (ws : List (List ℤ)) (k m : ℕ), m ≤ k * L →
    (packOverlapAdd L ws).take m = (packOverlapAdd L (ws.take k)).take m
  | [], _, _, _ => by simp
  | x :: xs, 0, m, hm => by simp [Nat.le_zero.1 (by simpa using hm)]
  | x :: xs, k + 1, m, hm => by
    rw [List.take_succ_cons, packOverlapAdd, packOverlapAdd, take_packAddZ, take_packAddZ,
      List.take_append, List.take_append, take_packOverlapAdd_take L xs k (m - _) (by
        simp only [List.length_replicate]
        rw [Nat.add_mul, one_mul] at hm
        omega)]

/-- The overlap-add carried into block `s`: the tail of window `s - 1` (nothing at `s = 0`). -/
def localCarry (adv : PackedAdvice) : ℕ → List ℤ
  | 0 => []
  | s + 1 => (adv.rounded.getD s []).drop adv.blockLen

/-- The overlap-add from block `s` on, through the windows `s, …, t - 1` only. -/
def localWindow (adv : PackedAdvice) (s t : ℕ) : List ℤ :=
  packAddZ (localCarry adv s) (packOverlapAdd adv.blockLen ((adv.rounded.drop s).take (t - s)))

/-- The slot piece `[a, b)` of the combined target from the windows `s - 1, …, t - 1`. -/
def localPiece (adv : PackedAdvice) (s t a b : ℕ) : List (CertKey × ℤ) :=
  ((List.range' a (b - a)).zip (packTakePad (b - a)
    ((localWindow adv s t).drop (a - s * adv.blockLen)))).filterMap adv.targetEntry

theorem drop_packOverlapAdd_local (adv : PackedAdvice)
    (hw : ∀ w ∈ adv.rounded, w.length ≤ 2 * adv.blockLen) (s : ℕ) :
    (packOverlapAdd adv.blockLen adv.rounded).drop (s * adv.blockLen) =
      packAddZ (localCarry adv s) (packOverlapAdd adv.blockLen (adv.rounded.drop s)) := by
  cases s with
  | zero => simp [localCarry, packAddZ]
  | succ s => rw [drop_packOverlapAdd _ _ _ hw]; rfl

theorem packTakePad_congr {m : ℕ} {l l' : List ℤ} (h : l.take m = l'.take m) :
    packTakePad m l = packTakePad m l' := by
  rw [packTakePad_eq, packTakePad_eq, h]

theorem take_drop_combined (adv : PackedAdvice) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ adv.prodLen) :
    (adv.combined.drop a).take (b - a) =
      packTakePad (b - a) ((packOverlapAdd adv.blockLen adv.rounded).drop a) := by
  set O := packOverlapAdd adv.blockLen adv.rounded
  have hc : adv.combined = (O ++ List.replicate adv.prodLen 0).take adv.prodLen := rfl
  rw [hc, List.drop_take, List.take_take, show min (b - a) (adv.prodLen - a) = b - a by omega,
    List.drop_append, List.drop_replicate, packTakePad_eq, List.take_append]
  congr 1
  have hlen : ((List.drop a O).take (b - a)).length = min (b - a) (O.length - a) := by simp
  rw [List.take_replicate, hlen]
  simp only [List.length_drop] at *
  congr 1
  omega

/-- **Local pieces.** For `s · L ≤ a ≤ b ≤ t · L` (`L = blockLen`) and `b ≤ prodLen`, with every
window at most `2 L` slots, the piece `[a, b)` of the combined target is computed from the
windows `s - 1, …, t - 1` alone. -/
theorem pieceAt_eq_localPiece (adv : PackedAdvice)
    (hw : ∀ w ∈ adv.rounded, w.length ≤ 2 * adv.blockLen) {s t a b : ℕ}
    (hsa : s * adv.blockLen ≤ a) (hab : a ≤ b) (hbt : b ≤ t * adv.blockLen) (hb : b ≤ adv.prodLen) :
    pieceAt adv.targetEntry adv.combined a b = localPiece adv s t a b := by
  unfold pieceAt localPiece
  congr 2
  rw [take_drop_combined adv hab hb]
  apply packTakePad_congr
  have hd : a = s * adv.blockLen + (a - s * adv.blockLen) := by omega
  conv_lhs => rw [hd, ← List.drop_drop, drop_packOverlapAdd_local adv hw s]
  unfold localWindow
  rw [List.take_drop, List.take_drop, take_packAddZ, take_packAddZ,
    take_packOverlapAdd_take _ _ (t - s) _ (by
      have : (t - s) * adv.blockLen = t * adv.blockLen - s * adv.blockLen := Nat.sub_mul ..
      omega)]
  rw [show b - (s * adv.blockLen + (a - s * adv.blockLen)) = b - a by omega]

section Decode

variable {α : Type} [CertArith α]

/-- The decode of a piece from the decode of its local form (`pieceAt_eq_localPiece`). -/
theorem dyadicTerms_pieceAt_of_local (P2 sc : ℕ) (place : α → CC α) (adv : PackedAdvice)
    (hw : ∀ w ∈ adv.rounded, w.length ≤ 2 * adv.blockLen) {s t a b : ℕ}
    (hsa : s * adv.blockLen ≤ a) (hab : a ≤ b) (hbt : b ≤ t * adv.blockLen) (hb : b ≤ adv.prodLen)
    {X : List (CertKey × CC α)} (h : dyadicTerms P2 sc place (localPiece adv s t a b) = some X) :
    dyadicTerms P2 sc place (pieceAt adv.targetEntry adv.combined a b) = some X := by
  rw [pieceAt_eq_localPiece adv hw hsa hab hbt hb]
  exact h

/-- The same for a termwise-transformed piece (the negated `ii` part). -/
theorem dyadicTerms_pieceAt_map_of_local (P2 sc : ℕ) (place : α → CC α) (adv : PackedAdvice)
    (g : CertKey × ℤ → CertKey × ℤ)
    (hw : ∀ w ∈ adv.rounded, w.length ≤ 2 * adv.blockLen) {s t a b : ℕ}
    (hsa : s * adv.blockLen ≤ a) (hab : a ≤ b) (hbt : b ≤ t * adv.blockLen) (hb : b ≤ adv.prodLen)
    {X : List (CertKey × CC α)}
    (h : dyadicTerms P2 sc place ((localPiece adv s t a b).map g) = some X) :
    dyadicTerms P2 sc place ((pieceAt adv.targetEntry adv.combined a b).map g) = some X := by
  rw [pieceAt_eq_localPiece adv hw hsa hab hbt hb]
  exact h

end Decode

end KAM.Magnetic.Data
