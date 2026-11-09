/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.MulPacked
public import KAM.Magnetic.Support.DecSplit

/-!
# The remainder bound of a packed product in slot ranges (MAG-SEAL)

`PackedAdvice.remainderBound` sums a natural-number term over every product slot, with the
largest slot degree `maxSlotDeg` (a maximum over every slot) in the exponents. For the largest
products one kernel evaluation of either is too costly (copied from
`KAM.SpinOrbit.Data.LockN65.RemSplit`; the magnetic product assemblies are consumed with the
bound as a literal).
This module cuts both at slot boundaries:

* `packRangeMax_le_iff`, `packRangeMax_split`, `packRangeSum_split`: the range maximum and the
  range sum split at any point (any fuel);
* `packRangeMax_eq_cuts`, `packRangeSum_eq_cuts`: along a monotone list of cuts;
* `maxSlotDeg_eq_of_cuts`, `remainderBound_eq_of_cuts`: the two quantities from the values on
  the ranges (each range its own kernel theorem).

Nothing here is assumed about the data.
-/

@[expose] public section

namespace KAM.Magnetic.Data

open KAM.Certificate

/-- A natural number from its base-`2^256` digits, most significant first (long literals of the
generated data, one digit per source line). -/
def natOfChunks (cs : List ℕ) : ℕ :=
  cs.foldl (fun acc c => acc * 2 ^ 256 + c) 0

theorem foldr_max_le_iff (l : List ℕ) (m : ℕ) : l.foldr max 0 ≤ m ↔ ∀ x ∈ l, x ≤ m := by
  induction l with
  | nil => simp
  | cons y l ih => simp [List.foldr_cons, max_le_iff, ih]

theorem packRangeMax_le_iff (f : ℕ → ℕ) (fuel : ℕ) : ∀ base size m : ℕ,
    packRangeMax f fuel base size ≤ m ↔ ∀ q < size, f (base + q) ≤ m := by
  induction fuel with
  | zero => intro base size m; simp [packRangeMax, foldr_max_le_iff]
  | succ fuel ih =>
    intro base size m
    rw [packRangeMax]
    split_ifs with hs
    · simp [foldr_max_le_iff]
    · rw [max_le_iff, ih, ih]
      constructor
      · rintro ⟨h1, h2⟩ q hq
        by_cases hq2 : q < size / 2
        · exact h1 q hq2
        · have := h2 (q - size / 2) (by omega)
          rwa [show base + size / 2 + (q - size / 2) = base + q by omega] at this
      · intro h
        refine ⟨fun q hq => h q (by omega), fun q hq => ?_⟩
        have := h (size / 2 + q) (by omega)
        rwa [show base + (size / 2 + q) = base + size / 2 + q by omega] at this

theorem packRangeMax_split (f : ℕ → ℕ) (F F₁ F₂ base a b : ℕ) :
    packRangeMax f F base (a + b) =
      max (packRangeMax f F₁ base a) (packRangeMax f F₂ (base + a) b) := by
  have key : ∀ m, packRangeMax f F base (a + b) ≤ m ↔
      max (packRangeMax f F₁ base a) (packRangeMax f F₂ (base + a) b) ≤ m := by
    intro m
    rw [max_le_iff, packRangeMax_le_iff, packRangeMax_le_iff, packRangeMax_le_iff]
    constructor
    · intro h
      refine ⟨fun q hq => h q (by omega), fun q hq => ?_⟩
      have := h (a + q) (by omega)
      rwa [show base + (a + q) = base + a + q by omega] at this
    · rintro ⟨h1, h2⟩ q hq
      by_cases hqa : q < a
      · exact h1 q hqa
      · have := h2 (q - a) (by omega)
        rwa [show base + a + (q - a) = base + q by omega] at this
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

theorem packRangeSum_split (f : ℕ → ℕ) (F F₁ F₂ base a b : ℕ) :
    packRangeSum f F base (a + b) = packRangeSum f F₁ base a + packRangeSum f F₂ (base + a) b := by
  rw [packRangeSum_eq, packRangeSum_eq, packRangeSum_eq, Finset.sum_range_add]
  simp only [add_assoc]

theorem packRangeMax_zero_size (f : ℕ → ℕ) (F base : ℕ) : packRangeMax f F base 0 = 0 :=
  Nat.le_zero.1 ((packRangeMax_le_iff f F base 0 0).2 fun _ h => absurd h (Nat.not_lt_zero _))

theorem packRangeSum_zero_size (f : ℕ → ℕ) (F base : ℕ) : packRangeSum f F base 0 = 0 := by
  rw [packRangeSum_eq]
  simp

/-- The range maximum along the cuts `a :: rest` (each range with its own length as fuel). -/
theorem packRangeMax_eq_cuts (f : ℕ → ℕ) :
    ∀ (a : ℕ) (rest : List ℕ) (F : ℕ), monoFrom a rest = true →
      packRangeMax f F a ((a :: rest).getLast (List.cons_ne_nil _ _) - a) =
        ((cutPairs (a :: rest)).map fun p => packRangeMax f (p.2 - p.1) p.1 (p.2 - p.1)).foldr
          max 0
  | a, [], F, _ => by simp [cutPairs, packRangeMax_zero_size]
  | a, b :: rest, F, hch => by
    simp only [monoFrom, Bool.and_eq_true, decide_eq_true_eq] at hch
    have hb := le_getLast_of_monoFrom b rest hch.2
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    rw [show (b :: rest).getLast (List.cons_ne_nil _ _) - a =
        (b - a) + ((b :: rest).getLast (List.cons_ne_nil _ _) - b) by omega,
      packRangeMax_split f F (b - a) ((b :: rest).getLast (List.cons_ne_nil _ _) - b),
      show a + (b - a) = b by omega, packRangeMax_eq_cuts f b rest _ hch.2]
    simp [cutPairs]

/-- The range sum along the cuts `a :: rest`. -/
theorem packRangeSum_eq_cuts (f : ℕ → ℕ) :
    ∀ (a : ℕ) (rest : List ℕ) (F : ℕ), monoFrom a rest = true →
      packRangeSum f F a ((a :: rest).getLast (List.cons_ne_nil _ _) - a) =
        ((cutPairs (a :: rest)).map fun p => packRangeSum f (p.2 - p.1) p.1 (p.2 - p.1)).sum
  | a, [], F, _ => by simp [cutPairs, packRangeSum_zero_size]
  | a, b :: rest, F, hch => by
    simp only [monoFrom, Bool.and_eq_true, decide_eq_true_eq] at hch
    have hb := le_getLast_of_monoFrom b rest hch.2
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    rw [show (b :: rest).getLast (List.cons_ne_nil _ _) - a =
        (b - a) + ((b :: rest).getLast (List.cons_ne_nil _ _) - b) by omega,
      packRangeSum_split f F (b - a) ((b :: rest).getLast (List.cons_ne_nil _ _) - b),
      show a + (b - a) = b by omega, packRangeSum_eq_cuts f b rest _ hch.2]
    simp [cutPairs]

theorem sum_map_eq_of_forall₂ {g : ℕ × ℕ → ℕ} :
    ∀ {ps : List (ℕ × ℕ)} {Ns : List ℕ}, List.Forall₂ (fun p N => g p = N) ps Ns →
      (ps.map g).sum = Ns.sum
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    rw [List.map_cons, List.sum_cons, List.sum_cons, h, sum_map_eq_of_forall₂ hs]

theorem foldr_max_map_eq_of_forall₂ {g : ℕ × ℕ → ℕ} :
    ∀ {ps : List (ℕ × ℕ)} {Ms : List ℕ}, List.Forall₂ (fun p M => g p = M) ps Ms →
      (ps.map g).foldr max 0 = Ms.foldr max 0
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, h, foldr_max_map_eq_of_forall₂ hs]

/-- `maxSlotDeg` from the maxima of the slot degrees on the ranges along the cuts `0 :: rest`
(ending at `prodLen = n`). -/
theorem maxSlotDeg_eq_of_cuts (adv : PackedAdvice) (n : ℕ) (hn : adv.prodLen = n)
    (rest : List ℕ) (hch : monoFrom 0 rest = true)
    (hl : ((0 :: rest).getLast (List.cons_ne_nil _ _)) = n) {Ms : List ℕ}
    (h : List.Forall₂ (fun p M => packRangeMax adv.slotDeg (p.2 - p.1) p.1 (p.2 - p.1) = M)
      (cutPairs (0 :: rest)) Ms) :
    adv.maxSlotDeg = Ms.foldr max 0 := by
  unfold PackedAdvice.maxSlotDeg
  rw [hn, ← foldr_max_map_eq_of_forall₂ h, ← packRangeMax_eq_cuts adv.slotDeg 0 rest n hch, hl,
    Nat.sub_zero]

/-- `remainderBound` from the slot sums on the ranges along the cuts `0 :: rest` (ending at
`prodLen = n`), with the largest slot degree `M`. -/
theorem remainderBound_eq_of_cuts (adv : PackedAdvice) (W : CertWeight) (P2 n M : ℕ)
    (hn : adv.prodLen = n) (hM : adv.maxSlotDeg = M) (rest : List ℕ)
    (hch : monoFrom 0 rest = true) (hl : ((0 :: rest).getLast (List.cons_ne_nil _ _)) = n)
    {Ns : List ℕ}
    (h : List.Forall₂ (fun p N => packRangeSum (fun i => adv.slotErr i *
      W.w.num.toNat ^ adv.slotDeg i * W.w.den ^ (M - adv.slotDeg i)) (p.2 - p.1) p.1 (p.2 - p.1) =
        N)
      (cutPairs (0 :: rest)) Ns) :
    adv.remainderBound W P2 = ((Ns.sum : ℕ) : ℚ) / ((W.w.den ^ M * 2 ^ P2 : ℕ) : ℚ) := by
  unfold PackedAdvice.remainderBound
  rw [hM, hn, ← sum_map_eq_of_forall₂ h, ← packRangeSum_eq_cuts _ 0 rest n hch, hl, Nat.sub_zero]

end KAM.Magnetic.Data
