/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Ops

/-!
# Chunked evaluation of the graph check's large term lists (lock-owned)

The models of the keyed graph checks (SOS option (a)) carry ~26k terms; one kernel run over such a
list costs ~0.3-0.4 MB per term, past the 10 GB budget. These lemmas split each list computation
into pieces, each one kernel run:

* `mergeErrTerms_append_sep`: the merge of two lists split at a key separation is the
  concatenation of the merges of the pieces;
* `mergeErrTerms_append_last`: a merge into a run `R ++ Rest` stays inside `R` when every key of
  the inserted list is below the last key of `R` (the rest is copied);
* `mergeErrTerms_single_lt`, `mergeErrTerms_single_stop`: a merge with a one-term list (the
  constant of `realLowerModelK`);
* `sumUp_flatten_of_maps`: a balanced sum over a chunked list from the chunks' mapped values.

Equations between computable terms; nothing is assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate CertArith

theorem keyCmp_swap_lt : ∀ {k l : CertKey}, keyCmp k l = .lt → keyCmp l k = .gt
  | [], [], h => by simp [keyCmp] at h
  | [], _ :: _, _ => by simp [keyCmp]
  | _ :: _, [], h => by simp [keyCmp] at h
  | a :: as, b :: bs, h => by
    simp only [keyCmp] at h ⊢
    by_cases hab : a < b
    · simp [hab, not_lt.2 (le_of_lt hab)]
    · by_cases hba : b < a
      · simp [hab, hba] at h
      · simp only [hab, hba, ite_false] at h ⊢
        exact keyCmp_swap_lt h

variable {α : Type} [CertArith α]

/-- Every key of `X` precedes every key of `Y`. -/
def KeySep (X Y : List (ErrTerm α)) : Prop := ∀ a ∈ X, ∀ b ∈ Y, keyCmp a.1 b.1 = .lt

theorem mergeErrTerms_nil_right : ∀ A : List (ErrTerm α), mergeErrTerms A [] = A
  | [] => rfl
  | _ :: _ => rfl

theorem mergeErrTerms_cons (x : ErrTerm α) (xs ys : List (ErrTerm α)) :
    mergeErrTerms (x :: xs) ys = mergeErrInsert x xs (mergeErrTerms xs) ys := rfl

/-- Merging into `B ++ C` where every key of `B` precedes every key of `A`: `B` is copied. -/
theorem mergeErrTerms_prefix_lt (A C : List (ErrTerm α)) :
    ∀ B : List (ErrTerm α), KeySep B A → mergeErrTerms A (B ++ C) = B ++ mergeErrTerms A C
  | [], _ => rfl
  | y :: B, h => by
    match A, h with
    | [], _ => simp [mergeErrTerms]
    | x :: xs, h =>
      have hyx : keyCmp x.1 y.1 = .gt := keyCmp_swap_lt (h y (by simp) x (by simp))
      have ih := mergeErrTerms_prefix_lt (x :: xs) C B (fun a ha b hb => h a (by simp [ha]) b hb)
      rw [List.cons_append, mergeErrTerms_cons]
      simp only [mergeErrInsert, hyx]
      rw [← mergeErrTerms_cons, ih, List.cons_append]

theorem mergeErrTerms_append_sep :
    ∀ (A1 A2 B1 B2 : List (ErrTerm α)), KeySep (A1 ++ B1) (A2 ++ B2) →
      mergeErrTerms (A1 ++ A2) (B1 ++ B2) = mergeErrTerms A1 B1 ++ mergeErrTerms A2 B2
  | [], A2, B1, B2, h => by
    simp only [List.nil_append, mergeErrTerms]
    exact mergeErrTerms_prefix_lt A2 B2 B1 (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))
  | x :: xs, A2, B1, B2, h => by
    have ih : ∀ B1, KeySep (xs ++ B1) (A2 ++ B2) →
        mergeErrTerms (xs ++ A2) (B1 ++ B2) = mergeErrTerms xs B1 ++ mergeErrTerms A2 B2 :=
      fun B1 h' => mergeErrTerms_append_sep xs A2 B1 B2 h'
    have hx : ∀ b ∈ A2 ++ B2, keyCmp x.1 b.1 = .lt := fun b hb => h x (by simp) b hb
    rw [List.cons_append, mergeErrTerms_cons, mergeErrTerms_cons]
    induction B1 with
    | nil =>
      simp only [List.nil_append]
      cases B2 with
      | nil =>
        simp only [mergeErrInsert, List.cons_append, mergeErrTerms_nil_right]
      | cons y ys =>
        have hxy : keyCmp x.1 y.1 = .lt := hx y (by simp)
        simp only [mergeErrInsert, hxy, List.cons_append]
        have := ih [] (fun a ha b hb => h a (by simp at ha ⊢; exact Or.inr ha) b hb)
        simpa [mergeErrTerms_nil_right] using this
    | cons y B1 ihB =>
      have hs : KeySep (xs ++ B1) (A2 ++ B2) :=
        fun a ha b hb => h a (by simp at ha ⊢; tauto) b hb
      have hs' : KeySep (xs ++ y :: B1) (A2 ++ B2) :=
        fun a ha b hb => h a (by simp at ha ⊢; tauto) b hb
      rw [List.cons_append]
      cases hc : keyCmp x.1 y.1 with
      | lt =>
        simp only [mergeErrInsert, hc, List.cons_append]
        rw [← List.cons_append, ih (y :: B1) hs']
      | gt =>
        simp only [mergeErrInsert, hc, List.cons_append]
        rw [ihB (fun a ha b hb => h a (by simp at ha ⊢; tauto) b hb)]
      | eq =>
        simp only [mergeErrInsert, hc, List.cons_append]
        rw [ih B1 hs]

/-- A merge into `R ++ Rest`, where `R` ends with `z` and every key of `A` is below `z`'s, stays
inside `R`: the rest is copied. -/
theorem mergeErrTerms_append_last (Rest : List (ErrTerm α)) (z : ErrTerm α) :
    ∀ (A R : List (ErrTerm α)), (∀ a ∈ A, keyCmp a.1 z.1 = .lt) →
      mergeErrTerms A (R ++ z :: Rest) = mergeErrTerms A (R ++ [z]) ++ Rest
  | [], R, _ => by simp [mergeErrTerms]
  | x :: xs, R, h => by
    have ih : ∀ R, mergeErrTerms xs (R ++ z :: Rest) = mergeErrTerms xs (R ++ [z]) ++ Rest :=
      fun R => mergeErrTerms_append_last Rest z xs R (fun a ha => h a (by simp [ha]))
    rw [mergeErrTerms_cons, mergeErrTerms_cons]
    induction R with
    | nil =>
      have hxz : keyCmp x.1 z.1 = .lt := h x (by simp)
      simp only [List.nil_append, mergeErrInsert, hxz, List.cons_append]
      rw [← List.nil_append (z :: Rest), ih [], List.nil_append]
    | cons y R ihR =>
      simp only [List.cons_append]
      cases hc : keyCmp x.1 y.1 with
      | lt =>
        simp only [mergeErrInsert, hc, List.cons_append]
        rw [← List.cons_append, ih (y :: R)]
        rfl
      | gt =>
        simp only [mergeErrInsert, hc, List.cons_append]
        rw [ihR]
      | eq =>
        simp only [mergeErrInsert, hc, List.cons_append]
        rw [ih R]

/-- A merge with a one-term list, past a prefix whose keys precede the term's: the prefix is
copied. -/
theorem mergeErrTerms_single_lt (k : ErrTerm α) (Q : List (ErrTerm α)) :
    ∀ P : List (ErrTerm α), (∀ a ∈ P, keyCmp a.1 k.1 = .lt) →
      mergeErrTerms (P ++ Q) [k] = P ++ mergeErrTerms Q [k]
  | [], _ => rfl
  | x :: xs, h => by
    have hx : keyCmp x.1 k.1 = .lt := h x (by simp)
    rw [List.cons_append, mergeErrTerms_cons]
    simp only [mergeErrInsert, hx, List.cons_append]
    rw [mergeErrTerms_single_lt k Q xs (fun a ha => h a (by simp [ha]))]

/-- A merge with a one-term list at a term whose key does not precede it: the rest is copied. -/
theorem mergeErrTerms_single_stop (k x : ErrTerm α) (R : List (ErrTerm α))
    (hx : keyCmp x.1 k.1 ≠ .lt) : mergeErrTerms (x :: R) [k] = mergeErrTerms [x] [k] ++ R := by
  rw [mergeErrTerms_cons, mergeErrTerms_cons]
  cases hc : keyCmp x.1 k.1 with
  | lt => exact absurd hc hx
  | gt => simp [mergeErrInsert, hc]
  | eq => simp [mergeErrInsert, hc, mergeErrTerms, mergeErrTerms_nil_right]

/-- A balanced sum over a chunked list, from the chunks' mapped values. -/
theorem sumUp_flatten_of_maps {β : Type} (g : β → α) :
    ∀ (Ls : List (List β)) (Vs : List (List α)), List.Forall₂ (fun l v => l.map g = v) Ls Vs →
      sumUp g Ls.flatten = (pairRounds 64 Vs.flatten).foldr upAdd (ofInt 0)
  | Ls, Vs, h => by
    unfold sumUp
    congr 2
    induction h with
    | nil => rfl
    | cons hlv _ ih => simp only [List.flatten_cons, List.map_append, hlv, ih]

/-! ### Key order -/

theorem keyCmp_lt_trans : ∀ {k l m : CertKey}, keyCmp k l = .lt → keyCmp l m ≠ .gt →
    keyCmp k m = .lt
  | [], [], _, h, _ => by simp [keyCmp] at h
  | [], _ :: _, [], _, h' => by simp [keyCmp] at h'
  | [], _ :: _, _ :: _, _, _ => by simp [keyCmp]
  | _ :: _, [], _, h, _ => by simp [keyCmp] at h
  | _ :: _, _ :: _, [], _, h' => by simp [keyCmp] at h'
  | a :: as, b :: bs, c :: cs, h, h' => by
    simp only [keyCmp] at h h' ⊢
    by_cases hab : a < b
    · by_cases hbc : b < c
      · simp [show a < c by omega]
      · by_cases hcb : c < b
        · simp [hbc, hcb] at h'
        · simp [show a < c by omega]
    · by_cases hba : b < a
      · simp [hab, hba] at h
      · have e : a = b := by omega
        subst e
        simp only [hab, hba, ite_false] at h
        by_cases hac : a < c
        · simp [hac]
        · by_cases hca : c < a
          · simp [hac, hca] at h'
          · simp only [hac, hca, ite_false] at h' ⊢
            exact keyCmp_lt_trans h h'

theorem keyCmp_swap_gt : ∀ {k l : CertKey}, keyCmp k l = .gt → keyCmp l k = .lt
  | [], [], h => by simp [keyCmp] at h
  | [], _ :: _, h => by simp [keyCmp] at h
  | _ :: _, [], _ => by simp [keyCmp]
  | a :: as, b :: bs, h => by
    simp only [keyCmp] at h ⊢
    by_cases hab : a < b
    · simp [hab] at h
    · by_cases hba : b < a
      · simp [hba]
      · simp only [hab, hba, ite_false] at h ⊢
        exact keyCmp_swap_gt h

/-- A threshold key `t` separates `X` (keys below `t`) from `Y` (keys not below `t`). -/
theorem keySep_of_threshold (X Y : List (ErrTerm α)) (t : CertKey)
    (hX : (X.all fun a => keyCmp a.1 t == .lt) = true)
    (hY : (Y.all fun b => keyCmp b.1 t != .lt) = true) : KeySep X Y := by
  intro a ha b hb
  have h1 : keyCmp a.1 t = .lt := by simpa using List.all_eq_true.mp hX a ha
  have h2 : keyCmp b.1 t ≠ .lt := by simpa using List.all_eq_true.mp hY b hb
  refine keyCmp_lt_trans h1 ?_
  intro h3
  exact h2 (keyCmp_swap_gt h3)

/-! ### Forms used by the generated modules -/

/-- `mergeErrTerms_append_last` with the run's last term read off by `getLast?`. -/
theorem mergeErrTerms_append_run (A R Rest : List (ErrTerm α)) (z : ErrTerm α)
    (hz : R.getLast? = some z) (h : (A.all fun a => keyCmp a.1 z.1 == .lt) = true) :
    mergeErrTerms A (R ++ Rest) = mergeErrTerms A R ++ Rest := by
  have hR : R = R.dropLast ++ [z] := by
    rw [List.getLast?_eq_some_iff] at hz
    obtain ⟨ys, hys⟩ := hz
    subst hys
    simp
  have h' : ∀ a ∈ A, keyCmp a.1 z.1 = .lt := fun a ha => by
    simpa using List.all_eq_true.mp h a ha
  rw [hR, List.append_assoc, List.singleton_append, mergeErrTerms_append_last Rest z A _ h']

/-- `mergeErrTerms_append_run` with the run's last key (decidable) in place of its last term. -/
theorem mergeErrTerms_append_runK (A R Rest : List (ErrTerm α)) (zk : CertKey)
    (hz : (R.getLast?.map Prod.fst) = some zk) (h : (A.all fun a => keyCmp a.1 zk == .lt) = true) :
    mergeErrTerms A (R ++ Rest) = mergeErrTerms A R ++ Rest := by
  cases hr : R.getLast? with
  | none => simp [hr] at hz
  | some z =>
    have hzk : z.1 = zk := by simpa [hr] using hz
    subst hzk
    exact mergeErrTerms_append_run A R Rest z hr h

/-- `mergeErrTerms_single_stop` at the head of a list (`take 1`/`drop 1`). -/
theorem mergeErrTerms_single_head (k : ErrTerm α) (Q : List (ErrTerm α))
    (h : (Q.head?.all fun x => keyCmp x.1 k.1 != .lt) = true) (hne : Q.isEmpty = false) :
    mergeErrTerms Q [k] = mergeErrTerms (Q.take 1) [k] ++ Q.drop 1 := by
  match Q, h, hne with
  | x :: R, h, _ =>
    have hx : keyCmp x.1 k.1 ≠ .lt := by simpa using h
    simpa using mergeErrTerms_single_stop k x R hx

/-- `mergeErrTerms_single_lt` with its hypothesis as a Boolean check. -/
theorem mergeErrTerms_single_lt' (k : ErrTerm α) (P Q : List (ErrTerm α))
    (h : (P.all fun a => keyCmp a.1 k.1 == .lt) = true) :
    mergeErrTerms (P ++ Q) [k] = P ++ mergeErrTerms Q [k] :=
  mergeErrTerms_single_lt k Q P fun a ha => by simpa using List.all_eq_true.mp h a ha

/-- Truncation keeps every term of a list whose key degrees are at most the cutoff. -/
theorem truncPoly_of_all (c : ℕ) (L : List (ErrTerm α))
    (h : (L.all fun t => truncKeep c t) = true) :
    truncPoly c L = ⟨L.map fun t => (t.1, t.2.1)⟩ := by
  simp only [truncPoly, List.filter_eq_self.2 (fun t ht => List.all_eq_true.mp h t ht)]

theorem map_truncErr_of_all (c : ℕ) (L : List (ErrTerm α))
    (h : (L.all fun t => truncKeep c t) = true) : L.map (truncErr c) = L := by
  conv_rhs => rw [← List.map_id L]
  apply List.map_congr_left
  intro t ht
  simp [truncErr, List.all_eq_true.mp h t ht]

/-- A Boolean check over a chunked list, from the chunks' checks. -/
theorem all_flatten_of {β : Type} (p : β → Bool) :
    ∀ Ls : List (List β), (Ls.all fun l => l.all p) = true → (Ls.flatten.all p) = true := by
  intro Ls h
  simp only [List.all_flatten, h]

theorem rowItems_append (s : CertKey × CC α) (A B : List (CertKey × CC α)) :
    rowItems s (A ++ B) = rowItems s A ++ rowItems s B :=
  List.map_append

theorem toErrTerms_itemsPoly_map (X : List (CertKey × CC α)) :
    CertPoly.toErrTerms (itemsPoly (X.map fun t => (t.1, t.2, ofInt 0))) =
      X.map fun t => (t.1, t.2, ofInt 0) := by
  simp [CertPoly.toErrTerms, itemsPoly]

theorem itemsPoly_map_toErr (X : List (CertKey × CC α)) :
    itemsPoly (X.map fun t => (t.1, t.2, ofInt 0)) = ⟨X⟩ := by
  simp only [itemsPoly, List.map_map, Function.comp_def, Prod.mk.eta, List.map_id']

end KAM.SpinOrbit.Data.LockN65
