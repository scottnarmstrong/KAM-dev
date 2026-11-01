/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetLeaf

/-!
# A packed jet segment (`V2-PACKED.md` §12.5)

A segment runs consecutive slots of the jet program in the kernel, on packed nodes, from the nodes
of the slots it imports (the ledger). It exports nodes that are compared with ledger entries.
Every step is a `jAdd` or a `jMul` of two earlier slots, followed by an optional reduce in place;
a box-by-box product is reduced to the box at once (`jMul`). The steps carry only untrusted
numbers (the target scales): a bad choice fails closed.

`jSegOk_sound`: if the segment check passes and every imported node encloses its slot function
`θ ↦ p.val n (z θ) j`, then every exported node encloses its slot function. (The chain of segments
through the ledger, by induction on the slot, is the next step, §12.7 item 3.)

The slot semantics: `slpVal_add`, `slpVal_mul` (the value of an `add`/`mul` slot from the values of
its two earlier operands, `Slp.val_append`/`Slp.val_snoc_self`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-! ### Slot semantics -/

section Semantics

variable (n : ℕ) (p : Slp) (z : (Fin n → ℂ) × (Fin n → ℂ))

/-- The value of slot `i` is its operation on the values of the earlier slots. -/
theorem slpVal_eq_step {i : ℕ} (hi : i < p.ops.length) :
    p.val n z i = (p.ops[i]).step n z (Slp.vals n z (p.ops.take i)) := by
  have h1 : p.ops = (p.ops.take i ++ [p.ops[i]]) ++ p.ops.drop (i + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop]
  have key : (Slp.vals n z p.ops).getD i 0 =
      (Slp.vals n z (p.ops.take i ++ [p.ops[i]])).getD i 0 := by
    conv_lhs => rw [h1]
    exact Slp.val_append n z _ _ (by simp; omega)
  unfold Slp.val
  rw [key]
  have := Slp.val_snoc_self n z (p.ops.take i) p.ops[i]
  rwa [List.length_take, min_eq_left hi.le] at this

/-- The earlier slots read from the prefix. -/
theorem slpVals_take_getD {i a : ℕ} (hi : i ≤ p.ops.length) (ha : a < i) :
    (Slp.vals n z (p.ops.take i)).getD a 0 = p.val n z a := by
  unfold Slp.val
  conv_rhs => rw [← List.take_append_drop i p.ops]
  exact (Slp.val_append n z _ _ (by simp; omega)).symm

theorem slp_lt_of_getD {i : ℕ} {op : SlpOp} (h : p.ops.getD i (.const 0 0 0) = op)
    (hop : op ≠ .const 0 0 0) : i < p.ops.length := by
  by_contra hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  exact hop h.symm

theorem slpVal_add {i a b : ℕ} (h : p.ops.getD i (.const 0 0 0) = .add a b) (ha : a < i)
    (hb : b < i) : p.val n z i = p.val n z a + p.val n z b := by
  have hi := slp_lt_of_getD p h (by simp)
  rw [slpVal_eq_step n p z hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [Option.getD_some] at h
  rw [h]
  simp only [SlpOp.step]
  rw [slpVals_take_getD n p z hi.le ha, slpVals_take_getD n p z hi.le hb]

theorem slpVal_const {i : ℕ} {re im : ℚ} {deg : ℤ}
    (h : p.ops.getD i (.const 0 0 0) = .const re im deg) (hi : i < p.ops.length) :
    p.val n z i = slpConstVal re im deg := by
  rw [slpVal_eq_step n p z hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [Option.getD_some] at h
  rw [h]
  rfl

theorem slpVal_mul {i a b : ℕ} (h : p.ops.getD i (.const 0 0 0) = .mul a b) (ha : a < i)
    (hb : b < i) : p.val n z i = p.val n z a * p.val n z b := by
  have hi := slp_lt_of_getD p h (by simp)
  rw [slpVal_eq_step n p z hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [Option.getD_some] at h
  rw [h]
  simp only [SlpOp.step]
  rw [slpVals_take_getD n p z hi.le ha, slpVals_take_getD n p z hi.le hb]

end Semantics

/-! ### The segment -/

/-- One step: the slot, the target scale of a box-by-box product, and the target scale of a
reduce in place (`0`: none). -/
abbrev JStep := ℕ × ℕ × ℕ

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

/-- The node of slot `i` from the state; `ops` is the program from slot `base` on (read once per
segment, not from slot `0` at every step). -/
def jOp (ops : List SlpOp) (base : ℕ) (st : List (ℕ × JNode α)) (i eT : ℕ) : Option (JNode α) :=
  match ops.getD (i - base) (.const 0 0 0) with
  | .add a b =>
    if base ≤ i ∧ a < i ∧ b < i then
      match st.lookup a, st.lookup b with
      | some x, some y => jAdd n jb x y
      | _, _ => none
    else none
  | .mul a b =>
    if base ≤ i ∧ a < i ∧ b < i then
      match st.lookup a, st.lookup b with
      | some x, some y => jMul n W jb x y eT
      | _, _ => none
    else none
  | .const re im deg =>
    if base ≤ i ∧ i - base < ops.length then
      jLeaf W pe cfg jb true jb.aC (constModel n re im deg)
    else none
  | _ => none

/-- The optional reduce in place. -/
def jPost (nd : JNode α) (red : ℕ) : Option (JNode α) :=
  if red = 0 then some nd else jRed n W jb nd red

/-- **The run of a segment.** -/
def jRun (ops : List SlpOp) (base : ℕ) :
    List (ℕ × JNode α) → List JStep → Option (List (ℕ × JNode α))
  | st, [] => some st
  | st, (i, eT, red) :: rest =>
    match jOp n W pe cfg jb ops base st i eT with
    | some nd =>
      match jPost n W jb nd red with
      | some nd' => jRun ops base ((i, nd') :: st) rest
      | none => none
    | none => none

/-- An exported node against its ledger entry: the same packed value, layout, load and scale, a
radius and a norm bound below the entry's. -/
def jExportOk (nd m : JNode α) : Bool :=
  nd.u == m.u && nd.A == m.A && nd.e == m.e && nd.x.re == m.x.re && nd.x.im == m.x.im &&
    ble nd.r m.r && ble nd.nb m.nb

/-- **The segment check** of the steps from slot `start` on. -/
def jSegOk (p : Slp) (start : ℕ) (imports : List (ℕ × JNode α)) (steps : List JStep)
    (exports : List (ℕ × JNode α)) : Bool :=
  jBookOk n W jb &&
    match jRun n W pe cfg jb (p.ops.drop start) start imports steps with
    | some st =>
      exports.all fun m =>
        match st.lookup m.1 with
        | some nd => jExportOk nd m.2
        | none => false
    | none => false

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α} {jb : JBook}

theorem mem_of_lookup {β : Type} {st : List (ℕ × β)} {a : ℕ} {x : β}
    (h : st.lookup a = some x) : (a, x) ∈ st := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- The slot functions. -/
def slotFn (n : ℕ) (p : Slp) (z : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (j : ℕ) :
    (Fin n → ℂ) → ℂ := fun θ => p.val n (z θ) j

theorem getD_drop_sub {β : Type} (l : List β) {base i : ℕ} (h : base ≤ i) (d : β) :
    (l.drop base).getD (i - base) d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' h]

theorem jOp_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (hpe : checkPiEnclosure pe = true)
    (B : JBookFacts n W jb)
    (p : Slp) (z : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {st : List (ℕ × JNode α)}
    (hst : ∀ m ∈ st, JEnc n W jb m.2 (slotFn n p z m.1)) {i eT : ℕ} {nd : JNode α}
    {base : ℕ} (h : jOp n W pe cfg jb (p.ops.drop base) base st i eT = some nd) :
    JEnc n W jb nd (slotFn n p z i) := by
  unfold jOp at h
  split at h
  · rename_i a b hop
    split_ifs at h with hab
    rw [getD_drop_sub _ hab.1] at hop
    split at h
    · rename_i x y hx hy
      have := jAdd_sound B (hst _ (mem_of_lookup hx)) (hst _ (mem_of_lookup hy)) h
      exact PEnc.congr this fun θ _ => (slpVal_add n p (z θ) hop hab.2.1 hab.2.2).symm
    · cases h
  · rename_i a b hop
    split_ifs at h with hab
    rw [getD_drop_sub _ hab.1] at hop
    split at h
    · rename_i x y hx hy
      have := jMul_sound hW B (hst _ (mem_of_lookup hx)) (hst _ (mem_of_lookup hy)) h
      exact PEnc.congr this fun θ _ => (slpVal_mul n p (z θ) hop hab.2.1 hab.2.2).symm
    · cases h
  · rename_i re im deg hop
    split_ifs at h with hb
    rw [getD_drop_sub _ hb.1] at hop
    have hi : i < p.ops.length := by
      have := hb.2
      rw [List.length_drop] at this
      omega
    have := jLeaf_sound (cfg := cfg) hW hpe B (constModel_encloses n W.rho re im deg) h
    exact PEnc.congr this fun θ _ => (slpVal_const n p (z θ) hop hi).symm
  · cases h

theorem jRun_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (hpe : checkPiEnclosure pe = true)
    (B : JBookFacts n W jb)
    (p : Slp) (z : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (base : ℕ) :
    ∀ (steps : List JStep) (st st' : List (ℕ × JNode α)),
      (∀ m ∈ st, JEnc n W jb m.2 (slotFn n p z m.1)) →
      jRun n W pe cfg jb (p.ops.drop base) base st steps = some st' →
        ∀ m ∈ st', JEnc n W jb m.2 (slotFn n p z m.1)
  | [], st, st', hst, h => by
    simp only [jRun, Option.some.injEq] at h
    exact h ▸ hst
  | (i, eT, red) :: rest, st, st', hst, h => by
    simp only [jRun] at h
    split at h
    · rename_i nd hnd
      split at h
      · rename_i nd' hpost
        have h1 := jOp_sound hW hpe B p z hst hnd
        have h2 : JEnc n W jb nd' (slotFn n p z i) := by
          unfold jPost at hpost
          split_ifs at hpost
          · cases hpost; exact h1
          · exact jRed_sound hW B h1 hpost
        refine jRun_sound hW hpe B p z base rest _ st' (fun m hm => ?_) h
        rcases List.mem_cons.mp hm with rfl | hm
        · exact h2
        · exact hst m hm
      · cases h
    · cases h

/-- **Soundness of a packed jet segment**: from the imported nodes to the exported ones. -/
theorem jSegOk_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (p : Slp)
    (z : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {start : ℕ}
    {imports exports : List (ℕ × JNode α)} {steps : List JStep}
    (h : jSegOk n W pe cfg jb p start imports steps exports = true)
    (himp : ∀ m ∈ imports, JEnc n W jb m.2 (slotFn n p z m.1)) :
    ∀ m ∈ exports, JEnc n W jb m.2 (slotFn n p z m.1) := by
  unfold jSegOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hb, h⟩ := h
  have B := jBookOk_spec hb
  split at h
  · rename_i st hst
    have hall := jRun_sound hW hpe B p z start steps imports st himp hst
    intro m hm
    have hm' := List.all_eq_true.mp h m hm
    split at hm'
    · rename_i nd hnd
      have hnd' := hall _ (mem_of_lookup hnd)
      simp only [jExportOk, Bool.and_eq_true, beq_iff_eq] at hm'
      obtain ⟨⟨⟨⟨⟨⟨hu, hA⟩, he⟩, hre⟩, him⟩, hr⟩, hnb⟩ := hm'
      have hx : nd.x = m.2.x := by
        cases hx1 : nd.x
        cases hx2 : m.2.x
        rw [hx1, hx2] at hre him
        simp only at hre him
        rw [hre, him]
      unfold JEnc at hnd' ⊢
      rw [hu, hA, he, hx] at hnd'
      exact hnd'.weaken (LawfulCertArith.ble_sound _ _ hr) (LawfulCertArith.ble_sound _ _ hnb)
    · cases hm'
  · cases h

end Sound

end KAM.CertificateSharp.Packed
