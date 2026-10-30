/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Compose
public import KAM.Certificate.Gram

/-!
# Pruning a straight-line program to the slots a check consumes

`Slp.compose` evaluates every operation of the jet program, although invariance needs only the
`2n` slots `∂_a H` and energy only `H`. `pruneProg p wanted` replaces every operation outside the
backward closure of `wanted` by the constant `0` (slot numbers are unchanged, so every product key
`[0, slot]` and every operand reference is as before) and `pruneWit` drops the exp and reciprocal
witnesses that only the discarded operations consumed. A dead `exp`, `inv` or `mul` then costs
nothing.

The backward closure is computed by an untrusted pass and *verified* by `liveClosed`; when the
verification fails `prune` returns the program and the witnesses unchanged. The soundness lemma
`pruneProg_val` is unconditional: the pruned program has the same value as the original at every
wanted slot, and `Slp.composePruned_sound` is `Slp.compose_sound` for the original program.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM.Certificate

/-- The earlier slots an operation reads. -/
def opDeps : SlpOp → List ℕ
  | .add a b => [a, b]
  | .mul a b => [a, b]
  | .exp a => [a]
  | .inv a => [a]
  | _ => []

/-- The operation that replaces a discarded one. -/
def nopOp : SlpOp := .const 0 0 0

/-- One step of the backward pass: slot `k`, if wanted, wants its operands. -/
def liveStep (ops : List SlpOp) (S : List ℕ) (k : ℕ) : List ℕ :=
  if S.contains k then ((opDeps (ops.getD k nopOp)).filter fun j => !S.contains j) ++ S else S

/-- The slots needed for `wanted` (untrusted; checked by `liveClosed`). -/
def liveSet (ops : List SlpOp) (wanted : List ℕ) : List ℕ :=
  (List.range ops.length).reverse.foldl (liveStep ops) wanted

/-- `S` contains with every slot `i` the earlier operands of operation `i`. -/
def liveClosed (ops : List SlpOp) (S : List ℕ) : Bool :=
  (List.range ops.length).all fun i =>
    !S.contains i || (opDeps (ops.getD i nopOp)).all fun j => decide (i ≤ j) || S.contains j

/-- The operations of `ops` outside `S` replaced by `nopOp`. -/
def pruneOps (ops : List SlpOp) (S : List ℕ) : List SlpOp :=
  (List.range ops.length).map fun i => if S.contains i then ops.getD i nopOp else nopOp

/-- Whether the live set is a certified closure containing `wanted`. -/
def pruneOk (ops : List SlpOp) (wanted S : List ℕ) : Bool :=
  liveClosed ops S && wanted.all fun i => S.contains i

/-- The pruned program. -/
def pruneProg (p : Slp) (wanted : List ℕ) : Slp :=
  let S := liveSet p.ops wanted
  if pruneOk p.ops wanted S then ⟨pruneOps p.ops S⟩ else p

/-- Keep the entries whose flag is set. -/
def keepFlagged {β : Type} (l : List β) (flags : List Bool) : List β :=
  (l.zip flags).filterMap fun x => if x.2 then some x.1 else none

/-- The liveness flags of the `exp` operations, in program order. -/
def expFlags (ops : List SlpOp) (S : List ℕ) : List Bool :=
  (List.range ops.length).filterMap fun i =>
    match ops.getD i nopOp with
    | .exp _ => some (S.contains i)
    | _ => none

/-- The liveness flags of the `inv` operations, in program order. -/
def invFlags (ops : List SlpOp) (S : List ℕ) : List Bool :=
  (List.range ops.length).filterMap fun i =>
    match ops.getD i nopOp with
    | .inv _ => some (S.contains i)
    | _ => none

/-- The program and the witnesses of a pruned composition. -/
def prune {α : Type} (p : Slp) (wit : Witnesses α) (wanted : List ℕ) : Slp × Witnesses α :=
  let S := liveSet p.ops wanted
  if pruneOk p.ops wanted S then
    (⟨pruneOps p.ops S⟩, ⟨keepFlagged wit.expWit (expFlags p.ops S),
      keepFlagged wit.invWit (invFlags p.ops S), wit.charWit⟩)
  else (p, wit)

/-- `Slp.compose` of the pruned program with the pruned witnesses. -/
def Slp.composePruned {α : Type} [CertArith α] (n : ℕ) (p : Slp) (K : CertEmbedding α)
    (wit : Witnesses α) (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (wanted : List ℕ) : Option (List (CertModel α)) :=
  match prune p wit wanted with
  | (p', wit') => Slp.compose n p' K wit' W cfg pe wanted

/-! ### Soundness -/

theorem opDeps_step_congr (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (acc acc' : List ℂ)
    (op : SlpOp) (h : ∀ a ∈ opDeps op, acc.getD a 0 = acc'.getD a 0) :
    op.step n z acc = op.step n z acc' := by
  cases op <;> simp_all [SlpOp.step, opDeps]

theorem pruneOps_length (ops : List SlpOp) (S : List ℕ) : (pruneOps ops S).length = ops.length := by
  simp [pruneOps]

theorem pruneOps_getD (ops : List SlpOp) (S : List ℕ) {i : ℕ} (hi : i < ops.length) :
    (pruneOps ops S).getD i nopOp = if S.contains i then ops.getD i nopOp else nopOp := by
  simp [pruneOps, hi]

theorem liveClosed_spec {ops : List SlpOp} {S : List ℕ} (h : liveClosed ops S = true) {i : ℕ}
    (hi : i < ops.length) (hS : i ∈ S) {j : ℕ} (hj : j ∈ opDeps (ops.getD i nopOp)) (hji : j < i) :
    j ∈ S := by
  unfold liveClosed at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.mpr hi)
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at this
  rcases this with h1 | h1
  · exact absurd hS (by simpa using h1)
  · rcases h1 j hj with h2 | h2
    · omega
    · exact h2

/-- Prefix version: the values of the first `m` slots agree on `S`. -/
theorem prune_vals_take (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) {ops : List SlpOp} {S : List ℕ}
    (h : liveClosed ops S = true) :
    ∀ m, m ≤ ops.length → ∀ i < m, i ∈ S →
      (Slp.vals n z ((pruneOps ops S).take m)).getD i 0 = (Slp.vals n z (ops.take m)).getD i 0 := by
  intro m
  induction m with
  | zero => intro _ i hi; omega
  | succ m ih =>
    intro hm i him hiS
    have hmlt : m < ops.length := hm
    have hmlt' : m < (pruneOps ops S).length := by rwa [pruneOps_length]
    have e1 : ops.take (m + 1) = ops.take m ++ [ops.getD m nopOp] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hmlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmlt]
    have e2 : (pruneOps ops S).take (m + 1) =
        (pruneOps ops S).take m ++ [(pruneOps ops S).getD m nopOp] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hmlt']
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmlt']
    rw [e1, e2]
    have hlen1 : (ops.take m).length = m := by simp [List.length_take]; omega
    have hlen2 : ((pruneOps ops S).take m).length = m := by
      simp [List.length_take, pruneOps_length]; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp him with hlt | rfl
    · rw [Slp.val_append n z _ _ (by omega), Slp.val_append n z _ _ (by omega)]
      exact ih (by omega) i hlt hiS
    · have hop : (pruneOps ops S).getD i nopOp = ops.getD i nopOp := by
        rw [pruneOps_getD _ _ hmlt]
        simp [hiS]
      have s1 := Slp.val_snoc_self n z ((pruneOps ops S).take i) ((pruneOps ops S).getD i nopOp)
      have s2 := Slp.val_snoc_self n z (ops.take i) (ops.getD i nopOp)
      rw [hlen2] at s1
      rw [hlen1] at s2
      rw [s1, s2, hop]
      refine opDeps_step_congr n z _ _ _ fun a ha => ?_
      rcases lt_or_ge a i with hai | hai
      · exact ih (by omega) a hai (liveClosed_spec h hmlt hiS ha hai)
      · have l1 : (Slp.vals n z ((pruneOps ops S).take i)).length ≤ a := by
          rw [Slp.vals_length]; omega
        have l2 : (Slp.vals n z (ops.take i)).length ≤ a := by
          rw [Slp.vals_length]; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none l1, List.getElem?_eq_none l2]

/-- The pruned program has the value of the original one at every wanted slot. -/
theorem pruneProg_val (n : ℕ) (p : Slp) (wanted : List ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) {i : ℕ}
    (hi : i ∈ wanted) : (pruneProg p wanted).val n z i = p.val n z i := by
  unfold pruneProg
  dsimp only
  split
  · rename_i hok
    simp only [pruneOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hok
    have hS := hok.2 i hi
    unfold Slp.val
    by_cases hlt : i < p.ops.length
    · have := prune_vals_take n z hok.1 p.ops.length le_rfl i hlt hS
      rwa [List.take_of_length_le (by rw [pruneOps_length]), List.take_length] at this
    · have l1 : (Slp.vals n z (pruneOps p.ops (liveSet p.ops wanted))).length ≤ i := by
        rw [Slp.vals_length, pruneOps_length]; omega
      have l2 : (Slp.vals n z p.ops).length ≤ i := by rw [Slp.vals_length]; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none l1,
        List.getElem?_eq_none l2]
  · rfl

/-- **Soundness of the pruned composition**: the models enclose the slots of the original
program. -/
theorem Slp.composePruned_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (p : Slp)
    (K : CertEmbedding α) (wit : Witnesses α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (wanted : List ℕ) {ms : List (CertModel α)}
    (h : Slp.composePruned n p K wit W cfg pe wanted = some ms) :
    ms.length = wanted.length ∧ ∀ idx (hidx : idx < ms.length), ms[idx].Encloses n W.rho
      (fun θ => p.val n (K.eval n θ) (wanted.getD idx 0)) := by
  unfold Slp.composePruned at h
  split at h
  rename_i p' wit' hp
  obtain ⟨hlen, hm⟩ := Slp.compose_sound p' K wit' hW cfg hpe wanted h
  refine ⟨hlen, fun idx hidx => CertModel.Encloses.of_eq_fun (hm idx hidx) fun θ => ?_⟩
  have hmem : wanted.getD idx 0 ∈ wanted := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  have hp' : p' = pruneProg p wanted := by
    have := congrArg Prod.fst hp
    simp only at this
    rw [← this]
    unfold prune pruneProg
    dsimp only
    split <;> rfl
  rw [hp']
  exact pruneProg_val n p wanted _ hmem

end KAM.CertificateSharp
