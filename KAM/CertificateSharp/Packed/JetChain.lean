/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetSeg

/-!
# The packed jet chain (`V2-PACKED.md` §12.5, chain theorem)

The chain is an ordered list of **blocks**, each with imported and exported ledger entries
`(slot, node)`:
* a segment (`jSegOk`): sums, products and constants of earlier slots;
* an action block (`jActionsOk`): the action components of the embedding, packed from the landed
  `realCompModel` by `jLeaf`;
* a given block: entries supplied as hypotheses (`jChain_sound_of_given` names this dependence).
  The characters (`JetChar.lean`) and the witness operations (`JetWit.lean`) have packed blocks;
  `jChainW_slot` and `jChainT_slot` exclude given blocks.

`chain_sound` is the induction on the block order: if every block's exports enclose their slot
functions whenever its imports do, and every import is an export of an earlier block, then every
export encloses its slot function. The slot functions are those of the program at the embedding,
`θ ↦ p.val n (K.eval n θ) j`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- **The chain**: blocks in order, each sound, every import exported by an earlier block. -/
theorem chain_sound {β γ : Type} (P : γ → Prop) (blocks : List β) (imps exps : β → List γ)
    (hsound : ∀ b ∈ blocks, (∀ m ∈ imps b, P m) → ∀ m ∈ exps b, P m)
    (hfirst : ∀ k (hk : k < blocks.length), ∀ m ∈ imps blocks[k],
      ∃ k' < k, ∃ hk' : k' < blocks.length, m ∈ exps blocks[k']) :
    ∀ k (hk : k < blocks.length), ∀ m ∈ exps blocks[k], P m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk m hm
    refine hsound _ (List.getElem_mem hk) (fun m' hm' => ?_) m hm
    obtain ⟨k', hk'k, hk', hm''⟩ := hfirst k hk m' hm'
    exact ih k' hk'k hk' m' hm''

/-- A block of the packed chain. -/
inductive JBlock (α : Type) where
  | seg (start : ℕ) (imports : List (ℕ × JNode α)) (steps : List JStep)
      (exports : List (ℕ × JNode α))
  | actions (entries : List (ℕ × JNode α))
  | given (entries : List (ℕ × JNode α))

namespace JBlock

variable {α : Type}

def imports : JBlock α → List (ℕ × JNode α)
  | .seg _ i _ _ => i
  | _ => []

def exports : JBlock α → List (ℕ × JNode α)
  | .seg _ _ _ e => e
  | .actions e => e
  | .given e => e

def isGiven : JBlock α → Bool
  | .given _ => true
  | _ => false

end JBlock

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

/-- The landed model of the action component `j`. -/
def actionModel (K : CertEmbedding α) (j : ℕ) : CertModel α :=
  if j < n then realCompModel n (K.actionDeg.getD j 0) K.action[j]? else zeroModel

/-- **The action block**: every entry is an action slot, packed from the embedding. -/
def jActionsOk (K : CertEmbedding α) (p : Slp) (es : List (ℕ × JNode α)) : Bool :=
  es.all fun m =>
    match p.ops.getD m.1 (.const 0 0 0) with
    | .action j =>
      decide (m.1 < p.ops.length) &&
        match jLeaf W pe cfg jb false m.2.A (actionModel n K j) with
        | some nd => jExportOk nd m.2
        | none => false
    | _ => false

/-- The check of a block (a given block is not checked here). -/
def JBlock.ok (K : CertEmbedding α) (p : Slp) : JBlock α → Bool
  | .seg start i s e => jSegOk n W pe cfg jb p start i s e
  | .actions e => jActionsOk n W pe cfg jb K p e
  | .given _ => true

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α} {jb : JBook}

theorem slpVal_action (p : Slp) (z : (Fin n → ℂ) × (Fin n → ℂ)) {i j : ℕ}
    (h : p.ops.getD i (.const 0 0 0) = .action j) (hi : i < p.ops.length) :
    p.val n z i = if h : j < n then z.2 ⟨j, h⟩ else 0 := by
  rw [slpVal_eq_step n p z hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
  simp only [Option.getD_some] at h
  rw [h]
  rfl

/-- The action model encloses the slot's function at the embedding. -/
theorem actionModel_encloses (K : CertEmbedding α) (j : ℕ) :
    (actionModel n K j).Encloses n W.rho
      (fun θ => if h : j < n then (K.eval n θ).2 ⟨j, h⟩ else 0) := by
  unfold actionModel
  by_cases hj : j < n
  · simp only [hj, ↓reduceIte, ↓reduceDIte]
    exact realCompModel_encloses n W.rho _ _
  · simp only [hj, ↓reduceIte, ↓reduceDIte]
    exact zeroModel_encloses n W.rho

/-- The slot functions at the embedding. -/
abbrev embFn (n : ℕ) (K : CertEmbedding α) (p : Slp) (j : ℕ) : (Fin n → ℂ) → ℂ :=
  slotFn n p (fun θ => K.eval n θ) j

theorem jActionsOk_sound {s N : ℕ} (hW : checkWeight W s N = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) (K : CertEmbedding α) (p : Slp)
    {es : List (ℕ × JNode α)} (h : jActionsOk n W pe cfg jb K p es = true) :
    ∀ m ∈ es, JEnc n W jb m.2 (embFn n K p m.1) := by
  intro m hm
  have hm' := List.all_eq_true.mp h m hm
  split at hm'
  · rename_i j hop
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm'
    obtain ⟨hi, hm''⟩ := hm'
    split at hm''
    · rename_i nd hnd
      have hl := jLeaf_sound hW hpe B (actionModel_encloses (W := W) K j) hnd
      simp only [jExportOk, Bool.and_eq_true, beq_iff_eq] at hm''
      obtain ⟨⟨⟨⟨⟨⟨hu, hA⟩, he⟩, hre⟩, him⟩, hr⟩, hnb⟩ := hm''
      have hx : nd.x = m.2.x := by
        cases hx1 : nd.x
        cases hx2 : m.2.x
        rw [hx1, hx2] at hre him
        simp only at hre him
        rw [hre, him]
      unfold JEnc at hl ⊢
      rw [hu, hA, he, hx] at hl
      refine (hl.weaken (LawfulCertArith.ble_sound _ _ hr)
        (LawfulCertArith.ble_sound _ _ hnb)).congr fun θ _ => ?_
      simp only [embFn, slotFn]
      rw [slpVal_action p _ hop hi]
    · cases hm''
  · cases hm'

/-- A block is sound: its exports enclose when its imports do (a given block by hypothesis). -/
theorem JBlock.sound {s N : ℕ} (hW : checkWeight W s N = true)
    (hpe : checkPiEnclosure pe = true) (B : JBookFacts n W jb) (K : CertEmbedding α) (p : Slp)
    {b : JBlock α} (hok : b.ok n W pe cfg jb K p = true)
    (hgiven : b.isGiven = true → ∀ m ∈ b.exports, JEnc n W jb m.2 (embFn n K p m.1))
    (himp : ∀ m ∈ b.imports, JEnc n W jb m.2 (embFn n K p m.1)) :
    ∀ m ∈ b.exports, JEnc n W jb m.2 (embFn n K p m.1) := by
  cases b with
  | seg start i st e =>
    exact jSegOk_sound hW hpe p (fun θ => K.eval n θ) hok himp
  | actions e => exact jActionsOk_sound hW hpe B K p hok
  | given e => exact hgiven rfl

/-- **The packed jet chain, with the given blocks as hypotheses**: every export of every block
encloses its slot function at the embedding. -/
theorem jChain_sound_of_given {s N : ℕ} (hW : checkWeight W s N = true)
    (hpe : checkPiEnclosure pe = true) (hb : jBookOk n W jb = true) (K : CertEmbedding α)
    (p : Slp) (blocks : List (JBlock α))
    (hok : ∀ b ∈ blocks, b.ok n W pe cfg jb K p = true)
    (hgiven : ∀ b ∈ blocks, b.isGiven = true → ∀ m ∈ b.exports, JEnc n W jb m.2 (embFn n K p m.1))
    (hfirst : ∀ k (hk : k < blocks.length), ∀ m ∈ (blocks[k]).imports,
      ∃ k' < k, ∃ hk' : k' < blocks.length, m ∈ (blocks[k']).exports) :
    ∀ b ∈ blocks, ∀ m ∈ b.exports, JEnc n W jb m.2 (embFn n K p m.1) := by
  have B := jBookOk_spec hb
  have hc := chain_sound (fun m : ℕ × JNode α => JEnc n W jb m.2 (embFn n K p m.1)) blocks
    JBlock.imports JBlock.exports
    (fun b hbm himp => JBlock.sound hW hpe B K p (hok b hbm) (hgiven b hbm) himp) hfirst
  intro b hbm m hm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hbm
  exact hc k hk m hm

end Sound

end KAM.CertificateSharp.Packed
