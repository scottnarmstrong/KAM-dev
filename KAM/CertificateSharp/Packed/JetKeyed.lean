/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetStage

/-!
# The keyed packed jet chain: one ledger, key-only blocks, an order certificate

`jChainT_slot` (`JetStage.lean`) needs the block order `hfirst`: every `(key, node)` import of a
block is an export of an earlier block. `JNode` has no decidable equality, so this file reads
every node from one ledger by its key, and the order becomes a statement about keys:

* `JLed`, an `α`-free ledger node: the radius and the norm bound are rationals, rounded up by
  `JLed.node` (exactly, for a dyadic radius at the arithmetic's scale);
* `JLedger.look`, the node of a key; the partial sum of degree `0` is read as the Taylor term of
  degree `0` (both are `1`, `canonKey`);
* `KBlock`, a block given by its keys; `KBlock.toT` reads its nodes from the ledger, so its
  imports and exports are the pairs `(k, look k)` of its keys (`toT_imports`, `toT_exports`);
* `orderOk`, the order certificate: for every import of block `i`, the index of an earlier block
  that exports its key;
* `jetChainOk`, one Boolean for a whole chain, and `jetChainOk_sound`: every wanted slot's ledger
  node is a packed model of the slot's function at the embedding.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

deriving instance DecidableEq for TKey

/-- A ledger node without its arithmetic: the radius and the norm bound as rationals. -/
structure JLed where
  u : Bool
  A : ℕ
  e : ℕ
  x : PC
  r : ℚ
  nb : ℚ

instance : Inhabited JLed := ⟨⟨false, 0, 0, ⟨0, 0⟩, 0, 0⟩⟩

/-- The node of a ledger entry (radius and norm bound rounded up). -/
def JLed.node {α : Type} [CertArith α] (l : JLed) : JNode α :=
  ⟨l.u, l.A, l.e, l.x, ofRatUp l.r, ofRatUp l.nb⟩

/-- The canonical key: the partial sum of degree `0` is the Taylor term of degree `0`. -/
def canonKey : JKeyT → JKeyT
  | .inr (.sum j neg 0) => .inr (.term j neg 0)
  | k => k

theorem canonKey_canonKey (k : JKeyT) : canonKey (canonKey k) = canonKey k := by
  rcases k with k | (⟨j, neg⟩ | ⟨j, neg, m⟩ | ⟨j, neg, m⟩)
  · rfl
  · rfl
  · rfl
  · cases m <;> rfl

/-- The ledger: the nodes by key. -/
abbrev JLedger := List (JKeyT × JLed)

/-- The node of a key (`default` if the key is not on the ledger). -/
def JLedger.look {α : Type} [CertArith α] (L : JLedger) (k : JKeyT) : JNode α :=
  ((L.lookup (canonKey k)).getD default).node

theorem JLedger.look_canon {α : Type} [CertArith α] (L : JLedger) (k : JKeyT) :
    L.look (α := α) (canonKey k) = L.look k := by
  simp only [JLedger.look, canonKey_canonKey]

/-- The key of program slot `j`. -/
abbrev slotK (j : ℕ) : JKeyT := .inl (.inl j)

/-- The key of `exp(σ i 2π angleAt_j)^m`. -/
abbrev facK (j : ℕ) (neg : Bool) (m : ℕ) : JKeyT := .inl (.inr (j, neg, m))

/-- A block of the keyed chain: its kind and its keys, no node. -/
inductive KBlock where
  | seg (start : ℕ) (imps : List ℕ) (steps : List JStep) (exps : List ℕ)
  | actions (slots : List ℕ)
  | expo (j : ℕ) (neg : Bool) (N : ℕ)
  | powsX (j : ℕ) (neg : Bool) (cnt : ℕ)
  | chars (facs : List JKey) (ents : List ℕ)
  | inv (a j : ℕ) (cand : PC)
  | sqrt (a j : ℕ) (cand : PC) (cA cS s0 : ℚ)
  | tstart (j : ℕ) (neg : Bool)
  | tstep (j : ℕ) (neg : Bool) (m k : ℕ)
  | texp (j : ℕ) (neg : Bool) (N : ℕ)
  | pows (j : ℕ) (neg : Bool) (m cnt : ℕ)

instance : Inhabited KBlock := ⟨.actions []⟩

namespace KBlock

/-- The keys a block reads. -/
def imports : KBlock → List JKeyT
  | .seg _ imps _ _ => imps.map slotK
  | .actions _ => []
  | .expo .. => []
  | .powsX j neg _ => [facK j neg 1]
  | .chars facs _ => facs.map .inl
  | .inv a _ _ => [slotK a]
  | .sqrt a _ _ _ _ _ => [slotK a]
  | .tstart .. => []
  | .tstep j neg m _ => [.inr (.w j neg), .inr (.term j neg m), .inr (.sum j neg m)]
  | .texp j neg N => [.inr (.w j neg), .inr (.sum j neg N)]
  | .pows j neg m _ => [facK j neg 1, facK j neg m]

/-- The keys a block writes. -/
def exports : KBlock → List JKeyT
  | .seg _ _ _ exps => exps.map slotK
  | .actions slots => slots.map slotK
  | .expo j neg _ => [facK j neg 1]
  | .powsX j neg cnt => (List.range cnt).map fun i => facK j neg (i + 2)
  | .chars _ ents => ents.map slotK
  | .inv _ j _ => [slotK j]
  | .sqrt _ j _ _ _ _ => [slotK j]
  | .tstart j neg => [.inr (.w j neg), .inr (.term j neg 0), .inr (.sum j neg 0)]
  | .tstep j neg m k => [.inr (.term j neg (m + k)), .inr (.sum j neg (m + k))]
  | .texp j neg _ => [facK j neg 1]
  | .pows j neg m cnt => (List.range cnt).map fun i => facK j neg (m + 1 + i)

variable {α : Type}

/-- The block of `JetStage.lean` with its nodes read from `look`. -/
def toT (look : JKeyT → JNode α) : KBlock → JBlockT α
  | .seg start imps steps exps =>
    .lift (.x (.base (.seg start (imps.map fun i => (i, look (slotK i))) steps
      (exps.map fun i => (i, look (slotK i))))))
  | .actions slots => .lift (.x (.base (.actions (slots.map fun i => (i, look (slotK i))))))
  | .expo j neg N => .lift (.x (.expo j neg N (look (facK j neg 1))))
  | .powsX j neg cnt =>
    .lift (.x (.pows j neg (look (facK j neg 1))
      ((List.range cnt).map fun i => look (facK j neg (i + 2)))))
  | .chars facs ents =>
    .lift (.x (.chars (facs.map fun k => (k, look (.inl k)))
      (ents.map fun i => (i, look (slotK i)))))
  | .inv a j cand => .lift (.inv a j (look (slotK a)) cand (look (slotK j)))
  | .sqrt a j cand cA cS s0 =>
    .lift (.sqrt a j (look (slotK a)) cand cA cS s0 (look (slotK j)))
  | .tstart j neg => .tstart j neg (look (.inr (.w j neg))) (look (.inr (.term j neg 0)))
  | .tstep j neg m k =>
    .tstep j neg m k (look (.inr (.w j neg))) (look (.inr (.term j neg m)))
      (look (.inr (.sum j neg m))) (look (.inr (.term j neg (m + k))))
      (look (.inr (.sum j neg (m + k))))
  | .texp j neg N =>
    .texp j neg N (look (.inr (.w j neg))) (look (.inr (.sum j neg N))) (look (facK j neg 1))
  | .pows j neg m cnt =>
    .pows j neg m (look (facK j neg 1)) (look (facK j neg m))
      ((List.range cnt).map fun i => look (facK j neg (m + 1 + i)))

theorem toT_imports (look : JKeyT → JNode α) (kb : KBlock) :
    (kb.toT look).imports = kb.imports.map fun k => (k, look k) := by
  cases kb <;>
    simp [toT, imports, JBlockT.imports, JBlockW.imports, JBlockX.imports, JBlock.imports,
      List.map_map, Function.comp_def]

theorem toT_exports (look : JKeyT → JNode α) (hc : ∀ k, look (canonKey k) = look k)
    (kb : KBlock) : (kb.toT look).exports = kb.exports.map fun k => (k, look k) := by
  cases kb with
  | tstart j neg =>
    have h : look (.inr (.term j neg 0)) = look (.inr (.sum j neg 0)) := hc (.inr (.sum j neg 0))
    simp [toT, exports, JBlockT.exports, h]
  | _ =>
    simp [toT, exports, JBlockT.exports, JBlockW.exports, JBlockX.exports, JBlock.exports,
      List.map_map, Function.comp_def, List.zipWith_map_right, List.zipWith_self]

theorem toT_isGiven (look : JKeyT → JNode α) (kb : KBlock) : (kb.toT look).isGiven = false := by
  cases kb <;> rfl

end KBlock

/-- **The order certificate**: `cert[i][t]` is a block before block `i` that exports the key of
the `t`-th import of block `i`. Decided on keys. -/
def orderOk (kbs : List KBlock) (cert : List (List ℕ)) : Bool :=
  (List.range kbs.length).all fun i =>
    (List.range (kbs.getD i default).imports.length).all fun t =>
      let s := (cert.getD i []).getD t 0
      decide (s < i) && (kbs.getD s default).exports.contains ((kbs.getD i default).imports.getD t
        (slotK 0))

theorem orderOk_spec {kbs : List KBlock} {cert : List (List ℕ)} (h : orderOk kbs cert = true) :
    ∀ i (hi : i < kbs.length), ∀ k ∈ (kbs[i]).imports,
      ∃ s < i, ∃ hs : s < kbs.length, k ∈ (kbs[s]).exports := by
  intro i hi k hk
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hk
  simp only [orderOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at h
  have hgi : kbs.getD i default = kbs[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have h1 := h i hi t (by rw [hgi]; exact ht)
  rw [hgi] at h1
  obtain ⟨hs, hmem⟩ := h1
  set s := (cert.getD i []).getD t 0
  have hsl : s < kbs.length := lt_trans hs hi
  refine ⟨s, hs, hsl, ?_⟩
  have hgs : kbs.getD s default = kbs[s] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsl, Option.getD_some]
  have hgt : (kbs[i]).imports.getD t (slotK 0) = (kbs[i]).imports[t] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  rw [hgs, hgt] at hmem
  exact hmem

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

/-- **One Boolean for a whole keyed chain**: the book, every block on the ledger's nodes, the
order certificate, and every wanted slot exported by some block. -/
def jetChainOk (K : CertEmbedding α) (p : Slp) (L : JLedger) (kbs : List KBlock)
    (cert : List (List ℕ)) (wanted : List ℕ) : Bool :=
  jBookOk n W jb && kbs.all (fun kb => (kb.toT (L.look (α := α))).ok n W pe cfg jb K p) &&
    orderOk kbs cert && wanted.all fun j => kbs.any fun kb => kb.exports.contains (slotK j)

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α} {jb : JBook}

/-- **The keyed chain, end to end.** Every program slot exported by a block of a keyed chain
with a valid order certificate has its ledger node as a packed model of its function. -/
theorem jChainK_slot {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) (hb : jBookOk n W jb = true) (K : CertEmbedding α)
    (p : Slp) (L : JLedger) (kbs : List KBlock) (cert : List (List ℕ))
    (hok : ∀ kb ∈ kbs, (kb.toT (L.look (α := α))).ok n W pe cfg jb K p = true)
    (hord : orderOk kbs cert = true) :
    ∀ kb ∈ kbs, ∀ j, slotK j ∈ kb.exports →
      JEnc n W jb (L.look (α := α) (slotK j)) (fun θ => p.val n (K.eval n θ) j) := by
  have hc : ∀ k, L.look (α := α) (canonKey k) = L.look k := L.look_canon
  have hfirst : ∀ k (hk : k < (kbs.map (KBlock.toT (L.look (α := α)))).length),
      ∀ m ∈ ((kbs.map (KBlock.toT (L.look (α := α))))[k]).imports,
      ∃ k' < k, ∃ hk' : k' < (kbs.map (KBlock.toT (L.look (α := α)))).length,
        m ∈ ((kbs.map (KBlock.toT (L.look (α := α))))[k']).exports := by
    intro k hk m hm
    have hk0 : k < kbs.length := by simpa using hk
    simp only [List.getElem_map, KBlock.toT_imports, List.mem_map] at hm
    obtain ⟨key, hkey, rfl⟩ := hm
    obtain ⟨s, hsk, hs, hex⟩ := orderOk_spec hord k hk0 key hkey
    refine ⟨s, hsk, by simpa using hs, ?_⟩
    simp only [List.getElem_map, KBlock.toT_exports _ hc, List.mem_map]
    exact ⟨key, hex, rfl⟩
  have hok' : ∀ b ∈ kbs.map (KBlock.toT (L.look (α := α))), b.ok n W pe cfg jb K p = true := by
    intro b hb
    obtain ⟨kb, hkb, rfl⟩ := List.mem_map.mp hb
    exact hok kb hkb
  have hng : ∀ b ∈ kbs.map (KBlock.toT (L.look (α := α))), b.isGiven = false := by
    intro b hb
    obtain ⟨kb, -, rfl⟩ := List.mem_map.mp hb
    exact KBlock.toT_isGiven _ _
  intro kb hkb j hj
  refine jChainT_slot hW hpe hb K p _ hok' hng hfirst (kb.toT (L.look (α := α)))
    (List.mem_map_of_mem hkb) j _ ?_
  rw [KBlock.toT_exports _ hc]
  exact List.mem_map_of_mem (f := fun k => (k, L.look (α := α) k)) hj

/-- **Soundness of the Boolean of a keyed chain**: every wanted slot's ledger node is a packed
model of the slot's function at the embedding. -/
theorem jetChainOk_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) {K : CertEmbedding α} {p : Slp} {L : JLedger}
    {kbs : List KBlock} {cert : List (List ℕ)} {wanted : List ℕ}
    (h : jetChainOk n W pe cfg jb K p L kbs cert wanted = true) :
    ∀ j ∈ wanted, JEnc n W jb (L.look (α := α) (slotK j)) (fun θ => p.val n (K.eval n θ) j) := by
  simp only [jetChainOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨hb, hok⟩, hord⟩, hw⟩ := h
  intro j hj
  obtain ⟨kb, hkb, hex⟩ := hw j hj
  exact jChainK_slot hW hpe hb K p L kbs cert hok hord kb hkb j hex

end Sound

end KAM.CertificateSharp.Packed
