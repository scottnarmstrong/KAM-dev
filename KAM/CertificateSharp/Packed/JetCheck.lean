/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetKeyed

/-!
# The packed jet check and its contract (design §12.2)

The interface between the packed jet chain and its consumers (torsion, invariance, energy):

* `JetData`, a keyed packed jet chain without its arithmetic: the book, the ledger, the key-only
  blocks and the order certificate (`JetKeyed.lean`);
* `jetLed`, `jetNode`, `jetRad`, `jetNb`: the ledger entry of a slot and its packed value, radius
  and norm bound;
* `jetCheck`: the keyed chain at a program and an embedding (`jetChainOk`), and every wanted
  slot's entry on the box at the scale `2^P` with a load at most `B`;
* `jetPacked_sound`: **every wanted slot `i` has a packed model `PEnc jd.jb.Lb B jd.jb.P
  (jetNode jd i) (jetRad jd i) (jetNb jd i)` of its function `θ ↦ p.val n (K.eval n θ) i` on the
  strip.** A consumer takes these enclosures as hypotheses; `jetPacked_sound` discharges them.
* `jetCheck_of`: the Boolean from its parts (one block at a time), for the assembly of a chain
  whose blocks are checked in separate declarations.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- A keyed packed jet chain without its arithmetic. -/
structure JetData where
  /-- The book: the box `Lb` of the nodes, the window, the scale `P`, the guards. -/
  jb : JBook
  /-- The ledger: every exported node, by key. -/
  L : JLedger
  /-- The blocks, in order, by their keys. -/
  kbs : List KBlock
  /-- The order certificate: `cert[i][t]` is an earlier block exporting the `t`-th import of
  block `i`. -/
  cert : List (List ℕ)

namespace JetData

variable (jd : JetData)

/-- The ledger entry of program slot `i`. -/
def led (i : ℕ) : JLed := (jd.L.lookup (slotK i)).getD default

/-- The packed value of slot `i` on the box. -/
def node (i : ℕ) : PC := (jd.led i).x

/-- The radius of slot `i`. -/
def rad {α : Type} [CertArith α] (i : ℕ) : α := ofRatUp (jd.led i).r

/-- The norm bound of slot `i`. -/
def nb {α : Type} [CertArith α] (i : ℕ) : α := ofRatUp (jd.led i).nb

theorem look_slotK {α : Type} [CertArith α] (i : ℕ) :
    jd.L.look (α := α) (slotK i) = (jd.led i).node := rfl

end JetData

/-- The ledger entry of slot `i` of a chain (`JetData.led`). -/
abbrev jetLed (jd : JetData) (i : ℕ) : JLed := jd.led i

/-- The packed value of slot `i` of a chain. -/
abbrev jetNode (jd : JetData) (i : ℕ) : PC := jd.node i

/-- The radius of slot `i` of a chain. -/
abbrev jetRad {α : Type} [CertArith α] (jd : JetData) (i : ℕ) : α := jd.rad i

/-- The norm bound of slot `i` of a chain. -/
abbrev jetNb {α : Type} [CertArith α] (jd : JetData) (i : ℕ) : α := jd.nb i

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α)

/-- The wanted-slot guard: the entry is a box node at the book's scale with a load at most `B`. -/
def jetWantedOk (jd : JetData) (B : ℕ) (i : ℕ) : Bool :=
  !(jd.led i).u && (jd.led i).e == jd.jb.P && decide ((jd.led i).A ≤ B)

/-- **The packed jet check** (design §12.2): the keyed chain `jd` at the program `p` and the
embedding `K`, and every wanted slot's entry on the box at the scale `2^P` with load at most `B`. -/
def jetCheck (K : CertEmbedding α) (p : Slp) (jd : JetData) (B : ℕ) (wanted : List ℕ) : Bool :=
  jetChainOk n W pe cfg jd.jb K p jd.L jd.kbs jd.cert wanted && wanted.all (jetWantedOk jd B)

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α}

/-- **The contract of the packed jet** (design §12.2): every wanted slot of a passing chain has a
packed model of its function at the embedding, on the box, at the scale `2^P`, with load `B`. -/
theorem jetPacked_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) {K : CertEmbedding α} {p : Slp} {jd : JetData} {B : ℕ}
    {wanted : List ℕ} (h : jetCheck n W pe cfg K p jd B wanted = true) :
    ∀ i ∈ wanted, PEnc jd.jb.Lb B jd.jb.P (jetNode jd i) (jetRad (α := α) jd i)
      (jetNb (α := α) jd i) n W.rho (fun θ => p.val n (K.eval n θ) i) := by
  simp only [jetCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hc, hw⟩ := h
  intro i hi
  have he := jetChainOk_sound hW hpe hc i hi
  have hg := hw i hi
  simp only [jetWantedOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    decide_eq_true_eq] at hg
  obtain ⟨⟨hu, hP⟩, hA⟩ := hg
  rw [jd.look_slotK] at he
  unfold JEnc jLay JLed.node at he
  simp only [hu, hP, Bool.false_eq_true, ↓reduceIte] at he
  exact he.mono hA

omit [LawfulCertArith α] in
/-- **The packed jet check from its parts**: the book, each block (in separate declarations), the
order certificate, the wanted slots exported and their guards. -/
theorem jetCheck_of {K : CertEmbedding α} {p : Slp} {jd : JetData} {B : ℕ} {wanted : List ℕ}
    (hb : jBookOk n W jd.jb = true)
    (hok : ∀ kb ∈ jd.kbs, (kb.toT (jd.L.look (α := α))).ok n W pe cfg jd.jb K p = true)
    (hord : orderOk jd.kbs jd.cert = true)
    (hex : (wanted.all fun j => jd.kbs.any fun kb => kb.exports.contains (slotK j)) = true)
    (hw : wanted.all (jetWantedOk jd B) = true) :
    jetCheck n W pe cfg K p jd B wanted = true := by
  simp only [jetCheck, jetChainOk, hb, hord, hex, hw, Bool.and_true, Bool.true_and,
    List.all_eq_true]
  exact hok

end Sound

end KAM.CertificateSharp.Packed
