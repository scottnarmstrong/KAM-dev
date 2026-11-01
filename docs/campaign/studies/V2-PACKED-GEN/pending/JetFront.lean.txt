/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetCheck

/-!
# A jet ledger with its wanted nodes in front

The consumers of the packed jet (`checkTorsionJ`, `checkInvarianceJ`, `checkEnergyJ`) read the
wanted nodes of a chain through `List.lookup` in the chain's whole ledger (`JetData.led`; about
3,800 nodes for LG00's `cfgLow` chain). In the kernel each read walks the ledger, and a consumer
stage that reads several wanted nodes does not fit 4 GB. `JetData.withFront jd front` is the same
chain with `front` (some of its own entries) prepended to the ledger: a lookup of a front key stops
in the front, every other lookup is unchanged.

* `lookup_withFront`: if every front entry is the ledger's own (`frontOk`, decided entry by entry
  with `lookOk`), then the two ledgers have the same lookups;
* `jetCheck_withFront`: the chain check is unchanged, so the chain theorem of `jd` gives the one of
  `jd.withFront front`, and the consumers can be stated at `jd.withFront front`.

No consumer, chain or block definition changes.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

deriving instance DecidableEq for PC
deriving instance DecidableEq for JLed

/-- The chain `jd` with `front` prepended to its ledger. -/
def JetData.withFront (jd : JetData) (front : JLedger) : JetData :=
  ⟨jd.jb, front ++ jd.L, jd.kbs, jd.cert⟩

/-- One front entry is the ledger's own. -/
def lookOk (jd : JetData) (k : JKeyT) (v : JLed) : Bool :=
  decide (jd.L.lookup k = some v)

/-- Every front entry is the ledger's own. -/
def frontOk (jd : JetData) (front : JLedger) : Bool :=
  front.all fun e => lookOk jd e.1 e.2

/-- With a correct front, the lookups are the ledger's. -/
theorem lookup_withFront {jd : JetData} {front : JLedger} (h : frontOk jd front = true)
    (k : JKeyT) : (front ++ jd.L).lookup k = jd.L.lookup k := by
  induction front with
  | nil => rfl
  | cons e front ih =>
    simp only [frontOk, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨he, hf⟩ := h
    simp only [lookOk, decide_eq_true_eq] at he
    obtain ⟨k', v⟩ := e
    rw [List.cons_append, List.lookup_cons]
    by_cases hk : k = k'
    · subst hk
      simp only [beq_self_eq_true]
      exact he.symm
    · have : (k == k') = false := beq_false_of_ne hk
      rw [this]
      exact ih hf

/-- With a correct front, `look` is the ledger's. -/
theorem look_withFront {α : Type} [CertArith α] {jd : JetData} {front : JLedger}
    (h : frontOk jd front = true) : (front ++ jd.L).look (α := α) = jd.L.look := by
  funext k
  simp only [JLedger.look, lookup_withFront h]

/-- **The chain check is unchanged by a correct front.** -/
theorem jetCheck_withFront {n : ℕ} {α : Type} [CertArith α] {W : CertWeight}
    {pe : PiEnclosure α} {cfg : ModelConfig α} {K : CertEmbedding α} {p : Slp} {jd : JetData}
    {front : JLedger} (h : frontOk jd front = true) (B : ℕ) (wanted : List ℕ) :
    jetCheck n W pe cfg K p (jd.withFront front) B wanted =
      jetCheck n W pe cfg K p jd B wanted := by
  have hw : jetWantedOk (jd.withFront front) B = jetWantedOk jd B := by
    funext i
    simp only [jetWantedOk, JetData.led, JetData.withFront, lookup_withFront h]
    rfl
  rw [jetCheck, jetCheck, hw]
  simp only [jetChainOk, JetData.withFront, look_withFront h]

/-- `frontOk` from its entries (for proofs split across declarations: one lookup each). -/
theorem frontOk_of {jd : JetData} {front : JLedger} (h : ∀ e ∈ front, lookOk jd e.1 e.2 = true) :
    frontOk jd front = true := by
  simp only [frontOk, List.all_eq_true]
  exact h

end KAM.CertificateSharp.Packed

end
