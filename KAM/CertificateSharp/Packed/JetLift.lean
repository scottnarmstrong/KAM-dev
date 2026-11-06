/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Shift.Node
public import KAM.CertificateSharp.Packed.JetConsTors
public import KAM.CertificateSharp.Packed.JetCheck
public import KAM.CertificateSharp.Packed.JetFront

/-!
# Constant wanted slots of the packed jet, lifted to the box

The packed jet check `jetCheck` requires every wanted slot's ledger entry to be a box node
(`jetWantedOk`: `!u`). A Hamiltonian that is linear in an action has constant derivative slots: for
MAG, `∂_J H = 1` is the program's constant `1`, and the structurally zero second derivatives point
at the constant `0`. The chain computes such a slot as a constant on the one-slot layout `LU0`, so
the landed guard rejects it. Here:
* `jetNodeL`, `jetLoadL`, `jetSlotsL`: a constant entry is lifted to the box by the unit at the
  box's zero slot (`jUp` to the box at its own scale: the radius and the norm bound are unchanged,
  the load becomes `mulLoad LU0 Lb A 1`), a box entry stays as it is;
* `jetCheckL`: the keyed chain and, for every wanted slot, the book's scale and the lifted load at
  most `B` (`jetWantedOkL`);
* `jetPackedL_sound`: every wanted slot of a passing chain has a packed model of its function on the
  box at the scale `2^P` with load `B` (the contract of `jetPacked_sound`, for the lifted slots);
* `jetCheckL_of`, `jetCheckL_withFront`: the check from its parts, and unchanged by a correct front
  (as `jetCheck_of`, `jetCheck_withFront`). The unit is written as a shift (`jUnitS`,
  `Shift/Node.lean`), so the lift runs at any window size.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α)

/-- The packed value of a wanted slot on the box: a constant lifted by the box's unit. -/
def jetNodeL (jd : JetData) (i : ℕ) : PC :=
  if (jd.led i).u then pcMul (jd.led i).x (jUnitS n jd.jb.Lb 0) else (jd.led i).x

/-- The load of a wanted slot on the box. -/
def jetLoadL (jd : JetData) (i : ℕ) : ℕ :=
  if (jd.led i).u then mulLoad jd.jb.LU0 jd.jb.Lb (jd.led i).A (2 ^ 0) else (jd.led i).A

/-- The packed models of a keyed jet chain's slots, the constants lifted to the box. -/
def jetSlotsL (jd : JetData) : JSlots α := ⟨jetNodeL n jd, jetRad jd, jetNb jd⟩

/-- The wanted-slot guard with the lift: the entry is at the book's scale, its lifted load at most
`B`. -/
def jetWantedOkL (jd : JetData) (B : ℕ) (i : ℕ) : Bool :=
  (jd.led i).e == jd.jb.P && decide (jetLoadL jd i ≤ B)

/-- **The packed jet check with lifted constants**: the keyed chain `jd` and every wanted slot's
lifted entry on the box at the scale `2^P` with load at most `B`. -/
def jetCheckL (K : CertEmbedding α) (p : Slp) (jd : JetData) (B : ℕ) (wanted : List ℕ) : Bool :=
  jetChainOk n W pe cfg jd.jb K p jd.L jd.kbs jd.cert wanted && wanted.all (jetWantedOkL jd B)

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α}

/-- **The contract of the packed jet with lifted constants**: every wanted slot of a passing chain
has a packed model of its function at the embedding, on the box, at the scale `2^P`, with load
`B`. -/
theorem jetPackedL_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) {K : CertEmbedding α} {p : Slp} {jd : JetData} {B : ℕ}
    {wanted : List ℕ} (h : jetCheckL n W pe cfg K p jd B wanted = true) :
    ∀ i ∈ wanted, PEnc jd.jb.Lb B jd.jb.P (jetNodeL n jd i) (jetRad (α := α) jd i)
      (jetNb (α := α) jd i) n W.rho (fun θ => p.val n (K.eval n θ) i) := by
  simp only [jetCheckL, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hc, hw⟩ := h
  have hb : jBookOk n W jd.jb = true := by
    simp only [jetChainOk, Bool.and_eq_true] at hc
    exact hc.1.1.1
  have BF := jBookOk_spec hb
  intro i hi
  have he := jetChainOk_sound hW hpe hc i hi
  have hg := hw i hi
  simp only [jetWantedOkL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
  obtain ⟨hP, hA⟩ := hg
  rw [jd.look_slotK] at he
  by_cases hu : (jd.led i).u = true
  · have hup : jUp n jd.jb ((jd.led i).node (α := α)) false (jd.led i).e =
        some ⟨false, mulLoad jd.jb.LU0 jd.jb.Lb (jd.led i).A (2 ^ 0), (jd.led i).e,
          pcMul (jd.led i).x (jUnit n jd.jb.Lb 0), ofRatUp (jd.led i).r,
          ofRatUp (jd.led i).nb⟩ := by
      unfold jUp
      simp [JLed.node, hu]
    have h2 := jUp_sound BF he hup
    unfold JEnc jLay at h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    have hx : jetNodeL n jd i = pcMul (jd.led i).x (jUnit n jd.jb.Lb 0) := by
      simp only [jetNodeL, hu, ↓reduceIte, jUnitS_eq]
    have hl : jetLoadL jd i = mulLoad jd.jb.LU0 jd.jb.Lb (jd.led i).A (2 ^ 0) := by
      simp only [jetLoadL, hu, ↓reduceIte]
    rw [hx]
    rw [hl] at hA
    rw [hP] at h2
    exact h2.mono hA
  · have hu' : (jd.led i).u = false := by simpa using hu
    unfold JEnc jLay JLed.node at he
    simp only [hu', Bool.false_eq_true, ↓reduceIte] at he
    have hx : jetNodeL n jd i = (jd.led i).x := by simp only [jetNodeL, hu', Bool.false_eq_true,
      ↓reduceIte]
    have hl : jetLoadL jd i = (jd.led i).A := by simp only [jetLoadL, hu', Bool.false_eq_true,
      ↓reduceIte]
    rw [hx]
    rw [hl] at hA
    rw [hP] at he
    exact he.mono hA

omit [LawfulCertArith α] in
/-- **The packed jet check with lifted constants from its parts**: the book, each block, the order
certificate, the wanted slots exported and their lifted guards. -/
theorem jetCheckL_of {K : CertEmbedding α} {p : Slp} {jd : JetData} {B : ℕ} {wanted : List ℕ}
    (hb : jBookOk n W jd.jb = true)
    (hok : ∀ kb ∈ jd.kbs, (kb.toT (jd.L.look (α := α))).ok n W pe cfg jd.jb K p = true)
    (hord : orderOk jd.kbs jd.cert = true)
    (hex : (wanted.all fun j => jd.kbs.any fun kb => kb.exports.contains (slotK j)) = true)
    (hw : wanted.all (jetWantedOkL jd B) = true) :
    jetCheckL n W pe cfg K p jd B wanted = true := by
  simp only [jetCheckL, jetChainOk, hb, hord, hex, hw, Bool.and_true, Bool.true_and,
    List.all_eq_true]
  exact hok

omit [LawfulCertArith α] in
/-- **The check with lifted constants is unchanged by a correct front.** -/
theorem jetCheckL_withFront {K : CertEmbedding α} {p : Slp} {jd : JetData} {front : JLedger}
    (h : frontOk jd front = true) (B : ℕ) (wanted : List ℕ) :
    jetCheckL n W pe cfg K p (jd.withFront front) B wanted =
      jetCheckL n W pe cfg K p jd B wanted := by
  have hw : jetWantedOkL (jd.withFront front) B = jetWantedOkL jd B := by
    funext i
    simp only [jetWantedOkL, jetLoadL, JetData.led, JetData.withFront, lookup_withFront h]
    rfl
  rw [jetCheckL, jetCheckL, hw]
  simp only [jetChainOk, JetData.withFront, look_withFront h]

end Sound

end KAM.CertificateSharp.Packed
