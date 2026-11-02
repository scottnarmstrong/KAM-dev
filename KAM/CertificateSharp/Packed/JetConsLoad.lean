/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetConsInv

/-!
# The jet's load bound at the consumers

The consumers call the jet check with their own books' load bounds (`jetLowOk`: `rb.bA`, the
torsion book's guarded load; `jetFullOk`: `ib.bJ`), while a chain theorem is stated at the
generator's bound (the largest load of a wanted node). The bound enters `jetCheck` only through
`jetWantedOk`, monotonically:

* `jetCheck_mono`: a passing jet check passes at every larger load bound;
* `jetLowOk_of`, `jetFullOk_of`: the consumers' jet conjuncts from a jet check at any bound below
  the book's, with the box and scale agreement (agreed with kamx-packed, AUDIT-V2-PACKED-CONS-1 L1).
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate

variable {n : ℕ} {α : Type} [CertArith α]

/-- **A passing jet check passes at every larger load bound.** -/
theorem jetCheck_mono {W : CertWeight} {pe : PiEnclosure α} {cfg : ModelConfig α}
    {K : CertEmbedding α} {p : Slp} {jd : JetData} {B B' : ℕ} {ws : List ℕ}
    (h : jetCheck n W pe cfg K p jd B ws = true) (hB : B ≤ B') :
    jetCheck n W pe cfg K p jd B' ws = true := by
  simp only [jetCheck, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun i hi => ?_⟩
  have hw := h.2 i hi
  simp only [jetWantedOk, Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
  exact ⟨hw.1, hw.2.trans hB⟩

/-- The torsion's jet conjunct from a jet check at any load bound at most `rb.bA`. -/
theorem jetLowOk_of {c : TorusCertificate n α} {rb : PRBook} {jd : JetData} {B : ℕ}
    (hL : layoutEq jd.jb.Lb rb.Lb = true) (hP : jd.jb.P = rb.P)
    (hj : jetCheck n c.weight c.piEnc c.cfgLow c.emb c.ham.jet.prog jd B
      (torsionSlots n c.ham.jet) = true) (hB : B ≤ rb.bA) :
    jetLowOk rb jd c = true := by
  simp only [jetLowOk, hL, hP, beq_self_eq_true, jetCheck_mono hj hB, Bool.and_self]

/-- The invariance and energy jet conjunct from a jet check at any load bound at most `ib.bJ`. -/
theorem jetFullOk_of {c : TorusCertificate n α} {ib : PIBook} {jd : JetData} {B : ℕ}
    (hL : layoutEq jd.jb.Lb ib.Lb = true) (hP : jd.jb.P = ib.P)
    (hj : jetCheck n c.weight c.piEnc c.cfgFull c.emb c.ham.jet.prog jd B
      (c.ham.jet.v0 :: d1Slots n c.ham.jet) = true) (hB : B ≤ ib.bJ) :
    jetFullOk ib jd c = true := by
  simp only [jetFullOk, hL, hP, beq_self_eq_true, jetCheck_mono hj hB, Bool.and_self]

end KAM.CertificateSharp.Packed
