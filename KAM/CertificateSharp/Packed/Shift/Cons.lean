/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Shift.Base
public import KAM.CertificateSharp.Packed.JetConsEnergy

/-!
# Window-sized powers as shifts: the invariance and energy rows

The `DK` matrix `ptK` of the torsion, the invariance row `ivRowOk` (`JetConsInv.lean`) and the
energy test `enOk` (`JetConsEnergy.lean`) with the shift leaves of `Shift/Base.lean`, each equal to
the landed one (`…S_eq`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (box : FreqBox) (s : ℚ) (J : HamJet)
  (js : JSlots α) (ib : PIBook) (mm : PGramMemo)

/-- `ptK` with shifts. -/
def ptKS (W : CertWeight) (tb : PTorsBook) (mm : PGramMemo) : PMat α :=
  ⟨fun r a => ⟨packOf tb.L1 (mm.reAt r a), packOf tb.L1 (mm.imAt r a)⟩,
    fun r a => ofRatUp (mm.radAt r a),
    fun r a => pnormS W tb.q tb.lK tb.L1 tb.P
      ⟨packOf tb.L1 (mm.reAt r a), packOf tb.L1 (mm.imAt r a)⟩⟩

/-- `ivDK` with shifts. -/
def ivDKS (a : ℕ) : PC :=
  pcSumN (fun l => pcMul ((ptKS (α := α) W ib.toT mm).x a l) (ptF n box s ib.toT l)) n

/-- `ivX` with shifts. -/
def ivXS (a : ℕ) : PC :=
  pcAdd (pcMul (ivXH n J js a) (pcUnitS ib.LU0.width (zslot n ib.LU0) (2 ^ ib.P)))
    (pcNeg (ivDKS (α := α) n W box s ib mm a))

/-- `ivR` with shifts. -/
def ivRS (a : ℕ) : α :=
  upAdd (js.r (ivSlot n J a)) (sumUp (fun l => pmulRad ((ptKS (α := α) W ib.toT mm).nb a l)
    ((ptKS (α := α) W ib.toT mm).r a l) (ofRatUp (|(ptFc box s ib.toT l : ℚ)| / 2 ^ ib.P))
    (ofRatUp (ptFr box s ib.toT l))) (List.range n))

/-- `ivRowOk` with shifts. -/
def ivRowOkS (err : ℚ) (a : ℕ) : Bool :=
  ble (upAdd (pnormS W ib.q ib.lI ib.LI (ib.P + ib.P) (ivXS n W box s J js ib mm a))
    (ivRS n W box s J js ib mm a)) (ofRatDown err)

/-- `enOk` with shifts. -/
def enOkS (E0 err : ℚ) : Bool :=
  ble (upAdd (ofRatUp (|(ptDigitS n ib.Lb ib.P (js.x J.v0)).1 - E0| +
      |(ptDigitS n ib.Lb ib.P (js.x J.v0)).2|)) (js.r J.v0)) (ofRatDown err)

end Defs

section Eq

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (box : FreqBox) (s : ℚ) (J : HamJet)
  (js : JSlots α) (ib : PIBook) (mm : PGramMemo)

theorem ptKS_eq (tb : PTorsBook) : ptKS (α := α) W tb mm = ptK W tb mm := by
  simp only [ptKS, ptK, pnormS_eq]

theorem ivDKS_eq (a : ℕ) : ivDKS (α := α) n W box s ib mm a = ivDK (α := α) n W box s ib mm a := by
  simp only [ivDKS, ivDK, ptKS_eq]

theorem ivXS_eq (a : ℕ) : ivXS n W box s J js ib mm a = ivX n W box s J js ib mm a := by
  simp only [ivXS, ivX, ivDKS_eq, pcUnitS_eq]

theorem ivRS_eq (a : ℕ) : ivRS n W box s J js ib mm a = ivR n W box s J js ib mm a := by
  simp only [ivRS, ivR, ptKS_eq]

theorem ivRowOkS_eq (err : ℚ) (a : ℕ) :
    ivRowOkS n W box s J js ib mm err a = ivRowOk n W box s J js ib mm err a := by
  simp only [ivRowOkS, ivRowOk, pnormS_eq, ivXS_eq, ivRS_eq]

theorem enOkS_eq (E0 err : ℚ) : enOkS n J js ib E0 err = enOk n J js ib E0 err := by
  simp only [enOkS, enOk, ptDigitS_eq]

end Eq

end KAM.CertificateSharp.Packed
