/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Interface
public import KAM.Certificate.Arith.PiHigh

/-!
# `π` at backend precision

A `PiEnclosure α` is an enclosure `|π - centre| ≤ rad` at backend precision, validated against
the Machin rational enclosure `piLowRat k j < π < piUpRat k j` of `PiHigh`. The validation uses
the backend rounding errors: `centre - rad` is bounded above by `upAdd` of the computed value and
its `addErr`, and `centre + rad` is bounded below through `hi + addErr ≤ computed value`.
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-- An enclosure `|π - centre| ≤ rad` at backend precision, with the Machin parameters
`(machinK, machinJ)` that validate it. Used when models of different `2π`-degrees are added
(`CertModel.toDeg`) and for lower bounds of `(2π)^deg`, `deg < 0`. Data only. -/
structure PiEnclosure (α : Type) where
  centre : α
  rad : α
  machinK : ℕ
  machinJ : ℕ

/-- Validation: `centre - rad ≤ piLowRat k j` and `piUpRat k j ≤ centre + rad` (outward
conversions `ofRatDown`/`ofRatUp`, backend comparisons). -/
def checkPiEnclosure {α : Type} [CertArith α] (pe : PiEnclosure α) : Bool :=
  ble (upAdd (add pe.centre (neg pe.rad)) (addErr pe.centre (neg pe.rad)))
      (ofRatDown (piLowRat pe.machinK pe.machinJ)) &&
    ble (upAdd (ofRatUp (piUpRat pe.machinK pe.machinJ)) (addErr pe.centre pe.rad))
      (add pe.centre pe.rad)

theorem checkPiEnclosure_sound {α : Type} [CertArith α] [LawfulCertArith α] {pe : PiEnclosure α}
    (h : checkPiEnclosure pe = true) : |Real.pi - val pe.centre| ≤ val pe.rad := by
  simp only [checkPiEnclosure, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have a1 := LawfulCertArith.ble_sound _ _ h1
  have a2 := LawfulCertArith.ble_sound _ _ h2
  have u1 := LawfulCertArith.upAdd_ge (add pe.centre (neg pe.rad)) (addErr pe.centre (neg pe.rad))
  have u2 := LawfulCertArith.upAdd_ge (ofRatUp (piUpRat pe.machinK pe.machinJ))
    (addErr pe.centre pe.rad)
  have e1 := LawfulCertArith.add_err pe.centre (neg pe.rad)
  have e2 := LawfulCertArith.add_err pe.centre pe.rad
  have d1 := LawfulCertArith.ofRatDown_le (α := α) (piLowRat pe.machinK pe.machinJ)
  have d2 := LawfulCertArith.ofRatUp_ge (α := α) (piUpRat pe.machinK pe.machinJ)
  have n := LawfulCertArith.val_neg pe.rad
  have p1 := piLowRat_lt_pi pe.machinK pe.machinJ
  have p2 := pi_lt_piUpRat pe.machinK pe.machinJ
  rw [abs_le] at e1 e2 ⊢
  rw [n] at e1
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

end KAM.Certificate
