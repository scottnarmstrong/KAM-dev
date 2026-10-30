/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Ham.TrigCertifier
public import KAM.Certificate.Tests.Toy2
public import KAM.Certificate.Tests.Toy3

/-!
# The cosh ball pass on the toys and on a cosine test model

* T2 and T3 have polynomial Hamiltonians: the cosh pass returns exactly the balls of the landed
  pass (`toyCert2_trig_eq`, `toyCert3_trig_eq`), so `checkHamBoundsTrig` agrees with
  `checkHamBounds`.
* `cosCert` is T2's certificate (strip `ρ_H = 451/50`) with `H = p₂ + p₁²/2 + (1/10) cos 2π(3θ₁ +
  θ₂)`. The five jet sums of the two passes differ by the factor `1/2`
  (`cosCert_sums_trig`, `cosCert_sums_disc`: `‖D²X_H‖ ≤ 1.69·10¹⁰¹` against `3.38·10¹⁰¹`), because
  a mode `c(χ_k + χ_{-k})` is bounded by `c(e^A + e^{-A})` and not by `2c e^A`. For `M = 2·10¹⁰¹`
  the cosh pass accepts and the disc pass rejects (`cosCert_trig_ok`, `cosCert_disc_fails`).
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM.Certificate

/-- A decidable view of a ball list. -/
def ballData (o : Option (List (CC ℚ × ℚ))) : Option (List (ℚ × ℚ × ℚ)) :=
  o.map fun l => l.map fun b => (b.1.re, b.1.im, b.2)

theorem toyCert2_trig_eq :
    ballData (ballsTrig 2 toyCert2.ham.jet.prog toyCert2.weightH toyCert2.centre toyCert2.radius
      toyCert2.expOrder) =
    ballData (toyCert2.ham.jet.prog.balls 2 toyCert2.weightH toyCert2.centre toyCert2.radius
      toyCert2.expOrder) := by decide +kernel

theorem toyCert3_trig_eq :
    ballData (ballsTrig 3 toyCert3.ham.jet.prog toyCert3.weightH toyCert3.centre toyCert3.radius
      toyCert3.expOrder) =
    ballData (toyCert3.ham.jet.prog.balls 3 toyCert3.weightH toyCert3.centre toyCert3.radius
      toyCert3.expOrder) := by decide +kernel

theorem toyCert2_trig_ham : checkHamBoundsTrig toyCert2 = true := by decide +kernel
theorem toyCert3_trig_ham : checkHamBoundsTrig toyCert3 = true := by decide +kernel

/-- T2 with a cosine mode in `H`. -/
def cosCert : TorusCertificate 2 ℚ :=
  { toyCert2 with
    ham := .add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
      (.mul (.const (1 / 10)) (.cosMode [3, 1]))) }

/-- The five jet sums of the cosh pass. -/
def cosSumsTrig : Option HamSplit :=
  (ballsTrig 2 cosCert.ham.jet.prog cosCert.weightH cosCert.centre cosCert.radius
    cosCert.expOrder).map (hamSums 4 cosCert.ham.jet)

/-- The five jet sums of the landed disc pass. -/
def cosSumsDisc : Option HamSplit :=
  (cosCert.ham.jet.prog.balls 2 cosCert.weightH cosCert.centre cosCert.radius
    cosCert.expOrder).map (hamSums 4 cosCert.ham.jet)

/-- Every cosh sum is at most `0.51` of the corresponding disc sum, and at least `0.49`. -/
theorem cosCert_sums_halved : (match cosSumsTrig, cosSumsDisc with
    | some t, some d => decide (t.dh * 100 ≤ 51 * d.dh ∧ 49 * d.dh ≤ t.dh * 100 ∧
        t.x * 100 ≤ 51 * d.x ∧ 49 * d.x ≤ t.x * 100 ∧
        t.dx * 100 ≤ 51 * d.dx ∧ 49 * d.dx ≤ t.dx * 100 ∧
        t.d2x * 100 ≤ 51 * d.d2x ∧ 49 * d.d2x ≤ t.d2x * 100 ∧
        t.d2h * 100 ≤ 51 * d.d2h ∧ 49 * d.d2h ≤ t.d2h * 100)
    | _, _ => false) = true := by decide +kernel

/-- `‖D²X_H‖` sums: cosh `< 1.7·10¹⁰¹`, disc `> 3.3·10¹⁰¹`. -/
theorem cosCert_d2x : (match cosSumsTrig, cosSumsDisc with
    | some t, some d => decide (t.d2x < 17 * 10 ^ 100 ∧ 33 * 10 ^ 100 < d.d2x)
    | _, _ => false) = true := by decide +kernel

/-- `cosCert` with `M = 2·10¹⁰¹`. -/
def cosCertM : TorusCertificate 2 ℚ :=
  { cosCert with params := { cosCert.params with M := 2 * 10 ^ 101 } }

theorem cosCert_trig_ok : checkHamBoundsTrig cosCertM = true := by decide +kernel

theorem cosCert_disc_fails : checkHamBounds cosCertM = false := by decide +kernel

/-- The split check accepts the measured sums of the cosh pass (and is exact for them). -/
theorem cosCert_split_ok : (match cosSumsTrig with
    | some t => checkHamBoundsTrigSplit cosCert t
    | none => false) = true := by decide +kernel

end KAM.CertificateSharp
