/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.SegChain
public import KAM.Certificate.Defs

/-!
# Segmented composition: the certificate bridges (SO-CSEG-B)

The landed `checkInvariance` and `checkEnergy` from a composition equation
(`checkInvariance_eq_of_compose`, `checkEnergy_eq_of_compose`, proved by rewriting the landed
bodies), and the two assembly templates that the generated lunar modules instantiate:
`checkEnergy_of_ckpt` and `checkInvariance_of_ckpt`. Both take the same plan proof `hplan` and
segment proofs `hseg` of the cfgFull chain over the literal jet `J` (`hjet : c.ham.jet = J`, the jet
bridge M0) and differ only in the projection check `hw` and the residual (the energy test, or one
theorem per derivative row).
-/

@[expose] public section

namespace KAM.Certificate

open KAM KAM.CertificateSharp CertArith

variable {α : Type} [CertArith α] {n : ℕ}

theorem all_range_of_lt {f : ℕ → Bool} {m : ℕ} (h : ∀ a < m, f a = true) :
    (List.range m).all f = true := by
  simp only [List.all_eq_true, List.mem_range]
  exact h

theorem checkInvariance_eq_of_compose {c : TorusCertificate n α} {ms : List (CertModel α)}
    (h : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms) :
    checkInvariance c = (List.range (n + n)).all fun a =>
      ble ((invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms a).supBound
        c.weight) (ofRatDown c.params.err) := by
  simp only [checkInvariance, h]

theorem checkEnergy_eq_of_compose {c : TorusCertificate n α} {m : CertModel α}
    (h : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      [c.ham.jet.v0] = some [m]) :
    checkEnergy c = energyOk n c.weight c.piEnc m c.params.E0 c.params.err := by
  simp only [checkEnergy, h]

/-- **Assembly template: energy** (the generated `lower_energy` instantiates it). One plan proof
`hplan` and the segment proofs `hseg` are shared with invariance; only `hw` changes. -/
theorem checkEnergy_of_ckpt [DecidableEq α] {c : TorusCertificate n α} {J : HamJet}
    (hjet : c.ham.jet = J) (C : ComposeCkpt α)
    (hplan : C.planOk J.prog.ops.length = true)
    (hseg : ∀ j < C.segs.length,
      C.segOk n J.prog.ops c.emb c.wit c.weight c.cfgFull c.piEnc j = true)
    (hw : C.wantedOk [J.v0] = true)
    (hen : energyOk n c.weight c.piEnc (C.slotPair c.weight J.v0).1 c.params.E0 c.params.err =
      true) :
    checkEnergy c = true := by
  have h := ComposeCkpt.compose_eq n c.emb c.wit c.weight c.cfgFull c.piEnc C hplan hseg hw
  rw [← hjet] at h
  rw [checkEnergy_eq_of_compose (m := (C.slotPair c.weight J.v0).1) (by rw [h, hjet]; rfl)]
  exact hen

/-- **Assembly template: invariance**, from the shared chain and one theorem per row. -/
theorem checkInvariance_of_ckpt [DecidableEq α] {c : TorusCertificate n α} {J : HamJet}
    (hjet : c.ham.jet = J) (C : ComposeCkpt α)
    (hplan : C.planOk J.prog.ops.length = true)
    (hseg : ∀ j < C.segs.length,
      C.segOk n J.prog.ops c.emb c.wit c.weight c.cfgFull c.piEnc j = true)
    (hw : C.wantedOk (d1Slots n J) = true)
    (hrow : ∀ a < n + n, ble ((invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull
      c.piEnc ((d1Slots n J).map fun i => (C.slotPair c.weight i).1) a).supBound c.weight)
      (ofRatDown c.params.err) = true) :
    checkInvariance c = true := by
  have h := ComposeCkpt.compose_eq n c.emb c.wit c.weight c.cfgFull c.piEnc C hplan hseg hw
  rw [← hjet] at h
  rw [checkInvariance_eq_of_compose h]
  rw [hjet]
  exact all_range_of_lt hrow

end KAM.Certificate
