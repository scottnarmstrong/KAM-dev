/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroRotData
public import KAM.CertificateSharp.V2.Tests.Forced.MicroData
public import KAM.CertificateSharp.V2.Tests.Forced.Lemmas

/-!
# Drift mutations of the rotated normalization `MicroRot`

A normalization applied to only part of the data is rejected. Each mutation decides that the
rejecting landed sub-check, `checkInvariance`, is `false`, and `*_rejected` lifts that to the whole
v2 certifier at every engine and witness (`landedBase.check` is a conjunction containing it):
* `mut_unrotatedBox`: the rotated Hamiltonian and torus with `Micro`'s (unrotated) frequency box;
* `mut_unrotatedTorus`: the rotated Hamiltonian with `Micro`'s (unrotated) torus and witness.
The mirror (`scripts/certifier/forced/forced_rot.py`) rejects both as well
(`scripts/certifier/fixtures/forced-toy/MicroRot.json`, `mutations`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroRot

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The rotated certificate with `Micro`'s box. -/
def certUnrotatedBox : TorusCertificate 2 FB := { cert with freqBox := Micro.cert.freqBox }

/-- The rotated Hamiltonian with `Micro`'s torus and character witness. -/
def certUnrotatedTorus : TorusCertificate 2 FB :=
  { cert with emb := Micro.cert.emb, wit := Micro.cert.wit }

theorem mut_unrotatedBox : checkInvariance certUnrotatedBox = false := by decide +kernel

theorem mut_unrotatedTorus : checkInvariance certUnrotatedTorus = false := by decide +kernel

theorem landedBase_eq_false {c : TorusCertificate 2 FB} (h : checkInvariance c = false) :
    landedBase.check c = false := by
  show (checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c &&
    checkEnergy c && checkGram c && checkTorsion c) = false
  rw [h]
  simp

/-- The v2 certifier rejects the unrotated box at every engine and witness. -/
theorem unrotatedBox_rejected (E : EngineV2) (w : E.Wit) :
    checkTorusCertificateV2 E certUnrotatedBox w = false := by
  rw [checkV2_eq, landedBase_eq_false mut_unrotatedBox, Bool.false_and]

/-- The v2 certifier rejects the unrotated torus at every engine and witness. -/
theorem unrotatedTorus_rejected (E : EngineV2) (w : E.Wit) :
    checkTorusCertificateV2 E certUnrotatedTorus w = false := by
  rw [checkV2_eq, landedBase_eq_false mut_unrotatedTorus, Bool.false_and]

end KAM.CertificateSharp.V2.Forced.MicroRot

end
