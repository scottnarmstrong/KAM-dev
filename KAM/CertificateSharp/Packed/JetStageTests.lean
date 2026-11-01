/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetStage
public import KAM.CertificateSharp.Packed.JetTests

/-!
# Small kernel tests of the staged exponential (default build, cheap)

On the toy book of `JetTests` (`n = 2`, the `3 × 3` box at `CertFixed 64`), with `w = e^{i θ₀}/4`:
three staged Taylor steps from the constant `1` (`jTSteps`) give exactly the term and the partial
sum of `jTaylor` of degree `3`, and so do one step followed by two more (the staged chain resumes
from the ledger entries `(term, partial sum)`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.JetStageTests

open KAM KAM.Certificate KAM.CertificateSharp.Packed KAM.CertificateSharp.Packed.JetTests

/-- `w = e^{i θ₀} / 4` at scale `2^64` (key `(1, 0)` at slot `11`). -/
def nW : JNode F := ⟨false, 2 ^ 65, 64, ⟨2 ^ 62 * 2 ^ (200 * 11), 0⟩, ⟨0⟩, ⟨2 ^ 63⟩⟩

/-- Both pairs exist and agree exactly. -/
def samePair : Option (JNode F × JNode F) → Option (JNode F × JNode F) → Bool
  | some (t1, s1), some (t2, s2) =>
    jExportOk t1 t2 && jExportOk t2 t1 && jExportOk s1 s2 && jExportOk s2 s1
  | _, _ => false

/-- The staged steps from `jConstQ 1`. -/
def staged (k : ℕ) : Option (JNode F × JNode F) :=
  match jConstQ 2 tW tPe tCfg tJb 1 with
  | some o => jTSteps 2 tW tPe tCfg tJb nW 0 k o o
  | none => none

/-- One step, then two more from the result. -/
def resumed : Option (JNode F × JNode F) :=
  match staged 1 with
  | some (t, s) => jTSteps 2 tW tPe tCfg tJb nW 1 2 t s
  | none => none

example : samePair (staged 3) (jTaylor 2 tW tPe tCfg tJb nW 3) = true := by decide +kernel

example : samePair resumed (jTaylor 2 tW tPe tCfg tJb nW 3) = true := by decide +kernel

/-- A control: three steps are not two. -/
example : samePair (staged 2) (jTaylor 2 tW tPe tCfg tJb nW 3) = false := by decide +kernel

end KAM.CertificateSharp.Packed.JetStageTests
