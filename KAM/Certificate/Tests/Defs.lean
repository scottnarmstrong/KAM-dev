/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs
public import KAM.Certificate.Tests.Torsion

/-!
# Checker tests (`Defs`)

The toy of `Tests/Torsion` (`n = 1`, `H = I²/2`, `K(θ) = (θ + U/2π, A)`) as a whole
`TorusCertificate 1 ℚ` on `D = T_{1/20} × {|I - 1| < 1/10}`: the sub-checks `checkHamBounds`,
`checkEmbedding`, `checkInvariance`, `checkEnergy`, `checkGram` and `checkTorsion` pass by
`decide +kernel`; each fails closed when its bound is tightened. `checkStatic` (hence
`checkTorusCertificate`) rejects the toy (`n = 1`, `s = 1`).
-/

public section

namespace KAM.Certificate

/-- The configuration of `Tests/Torsion` plus the invariance keys `[5, a, l]`. -/
def defsTestCfg : ModelConfig ℚ :=
  { torsTestCfg with
    advice := torsTestCfg.advice ++ ((List.range 2).flatMap fun a => (List.range 1).map fun l =>
      ([5, a, l], .direct)) }

def defsTestParams (M σK err E0 : ℚ) : CertParams :=
  { tau := 1, rho := 1 / 100, rhoInf := 1 / 200, M := M, σK := σK, σB := 2 + 1 / 1000,
    σT := 4 + 1 / 1000, μ := 1 / 1000, γbar := 1, σω := 2, nuRay := 1 / 1000, γ := 1, s := 1,
    err := err, E0 := E0, disp := 1 }

def defsTestCert (M σK err E0 : ℚ) (rH : ℚ := 1 / 10) : TorusCertificate 1 ℚ where
  params := defsTestParams M σK err E0
  ham := torsTestH
  weightH := ⟨1 / 20, 3 / 2⟩
  centre := [1]
  radius := [rH]
  freqBox := torsTestBox
  emb := torsTestK
  weight := torsTestW
  wit := torsTestWit
  gramInv := torsTestB
  torsInv := torsTestS
  cfgFull := defsTestCfg
  cfgLow := torsTestCfg
  piEnc := torsTestPi
  expHalvings := 0
  expOrder := 6

theorem defsTest_ham : checkHamBounds (defsTestCert 2 2 (1 / 2) (1 / 2)) = true := by
  decide +kernel

theorem defsTest_ham_fail : checkHamBounds (defsTestCert 1 2 (1 / 2) (1 / 2)) = false := by
  decide +kernel

theorem defsTest_emb : checkEmbedding (defsTestCert 2 2 (1 / 2) (1 / 2)) = true := by
  decide +kernel

theorem defsTest_emb_fail : checkEmbedding (defsTestCert 2 (11 / 10) (1 / 2) (1 / 2)) = false ∧
    checkEmbedding (defsTestCert 2 2 (1 / 2) (1 / 2) (1 / 100)) = false := by
  decide +kernel

theorem defsTest_inv : checkInvariance (defsTestCert 2 2 (1 / 2) (1 / 2)) = true := by
  decide +kernel

theorem defsTest_inv_fail : checkInvariance (defsTestCert 2 2 (1 / 100) (1 / 2)) = false := by
  decide +kernel

theorem defsTest_energy : checkEnergy (defsTestCert 2 2 (1 / 100) (1 / 2)) = true := by
  decide +kernel

theorem defsTest_energy_fail : checkEnergy (defsTestCert 2 2 (1 / 100) (1 / 4)) = false := by
  decide +kernel

theorem defsTest_gram : checkGram (defsTestCert 2 2 (1 / 2) (1 / 2)) = true := by
  decide +kernel

theorem defsTest_torsion : checkTorsion (defsTestCert 2 2 (1 / 2) (1 / 2)) = true := by
  decide +kernel

theorem defsTest_static_fail : checkStatic (defsTestCert 2 2 (1 / 2) (1 / 2)) = false ∧
    checkTorusCertificate (defsTestCert 2 2 (1 / 2) (1 / 2)) = false := by
  decide +kernel

end KAM.Certificate
