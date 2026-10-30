/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs
public import KAM.Certificate.Arith.Rat

/-!
# Checker tests (`Defs`)

The toy of `Tests/Torsion` (data copied) (`n = 1`, `H = I²/2`, `K(θ) = (θ + U/2π, A)`) as a whole
`TorusCertificate 1 ℚ` on `D = T_{1/20} × {|I - 1| < 1/10}`: the sub-checks `checkHamBounds`,
`checkEmbedding`, `checkInvariance`, `checkEnergy`, `checkGram` and `checkTorsion` pass by
`decide +kernel`; the first four fail closed when their bound is tightened (negative Gram and
torsion tests are in `Tests/Torsion`). `checkStatic` (hence `checkTorusCertificate`) rejects the
toy (`n = 1`, `s = 1`); positive whole-checker and `checkSmallness` tests are the
toys `Tests/Toy2`, `Tests/Toy3`.
-/

public section

namespace KAM.Certificate

open CertArith

/-! ### The toy data (copied from `Tests/Torsion`, whose bodies are not exposed) -/

def defsToyW : CertWeight := ⟨1 / 100, 11 / 10⟩

def defsToyPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

/-- Every torsion, Gram and composition product key, advised `direct`. -/
def defsToyCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none,
    (((List.range 11).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [4, t, i, j, k]) ++
     ((List.range 2).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [3, t, i, j, k]) ++
     ((List.range 32).map fun k => [0, k])).map fun key => (key, .direct)⟩

/-- `c + a cos 2πθ` as real data. -/
def defsToyCos (c a : ℚ) : CertRealPoly ℚ := ⟨c, [([1], ⟨a / 2, 0⟩)]⟩

/-- `K(θ) = (θ + U/2π, A)`, `U = 0.1 cos 2πθ`, `A = 1 + 0.01 cos 2πθ`. -/
def defsToyK : CertEmbedding ℚ := ⟨[-1], [defsToyCos 0 (1 / 10)], [0], [defsToyCos 1 (1 / 100)]⟩

/-- `H = I²/2`. -/
def defsToyH : HamExpr 1 := .mul (.const (1 / 2)) (.mul (.action 0) (.action 0))

/-- The Gram witness `1 + 0.2 sin 2πθ`. -/
def defsToyB : List (List (CertPoly ℚ)) :=
  [[⟨[([-1], ⟨0, 1 / 10⟩), ([0], ⟨1, 0⟩), ([1], ⟨0, -1 / 10⟩)]⟩]]

def defsToyWit : Witnesses ℚ := ⟨[], [], [], []⟩

def defsToyBox : FreqBox := [(1, 1 / 1000)]

def defsToyCC (A : List (List ℚ)) : List (List (CC ℚ)) := A.map fun row => row.map fun c => ⟨c, 0⟩

/-- The averaging witness `≈ [[0, 1/0.99], [1, -0.985/0.99]]`. -/
def defsToyS : List (List (CC ℚ)) := defsToyCC [[0, 101 / 100], [1, -1]]

/-- The configuration of `Tests/Torsion` plus the invariance keys `[5, a, l]`. -/
def defsTestCfg : ModelConfig ℚ :=
  { defsToyCfg with
    advice := defsToyCfg.advice ++ ((List.range 2).flatMap fun a => (List.range 1).map fun l =>
      ([5, a, l], .direct)) }

def defsTestParams (M σK err E0 : ℚ) : CertParams :=
  { tau := 1, rho := 1 / 100, rhoInf := 1 / 200, M := M, σK := σK, σB := 2 + 1 / 1000,
    σT := 4 + 1 / 1000, μ := 1 / 1000, γbar := 1, σω := 2, nuRay := 1 / 1000, γ := 1, s := 1,
    err := err, E0 := E0, disp := 1 }

def defsTestCert (M σK err E0 : ℚ) (rH : ℚ := 1 / 10) : TorusCertificate 1 ℚ where
  params := defsTestParams M σK err E0
  ham := defsToyH
  weightH := ⟨1 / 20, 3 / 2⟩
  centre := [1]
  radius := [rH]
  freqBox := defsToyBox
  emb := defsToyK
  weight := defsToyW
  wit := defsToyWit
  gramInv := defsToyB
  torsInv := defsToyS
  cfgFull := defsTestCfg
  cfgLow := defsToyCfg
  piEnc := defsToyPi
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
