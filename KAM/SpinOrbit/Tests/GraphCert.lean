/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Cert
public import KAM.Certificate.Arith.Rat

/-!
# Tests of `checkSoGraph` (`ℚ` backend, `decide +kernel`)

Toy embedding (`n = 2`): `K(θ) = (θ₀ + U/2π, θ₁, A, 0)` with `U = cos 2πθ₀ / 10` and
`A = 1 + cos 2πθ₀ / 100`, so `∂_{θ₀} K_{.1 0} = 1 - sin 2πθ₀ / 10 ∈ [9/10, 11/10]` and
`K_{.2 0} ∈ [99/100, 101/100]`. The graph check passes with `mono = 4/5`, `[pLo, pHi] =
[97/100, 103/100]` and empty SOS witnesses, and fails closed when the monotonicity margin, the
range or the strict Cauchy margin `disp < mono ρ∞` is tightened. Only the fields read by
`checkSoGraph` are meaningful; the rest of the torus certificate is placeholder data.
-/

public section

namespace KAM.SpinOrbit

open KAM.Certificate CertArith

def graphToyW : CertWeight := ⟨1 / 100, 11 / 10⟩

def graphToyPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

def graphToyCfg : ModelConfig ℚ := ⟨100, 0, 0, fun _ _ => none, []⟩

/-- `c + a cos 2πθ₀` as real data in two angles. -/
def graphToyCos (c a : ℚ) : CertRealPoly ℚ := ⟨c, [([1, 0], ⟨a / 2, 0⟩)]⟩

def graphToyK : CertEmbedding ℚ :=
  ⟨[-1], [graphToyCos 0 (1 / 10)], [0], [graphToyCos 1 (1 / 100)]⟩

def graphToyParams (disp : ℚ) : CertParams :=
  { tau := 1, rho := 1 / 100, rhoInf := 1 / 200, M := 1, σK := 1, σB := 1, σT := 1, μ := 1,
    γbar := 1, σω := 2, nuRay := 1, γ := 1, s := 1, err := 0, E0 := 0, disp := disp }

def graphToyBase (disp : ℚ) : TorusCertificate 2 ℚ where
  params := graphToyParams disp
  ham := .const 0
  weightH := graphToyW
  centre := [0, 0]
  radius := [1, 1]
  freqBox := [(1, 0), (1, 0)]
  emb := graphToyK
  weight := graphToyW
  wit := ⟨[], [], [], []⟩
  gramInv := []
  torsInv := []
  cfgFull := graphToyCfg
  cfgLow := graphToyCfg
  piEnc := graphToyPi
  expHalvings := 0
  expOrder := 6

def graphToy (disp mono pLo pHi : ℚ) : SoGraphCert ℚ where
  base := graphToyBase disp
  mono := mono
  mono₀ := 1
  pLo := pLo
  pLo₀ := 1
  pHi := pHi
  pHi₀ := 1
  sosMono := ⟨[]⟩
  sosLo := ⟨[]⟩
  sosHi := ⟨[]⟩

theorem graphTest_pass :
    checkSoGraph (graphToy (1 / 1000) (4 / 5) (97 / 100) (103 / 100)) = true := by
  decide +kernel

theorem graphTest_mono_fail :
    checkSoGraph (graphToy (1 / 1000) (99 / 100) (97 / 100) (103 / 100)) = false := by
  decide +kernel

theorem graphTest_range_fail :
    checkSoGraph (graphToy (1 / 1000) (4 / 5) (999 / 1000) (103 / 100)) = false ∧
      checkSoGraph (graphToy (1 / 1000) (4 / 5) (97 / 100) (1001 / 1000)) = false := by
  decide +kernel

/-- `disp = 1/200 ≥ mono ρ∞ = 1/250`: the Cauchy margin fails. -/
theorem graphTest_margin_fail :
    checkSoGraph (graphToy (1 / 200) (4 / 5) (97 / 100) (103 / 100)) = false := by
  decide +kernel

end KAM.SpinOrbit
