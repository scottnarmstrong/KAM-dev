/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs
public import KAM.Certificate.Arith.Rat

/-!
# Negative tests of the checker

Every check below is decided by `decide +kernel` (kernel reduction only), in `ℚ`.

**The base `negBase`** (`n = 2`, `τ = 1`) is the checker-only toy TR on a small strip:
`H = J + p²/2` (`p = I₀`, `J = I₁`), `K(θ) = (θ, (1/2, -1/8))`, the exact box `(1/4, 1/2)`,
`s = 2`, zero error (`X_H ∘ K = (1/2, 1) = 2 ω` exactly), Gram witness `B = I`, the exact torsion
inverse `S`. It passes `checkTorusCertificate` (`negBase_passes`); TR's resonant box admits no
Diophantine premise, so it exercises the checker only.

**Variants.** `negDiv` (`H = J + (p²/2)(p/p)`, reciprocal witness `Q = 2`, exact at
`p ∘ K = 1/2`) passes the whole checker too. `negExp` (`H = J + (p²/2) exp 0`, exp witness
`E = 1`) and `negChar` (`H = J + p²/2 + cos 2πq / 1000`, `U₀ = 1/4`, character witness `E = i`)
carry nonzero composition radii; their base controls are the intended sub-check at a loose error.

The ten items, each `checkTorusCertificate _ = false` and the intended sub-check `= false`:
1. a false residual bound (box centre `1/5`, `err = 0`): `checkInvariance`;
2. Gram witness `B = 0` (`δ = 1`) or `B = 2I` (`δ ≥ 1`): `checkGram`; torsion witness `S = 0`:
   `checkTorsion`;
3. `μ = 0`: `checkStatic`;
4. an exp witness with a wrong mean (`E = 2`): the pin radius fails `checkInvariance`;
5. `w = 1 < e^{2πρ}`: `checkWeight`, hence `checkStatic`;
6. (div) the denominator ball `p ∈ 1/2 ± 1` contains `0` on `D`: `checkHamBounds`; the reciprocal
   witness `Q = 0` (`δ = 1`) fails the composition, hence `checkInvariance`;
7. (box) a box `(0 ± 1, 0 ± 1)` that does not exclude `0`, or `ν = 6/10 > (s - 1) L = 1/2`:
   `checkStatic`;
8. (`π`) a `π` enclosure narrower than the Machin bounds: `checkPiEnclosure`, hence `checkStatic`;
9. (shape) at `n = 1` (the toy of `Tests/Defs`), the self-inverse `3 × 3` permutation as the
   torsion witness fails `torsionAvgCheck 1`, hence `checkTorsion`, although it is a valid inverse
   pair with zero defect;
10. (pin) the character pin `exp(2πi · 1/4)` (`|2π/4| > 1`) at `pinHalvings = 0` fails
   `Slp.compose`, hence `checkInvariance`; with `pinHalvings = 2` the composition succeeds.
-/

public section

namespace KAM.Certificate

open CertArith

/-! ### The base certificate -/

/-- Every product key the toys use, advised `direct`: torsion `[4, …]`, Gram `[3, …]`,
invariance `[5, a, l]`, composition `[0, slot]`, witnesses `[1, i, j]`, `[1, j]`, `[2, i]`,
`[2]`. -/
def negCfg : ModelConfig ℚ :=
  ⟨1000, 10, 4, fun _ _ => none,
    (((List.range 11).flatMap fun t => (List.range 3).flatMap fun i => (List.range 3).flatMap
      fun j => (List.range 4).map fun k => [4, t, i, j, k]) ++
     ((List.range 2).flatMap fun t => (List.range 2).flatMap fun i => (List.range 2).flatMap
      fun j => (List.range 4).map fun k => [3, t, i, j, k]) ++
     ((List.range 4).flatMap fun a => (List.range 2).map fun l => [5, a, l]) ++
     ((List.range 60).map fun k => [0, k]) ++ [[1, 0, 0], [1, 1, 0], [1, 0], [2, 0], [2]]).map
      fun key => (key, .direct)⟩

/-- `K(θ) = (θ + U, A)` with constant `U = (u, 0)`, `A = (1/2, -1/8)`. -/
def negK (u : ℚ) : CertEmbedding ℚ :=
  ⟨[0, 0], [⟨u, []⟩, ⟨0, []⟩], [0, 0], [⟨1 / 2, []⟩, ⟨-1 / 8, []⟩]⟩

/-- `H = J + p²/2`. -/
def negH : HamExpr 2 := .add (.action 1) (.mul (.const (1 / 2)) (.pow (.action 0) 2))

/-- The constant polynomial `c`. -/
def negConst (c : CC ℚ) : CertPoly ℚ := ⟨[([0, 0], c)]⟩

/-- Gram witness `c I`. -/
def negB (c : ℚ) : List (List (CertPoly ℚ)) :=
  [[negConst ⟨c, 0⟩, ⟨[]⟩], [⟨[]⟩, negConst ⟨c, 0⟩]]

def negCC (A : List (List ℚ)) : List (List (CC ℚ)) := A.map fun row => row.map fun c => ⟨c, 0⟩

/-- The exact inverse of the averaged extended torsion matrix (TR's witness). -/
def negS : List (List (CC ℚ)) := negCC [[1, -1 / 2, 0], [-1 / 2, 1 / 4, 1], [0, 1, 0]]

def negParams : CertParams :=
  { tau := 1, rho := 1 / 100, rhoInf := 1 / 200, M := 2, σK := 2, σB := 2, σT := 2,
    μ := 1 / 100, γbar := 1, σω := 3, nuRay := 49 / 100, γ := 1, s := 2, err := 0, E0 := 0,
    disp := 0 }

def negPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

def negBase : TorusCertificate 2 ℚ where
  params := negParams
  ham := negH
  weightH := ⟨1 / 20, 3 / 2⟩
  centre := [1 / 2, -1 / 8]
  radius := [1 / 50, 1 / 50]
  freqBox := [(1 / 4, 0), (1 / 2, 0)]
  emb := negK 0
  weight := ⟨1 / 100, 11 / 10⟩
  wit := ⟨[], [], [], []⟩
  gramInv := negB 1
  torsInv := negS
  cfgFull := negCfg
  cfgLow := negCfg
  piEnc := negPi
  expHalvings := 0
  expOrder := 6

theorem negBase_passes : checkTorusCertificate negBase = true := by decide +kernel

/-! ### 1. A false residual bound -/

/-- The box centre `1/5` instead of `1/4`: the residual `2 · 1/20` exceeds `err = 0`. -/
def negResidual : TorusCertificate 2 ℚ := { negBase with freqBox := [(1 / 5, 0), (1 / 2, 0)] }

theorem negResidual_fails :
    checkInvariance negResidual = false ∧ checkTorusCertificate negResidual = false := by
  decide +kernel

/-! ### 2. Gram and torsion witnesses -/

theorem negGramZero_fails :
    checkGram { negBase with gramInv := negB 0 } = false ∧
      checkTorusCertificate { negBase with gramInv := negB 0 } = false := by
  decide +kernel

theorem negGramTwo_fails :
    checkGram { negBase with gramInv := negB 2 } = false ∧
      checkTorusCertificate { negBase with gramInv := negB 2 } = false := by
  decide +kernel

theorem negTorsZero_fails :
    checkTorsion { negBase with torsInv := negCC [[0, 0, 0], [0, 0, 0], [0, 0, 0]] } = false ∧
      checkTorusCertificate
        { negBase with torsInv := negCC [[0, 0, 0], [0, 0, 0], [0, 0, 0]] } = false := by
  decide +kernel

/-! ### 3. `μ = 0` -/

theorem negMu_fails :
    checkStatic { negBase with params := { negParams with μ := 0 } } = false ∧
      checkTorusCertificate { negBase with params := { negParams with μ := 0 } } = false := by
  decide +kernel

/-! ### 4. An exp witness with a wrong mean -/

/-- `H = J + (p²/2) exp 0`. -/
def negExpH : HamExpr 2 :=
  .add (.action 1) (.mul (.mul (.const (1 / 2)) (.pow (.action 0) 2)) (.exp (.const 0)))

/-- The exp variant with witness `E` (constant) and error `err`. -/
def negExp (E err : ℚ) : TorusCertificate 2 ℚ :=
  { negBase with
    ham := negExpH
    wit := ⟨[⟨negConst ⟨E, 0⟩, 0, 6⟩], [], [], []⟩
    params := { negParams with err := err } }

/-- Control: the correct witness `E = 1` certifies the residual at `err = 1/1000`. -/
theorem negExp_control : checkInvariance (negExp 1 (1 / 1000)) = true := by decide +kernel

theorem negExp_fails :
    checkInvariance (negExp 2 (1 / 1000)) = false ∧
      checkTorusCertificate (negExp 2 (1 / 1000)) = false := by
  decide +kernel

/-! ### 5. `w < e^{2πρ}` -/

theorem negWeight_fails :
    checkWeight ⟨1 / 100, 1⟩ 0 6 = false ∧
      checkStatic { negBase with weight := ⟨1 / 100, 1⟩ } = false ∧
      checkTorusCertificate { negBase with weight := ⟨1 / 100, 1⟩ } = false := by
  decide +kernel

/-! ### 6. Division -/

/-- `H = J + (p²/2)(p/p)`. -/
def negDivH : HamExpr 2 :=
  .add (.action 1) (.mul (.mul (.const (1 / 2)) (.pow (.action 0) 2)) (.div (.action 0)
    (.action 0)))

/-- The division variant: reciprocal witness `Q`, action radius `r₀` of `p`, `M = 150` (the
ball bound of `‖D²X_H‖` is about `113`). -/
def negDiv (Q : CertPoly ℚ) (r₀ : ℚ) : TorusCertificate 2 ℚ :=
  { negBase with
    ham := negDivH
    wit := ⟨[], [Q], [], []⟩
    radius := [r₀, 1 / 50]
    params := { negParams with M := 150 } }

theorem negDiv_passes : checkTorusCertificate (negDiv (negConst ⟨2, 0⟩) (1 / 50)) = true := by
  decide +kernel

/-- `p ∈ 1/2 ± 1` on `D`: the denominator ball contains `0`. -/
theorem negDivBall_fails :
    checkHamBounds (negDiv (negConst ⟨2, 0⟩) 1) = false ∧
      checkTorusCertificate (negDiv (negConst ⟨2, 0⟩) 1) = false := by
  decide +kernel

/-- The reciprocal witness `Q = 0` (`δ = 1`) fails the composition. -/
theorem negDivWit_fails :
    checkInvariance (negDiv ⟨[]⟩ (1 / 50)) = false ∧
      checkTorusCertificate (negDiv ⟨[]⟩ (1 / 50)) = false := by
  decide +kernel

/-! ### 7. The box and the ray margins -/

theorem negBoxZero_fails :
    checkStatic { negBase with freqBox := [(0, 1), (0, 1)] } = false ∧
      checkTorusCertificate { negBase with freqBox := [(0, 1), (0, 1)] } = false := by
  decide +kernel

theorem negRay_fails :
    checkStatic { negBase with params := { negParams with nuRay := 6 / 10 } } = false ∧
      checkTorusCertificate
        { negBase with params := { negParams with nuRay := 6 / 10 } } = false := by
  decide +kernel

/-! ### 8. A narrow `π` enclosure -/

/-- `π ∈ 3.14159 ± 10⁻⁷`, narrower than the Machin bounds at `(5, 2)`. -/
def negPiNarrow : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10 ^ 7, 5, 2⟩

theorem negPi_fails :
    checkPiEnclosure negPiNarrow = false ∧
      checkStatic { negBase with piEnc := negPiNarrow } = false ∧
      checkTorusCertificate { negBase with piEnc := negPiNarrow } = false := by
  decide +kernel

/-! ### 9. A `3 × 3` torsion witness at `n = 1` -/

/-- The `n = 1` toy of `Tests/Defs` (data copied: its bodies are not exposed). -/
def negOneW : CertWeight := ⟨1 / 100, 11 / 10⟩

def negOnePi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

/-- Every torsion, Gram and composition product key, advised `direct`. -/
def negOneCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none,
    (((List.range 11).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [4, t, i, j, k]) ++
     ((List.range 2).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [3, t, i, j, k]) ++
     ((List.range 32).map fun k => [0, k])).map fun key => (key, .direct)⟩

/-- `c + a cos 2πθ` as real data. -/
def negOneCos (c a : ℚ) : CertRealPoly ℚ := ⟨c, [([1], ⟨a / 2, 0⟩)]⟩

/-- `K(θ) = (θ + U/2π, A)`, `U = 0.1 cos 2πθ`, `A = 1 + 0.01 cos 2πθ`. -/
def negOneK : CertEmbedding ℚ := ⟨[-1], [negOneCos 0 (1 / 10)], [0], [negOneCos 1 (1 / 100)]⟩

/-- `H = I²/2`. -/
def negOneH : HamExpr 1 := .mul (.const (1 / 2)) (.mul (.action 0) (.action 0))

/-- The Gram witness `1 + 0.2 sin 2πθ`. -/
def negOneB : List (List (CertPoly ℚ)) :=
  [[⟨[([-1], ⟨0, 1 / 10⟩), ([0], ⟨1, 0⟩), ([1], ⟨0, -1 / 10⟩)]⟩]]

def negOneWit : Witnesses ℚ := ⟨[], [], [], []⟩

def negOneBox : FreqBox := [(1, 1 / 1000)]

def negOneCC (A : List (List ℚ)) : List (List (CC ℚ)) := A.map fun row => row.map fun c => ⟨c, 0⟩

/-- The averaging witness `≈ [[0, 1/0.99], [1, -0.985/0.99]]`. -/
def negOneS : List (List (CC ℚ)) := negOneCC [[0, 101 / 100], [1, -1]]

/-- The configuration of `Tests/Torsion` plus the invariance keys `[5, a, l]`. -/
def negOneTestCfg : ModelConfig ℚ :=
  { negOneCfg with
    advice := negOneCfg.advice ++ ((List.range 2).flatMap fun a => (List.range 1).map fun l =>
      ([5, a, l], .direct)) }

def negOneTestParams (M σK err E0 : ℚ) : CertParams :=
  { tau := 1, rho := 1 / 100, rhoInf := 1 / 200, M := M, σK := σK, σB := 2 + 1 / 1000,
    σT := 4 + 1 / 1000, μ := 1 / 1000, γbar := 1, σω := 2, nuRay := 1 / 1000, γ := 1, s := 1,
    err := err, E0 := E0, disp := 1 }

def negOneTestCert (M σK err E0 : ℚ) (rH : ℚ := 1 / 10) : TorusCertificate 1 ℚ where
  params := negOneTestParams M σK err E0
  ham := negOneH
  weightH := ⟨1 / 20, 3 / 2⟩
  centre := [1]
  radius := [rH]
  freqBox := negOneBox
  emb := negOneK
  weight := negOneW
  wit := negOneWit
  gramInv := negOneB
  torsInv := negOneS
  cfgFull := negOneTestCfg
  cfgLow := negOneCfg
  piEnc := negOnePi
  expHalvings := 0
  expOrder := 6

theorem negOne_torsion : checkTorsion (negOneTestCert 2 2 (1 / 2) (1 / 2)) = true := by
  decide +kernel

/-- The self-inverse `A = [1 0 0; 0 0 1; 0 1 0]`. -/
def negPerm3 : List (List (CC ℚ)) := negCC [[1, 0, 0], [0, 0, 1], [0, 1, 0]]

/-- `A` is a valid inverse pair with itself (zero defect). -/
theorem negPerm3_selfInverse :
    (List.range 3).all (fun i => (List.range 3).all fun j =>
      decide ((((List.range 3).map fun k =>
        ((negPerm3.getD i []).getD k ⟨0, 0⟩).re * ((negPerm3.getD k []).getD j ⟨0, 0⟩).re).sum) =
          if i = j then 1 else 0)) = true := by
  decide +kernel

/-- The toy of `Tests/Defs` (whose `checkTorsion` passes) with the witness `A`. -/
theorem negPerm3_fails :
    checkTorsion { negOneTestCert 2 2 (1 / 2) (1 / 2) with torsInv := negPerm3 } = false ∧
      checkTorusCertificate
        { negOneTestCert 2 2 (1 / 2) (1 / 2) with torsInv := negPerm3 } = false := by
  decide +kernel

/-! ### 10. A large character pin -/

/-- `H = J + p²/2 + cos 2πq / 1000`. -/
def negCharH : HamExpr 2 :=
  .add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
    (.mul (.const (1 / 1000)) (.cosMode [1, 0])))

/-- `U₀ = 1/4`: the pin `exp(2πi/4) = i` (witness `E = i`, exact) with `|2π/4| > 1`;
`h` pin halvings; `err = 1/100` covers the perturbation. -/
def negChar (h : ℕ) : TorusCertificate 2 ℚ :=
  { negBase with
    ham := negCharH
    emb := negK (1 / 4)
    wit := ⟨[], [], [([1, 0], ⟨negConst ⟨0, 1⟩, h, 20⟩)], []⟩
    params := { negParams with err := 1 / 100 } }

/-- The composition of the invariance slots. -/
def negCharCompose (h : ℕ) : Option (List (CertModel ℚ)) :=
  Slp.compose 2 negCharH.jet.prog (negK (1 / 4)) (negChar h).wit (negChar h).weight negCfg negPi
    (d1Slots 2 negCharH.jet)

theorem negChar_pin_fails :
    negCharCompose 0 = none ∧ checkInvariance (negChar 0) = false ∧
      checkTorusCertificate (negChar 0) = false := by
  decide +kernel

/-- With a sufficient count the same certificate passes that pin (and the invariance bound). -/
theorem negChar_pin_passes :
    (negCharCompose 2).isSome = true ∧ checkInvariance (negChar 2) = true := by
  decide +kernel

end KAM.Certificate
