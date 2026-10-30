/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs
public import KAM.Certificate.Arith.Rat

/-!
# Square-root tests

Kernel evaluations (exact rational backend, `n = 1`) of the `sqrt` primitive:

* the ball rule `ballSqrt`: the ball of `√z` on `|z - 4| ≤ 1/100` is centred within `10⁻⁶` of `2`
  with radius `≤ 1/100` and contains `√z` (`ballSqrt_sound`); balls touching the left half-plane
  fail closed;
* the composition witness `sqrtWitnessRadius`: the witness `W = 2` (anchor `2`, margin `1/10`) of
  `√4` passes, the opposite root `W = -2` and a negative anchor fail; a two-slot program
  `[4, √slot 0]` composes with a slot-keyed witness, and fails without it;
* the expression layer: `H = √I` on `|I - 1| < 1/10` passes `checkHamBounds` with `M = 2` and
  fails it with `M = 1/4` (the toy of `Tests/Defs`, data copied since its bodies are not exposed);
  `H = ½ √(I⁴)` passes with a loose bound, and its ball pass certifies `H.NonvanishingOn` (through
  `HamExpr.nonvanishingOn_of_balls`, i.e. the new `sqrt` safety extraction), and `√I` on a domain
  containing `I = 0` fails closed.
-/

public section

namespace KAM.Certificate

open CertArith

/-! ### Toy data (copied from `Tests/Defs` and `Tests/Ball`) -/

def sqrtToyW : CertWeight := ⟨1 / 100, 11 / 10⟩

def sqrtToyPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

def sqrtToyCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none,
    (((List.range 11).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [4, t, i, j, k]) ++
     ((List.range 2).flatMap fun t => (List.range 4).flatMap fun i => (List.range 4).flatMap
      fun j => (List.range 4).map fun k => [3, t, i, j, k]) ++
     ((List.range 32).map fun k => [0, k])).map fun key => (key, .direct)⟩

def sqrtToyCos (c a : ℚ) : CertRealPoly ℚ := ⟨c, [([1], ⟨a / 2, 0⟩)]⟩

def sqrtToyK : CertEmbedding ℚ := ⟨[-1], [sqrtToyCos 0 (1 / 10)], [0], [sqrtToyCos 1 (1 / 100)]⟩

def sqrtToyCC (A : List (List ℚ)) : List (List (CC ℚ)) := A.map fun row => row.map fun c => ⟨c, 0⟩

def sqrtTestParams (M : ℚ) : CertParams :=
  { tau := 1, rho := 1 / 100, rhoInf := 1 / 200, M := M, σK := 2, σB := 2 + 1 / 1000,
    σT := 4 + 1 / 1000, μ := 1 / 1000, γbar := 1, σω := 2, nuRay := 1 / 1000, γ := 1, s := 1,
    err := 1 / 2, E0 := 1 / 2, disp := 1 }

def sqrtTestCert (ham : HamExpr 1) (M : ℚ) : TorusCertificate 1 ℚ where
  params := sqrtTestParams M
  ham := ham
  weightH := ⟨1 / 20, 3 / 2⟩
  centre := [1]
  radius := [1 / 10]
  freqBox := [(1, 1 / 1000)]
  emb := sqrtToyK
  weight := sqrtToyW
  wit := ⟨[], [], [], []⟩
  gramInv := [[⟨[([-1], ⟨0, 1 / 10⟩), ([0], ⟨1, 0⟩), ([1], ⟨0, -1 / 10⟩)]⟩]]
  torsInv := sqrtToyCC [[0, 101 / 100], [1, -1]]
  cfgFull := sqrtToyCfg
  cfgLow := sqrtToyCfg
  piEnc := sqrtToyPi
  expHalvings := 0
  expOrder := 6

/-- The weight of `Tests/Ball` (`ρ = 1/4`, `e^{π/2} < 5`). -/
def sqrtBallWeight : CertWeight := ⟨1 / 4, 5⟩

theorem sqrtTest_ballWeight : checkWeight sqrtBallWeight 4 12 = true := by decide +kernel

/-! ### The ball rule -/

theorem sqrtTest_ball :
    (match ballSqrt slpBallPrec ⟨4, 0⟩ (1 / 100) with
    | some b => decide (|b.1.re - 2| ≤ 1 / 10 ^ 6 ∧ b.1.im = 0 ∧ b.2 ≤ 1 / 100)
    | none => false) = true := by
  decide +kernel

theorem sqrtTest_ball_isSome : (ballSqrt slpBallPrec ⟨4, 0⟩ (1 / 100)).isSome = true := by
  decide +kernel

theorem sqrtTest_ball_mem {z : ℂ} (hz : ‖z - CC.toC (⟨4, 0⟩ : CC ℚ)‖ ≤ ((1 / 100 : ℚ) : ℝ)) :
    ∃ b, ballSqrt slpBallPrec ⟨4, 0⟩ (1 / 100) = some b ∧ ‖sqrtE z - b.1.toC‖ ≤ (b.2 : ℝ) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp sqrtTest_ball_isSome
  exact ⟨b, hb, ballSqrt_sound slpBallPrec hb hz⟩

theorem sqrtTest_ball_left_fails : ballSqrt slpBallPrec ⟨-4, 0⟩ (1 / 100) = none := by
  decide +kernel

theorem sqrtTest_ball_axis_fails : ballSqrt slpBallPrec ⟨1 / 1000, 1⟩ (1 / 100) = none := by
  decide +kernel

/-- The anchor of a small radicand: `√(1/100) ≈ 1/10`. -/
theorem sqrtTest_anchor_small : |sqrtAnchor slpBallPrec (1 / 100) - 1 / 10| ≤ 1 / 10 ^ 30 := by
  decide +kernel

/-! ### The composition witness -/

def sqrtTestG : CertModel ℚ := constModel 1 4 0 0

def sqrtTestWit (w anchor : ℚ) : SqrtWitness ℚ := ⟨⟨[([0], ⟨w, 0⟩)]⟩, anchor, 1 / 10⟩

theorem sqrtTest_witness :
    (sqrtWitnessRadius 1 sqrtToyW sqrtToyCfg sqrtTestG (sqrtTestWit 2 2)).isSome = true := by
  decide +kernel

theorem sqrtTest_witness_opposite_root :
    sqrtWitnessRadius 1 sqrtToyW sqrtToyCfg sqrtTestG (sqrtTestWit (-2) 2) = none := by
  decide +kernel

theorem sqrtTest_witness_negative_anchor :
    sqrtWitnessRadius 1 sqrtToyW sqrtToyCfg sqrtTestG (sqrtTestWit (-2) (-2)) = none := by
  decide +kernel

/-- The model `⟨0, 2, r⟩` encloses `√4` on the strip. -/
theorem sqrtTest_witness_encloses :
    ∃ r, sqrtWitnessRadius 1 sqrtToyW sqrtToyCfg sqrtTestG (sqrtTestWit 2 2) = some r ∧
      (⟨0, (sqrtTestWit 2 2).poly, r⟩ : CertModel ℚ).Encloses 1 sqrtToyW.rho
        (fun _ => sqrtE (slpConstVal 4 0 0)) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp sqrtTest_witness
  have hW : checkWeight sqrtToyW 1 8 = true := by decide +kernel
  exact ⟨r, hr, (sqrtWitness_sound hW sqrtToyCfg (constModel_encloses 1 _ 4 0 0) rfl hr).2⟩

/-- The program `[4, √(slot 0)]`. -/
def sqrtTestProg : Slp := ⟨[.const 4 0 0, .sqrt 0]⟩

theorem sqrtTest_compose :
    (Slp.compose 1 sqrtTestProg sqrtToyK ⟨[], [], [], [(1, sqrtTestWit 2 2)]⟩ sqrtToyW sqrtToyCfg
      sqrtToyPi [1]).isSome = true := by
  decide +kernel

theorem sqrtTest_compose_missing_witness :
    Slp.compose 1 sqrtTestProg sqrtToyK ⟨[], [], [], [(0, sqrtTestWit 2 2)]⟩ sqrtToyW sqrtToyCfg
      sqrtToyPi [1] = none := by
  decide +kernel

/-! ### Expressions with a square root -/

/-- `H = ½ √(I⁴)` (`= I²/2` on `|I - 1| < 1/10`). -/
def sqrtTestH : HamExpr 1 :=
  .mul (.const (1 / 2)) (.sqrt (.mul (.mul (.action 0) (.action 0)) (.mul (.action 0) (.action 0))))

/-- `H = √I` on `|I - 1| < 1/10` passes `checkHamBounds` with `M = 2` and fails it with `M = 1/4`
(the first derivative is about `1/2` there). -/
theorem sqrtTest_ham : checkHamBounds (sqrtTestCert (.sqrt (.action 0)) 2) = true := by
  decide +kernel

theorem sqrtTest_ham_fail : checkHamBounds (sqrtTestCert (.sqrt (.action 0)) (1 / 4)) = false := by
  decide +kernel

/-- `½ √(I⁴)` passes with the loose bound `M = 1000`: the ball arithmetic of its third derivative
(`⅜ w⁵ f_a f_b f_c - ¼ w³ (cross terms) + ½ w f_abc`) overestimates the exact value `0`. -/
theorem sqrtTest_ham_quartic : checkHamBounds (sqrtTestCert sqrtTestH 1000) = true := by
  decide +kernel

theorem sqrtTest_balls :
    (sqrtTestH.jet.prog.balls 1 sqrtBallWeight [1] [1 / 10] 8).isSome = true := by
  decide +kernel

/-- The ball pass certifies the square-root operand on the domain. -/
theorem sqrtTest_nonvanishing :
    sqrtTestH.NonvanishingOn (certDomain 1 sqrtBallWeight.rho [1] [1 / 10]) := by
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp sqrtTest_balls
  exact HamExpr.nonvanishingOn_of_balls sqrtTestH sqrtTest_ballWeight hbs

theorem sqrtTest_balls_fail_closed :
    (HamExpr.sqrt (.action 0) : HamExpr 1).jet.prog.balls 1 sqrtBallWeight [0] [1 / 2] 8 =
      none := by
  decide +kernel

end KAM.Certificate
