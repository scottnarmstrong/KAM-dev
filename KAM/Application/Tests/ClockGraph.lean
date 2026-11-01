/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.ClockGraphCheck
public import KAM.Certificate.Tests.Toy2

/-!
# Tests of the clock-triangular graph adapter (`ℚ` backend, `decide +kernel`)

* **Clock check** on the toy T2 (`H = I₁ + I₀²/2`): angle `1` is a clock of slope `1`
  (`checkClock toyCert2 0 1`); wrong free angle, wrong slope and unsupported shapes fail closed.
* **Diagonal checks** on T2's data with one angle mode added to `U₀` (`clockProbe k a`, not a
  certified torus, only the checks are exercised):
  - an off-diagonal mode `k = (0, 1)`, `a = 1/10`: `sup |∂₁ U₀| = 4π/10 > 1`, so the near-identity
    check `checkAngleGraphReal` fails for every `δ < 1`, while both clock checks pass at
    `mono = 99/100` (the diagonal `∂₀ U₀` vanishes);
  - a diagonal mode `k = (1, 0)`, `a = 1/100`: `sup_ℝ |∂₀ U₀| = 4π/100 ≈ 0.126`; the real check
    passes at `mono = 4/5` and fails at `9/10`; the SOS check with an empty witness fails at
    `4/5` (its residual is measured in the strip weight, `ρ = 9`);
  - the margin `disp < mono ρ∞` fails at `mono = 0`.
* **Full chain** on the certified torus T2 (`toyCert2_torus`, `ω* = (ν₋/2, 1/2)`):
  `CertifiedTorus.exists_clockGraph_of_checks` through either diagonal check gives an exact torus
  whose real restriction is a clock-triangular analytic graph over the angles, with the clock
  frequency `s∞ ω*₁ = 1`, i.e. `s∞ = 2`.
-/

public section

namespace KAM.Application.ClockTests

open KAM KAM.Certificate KAM.Application Function

/-! ### The clock check -/

theorem toyT2_clock : checkClock toyCert2 0 1 = true := by decide +kernel

/-- `I₀²/2` is not affine in `I₀`: angle `0` is no clock. -/
theorem toyT2_clock_wrongFree : checkClock toyCert2 1 1 = false := by decide +kernel

theorem toyT2_clock_wrongSlope : checkClock toyCert2 0 2 = false := by decide +kernel

/-- A constant left factor scales the slope (the time-scaled Moon Hamiltonians have this shape);
a right factor and products of actions are not recognised (fail closed). -/
theorem actionSlope_examples :
    actionSlope 1 (.mul (.const (3 / 2)) toyT2Ham) = some (3 / 2) ∧
      actionSlope 0 toyT2Ham = none ∧
      actionSlope 1 (.mul toyT2Ham (.const 2)) = none ∧
      actionSlope (1 : Fin 2) (.mul (.action 1) (.action 1)) = none := by
  decide +kernel

/-! ### The diagonal checks on probe data -/

/-- T2's certificate with the angle displacement `U₀` replaced by one mode `k` of amplitude `a`. -/
def clockProbe (k : List ℤ) (a : ℚ) : TorusCertificate 2 ℚ :=
  { toyCert2 with emb := { toyCert2.emb with angle := [⟨0, [(k, ⟨a, 0⟩)]⟩, ⟨0, []⟩] } }

/-- Off-diagonal mode: the near-identity check fails, the clock checks pass. -/
theorem probe_offDiag :
    checkAngleGraphReal (clockProbe [0, 1] (1 / 10)) (99 / 100) = false ∧
      checkClockGraphReal (clockProbe [0, 1] (1 / 10)) 0 (99 / 100) = true ∧
      checkClockGraph (clockProbe [0, 1] (1 / 10)) 0 (99 / 100) 1 ⟨[]⟩ = true := by
  decide +kernel

/-- Diagonal mode `4π/100`: the real check brackets it. -/
theorem probe_diag_real :
    checkClockGraphReal (clockProbe [1, 0] (1 / 100)) 0 (4 / 5) = true ∧
      checkClockGraphReal (clockProbe [1, 0] (1 / 100)) 0 (9 / 10) = false := by
  decide +kernel

/-- The SOS check (strip-weighted residual) with an empty witness fails on the same data. -/
theorem probe_diag_sos :
    checkClockGraph (clockProbe [1, 0] (1 / 100)) 0 (4 / 5) 1 ⟨[]⟩ = false := by
  decide +kernel

/-- The margin `disp < mono ρ∞` fails at `mono = 0`. -/
theorem probe_margin :
    checkClockGraphReal toyCert2 0 0 = false ∧ checkClockGraph toyCert2 0 0 1 ⟨[]⟩ = false := by
  decide +kernel

/-! ### The full chain on the certified torus T2 -/

theorem toyCert2_clockGraphReal : checkClockGraphReal toyCert2 0 (99 / 100) = true := by
  decide +kernel

theorem toyCert2_clockGraphSOS : checkClockGraph toyCert2 0 (99 / 100) 1 ⟨[]⟩ = true := by
  decide +kernel

theorem toyCert2_static_hamBounds :
    checkStatic toyCert2 = true ∧ checkHamBounds toyCert2 = true :=
  checkStatic_checkHamBounds_of_checkTorusCertificate toyCert2_passes

/-- **T2 is a clock-triangular graph**: an exact torus of T2 whose real restriction is a real model
torus and a clock-triangular analytic graph over the angles (free angle `0`, clock `1`, diagonal
`∂₀ A₀ ≥ 99/100 - disp/ρ∞`); the clock lemma fixes `s∞ = 2`. -/
theorem toyCert2_clockGraph :
    ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)),
      CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf 2 ∧
      IsRealModelTorus (realHam toyCert2.H) ((2 : ℝ) • ![lunarNuMinus / 2, 1 / 2])
        toyCert2.params.E0 (realRestriction Kinf) ∧
      ∃ cc : Fin 2 → ℝ, IsClockAngleGraph (realRestriction Kinf) 0 cc
        (((99 / 100 : ℚ) : ℝ) - (toyCert2.params.disp : ℝ) / toyCert2.params.rhoInf) := by
  obtain ⟨Kinf, sinf, hT, hR, hf, hG⟩ :=
    toyCert2_torus.exists_clockGraph_of_checks toyCert2_static_hamBounds.1
      toyCert2_static_hamBounds.2 toyT2_clock (by norm_num : (0 : ℝ) < 1 / 42)
      lunarNuMinus_half_isDiophantine (.inl toyCert2_clockGraphReal)
  have h1 := hf 1 (by decide)
  have hs : sinf = 2 := by
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Rat.cast_one] at h1
    linarith
  subst hs
  exact ⟨Kinf, hT, hR, hG⟩

/-- The SOS route through the same theorem. -/
example : ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
    CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf sinf ∧ ∃ cc : Fin 2 → ℝ,
      IsClockAngleGraph (realRestriction Kinf) 0 cc
        (((99 / 100 : ℚ) : ℝ) - (toyCert2.params.disp : ℝ) / toyCert2.params.rhoInf) := by
  obtain ⟨Kinf, sinf, hT, -, -, hG⟩ :=
    toyCert2_torus.exists_clockGraph_of_checks toyCert2_static_hamBounds.1
      toyCert2_static_hamBounds.2 toyT2_clock (by norm_num : (0 : ℝ) < 1 / 42)
      lunarNuMinus_half_isDiophantine (.inr ⟨1, ⟨[]⟩, toyCert2_clockGraphSOS⟩)
  exact ⟨Kinf, sinf, hT, hG⟩

/-- Consuming the graph: the torus is the graph of `G` over the angles, the angle map is a
homeomorphism, and the clock component of its inverse is `φ₁ - c₁`. -/
example {k : (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)} {cc : Fin 2 → ℝ} {m : ℝ}
    (hG : IsClockAngleGraph k 0 cc m) (φ : Fin 2 → ℝ) :
    k (invFun (torusAngle k) φ) = (φ, torusGraph k φ) ∧
      invFun (torusAngle k) φ 1 = φ 1 - cc 1 ∧ Continuous (invFun (torusAngle k)) :=
  ⟨hG.k_invFun φ, hG.triangular.invFun_clock φ (by decide), hG.continuous_angleInv⟩

end KAM.Application.ClockTests
