/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.MirrorQ
public import KAM.Sharp2.RouteA.Ref.Constants
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The rational mirror of lever L8′ at `τ = 1`

The extension of `MirrorQ` to the constants of `KAM/Sharp2/RouteA/Ref/Constants.lean`.
`NumQ.okR` is the Boolean form of `routeAOkR`, and `NumQ.okR_sound` its soundness.
-/

@[expose] public section

namespace KAM.Sharp2.Examples

open KAM.Sharp.Engine KAM.Sharp2.RouteA

namespace StepQ

variable (p : StepQ)

def rAb : ℚ := p.CDab * p.CDK

/-- The local bound; `2^{κ+1} = 4`. -/
def bLoc0 (ch : ℚ) : ℚ :=
  p.n * p.sNt * p.sB * (p.γb ^ 4 * p.δ ^ 3) +
    4 * p.sB ^ 3 * p.w * (2 * ((p.n : ℚ) - 1) * ch * p.sLt) * (p.γb ^ 3 * p.δ ^ 2)

/-- The seven rates. -/
def rateR : Fin 7 → ℚ :=
  ![p.CDK, p.n * p.CDK, p.CB * p.CDK, p.rAb, 2 * p.n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK]

/-- The step conditions, without the Neumann condition of `⟨T̄⟩`. -/
def cond0 (x : ℚ) : Bool :=
  decide (p.γb ^ 4 * p.δ ^ 3 * x ≤ 1) &&
    decide (p.CSym * (p.γb ^ 3 * p.δ ^ 2) * x ≤ 1 / 2) && decide (p.CE * x ≤ 1) &&
    decide (p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ) * x ≤ p.th)

theorem cast_rAb : p.toA.rAb = (p.rAb : ℝ) := by
  have h : p.toA.iso = false := rfl
  simp only [StepInA.rAb, h, ite_false, Bool.false_eq_true, cast_CDab, cast_CDK]
  simp [rAb]

theorem cast_bLoc0 (ch : ℚ) : p.toA.bLoc0 (ch : ℝ) = (p.bLoc0 ch : ℝ) := by
  have e : (2 : ℝ) ^ ((1 : ℝ) + 1) = 4 := by
    rw [show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  simp only [StepInA.bLoc0, toA_κ, rpow_three_nat, rpow_two_nat', e, cast_w]
  simp [bLoc0, toA]

theorem cast_rateR (i : Fin 7) : NumA.rateR p.toA i = (p.rateR i : ℝ) := by
  fin_cases i <;>
    simp [NumA.rateR, rateR, cast_CDK, cast_CB, cast_rAb, cast_CNd, cast_CNtd, toA_n]

variable {p}

theorem cond0_sound {x : ℚ} (h : p.cond0 x = true) : p.toA.Cond0 (x : ℝ) := by
  simp only [cond0, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ((p.γb ^ 4 * p.δ ^ 3 * x : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h1
    simp only [toA_κ, rpow_three_nat]
    simpa [toA] using this
  · have : ((p.CSym * (p.γb ^ 3 * p.δ ^ 2) * x : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h2
    simp only [toA_κ, rpow_two_nat', cast_CSym]
    simpa [toA] using this
  · have : ((p.CE * x : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h3
    simp only [cast_CE]
    simpa using this
  · have : ((p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ) * x : ℚ) : ℝ) ≤ (p.th : ℝ) :=
      Rat.cast_le.mpr h5
    simp only [toA_κ, rpow_one_nat, cast_CGr, cast_CDK]
    simpa [toA] using this

end StepQ

namespace NumQ

variable (Q : NumQ)

/-- The local bound at stage `s`. -/
def bLocS (s : ℕ) : ℚ := (Q.inp s).bLoc0 (Q.cS (s + 1))

/-- The sum of (J3) for the rate `i`. -/
def sumR (Xs : ℚ) (i : Fin 7) : ℚ :=
  (∑ t ∈ Finset.range Q.kp, (Q.inp t).rateR i * Q.x Xs t * (Q.γb ^ 2 * Q.δ t ^ (2 - jR i))) +
    2 * (Q.inp Q.kp).rateR i * Q.x Xs Q.kp * (Q.γb ^ 2 * Q.δ Q.kp ^ (2 - jR i))

/-- The conditions of stage `s`. -/
def condR (bF : ℚ) (s : ℕ) (x : ℚ) : Bool :=
  (Q.inp s).cond0 x && decide (Q.bLocS s * x ≤ bF)

/-- `routeAOkR`, as one Boolean. -/
def okR (bF : ℚ) (σ m₀ : Fin 7 → ℚ) (Xs : ℚ) : Bool :=
  decide (0 ≤ Xs) && (List.range Q.kp).all (fun s => Q.condR bF s (Q.x Xs s)) &&
    Q.condR bF Q.kp (Q.x Xs Q.kp) && decide (16 * (Q.inp Q.kp).CE * Q.x Xs Q.kp ≤ 1) &&
    decide (∀ i, m₀ i + Q.sumR Xs i ≤ σ i)

theorem cast_cS (s : ℕ) : Q.toA.cS s = (Q.cS s : ℝ) := by
  have hk : Q.toA.kp = Q.kp := rfl
  by_cases h : s < Q.kp
  · simp only [NumA.cS, cS, hk, h, ite_true]
    rfl
  · simp only [NumA.cS, cS, hk, h, ite_false]
    rfl

theorem cast_bLocS (s : ℕ) : Q.toA.bLocS s = (Q.bLocS s : ℝ) := by
  have h : (Q.inp s).toA.iso = false := rfl
  simp only [NumA.bLocS, cast_inp, cast_cS, StepInA.bLoc, h, ite_false, Bool.false_eq_true,
    StepQ.cast_bLoc0, bLocS]

theorem cast_stageR_rate (s : ℕ) (i : Fin 7) :
    (Q.toA.stageR s).rate i = ((Q.inp s).rateR i : ℝ) := by
  show NumA.rateR (Q.toA.inp s) i = _
  rw [cast_inp, StepQ.cast_rateR]

theorem jR_le (i : Fin 7) : jR i ≤ 1 := by fin_cases i <;> simp [jR]

theorem rpow_sumR (y : ℝ) (i : Fin 7) :
    y ^ (2 * (2 * (1 : ℝ)) - (2 * (1 : ℝ) + (jR i : ℝ))) = y ^ (2 - jR i) := by
  have h := jR_le i
  have e : (2 * (2 * (1 : ℝ)) - (2 * (1 : ℝ) + (jR i : ℝ))) = ((2 - jR i : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e, Real.rpow_natCast]

theorem cast_sumR (Xs : ℚ) (i : Fin 7) :
    sumA (2 * Q.toA.τ) 3 Q.toA.ρ Q.toA.ρinf Q.toA.γb (Q.toA.xS (Xs : ℝ))
      (fun s => (Q.toA.stageR s).rate i) (2 * Q.toA.τ + (jR i : ℝ)) Q.toA.kp =
      (Q.sumR Xs i : ℝ) := by
  have hd : ∀ t, deltaSeq 3 Q.toA.ρ Q.toA.ρinf t = (Q.δ t : ℝ) := Q.cast_δ
  have hτ : Q.toA.τ = 1 := rfl
  have hk : Q.toA.kp = Q.kp := rfl
  have hγ : Q.toA.γb = (Q.γb : ℝ) := rfl
  simp only [sumA, hτ, hk, hγ, hd, cast_stageR_rate, cast_x, rpow_sumR, sumR]
  push_cast
  rfl

variable {Q}

theorem condR_sound {bF : ℚ} {s : ℕ} {x : ℚ} (h : Q.condR bF s x = true) :
    Q.toA.CondR bF s (x : ℝ) := by
  simp only [condR, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_⟩
  · rw [cast_inp]
    exact StepQ.cond0_sound h.1
  · rw [cast_bLocS]
    have : ((Q.bLocS s * x : ℚ) : ℝ) ≤ (bF : ℝ) := Rat.cast_le.mpr h.2
    simpa using this

/-- **Soundness of the rational check.** -/
theorem okR_sound {bF : ℚ} {σ m₀ : Fin 7 → ℚ} {Xs : ℚ} (h : Q.okR bF σ m₀ Xs = true) :
    routeAOkR Q.toA bF (fun i => (σ i : ℝ)) (fun i => (m₀ i : ℝ)) (Xs : ℝ) := by
  simp only [okR, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨by exact_mod_cast h0, fun s hs => ?_, ?_, ?_, fun i => ?_⟩
  · rw [cast_x]
    exact condR_sound (h1 s hs)
  · rw [cast_x]
    exact condR_sound h2
  · have e : (2 : ℝ) ^ (2 * (2 * Q.toA.τ)) = 16 := by
      rw [show (2 * (2 * Q.toA.τ)) = ((4 : ℕ) : ℝ) by
        show (2 * (2 * (1 : ℝ))) = _
        norm_num, Real.rpow_natCast]
      norm_num
    have hC : (Q.toA.stageR Q.toA.kp).CE = ((Q.inp Q.kp).CE : ℝ) := by
      show (Q.toA.inp Q.kp).CE = _
      rw [cast_inp, StepQ.cast_CE]
    have hk : Q.toA.kp = Q.kp := rfl
    rw [e, hC, hk, cast_x]
    have : ((16 * (Q.inp Q.kp).CE * Q.x Xs Q.kp : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h3
    simpa using this
  · rw [cast_sumR]
    have : ((m₀ i + Q.sumR Xs i : ℚ) : ℝ) ≤ (σ i : ℝ) := Rat.cast_le.mpr (h4 i)
    simpa using this

end NumQ

end KAM.Sharp2.Examples

end
