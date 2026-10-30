/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Data
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The rational mirror of route A at `τ = 1`

The constants of `KAM.Sharp2.RouteA.StepInA` are real numbers with real exponents, so `routeAOk`
is not a decidable statement. For rational data, `τ = 1` and the fixed-frequency mode, all of them
are rational: `StepQ` and `NumQ` are the rational records, `StepQ.toA` and `NumQ.toA` their
images, and the `cast_*` lemmas identify every constant with the cast of its rational mirror.

`NumQ.ok` is the Boolean form of (J1)–(J3), `NumQ.ok_sound` its soundness: `routeAOk` follows from
one evaluation, in exact rational arithmetic, with no float and no rounding.
-/

@[expose] public section

namespace KAM.Sharp2.Examples

open KAM.Sharp.Engine KAM.Sharp2.RouteA

theorem rpow_one_nat (x : ℝ) : x ^ (2 * (1 : ℝ) - 1) = x := by norm_num

theorem rpow_two_nat (x : ℝ) : x ^ (2 * (1 : ℝ)) = x ^ 2 := by norm_num

theorem rpow_three_nat (x : ℝ) : x ^ (2 * (2 * (1 : ℝ)) - 1) = x ^ 3 := by
  rw [show (2 * (2 * (1 : ℝ)) - 1) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem rpow_two_nat' (x : ℝ) : x ^ (3 * (1 : ℝ) - 1) = x ^ 2 := by
  rw [show (3 * (1 : ℝ) - 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The rational inputs of one additive step, `κ = 1`, fixed frequency. -/
structure StepQ where
  n : ℕ
  M1 : ℚ
  M2 : ℚ
  sK : ℚ
  sB : ℚ
  sT : ℚ
  sLt : ℚ
  sN : ℚ
  sNt : ℚ
  t : ℚ
  c : ℚ
  ca : ℚ
  γb : ℚ
  δ : ℚ
  th : ℚ

namespace StepQ

variable (p : StepQ)

/-- The real record. -/
noncomputable def toA : StepInA :=
  { n := p.n, κ := 1, M1 := p.M1, M2 := p.M2, sK := p.sK, sB := p.sB, sT := p.sT, sLt := p.sLt,
    sN := p.sN, sNt := p.sNt, t := p.t, c := p.c, ca := p.ca, γb := p.γb, δ := p.δ, th := p.th }

def g : ℚ := p.γb * p.δ
def COm : ℚ := 2 * ((p.n : ℚ) - 1) * p.c * p.sLt
def CSym : ℚ := max 1 (p.sB ^ 2) * p.COm
def CRed : ℚ := p.n * max p.sNt (p.sLt + 2 * p.sN)
def w : ℚ := 2 * p.M1 * p.sLt * p.sK + (2 * p.n * p.sK + p.n * p.sLt)
def CS : ℚ := p.sT * (p.sNt * p.g + p.t * p.ca * p.sLt)
def CXiN : ℚ := p.CS + p.c * p.sLt
def CG : ℚ := p.t * p.CXiN + p.sNt * p.g
def CDXi : ℚ := max p.CG (p.sLt * p.g)
def CXi : ℚ := max (p.c * p.CG) (p.g * p.CXiN)
def CDK : ℚ := p.sK * p.c * p.CG + p.sN * p.g * p.CXiN
def CLin : ℚ := p.CRed * p.CXi + p.CSym * p.CDXi
def P : ℚ := p.sK + p.sN
def CE : ℚ := 2 * p.P * (p.γb ^ 2 * p.δ) * p.CLin + p.M2 / 2 * p.CDK ^ 2
def CGr : ℚ := p.n * p.sLt + 2 * p.n * p.sK
def CB : ℚ := p.sB ^ 2 * p.CGr / (1 - p.th)
def CNd : ℚ := p.n * p.sB + p.sK * p.CB
def CNtd : ℚ := p.CB * p.sLt + 2 * p.n * p.sB
def CDab : ℚ := 2 * p.M1 * (p.CNtd * p.sN + p.sNt * p.CNd) + 2 * p.M2 * p.sNt * p.sN * p.δ
def CDc : ℚ := p.sB ^ 3 * p.w * (2 * p.n * p.sK + p.n * p.sLt)
def CDT : ℚ := (p.CDab + p.CDc) * p.CDK + 2 * p.n * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ 2) +
  2 * p.sB ^ 3 * p.w * p.COm * p.g
def rT : ℚ := p.sT ^ 2 / (1 - p.th) * p.CDT

/-- The eight rates. -/
def rate : Fin 8 → ℚ :=
  ![p.CDK, p.n * p.CDK, p.CB * p.CDK, p.rT, 2 * p.n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK, p.CDT]

theorem toA_κ : p.toA.κ = 1 := rfl
theorem toA_n : p.toA.n = p.n := rfl

theorem cast_g : p.toA.g = (p.g : ℝ) := by simp [StepInA.g, g, toA]
theorem cast_COm : p.toA.COm = (p.COm : ℝ) := by simp [StepInA.COm, COm, toA]
theorem cast_CSym : p.toA.CSym = (p.CSym : ℝ) := by
  simp only [StepInA.CSym, cast_COm]
  simp [CSym, toA]
theorem cast_CRed : p.toA.CRed = (p.CRed : ℝ) := by simp [StepInA.CRed, CRed, toA]
theorem cast_w : p.toA.w = (p.w : ℝ) := by simp [StepInA.w, w, toA]
theorem cast_CS : p.toA.CS = (p.CS : ℝ) := by
  simp only [StepInA.CS, cast_g]
  simp [CS, toA]
theorem cast_CXiN : p.toA.CXiN = (p.CXiN : ℝ) := by
  simp only [StepInA.CXiN, cast_CS]
  simp [CXiN, toA]
theorem cast_CG : p.toA.CG = (p.CG : ℝ) := by
  simp only [StepInA.CG, cast_CXiN, cast_CS, cast_g]
  simp [CG, toA]
theorem cast_CDXi : p.toA.CDXi = (p.CDXi : ℝ) := by
  simp only [StepInA.CDXi, cast_CG, cast_g]
  simp [CDXi, toA]
theorem cast_CXi : p.toA.CXi = (p.CXi : ℝ) := by
  simp only [StepInA.CXi, cast_CG, cast_CXiN, cast_g]
  simp [CXi, toA]
theorem cast_CDK : p.toA.CDK = (p.CDK : ℝ) := by
  simp only [StepInA.CDK, cast_CG, cast_CXiN, cast_g]
  simp [CDK, toA]
theorem cast_CLin : p.toA.CLin = (p.CLin : ℝ) := by
  simp only [StepInA.CLin, cast_CRed, cast_CXi, cast_CSym, cast_CDXi]
  simp [CLin, toA]
theorem cast_P : p.toA.P = (p.P : ℝ) := by simp [StepInA.P, P, toA]
theorem cast_CE : p.toA.CE = (p.CE : ℝ) := by
  have h : p.toA.iso = false := rfl
  simp only [StepInA.CE, StepInA.CE1, h, ite_false, Bool.false_eq_true, cast_P, cast_CLin, cast_CDK,
    toA_κ, rpow_one_nat]
  simp [CE, toA]
theorem cast_CGr : p.toA.CGr = (p.CGr : ℝ) := by simp [StepInA.CGr, CGr, toA]
theorem cast_CB : p.toA.CB = (p.CB : ℝ) := by
  simp only [StepInA.CB, cast_CGr]
  simp [CB, toA]
theorem cast_CNd : p.toA.CNd = (p.CNd : ℝ) := by
  simp only [StepInA.CNd, cast_CB]
  simp [CNd, toA]
theorem cast_CNtd : p.toA.CNtd = (p.CNtd : ℝ) := by
  simp only [StepInA.CNtd, cast_CB]
  simp [CNtd, toA]
theorem cast_CDab : p.toA.CDab = (p.CDab : ℝ) := by
  simp only [StepInA.CDab, cast_CNtd, cast_CNd]
  simp [CDab, toA]
theorem cast_CDc : p.toA.CDc = (p.CDc : ℝ) := by
  simp only [StepInA.CDc, cast_w]
  simp [CDc, toA]
theorem cast_CDT : p.toA.CDT = (p.CDT : ℝ) := by
  have h : p.toA.iso = false := rfl
  simp only [StepInA.CDT, StepInA.CDT0, h, ite_false, Bool.false_eq_true, cast_CDab, cast_CDc,
    cast_CDK, cast_w, cast_COm, cast_g, toA_κ, rpow_two_nat]
  simp [CDT, toA]
theorem cast_rT : p.toA.rT = (p.rT : ℝ) := by
  simp only [StepInA.rT, cast_CDT]
  simp [rT, toA]

/-- The step conditions at the normalised error `x`. -/
def cond (x : ℚ) : Bool :=
  decide (p.γb ^ 4 * p.δ ^ 3 * x ≤ 1) &&
    decide (p.CSym * (p.γb ^ 3 * p.δ ^ 2) * x ≤ 1 / 2) && decide (p.CE * x ≤ 1) &&
    decide (p.sT * p.CDT * (p.γb ^ 2 * p.δ) * x ≤ p.th) &&
    decide (p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ) * x ≤ p.th)

variable {p}

theorem cond_sound {x : ℚ} (h : p.cond x = true) : p.toA.Cond (x : ℝ) := by
  simp only [cond, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : ((p.γb ^ 4 * p.δ ^ 3 * x : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h1
    simp only [toA_κ, rpow_three_nat]
    simpa [toA] using this
  · have : ((p.CSym * (p.γb ^ 3 * p.δ ^ 2) * x : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h2
    simp only [toA_κ, rpow_two_nat', cast_CSym]
    simpa [toA] using this
  · have : ((p.CE * x : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h3
    simp only [cast_CE]
    simpa using this
  · have : ((p.sT * p.CDT * (p.γb ^ 2 * p.δ) * x : ℚ) : ℝ) ≤ (p.th : ℝ) := Rat.cast_le.mpr h4
    simp only [toA_κ, rpow_one_nat, cast_CDT]
    simpa [toA] using this
  · have : ((p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ) * x : ℚ) : ℝ) ≤ (p.th : ℝ) :=
      Rat.cast_le.mpr h5
    simp only [toA_κ, rpow_one_nat, cast_CGr, cast_CDK]
    simpa [toA] using this

variable (p)

theorem cast_rate (i : Fin 8) : NumA.rateV p.toA i = (p.rate i : ℝ) := by
  fin_cases i <;>
    simp [NumA.rateV, rate, cast_CDK, cast_CB, cast_rT, cast_CNd, cast_CNtd, cast_CDT, toA_n]

end StepQ

/-- The rational numbers of a run. -/
structure NumQ where
  n : ℕ
  ρ : ℚ
  ρinf : ℚ
  M1 : ℚ
  M2 : ℚ
  sK : ℚ
  sB : ℚ
  sT : ℚ
  sLt : ℚ
  sN : ℚ
  sNt : ℚ
  t : ℚ
  th : ℚ
  γb : ℚ
  c : ℕ → ℚ
  cbar : ℕ → ℚ
  ctail : ℚ
  kp : ℕ

namespace NumQ

variable (Q : NumQ)

/-- The real record. -/
noncomputable def toA : NumA :=
  { n := Q.n, τ := 1, ρ := Q.ρ, ρinf := Q.ρinf, M1 := Q.M1, M2 := Q.M2, sK := Q.sK, sB := Q.sB,
    sT := Q.sT, sLt := Q.sLt, sN := Q.sN, sNt := Q.sNt, t := Q.t, th := Q.th, γb := Q.γb,
    c := fun s => Q.c s, cbar := fun s => Q.cbar s, ctail := Q.ctail, kp := Q.kp }

def δ0 : ℚ := min 1 ((Q.ρ - Q.ρinf) / (2 * 3))
def δ (s : ℕ) : ℚ := (2 : ℚ)⁻¹ ^ s * Q.δ0
def r (s : ℕ) : ℚ := Q.ρ - 2 * 3 * Q.δ0 * (1 - (2 : ℚ)⁻¹ ^ s)
def cS (s : ℕ) : ℚ := if s < Q.kp then Q.c s else Q.ctail
def caS (s : ℕ) : ℚ := if s < Q.kp then Q.cbar s * (Q.δ s / Q.r s) else Q.ctail
def dS (s : ℕ) : ℚ := Q.δ (min s Q.kp)

/-- The inputs of the step at stage `s`. -/
def inp (s : ℕ) : StepQ :=
  { n := Q.n, M1 := Q.M1, M2 := Q.M2, sK := Q.sK, sB := Q.sB, sT := Q.sT, sLt := Q.sLt, sN := Q.sN,
    sNt := Q.sNt, t := Q.t, c := Q.cS s, ca := Q.caS s, γb := Q.γb, δ := Q.dS s, th := Q.th }

/-- `x₀ = X⋆`, `x_{s+1} = 2⁴ C_{E,s} x_s²`. -/
def x (Xs : ℚ) : ℕ → ℚ
  | 0 => Xs
  | s + 1 => 16 * (Q.inp s).CE * x Xs s ^ 2

/-- The sum of (J3) for the rate `i`. -/
def sum (Xs : ℚ) (i : Fin 8) : ℚ :=
  (∑ t ∈ Finset.range Q.kp, (Q.inp t).rate i * Q.x Xs t * (Q.γb ^ 2 * Q.δ t ^ (2 - jA i))) +
    2 * (Q.inp Q.kp).rate i * Q.x Xs Q.kp * (Q.γb ^ 2 * Q.δ Q.kp ^ (2 - jA i))

/-- The sum of the closeness estimate, `c2A` without its powers of `ρ`, `X⋆`, `δ₀`. -/
def sumD (Xs : ℚ) : ℚ :=
  (∑ t ∈ Finset.range Q.kp, (Q.inp t).CDK * Q.x Xs t * (1 ^ 2 * Q.δ t ^ 2)) +
    2 * (Q.inp Q.kp).CDK * Q.x Xs Q.kp * (1 ^ 2 * Q.δ Q.kp ^ 2)

/-- (J1)–(J3), as one Boolean. -/
def ok (σ m₀ : Fin 8 → ℚ) (Xs : ℚ) : Bool :=
  decide (0 ≤ Xs) && (List.range Q.kp).all (fun s => (Q.inp s).cond (Q.x Xs s)) &&
    (Q.inp Q.kp).cond (Q.x Xs Q.kp) && decide (16 * (Q.inp Q.kp).CE * Q.x Xs Q.kp ≤ 1) &&
    decide (∀ i, m₀ i + Q.sum Xs i ≤ σ i)

theorem cast_δ0 : delta0 3 (Q.ρ : ℝ) (Q.ρinf : ℝ) = (Q.δ0 : ℝ) := by
  simp [delta0, δ0]

theorem cast_δ (s : ℕ) : Q.toA.δ s = (Q.δ s : ℝ) := by
  show deltaSeq 3 (Q.ρ : ℝ) (Q.ρinf : ℝ) s = _
  simp [deltaSeq, δ, cast_δ0]

theorem cast_r (s : ℕ) : Q.toA.r s = (Q.r s : ℝ) := by
  show rSeq 3 (Q.ρ : ℝ) (Q.ρinf : ℝ) s = _
  simp [rSeq, r, cast_δ0]

theorem cast_inp (s : ℕ) : Q.toA.inp s = (Q.inp s).toA := by
  have hc : Q.toA.cS s = (Q.cS s : ℝ) := by
    by_cases h : s < Q.kp
    · simp only [NumA.cS, cS]
      rw [if_pos (show s < Q.toA.kp from h), if_pos h]
      rfl
    · simp only [NumA.cS, cS]
      rw [if_neg (show ¬ s < Q.toA.kp from h), if_neg h]
      rfl
  have hca : Q.toA.caS s = (Q.caS s : ℝ) := by
    by_cases h : s < Q.kp
    · simp only [NumA.caS, caS]
      rw [if_pos (show s < Q.toA.kp from h), if_pos h, cast_δ,
        show Q.toA.bbar s = Q.toA.r s from rfl, cast_r]
      show (Q.cbar s : ℝ) * ((Q.δ s : ℝ) / (Q.r s : ℝ)) ^ (1 : ℝ) = _
      rw [Real.rpow_one]
      push_cast
      rfl
    · simp only [NumA.caS, caS]
      rw [if_neg (show ¬ s < Q.toA.kp from h), if_neg h]
      rfl
  have hd : Q.toA.dS s = (Q.dS s : ℝ) := cast_δ Q _
  simp only [NumA.inp, hc, hca, hd]
  rfl

theorem cast_x (Xs : ℚ) (s : ℕ) : Q.toA.xS (Xs : ℝ) s = (Q.x Xs s : ℝ) := by
  have e : (2 : ℝ) ^ (2 * (2 * (1 : ℝ))) = 16 := by
    rw [show (2 * (2 * (1 : ℝ))) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  induction s with
  | zero => rfl
  | succ s ih =>
    have hs : Q.toA.xS (Xs : ℝ) (s + 1) =
        2 ^ (2 * (2 * (1 : ℝ))) * (Q.toA.stage s).CE * Q.toA.xS (Xs : ℝ) s ^ 2 := rfl
    have hC : (Q.toA.stage s).CE = ((Q.inp s).CE : ℝ) := by
      show (Q.toA.inp s).CE = _
      rw [cast_inp, StepQ.cast_CE]
    rw [hs, ih, e, hC]
    simp [x]

theorem cast_stage_rate (s : ℕ) (i : Fin 8) :
    (Q.toA.stage s).rate i = ((Q.inp s).rate i : ℝ) := by
  show NumA.rateV (Q.toA.inp s) i = _
  rw [cast_inp, StepQ.cast_rate]

theorem jA_le (i : Fin 8) : jA i ≤ 1 := by fin_cases i <;> simp [jA]

theorem rpow_sum (y : ℝ) (i : Fin 8) :
    y ^ (2 * (2 * (1 : ℝ)) - (2 * (1 : ℝ) + (jA i : ℝ))) = y ^ (2 - jA i) := by
  have h := jA_le i
  have e : (2 * (2 * (1 : ℝ)) - (2 * (1 : ℝ) + (jA i : ℝ))) = ((2 - jA i : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e, Real.rpow_natCast]

theorem cast_sum (Xs : ℚ) (i : Fin 8) :
    sumA (2 * Q.toA.τ) 3 Q.toA.ρ Q.toA.ρinf Q.toA.γb (Q.toA.xS (Xs : ℝ))
      (fun s => (Q.toA.stage s).rate i) (2 * Q.toA.τ + (jA i : ℝ)) Q.toA.kp = (Q.sum Xs i : ℝ) := by
  have hd : ∀ t, deltaSeq 3 Q.toA.ρ Q.toA.ρinf t = (Q.δ t : ℝ) := Q.cast_δ
  have hτ : Q.toA.τ = 1 := rfl
  have hk : Q.toA.kp = Q.kp := rfl
  have hγ : Q.toA.γb = (Q.γb : ℝ) := rfl
  simp only [sumA, hτ, hk, hγ, hd, cast_stage_rate, cast_x, rpow_sum, sum]
  push_cast
  rfl

theorem cast_sumD (Xs : ℚ) :
    sumA (2 * Q.toA.τ) 3 Q.toA.ρ Q.toA.ρinf 1 (Q.toA.xS (Xs : ℝ))
      (fun s => (Q.toA.stage s).CD) (2 * Q.toA.τ) Q.toA.kp = (Q.sumD Xs : ℝ) := by
  have hd : ∀ t, deltaSeq 3 Q.toA.ρ Q.toA.ρinf t = (Q.δ t : ℝ) := Q.cast_δ
  have hτ : Q.toA.τ = 1 := rfl
  have hk : Q.toA.kp = Q.kp := rfl
  have hp : ∀ y : ℝ, y ^ (2 * (2 * (1 : ℝ)) - 2 * (1 : ℝ)) = y ^ 2 := fun y => by
    rw [show (2 * (2 * (1 : ℝ)) - 2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hC : ∀ s, (Q.toA.stage s).CD = ((Q.inp s).CDK : ℝ) := fun s => by
    show (Q.toA.inp s).CDK = _
    rw [cast_inp, StepQ.cast_CDK]
  simp only [sumA, hτ, hk, hd, hC, cast_x, hp, sumD]
  push_cast
  rfl

variable {Q}

/-- **Soundness of the rational check.** -/
theorem ok_sound {σ m₀ : Fin 8 → ℚ} {Xs : ℚ} (h : Q.ok σ m₀ Xs = true) :
    routeAOk Q.toA (fun i => (σ i : ℝ)) (fun i => (m₀ i : ℝ)) (Xs : ℝ) := by
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨by exact_mod_cast h0, fun s hs => ?_, ?_, ?_, fun i => ?_⟩
  · rw [cast_x, cast_inp]
    exact StepQ.cond_sound (h1 s hs)
  · rw [cast_x, cast_inp]
    exact StepQ.cond_sound h2
  · have e : (2 : ℝ) ^ (2 * (2 * Q.toA.τ)) = 16 := by
      rw [show (2 * (2 * Q.toA.τ)) = ((4 : ℕ) : ℝ) by
        show (2 * (2 * (1 : ℝ))) = _
        norm_num, Real.rpow_natCast]
      norm_num
    have hC : (Q.toA.stage Q.toA.kp).CE = ((Q.inp Q.kp).CE : ℝ) := by
      show (Q.toA.inp Q.kp).CE = _
      rw [cast_inp, StepQ.cast_CE]
    have hk : Q.toA.kp = Q.kp := rfl
    rw [e, hC, hk, cast_x]
    have : ((16 * (Q.inp Q.kp).CE * Q.x Xs Q.kp : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h3
    simpa using this
  · rw [cast_sum]
    have : ((m₀ i + Q.sum Xs i : ℚ) : ℝ) ≤ (σ i : ℝ) := Rat.cast_le.mpr (h4 i)
    simpa using this

end NumQ

end KAM.Sharp2.Examples

end
