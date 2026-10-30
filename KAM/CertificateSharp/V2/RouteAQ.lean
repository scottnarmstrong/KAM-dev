/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Engine
public import KAM.Iso.Sharp2.RouteA.Frozen

/-!
# Exact rational mirrors of the constants of route A

Every number of a run of the isoenergetic route A is a rational at rational data, for `τ ∈ ℕ`:
the bites `δ_s`, the radii `r_s` and all the powers are exact. So the test is the Lean definition
itself over `ℚ`, with no rounding.

* `StepQ`, `StepQ.CE`, …: the mirror of `KAM.Sharp2.RouteA.StepInA` (the isoenergetic branch),
  with `StepQ.toStep` and the equalities `StepQ.cast_*`;
* `NumQ`, `NumQ.inp`: the mirror of `KAM.Sharp2.RouteA.NumA`, with `NumQ.toNum`;
* `NumQ.x`, `NumQ.sumQ`, `NumQ.okB`: the mirror of `routeAOkI` (`okB_sound`);
* `NumQ.wfOk`: the mirror of `NumA.Wf` (`wfOk_sound`);
* `NumQ.c2Q`, `NumQ.c3Q`: the mirrors of `c2I`, `c3I`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Sharp.Engine

/-- The rational inputs of one bite, with a natural exponent `κ`. -/
structure StepQ where
  n : ℕ
  κ : ℕ
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
  Θ : ℚ
  HY : ℚ
  Mh2 : ℚ

namespace StepQ

variable (p : StepQ)

/-- The isoenergetic real inputs. -/
noncomputable def toStep : StepInA :=
  { n := p.n, κ := p.κ, M1 := p.M1, M2 := p.M2, sK := p.sK, sB := p.sB, sT := p.sT, sLt := p.sLt,
    sN := p.sN, sNt := p.sNt, t := p.t, c := p.c, ca := p.ca, γb := p.γb, δ := p.δ, th := p.th,
    iso := true, Θ := p.Θ, HY := p.HY, Mh2 := p.Mh2 }

def g : ℚ := p.γb * p.δ ^ p.κ
def COm : ℚ := 2 * ((p.n : ℚ) - 1) * p.c * p.sLt
def CSym : ℚ := max 1 (p.sB ^ 2) * p.COm
def CRed : ℚ := p.n * max p.sNt (p.sLt + 2 * p.sN)
def w : ℚ := 2 * p.M1 * p.sLt * p.sK + (2 * p.n * p.sK + p.n * p.sLt)
def CS : ℚ := p.sT * max (p.sNt * p.g + p.t * p.ca * p.sLt) (p.g + p.ca * p.HY * p.sLt)
def CXiN : ℚ := p.CS + p.c * p.sLt
def CG : ℚ := p.t * p.CXiN + p.Θ * p.CS + p.sNt * p.g
def CDXi : ℚ := max p.CG (p.sLt * p.g)
def CXi : ℚ := max (p.c * p.CG) (p.g * p.CXiN)
def CDK : ℚ := p.sK * p.c * p.CG + p.sN * p.g * p.CXiN
def CLin : ℚ := p.CRed * p.CXi + p.CSym * p.CDXi + p.Θ * p.COm * p.CS
def P : ℚ := p.sK + p.sN
def CDw : ℚ := p.Θ * p.g * p.CS
def CFr : ℚ := (p.M1 * p.sK + p.n) * (1 + p.sB) +
  p.sN * ((p.sLt * p.M1 + 2 * p.n) * p.sK + p.sLt * (p.M1 * p.sK + p.n)) * p.sB
def CdK : ℚ := p.CFr * p.CXi + p.P * p.g * p.CDXi
def CE1 : ℚ := 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * p.CLin + p.M2 / 2 * p.CDK ^ 2 +
  p.g * p.CS * p.CdK
def CE2 : ℚ := p.γb * p.δ ^ (p.κ - 1) * p.n * (p.sLt * p.g + p.Θ * p.COm) * p.c * p.CG +
  p.Mh2 / 2 * p.CDK ^ 2
def CE : ℚ := max p.CE1 p.CE2
def CGr : ℚ := p.n * p.sLt + 2 * p.n * p.sK
def CB : ℚ := p.sB ^ 2 * p.CGr / (1 - p.th)
def CNd : ℚ := p.n * p.sB + p.sK * p.CB
def CNtd : ℚ := p.CB * p.sLt + 2 * p.n * p.sB
def CDab : ℚ := 2 * p.M1 * (p.CNtd * p.sN + p.sNt * p.CNd) + 2 * p.M2 * p.sNt * p.sN * p.δ
def CDc : ℚ := p.sB ^ 3 * p.w * (2 * p.n * p.sK + p.n * p.sLt)
def CDT0 : ℚ := (p.CDab + p.CDc) * p.CDK + 2 * p.n * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ (2 * p.κ)) +
  2 * p.sB ^ 3 * p.w * p.COm * p.g
def CDT : ℚ :=
  max (p.CDT0 + p.CDw * p.δ) (p.n * p.CDw * p.δ + 2 * p.n * p.sNt * (p.γb ^ 2 * p.δ ^ (2 * p.κ)))
def rT : ℚ := p.sT ^ 2 / (1 - p.th) * p.CDT

/-- The five step conditions at `x`. -/
def condB (x : ℚ) : Bool :=
  decide (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1) * x ≤ 1) &&
    decide (p.CSym * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x ≤ 1 / 2) &&
    decide (p.CE * x ≤ 1) &&
    decide (p.sT * p.CDT * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th) &&
    decide (p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th)

/-- The nine rates of `rateI`. -/
def rateQ : Fin 9 → ℚ :=
  ![p.CDK, p.n * p.CDK, p.CB * p.CDK, p.rT, 2 * p.n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK, p.CDT,
    p.CDw]

/-! ### The casts -/

theorem rpow_nat (x : ℚ) {e : ℝ} {m : ℕ} (h : e = m) : (x : ℝ) ^ e = ((x ^ m : ℚ) : ℝ) := by
  rw [h, Real.rpow_natCast]; push_cast; rfl

variable {p}

theorem cast_g : p.toStep.g = (p.g : ℝ) := by
  simp only [StepInA.g, StepQ.g, toStep, rpow_nat p.δ rfl]; push_cast; rfl

theorem cast_COm : p.toStep.COm = (p.COm : ℝ) := by
  simp only [StepInA.COm, StepQ.COm, toStep]; push_cast; rfl

theorem cast_CSym : p.toStep.CSym = (p.CSym : ℝ) := by
  simp only [StepInA.CSym, StepQ.CSym, cast_COm]; simp only [toStep]; push_cast; rfl

theorem cast_CRed : p.toStep.CRed = (p.CRed : ℝ) := by
  simp only [StepInA.CRed, StepQ.CRed, toStep]; push_cast; rfl

theorem cast_w : p.toStep.w = (p.w : ℝ) := by
  simp only [StepInA.w, StepQ.w, toStep]; push_cast; rfl

theorem cast_CS : p.toStep.CS = (p.CS : ℝ) := by
  simp only [StepInA.CS, StepQ.CS, cast_g]; simp only [toStep, ite_true]; push_cast; rfl

theorem cast_CXiN : p.toStep.CXiN = (p.CXiN : ℝ) := by
  simp only [StepInA.CXiN, StepQ.CXiN, cast_CS]; simp only [toStep]; push_cast; rfl

theorem cast_CG : p.toStep.CG = (p.CG : ℝ) := by
  simp only [StepInA.CG, StepQ.CG, cast_CXiN, cast_CS, cast_g]; simp only [toStep]; push_cast; rfl

theorem cast_CDXi : p.toStep.CDXi = (p.CDXi : ℝ) := by
  simp only [StepInA.CDXi, StepQ.CDXi, cast_CG, cast_g]; simp only [toStep]; push_cast; rfl

theorem cast_CXi : p.toStep.CXi = (p.CXi : ℝ) := by
  simp only [StepInA.CXi, StepQ.CXi, cast_CG, cast_CXiN, cast_g]; simp only [toStep]; push_cast
  rfl

theorem cast_CDK : p.toStep.CDK = (p.CDK : ℝ) := by
  simp only [StepInA.CDK, StepQ.CDK, cast_CG, cast_CXiN, cast_g]; simp only [toStep]; push_cast
  rfl

theorem cast_CLin : p.toStep.CLin = (p.CLin : ℝ) := by
  simp only [StepInA.CLin, StepQ.CLin, cast_CRed, cast_CXi, cast_CSym, cast_CDXi, cast_COm,
    cast_CS]
  simp only [toStep]; push_cast; rfl

theorem cast_P : p.toStep.P = (p.P : ℝ) := by
  simp only [StepInA.P, StepQ.P, toStep]; push_cast; rfl

theorem cast_CDw : p.toStep.CDw = (p.CDw : ℝ) := by
  simp only [StepInA.CDw, StepQ.CDw, cast_g, cast_CS]; simp only [toStep]; push_cast; rfl

theorem cast_CFr : p.toStep.CFr = (p.CFr : ℝ) := by
  simp only [StepInA.CFr, StepQ.CFr, toStep]; push_cast; rfl

theorem cast_CdK : p.toStep.CdK = (p.CdK : ℝ) := by
  simp only [StepInA.CdK, StepQ.CdK, cast_CFr, cast_CXi, cast_P, cast_g, cast_CDXi]; push_cast; rfl

theorem cast_CE1 (hκ : 1 ≤ p.κ) : p.toStep.CE1 = (p.CE1 : ℝ) := by
  have e : ((2 * (p.κ : ℝ) - 1 : ℝ)) = ((2 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [StepInA.CE1, StepQ.CE1, cast_P, cast_CLin, cast_CDK, cast_g, cast_CS, cast_CdK]
  simp only [toStep, ite_true, rpow_nat p.δ e]; push_cast; rfl

theorem cast_CE2 (hκ : 1 ≤ p.κ) : p.toStep.CE2 = (p.CE2 : ℝ) := by
  have e : (((p.κ : ℝ) - 1 : ℝ)) = ((p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hκ]; push_cast; ring
  simp only [StepInA.CE2, StepQ.CE2, cast_g, cast_COm, cast_CG, cast_CDK]
  simp only [toStep, rpow_nat p.δ e]; push_cast; rfl

theorem cast_CE (hκ : 1 ≤ p.κ) : p.toStep.CE = (p.CE : ℝ) := by
  simp only [StepInA.CE, StepQ.CE, cast_CE1 hκ, cast_CE2 hκ]; simp only [toStep, ite_true]
  push_cast; rfl

theorem cast_CGr : p.toStep.CGr = (p.CGr : ℝ) := by
  simp only [StepInA.CGr, StepQ.CGr, toStep]; push_cast; rfl

theorem cast_CB : p.toStep.CB = (p.CB : ℝ) := by
  simp only [StepInA.CB, StepQ.CB, cast_CGr]; simp only [toStep]; push_cast; rfl

theorem cast_CNd : p.toStep.CNd = (p.CNd : ℝ) := by
  simp only [StepInA.CNd, StepQ.CNd, cast_CB]; simp only [toStep]; push_cast; rfl

theorem cast_CNtd : p.toStep.CNtd = (p.CNtd : ℝ) := by
  simp only [StepInA.CNtd, StepQ.CNtd, cast_CB]; simp only [toStep]; push_cast; rfl

theorem cast_CDab : p.toStep.CDab = (p.CDab : ℝ) := by
  simp only [StepInA.CDab, StepQ.CDab, cast_CNtd, cast_CNd]; simp only [toStep]; push_cast; rfl

theorem cast_CDc : p.toStep.CDc = (p.CDc : ℝ) := by
  simp only [StepInA.CDc, StepQ.CDc, cast_w]; simp only [toStep]; push_cast; rfl

theorem cast_CDT0 : p.toStep.CDT0 = (p.CDT0 : ℝ) := by
  have e : ((2 * (p.κ : ℝ) : ℝ)) = ((2 * p.κ : ℕ) : ℝ) := by push_cast; ring
  simp only [StepInA.CDT0, StepQ.CDT0, cast_CDab, cast_CDc, cast_CDK, cast_w, cast_COm, cast_g]
  simp only [toStep, rpow_nat p.δ e]; push_cast; rfl

theorem cast_CDT : p.toStep.CDT = (p.CDT : ℝ) := by
  have e : ((2 * (p.κ : ℝ) : ℝ)) = ((2 * p.κ : ℕ) : ℝ) := by push_cast; ring
  simp only [StepInA.CDT, StepQ.CDT, cast_CDT0, cast_CDw]
  simp only [toStep, ite_true, rpow_nat p.δ e]; push_cast; rfl

theorem cast_rT : p.toStep.rT = (p.rT : ℝ) := by
  simp only [StepInA.rT, StepQ.rT, cast_CDT]; simp only [toStep]; push_cast; rfl

theorem cast_rate (i : Fin 9) : rateI p.toStep i = (p.rateQ i : ℝ) := by
  have e1 := cast_CDK (p := p)
  have e2 := cast_CB (p := p)
  have e3 := cast_rT (p := p)
  have e4 := cast_CNd (p := p)
  have e5 := cast_CNtd (p := p)
  have e6 := cast_CDT (p := p)
  have e7 := cast_CDw (p := p)
  have e0 : (p.toStep.n : ℝ) = (p.n : ℝ) := rfl
  fin_cases i <;> simp [rateI, rateQ, e0, e1, e2, e3, e4, e5, e6, e7]

/-- `condB` gives the step conditions. -/
theorem condB_sound (hκ : 1 ≤ p.κ) {x : ℚ} (h : p.condB x = true) : p.toStep.Cond (x : ℝ) := by
  simp only [condB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have e4 : ((2 * (2 * (p.κ : ℝ)) - 1 : ℝ)) = ((2 * (2 * p.κ) - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : ((3 * (p.κ : ℝ) - 1 : ℝ)) = ((3 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((2 * (p.κ : ℝ) - 1 : ℝ)) = ((2 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [toStep, rpow_nat p.δ e4]; exact_mod_cast h1
  · simp only [cast_CSym]; simp only [toStep, rpow_nat p.δ e3]
    have := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at this ⊢
    exact this
  · rw [cast_CE hκ]; exact_mod_cast h3
  · simp only [cast_CDT]; simp only [toStep, rpow_nat p.δ e2]; exact_mod_cast h4
  · simp only [cast_CGr, cast_CDK]; simp only [toStep, rpow_nat p.δ e2]; exact_mod_cast h5

end StepQ

/-- The rational numbers of a run of the isoenergetic route A. -/
structure NumQ where
  n : ℕ
  τ : ℕ
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
  c : List ℚ
  cbar : List ℚ
  ctail : ℚ
  kp : ℕ
  Θ : ℚ
  HY : ℚ
  Mh2 : ℚ

namespace NumQ

variable (Q : NumQ)

/-- The real numbers of the run. -/
noncomputable def toNum : NumA :=
  { n := Q.n, τ := Q.τ, ρ := Q.ρ, ρinf := Q.ρinf, M1 := Q.M1, M2 := Q.M2, sK := Q.sK, sB := Q.sB,
    sT := Q.sT, sLt := Q.sLt, sN := Q.sN, sNt := Q.sNt, t := Q.t, th := Q.th, γb := Q.γb,
    c := fun s => (Q.c.getD s 0 : ℚ), cbar := fun s => (Q.cbar.getD s 0 : ℚ), ctail := Q.ctail,
    kp := Q.kp, iso := true, Θ := Q.Θ, HY := Q.HY, Mh2 := Q.Mh2 }

/-- `δ₀ = min {1, (ρ - ρ∞)/6}`. -/
def δ0 : ℚ := min 1 ((Q.ρ - Q.ρinf) / (2 * 3))
/-- `δ_s = 2^{-s} δ₀`. -/
def δ (s : ℕ) : ℚ := (2 : ℚ)⁻¹ ^ s * Q.δ0
/-- `r_s = ρ - 6 δ₀ (1 - 2^{-s})`. -/
def r (s : ℕ) : ℚ := Q.ρ - 2 * 3 * Q.δ0 * (1 - (2 : ℚ)⁻¹ ^ s)
/-- `c(δ_s)` in the prefix, `c_∞` in the tail. -/
def cS (s : ℕ) : ℚ := if s < Q.kp then Q.c.getD s 0 else Q.ctail
/-- `c̄_s (δ_s/r_s)^τ` in the prefix, `c_∞` in the tail. -/
def caS (s : ℕ) : ℚ := if s < Q.kp then Q.cbar.getD s 0 * (Q.δ s / Q.r s) ^ Q.τ else Q.ctail
/-- The value of the bite in the constants. -/
def dS (s : ℕ) : ℚ := Q.δ (min s Q.kp)

/-- The inputs of stage `s`. -/
def inp (s : ℕ) : StepQ :=
  { n := Q.n, κ := Q.τ, M1 := Q.M1, M2 := Q.M2, sK := Q.sK, sB := Q.sB, sT := Q.sT, sLt := Q.sLt,
    sN := Q.sN, sNt := Q.sNt, t := Q.t, c := Q.cS s, ca := Q.caS s, γb := Q.γb, δ := Q.dS s,
    th := Q.th, Θ := Q.Θ, HY := Q.HY, Mh2 := Q.Mh2 }

/-- The normalised error: `x_{s+1} = 2^{4τ} C_{E,s} x_s²`. -/
def x (Xs : ℚ) : ℕ → ℚ
  | 0 => Xs
  | s + 1 => 2 ^ (2 * (2 * Q.τ)) * (Q.inp s).CE * x Xs s ^ 2

/-- The sum of (J3) for a rate `c`, a scale `γ` and an exponent `e`. -/
def sumQ (γ : ℚ) (xs c : ℕ → ℚ) (e : ℕ) : ℚ :=
  KAM.Certificate.sumRangeQ Q.kp (fun t => c t * xs t * (γ ^ 2 * Q.δ t ^ e)) +
    2 * c Q.kp * xs Q.kp * (γ ^ 2 * Q.δ Q.kp ^ e)

/-- (J1)–(J3) over `ℚ`. -/
def okB (σ m₀ : Fin 9 → ℚ) (Xs : ℚ) : Bool :=
  decide (0 ≤ Xs) &&
    (List.range Q.kp).all (fun s => (Q.inp s).condB (Q.x Xs s)) &&
    (Q.inp Q.kp).condB (Q.x Xs Q.kp) &&
    decide (2 ^ (2 * (2 * Q.τ)) * (Q.inp Q.kp).CE * Q.x Xs Q.kp ≤ 1) &&
    (List.finRange 9).all fun i =>
      decide (m₀ i + Q.sumQ Q.γb (Q.x Xs) (fun s => (Q.inp s).rateQ i) (2 * Q.τ - jI i) ≤ σ i)

/-- `NumA.Wf` over `ℚ`. -/
def wfOk : Bool :=
  decide (2 ≤ Q.n) && decide (1 ≤ Q.τ) && decide (0 < Q.ρinf) && decide (Q.ρinf < Q.ρ) &&
    decide (0 ≤ Q.M1) && decide (0 ≤ Q.M2) && decide (0 < Q.sK) && decide (0 < Q.sB) &&
    decide (0 < Q.sT) && decide (0 ≤ Q.sLt) && decide (0 ≤ Q.sN) && decide (0 ≤ Q.sNt) &&
    decide (0 ≤ Q.t) && decide (0 < Q.th) && decide (Q.th < 1) && decide (0 < Q.γb) &&
    Q.c.all (fun a => decide (0 ≤ a)) && Q.cbar.all (fun a => decide (0 ≤ a)) &&
    decide (0 ≤ Q.ctail) && decide (0 ≤ Q.Θ) && decide (0 ≤ Q.HY) && decide (0 ≤ Q.Mh2)

/-- The mirror of `c2I`. -/
def c2Q (Xs : ℚ) : ℚ :=
  Q.ρ ^ (2 * Q.τ) * Q.sumQ 1 (Q.x Xs) (fun s => (Q.inp s).CDK) (2 * Q.τ) /
    (Xs * Q.δ0 ^ (4 * Q.τ))

/-- The mirror of `c3I`. -/
def c3Q (Xs : ℚ) : ℚ :=
  Q.ρ ^ (2 * Q.τ) * Q.sumQ 1 (Q.x Xs) (fun s => (Q.inp s).CDw) (2 * Q.τ) /
    (Xs * Q.δ0 ^ (4 * Q.τ))

/-! ### The casts -/

variable {Q}

theorem wfOk_sound (h : Q.wfOk = true) : Q.toNum.Wf := by
  simp only [wfOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩ := h
  have hc : ∀ (l : List ℚ), (∀ a ∈ l, 0 ≤ a) → ∀ s, (0 : ℝ) ≤ (l.getD s 0 : ℚ) := by
    intro l hl s
    have : 0 ≤ l.getD s 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hh : l[s]? with
      | none => simp
      | some a => simpa using hl a (List.mem_of_getElem? hh)
    exact_mod_cast this
  exact
    { two_le := h1
      τ_ge := by show (1 : ℝ) ≤ (Q.τ : ℝ); exact_mod_cast h2
      ρinf_pos := by show (0 : ℝ) < Q.ρinf; exact_mod_cast h3
      ρinf_lt := by show (Q.ρinf : ℝ) < Q.ρ; exact_mod_cast h4
      M1 := by show (0 : ℝ) ≤ Q.M1; exact_mod_cast h5
      M2 := by show (0 : ℝ) ≤ Q.M2; exact_mod_cast h6
      sK := by show (0 : ℝ) < Q.sK; exact_mod_cast h7
      sB := by show (0 : ℝ) < Q.sB; exact_mod_cast h8
      sT := by show (0 : ℝ) < Q.sT; exact_mod_cast h9
      sLt := by show (0 : ℝ) ≤ Q.sLt; exact_mod_cast h10
      sN := by show (0 : ℝ) ≤ Q.sN; exact_mod_cast h11
      sNt := by show (0 : ℝ) ≤ Q.sNt; exact_mod_cast h12
      t := by show (0 : ℝ) ≤ Q.t; exact_mod_cast h13
      th0 := by show (0 : ℝ) < Q.th; exact_mod_cast h14
      th1 := by show (Q.th : ℝ) < 1; exact_mod_cast h15
      γb := by show (0 : ℝ) < Q.γb; exact_mod_cast h16
      c := hc _ h17
      cbar := hc _ h18
      ctail := by show (0 : ℝ) ≤ Q.ctail; exact_mod_cast h19
      Θ := by show (0 : ℝ) ≤ Q.Θ; exact_mod_cast h20
      HY := by show (0 : ℝ) ≤ Q.HY; exact_mod_cast h21
      Mh2 := by show (0 : ℝ) ≤ Q.Mh2; exact_mod_cast h22 }

theorem cast_δ0 : delta0 3 (Q.ρ : ℝ) Q.ρinf = (Q.δ0 : ℝ) := by
  simp only [delta0, δ0]; push_cast; rfl

theorem cast_δ (s : ℕ) : Q.toNum.δ s = (Q.δ s : ℝ) := by
  show deltaSeq 3 (Q.ρ : ℝ) Q.ρinf s = _
  simp only [deltaSeq, δ, cast_δ0]; push_cast; rfl

theorem cast_r (s : ℕ) : Q.toNum.r s = (Q.r s : ℝ) := by
  show rSeq 3 (Q.ρ : ℝ) Q.ρinf s = _
  simp only [rSeq, r, cast_δ0]; push_cast; rfl

theorem cast_cS (s : ℕ) : Q.toNum.cS s = (Q.cS s : ℝ) := by
  unfold NumA.cS cS
  show (if s < Q.kp then ((Q.c.getD s 0 : ℚ) : ℝ) else (Q.ctail : ℝ)) = _
  split_ifs <;> rfl

theorem cast_caS (s : ℕ) : Q.toNum.caS s = (Q.caS s : ℝ) := by
  unfold NumA.caS caS
  show (if s < Q.kp then ((Q.cbar.getD s 0 : ℚ) : ℝ) * (Q.toNum.δ s / Q.toNum.r s) ^ (Q.τ : ℝ)
    else (Q.ctail : ℝ)) = _
  split_ifs
  · rw [cast_δ, cast_r, Real.rpow_natCast]; push_cast; rfl
  · rfl

theorem cast_dS (s : ℕ) : Q.toNum.dS s = (Q.dS s : ℝ) := by
  unfold NumA.dS dS; exact cast_δ _

theorem toStep_inp (s : ℕ) : (Q.inp s).toStep = Q.toNum.inp s := by
  simp only [StepQ.toStep, inp, NumA.inp, cast_cS, cast_caS, cast_dS]; rfl

theorem cast_CE (hτ : 1 ≤ Q.τ) (s : ℕ) : (Q.toNum.inp s).CE = ((Q.inp s).CE : ℝ) := by
  rw [← toStep_inp]; exact StepQ.cast_CE hτ

theorem cast_x (hτ : 1 ≤ Q.τ) (Xs : ℚ) (s : ℕ) : xI Q.toNum Xs s = (Q.x Xs s : ℝ) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show (2 : ℝ) ^ (2 * (2 * (Q.τ : ℝ))) * (stageI Q.toNum s).CE * xI Q.toNum Xs s ^ 2 = _
    have e : (2 * (2 * (Q.τ : ℝ))) = ((2 * (2 * Q.τ) : ℕ) : ℝ) := by push_cast; ring
    rw [ih, e, Real.rpow_natCast, show (stageI Q.toNum s).CE = (Q.toNum.inp s).CE from rfl,
      cast_CE hτ]
    simp only [x]
    push_cast
    rfl

theorem cast_sumA (γ : ℚ) {xs' c' : ℕ → ℝ} {xs c : ℕ → ℚ} {b : ℝ} {e : ℕ}
    (hx : ∀ s, xs' s = xs s) (hc : ∀ s, c' s = c s) (hb : 2 * (2 * (Q.τ : ℝ)) - b = e) :
    sumA (2 * (Q.τ : ℝ)) 3 Q.ρ Q.ρinf γ xs' c' b Q.kp = (Q.sumQ γ xs c e : ℝ) := by
  have hd : ∀ s, deltaSeq 3 (Q.ρ : ℝ) Q.ρinf s = (Q.δ s : ℝ) := cast_δ
  unfold sumA sumQ
  rw [hb, KAM.Certificate.sumRangeQ_eq]
  simp only [hx, hc, hd, Real.rpow_natCast]
  push_cast
  rfl

theorem cast_rate_at (s : ℕ) (i : Fin 9) :
    (stageI Q.toNum s).rate i = ((Q.inp s).rateQ i : ℝ) := by
  show rateI (Q.toNum.inp s) i = _
  rw [← toStep_inp]; exact StepQ.cast_rate i

/-- **The test `okB` gives (J1)–(J3).** -/
theorem okB_sound {σ m₀ : Fin 9 → ℚ} {Xs : ℚ} (hτ : 1 ≤ Q.τ) (h : Q.okB σ m₀ Xs = true) :
    routeAOkI Q.toNum (fun i => (σ i : ℝ)) (fun i => (m₀ i : ℝ)) (Xs : ℝ) := by
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have cond : ∀ s, (Q.inp s).condB (Q.x Xs s) = true →
      (Q.toNum.inp s).Cond (xI Q.toNum (Xs : ℝ) s) := fun s hs => by
    rw [cast_x hτ, ← toStep_inp]
    exact StepQ.condB_sound hτ hs
  refine ⟨by exact_mod_cast h1, fun s hs => cond s (h2 s hs), cond _ h3, ?_, fun i => ?_⟩
  · have e : (2 * (2 * (Q.τ : ℝ))) = ((2 * (2 * Q.τ) : ℕ) : ℝ) := by push_cast; ring
    show (2 : ℝ) ^ (2 * (2 * (Q.τ : ℝ))) * (Q.toNum.inp Q.kp).CE * xI Q.toNum Xs Q.kp ≤ 1
    rw [e, Real.rpow_natCast, cast_CE hτ, cast_x hτ]
    exact_mod_cast h4
  · have hj : (jI i : ℕ) ≤ 1 := by fin_cases i <;> simp [jI]
    have hb : 2 * (2 * (Q.τ : ℝ)) - (2 * (Q.τ : ℝ) + (jI i : ℝ)) = ((2 * Q.τ - jI i : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have := cast_sumA (Q := Q) Q.γb (xs' := xI Q.toNum Xs)
      (c' := fun s => (stageI Q.toNum s).rate i) (xs := Q.x Xs)
      (c := fun s => (Q.inp s).rateQ i) (b := 2 * (Q.τ : ℝ) + (jI i : ℝ)) (cast_x hτ Xs)
      (fun s => cast_rate_at s i) hb
    show (m₀ i : ℝ) + sumA (2 * (Q.τ : ℝ)) 3 Q.ρ Q.ρinf Q.γb (xI Q.toNum Xs)
      (fun s => (stageI Q.toNum s).rate i) (2 * (Q.τ : ℝ) + (jI i : ℝ)) Q.kp ≤ σ i
    rw [this]
    exact_mod_cast h5 i

/-- `c2I` at rational data is its mirror. -/
theorem cast_c2 (hτ : 1 ≤ Q.τ) (Xs : ℚ) : c2I Q.toNum Xs = (Q.c2Q Xs : ℝ) := by
  have hb : 2 * (2 * (Q.τ : ℝ)) - 2 * (Q.τ : ℝ) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have hs := cast_sumA (Q := Q) 1 (xs' := xI Q.toNum Xs)
    (c' := fun s => (stageI Q.toNum s).CD) (xs := Q.x Xs) (c := fun s => (Q.inp s).CDK)
    (b := 2 * (Q.τ : ℝ)) (cast_x hτ Xs)
    (fun s => by
      show (Q.toNum.inp s).CDK = _
      rw [← toStep_inp]; exact StepQ.cast_CDK) hb
  have e1 : ((1 : ℚ) : ℝ) = 1 := Rat.cast_one
  rw [e1] at hs
  have e2 : (2 * (Q.τ : ℝ)) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have e4 : (4 * (Q.τ : ℝ)) = ((4 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  show (Q.ρ : ℝ) ^ (2 * (Q.τ : ℝ)) * sumA (2 * (Q.τ : ℝ)) 3 Q.ρ Q.ρinf 1 (xI Q.toNum Xs)
    (fun s => (stageI Q.toNum s).CD) (2 * (Q.τ : ℝ)) Q.kp /
    ((Xs : ℝ) * delta0 3 (Q.ρ : ℝ) Q.ρinf ^ (4 * (Q.τ : ℝ))) = _
  rw [hs, cast_δ0, e4, Real.rpow_natCast, e2, Real.rpow_natCast]
  simp only [c2Q]
  push_cast
  rfl

/-- `c3I` at rational data is its mirror. -/
theorem cast_c3 (hτ : 1 ≤ Q.τ) (Xs : ℚ) : c3I Q.toNum Xs = (Q.c3Q Xs : ℝ) := by
  have hb : 2 * (2 * (Q.τ : ℝ)) - 2 * (Q.τ : ℝ) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have hs := cast_sumA (Q := Q) 1 (xs' := xI Q.toNum Xs)
    (c' := fun s => (stageI Q.toNum s).Cp) (xs := Q.x Xs) (c := fun s => (Q.inp s).CDw)
    (b := 2 * (Q.τ : ℝ)) (cast_x hτ Xs)
    (fun s => by
      show (Q.toNum.inp s).CDw = _
      rw [← toStep_inp]; exact StepQ.cast_CDw) hb
  have e1 : ((1 : ℚ) : ℝ) = 1 := Rat.cast_one
  rw [e1] at hs
  have e2 : (2 * (Q.τ : ℝ)) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have e4 : (4 * (Q.τ : ℝ)) = ((4 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  show (Q.ρ : ℝ) ^ (2 * (Q.τ : ℝ)) * sumA (2 * (Q.τ : ℝ)) 3 Q.ρ Q.ρinf 1 (xI Q.toNum Xs)
    (fun s => (stageI Q.toNum s).Cp) (2 * (Q.τ : ℝ)) Q.kp /
    ((Xs : ℝ) * delta0 3 (Q.ρ : ℝ) Q.ρinf ^ (4 * (Q.τ : ℝ))) = _
  rw [hs, cast_δ0, e4, Real.rpow_natCast, e2, Real.rpow_natCast]
  simp only [c3Q]
  push_cast
  rfl

end NumQ

end KAM.CertificateSharp.V2

end
