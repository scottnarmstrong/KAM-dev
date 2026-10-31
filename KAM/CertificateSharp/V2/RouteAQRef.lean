/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAQ
public import KAM.Iso.Sharp2.RouteA.Ref.G1

/-!
# Exact rational mirrors of lever L8′

The extension of `V2/RouteAQ.lean` to the torsion against the initial pair
(`KAM/Iso/Sharp2/RouteA/Ref`), isoenergetic branch, for every `τ ∈ ℕ`:

* `StepQ.rAb`, `StepQ.bLoc`, `StepQ.cond0`, `StepQ.rateR`: the mirrors of `StepInA.rAb`,
  `StepInA.bLoc`, `StepInA.Cond0`, `rateRI`;
* `NumQ.condR`, `NumQ.okR`: the mirrors of `NumA.CondR` and `routeAOkRI` (`okR_sound`);
* `NumQ.budgetOk`: the mirror of `Ref.Budget` (`budgetOk_sound`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp2.RouteA.Ref KAM.Sharp2.RouteA.Ref
  KAM.Sharp.Engine

namespace StepQ

variable (p : StepQ)

/-- The rate of `𝒯_ab`, bordered. -/
def rAb : ℚ := max (p.CDab * p.CDK + p.CDw * p.δ) (p.n * p.CDw * p.δ)

/-- `C_{T1} γ̄⁴ δ^{2a-1} + C_{T2} γ̄³ δ^{2a-κ-1}`, with `ch` the constant at the bite `δ/2`. -/
def bLoc0 (ch : ℚ) : ℚ :=
  p.n * p.sNt * p.sB * (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1)) +
    2 ^ (p.κ + 1) * p.sB ^ 3 * p.w * (2 * ((p.n : ℚ) - 1) * ch * p.sLt) *
      (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1))

/-- The local bound per unit `x`, with the `ηᴸ` row of the bordered torsion. -/
def bLoc (ch : ℚ) : ℚ := max (p.bLoc0 ch) (p.n * p.sNt * (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ))))

/-- The step conditions, without the Neumann condition of `⟨T̄⟩`. -/
def cond0 (x : ℚ) : Bool :=
  decide (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1) * x ≤ 1) &&
    decide (p.CSym * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x ≤ 1 / 2) &&
    decide (p.CE * x ≤ 1) &&
    decide (p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th)

/-- The eight rates of `rateRI`. -/
def rateR : Fin 8 → ℚ :=
  ![p.CDK, p.n * p.CDK, p.CB * p.CDK, p.rAb, 2 * p.n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK, p.CDw]

variable {p}

theorem cast_rAb : p.toStep.rAb = (p.rAb : ℝ) := by
  simp only [StepInA.rAb, StepQ.rAb, cast_CDab, cast_CDK, cast_CDw]
  simp only [toStep, ite_true]; push_cast; rfl

theorem cast_bLoc0 (hκ : 1 ≤ p.κ) (ch : ℚ) : p.toStep.bLoc0 (ch : ℝ) = (p.bLoc0 ch : ℝ) := by
  have e4 : ((2 * (2 * (p.κ : ℝ)) - 1 : ℝ)) = ((2 * (2 * p.κ) - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : ((3 * (p.κ : ℝ) - 1 : ℝ)) = ((3 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : (2 : ℝ) ^ ((p.κ : ℝ) + 1) = 2 ^ (p.κ + 1) := by
    rw [show ((p.κ : ℝ) + 1) = ((p.κ + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp only [StepInA.bLoc0, StepQ.bLoc0, cast_w]
  simp only [toStep, rpow_nat p.δ e4, rpow_nat p.δ e3, e2]; push_cast; rfl

theorem cast_bLoc (hκ : 1 ≤ p.κ) (ch : ℚ) : p.toStep.bLoc (ch : ℝ) = (p.bLoc ch : ℝ) := by
  have e : ((2 * (2 * (p.κ : ℝ)) : ℝ)) = ((2 * (2 * p.κ) : ℕ) : ℝ) := by push_cast; ring
  simp only [StepInA.bLoc, StepQ.bLoc, cast_bLoc0 hκ]
  simp only [toStep, ite_true, rpow_nat p.δ e]; push_cast; rfl

theorem cast_rateR (i : Fin 8) : rateRI p.toStep i = (p.rateR i : ℝ) := by
  have e1 := cast_CDK (p := p)
  have e2 := cast_CB (p := p)
  have e3 := cast_rAb (p := p)
  have e4 := cast_CNd (p := p)
  have e5 := cast_CNtd (p := p)
  have e7 := cast_CDw (p := p)
  have e0 : (p.toStep.n : ℝ) = (p.n : ℝ) := rfl
  fin_cases i <;> simp [rateRI, rateR, e0, e1, e2, e3, e4, e5, e7]

/-- `cond0` gives the step conditions. -/
theorem cond0_sound (hκ : 1 ≤ p.κ) {x : ℚ} (h : p.cond0 x = true) : p.toStep.Cond0 (x : ℝ) := by
  simp only [cond0, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h5⟩ := h
  have e4 : ((2 * (2 * (p.κ : ℝ)) - 1 : ℝ)) = ((2 * (2 * p.κ) - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : ((3 * (p.κ : ℝ) - 1 : ℝ)) = ((3 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((2 * (p.κ : ℝ) - 1 : ℝ)) = ((2 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [toStep, rpow_nat p.δ e4]; exact_mod_cast h1
  · simp only [cast_CSym]; simp only [toStep, rpow_nat p.δ e3]
    have := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at this ⊢
    exact this
  · rw [cast_CE hκ]; exact_mod_cast h3
  · simp only [cast_CGr, cast_CDK]; simp only [toStep, rpow_nat p.δ e2]; exact_mod_cast h5

end StepQ

namespace NumQ

variable (Q : NumQ)

/-- The local bound at stage `s`, with the constant `c_{s+1}` at the bite `δ_s/2`. -/
def bLocS (s : ℕ) : ℚ := (Q.inp s).bLoc (Q.cS (s + 1))

/-- The conditions of stage `s`. -/
def condR (bF : ℚ) (s : ℕ) (x : ℚ) : Bool :=
  (Q.inp s).cond0 x && decide (Q.bLocS s * x ≤ bF)

/-- `routeAOkRI` over `ℚ`. -/
def okR (bF : ℚ) (σ m₀ : Fin 8 → ℚ) (Xs : ℚ) : Bool :=
  decide (0 ≤ Xs) &&
    (List.range Q.kp).all (fun s => Q.condR bF s (Q.x Xs s)) &&
    Q.condR bF Q.kp (Q.x Xs Q.kp) &&
    decide (2 ^ (2 * (2 * Q.τ)) * (Q.inp Q.kp).CE * Q.x Xs Q.kp ≤ 1) &&
    (List.finRange 8).all fun i =>
      decide (m₀ i + Q.sumQ Q.γb (Q.x Xs) (fun s => (Q.inp s).rateR i) (2 * Q.τ - jRI i) ≤ σ i)

/-- `Ref.Budget` over `ℚ`. -/
def budgetOk (mT iH bF bT : ℚ) : Bool :=
  decide (0 < mT) && decide (mT < Q.sT) && decide (bT + 2 * bF ≤ (Q.sT - mT) / (Q.sT * mT)) &&
    decide (iH + bT + 2 * bF ≤ Q.t)

variable {Q}

theorem budgetOk_sound {mT iH bF bT : ℚ} (h : Q.budgetOk mT iH bF bT = true) :
    Budget Q.toNum (mT : ℝ) (iH : ℝ) (bF : ℝ) (bT : ℝ) := by
  simp only [budgetOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h3' := (Rat.cast_le (K := ℝ)).mpr h3
  have h4' := (Rat.cast_le (K := ℝ)).mpr h4
  push_cast at h3' h4'
  exact ⟨by exact_mod_cast h1, by show (mT : ℝ) < Q.sT; exact_mod_cast h2, h3', h4'⟩

theorem cast_bLocS (hτ : 1 ≤ Q.τ) (s : ℕ) : Q.toNum.bLocS s = (Q.bLocS s : ℝ) := by
  show (Q.toNum.inp s).bLoc (Q.toNum.cS (s + 1)) = _
  rw [cast_cS, ← toStep_inp]
  exact StepQ.cast_bLoc hτ _

theorem condR_sound (hτ : 1 ≤ Q.τ) {bF x : ℚ} {s : ℕ} (h : Q.condR bF s x = true) :
    Q.toNum.CondR bF s (x : ℝ) := by
  simp only [condR, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_⟩
  · rw [← toStep_inp]
    exact StepQ.cond0_sound hτ h.1
  · rw [cast_bLocS hτ]
    exact_mod_cast h.2

theorem cast_rateR_at (s : ℕ) (i : Fin 8) :
    (stageRI Q.toNum s).rate i = ((Q.inp s).rateR i : ℝ) := by
  show rateRI (Q.toNum.inp s) i = _
  rw [← toStep_inp]; exact StepQ.cast_rateR i

/-- **The test `okR` gives (J1)–(J3).** -/
theorem okR_sound {bF : ℚ} {σ m₀ : Fin 8 → ℚ} {Xs : ℚ} (hτ : 1 ≤ Q.τ)
    (h : Q.okR bF σ m₀ Xs = true) :
    routeAOkRI Q.toNum bF (fun i => (σ i : ℝ)) (fun i => (m₀ i : ℝ)) (Xs : ℝ) := by
  simp only [okR, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have cond : ∀ s, Q.condR bF s (Q.x Xs s) = true →
      Q.toNum.CondR bF s (xI Q.toNum (Xs : ℝ) s) := fun s hs => by
    rw [cast_x hτ]
    exact condR_sound hτ hs
  refine ⟨by exact_mod_cast h1, fun s hs => cond s (h2 s hs), cond _ h3, ?_, fun i => ?_⟩
  · have e : (2 * (2 * (Q.τ : ℝ))) = ((2 * (2 * Q.τ) : ℕ) : ℝ) := by push_cast; ring
    show (2 : ℝ) ^ (2 * (2 * (Q.τ : ℝ))) * (Q.toNum.inp Q.kp).CE * xI Q.toNum Xs Q.kp ≤ 1
    rw [e, Real.rpow_natCast, cast_CE hτ, cast_x hτ]
    exact_mod_cast h4
  · have hj : (jRI i : ℕ) ≤ 1 := by fin_cases i <;> simp [jRI]
    have hb : 2 * (2 * (Q.τ : ℝ)) - (2 * (Q.τ : ℝ) + (jRI i : ℝ)) =
        ((2 * Q.τ - jRI i : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have := cast_sumA (Q := Q) Q.γb (xs' := xI Q.toNum Xs)
      (c' := fun s => (stageRI Q.toNum s).rate i) (xs := Q.x Xs)
      (c := fun s => (Q.inp s).rateR i) (b := 2 * (Q.τ : ℝ) + (jRI i : ℝ)) (cast_x hτ Xs)
      (fun s => cast_rateR_at s i) hb
    show (m₀ i : ℝ) + sumA (2 * (Q.τ : ℝ)) 3 Q.ρ Q.ρinf Q.γb (xI Q.toNum Xs)
      (fun s => (stageRI Q.toNum s).rate i) (2 * (Q.τ : ℝ) + (jRI i : ℝ)) Q.kp ≤ σ i
    rw [this]
    exact_mod_cast h5 i

end NumQ

end KAM.CertificateSharp.V2

end
