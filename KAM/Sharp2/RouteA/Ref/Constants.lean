/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Data
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lever L8′ of route A: the constants

The torsion against the initial torus (item (L8′) of `bp:p2s2:constantsA`, `bp:p2s2:torsion-ref`).
The cap of `|⟨T⟩⁻¹|` and the Neumann condition of `⟨T̄⟩` are replaced by a cap on
`𝒯_ab(K_s) - 𝒯_ab(K₀)`, and the rest of the torsion is bounded at each stage by its own data.

* `StepInA.rAb`: the rate of `𝒯_ab`, `C_Δab C_ΔK` (with the bordered maximum in the iso case);
* `StepInA.bLoc ch`: the local bound per unit `x`, where `ch` is the small-divisor constant at the
  bite `δ/2`;
* `StepInA.Cond0`: the step conditions without the Neumann condition of `⟨T̄⟩`;
* `NumA.stageR`, `jR`, `NumA.capR`: the seven rates (the ball, `|DK|`, `|B|`, `𝒯_ab`, `|Lᵀ|`, `|N|`,
  `|Nᵀ|`) and their caps;
* `NumA.CondR`: `Cond0` and the local bound `bLoc x ≤ b_F`, with `ch = c_{s+1}`;
* `routeAOkR`: (J1)–(J3).
-/

@[expose] public noncomputable section

open KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA

namespace StepInA

variable (p : StepInA)

/-- The rate of `𝒯_ab` (with the shift of the frequency in the bordered case). -/
def rAb : ℝ :=
  if p.iso then max (p.CDab * p.CDK + p.CDw * p.δ) (p.n * p.CDw * p.δ) else p.CDab * p.CDK

/-- `C_{T1} γ̄⁴ δ^{2a-1} + C_{T2} γ̄³ δ^{2a-κ-1}`; `ch` is the constant at the bite `δ/2`. -/
def bLoc0 (ch : ℝ) : ℝ :=
  p.n * p.sNt * p.sB * (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1)) +
    2 ^ (p.κ + 1) * p.sB ^ 3 * p.w * (2 * ((p.n : ℝ) - 1) * ch * p.sLt) *
      (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1))

/-- The local bound per unit `x` (with the `ηᴸ` row in the bordered case). -/
def bLoc (ch : ℝ) : ℝ :=
  if p.iso then max (p.bLoc0 ch) (p.n * p.sNt * (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ))))
  else p.bLoc0 ch

/-- The step conditions, without the Neumann condition of `⟨T̄⟩`. -/
structure Cond0 (x : ℝ) : Prop where
  err : p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1) * x ≤ 1
  sym : p.CSym * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x ≤ 1 / 2
  quad : p.CE * x ≤ 1
  gram : p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th

variable {p}

theorem Pos.rAb (hp : p.Pos) : 0 ≤ p.rAb := by
  unfold StepInA.rAb
  split_ifs
  · exact le_max_of_le_left (add_nonneg (mul_nonneg hp.CDab hp.CDK)
      (mul_nonneg hp.CDw hp.δ.le))
  · exact mul_nonneg hp.CDab hp.CDK

theorem Pos.bLoc0 (hp : p.Pos) {ch : ℝ} (hch : 0 ≤ ch) : 0 ≤ p.bLoc0 ch := by
  have h1 : 0 ≤ (p.n : ℝ) - 1 := by linarith [hp.n_cast]
  have h2 := hp.sNt
  have h3 := hp.sB
  have h4 := hp.w
  have h5 := hp.sLt
  have h6 := hp.γb
  have h7 := Real.rpow_nonneg hp.δ.le (2 * (2 * p.κ) - 1)
  have h8 := Real.rpow_nonneg hp.δ.le (3 * p.κ - 1)
  have h9 : (0 : ℝ) ≤ 2 ^ (p.κ + 1) := Real.rpow_nonneg zero_le_two _
  unfold StepInA.bLoc0
  positivity

theorem Pos.bLoc (hp : p.Pos) {ch : ℝ} (hch : 0 ≤ ch) : 0 ≤ p.bLoc ch := by
  unfold StepInA.bLoc
  split_ifs
  · exact le_max_of_le_left (hp.bLoc0 hch)
  · exact hp.bLoc0 hch

/-- The step conditions are downward closed on nonnegative errors. -/
theorem Cond0.down (hp : p.Pos) {x y : ℝ} (hxy : x ≤ y) (h : p.Cond0 y) : p.Cond0 x := by
  have hw : ∀ {a b : ℝ}, 0 ≤ a → a * y ≤ b → a * x ≤ b := fun ha h1 =>
    (mul_le_mul_of_nonneg_left hxy ha).trans h1
  have hδ := hp.δ
  have hγ := hp.γb
  have hD4 : 0 ≤ p.δ ^ (2 * (2 * p.κ) - 1) := Real.rpow_nonneg hδ.le _
  have hD3 : 0 ≤ p.δ ^ (3 * p.κ - 1) := Real.rpow_nonneg hδ.le _
  have hD2 : 0 ≤ p.δ ^ (2 * p.κ - 1) := Real.rpow_nonneg hδ.le _
  have h1 := hp.CSym
  have h2 := hp.CE
  have h5 := hp.sB
  have h6 := hp.CGr
  have h7 := hp.CDK
  exact ⟨hw (by positivity) h.err, hw (by positivity) h.sym, hw h2 h.quad,
    hw (by positivity) h.gram⟩

end StepInA

/-- The weight exponents of the seven rates. -/
def jR : Fin 7 → ℕ := ![0, 1, 1, 1, 1, 1, 1]

namespace NumA

variable (N : NumA)

/-- The seven rates of the step with the torsion against the initial torus. -/
def rateR (p : StepInA) : Fin 7 → ℝ :=
  ![p.CDK, p.n * p.CDK, p.CB * p.CDK, p.rAb, 2 * p.n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK]

/-- The constants of stage `s`. -/
def stageR (s : ℕ) : StageA 7 where
  CE := (N.inp s).CE
  CD := (N.inp s).CDK
  Cp := 0
  rate := rateR (N.inp s)

/-- The caps; `b` is the ball budget, `bT` the budget of `𝒯_ab`. -/
def capR (b bT : ℝ) : Fin 7 → ℝ := ![b, N.sK, N.sB, bT, N.sLt, N.sN, N.sNt]

/-- The local bound at stage `s`, with the constant `c_{s+1}` at the bite `δ_s/2`. -/
def bLocS (s : ℕ) : ℝ := (N.inp s).bLoc (N.cS (s + 1))

/-- The conditions of stage `s`. -/
structure CondR (bF : ℝ) (s : ℕ) (x : ℝ) : Prop where
  base : (N.inp s).Cond0 x
  loc : N.bLocS s * x ≤ bF

variable {N}

theorem rateR_nonneg {p : StepInA} (hp : p.Pos) (i : Fin 7) : 0 ≤ rateR p i := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hDK := hp.CDK
  fin_cases i
  · exact hDK
  · exact mul_nonneg hn hDK
  · exact mul_nonneg hp.CB hDK
  · exact hp.rAb
  · exact mul_nonneg (mul_nonneg two_pos.le hn) hDK
  · exact mul_nonneg hp.CNd hDK
  · exact mul_nonneg hp.CNtd hDK

theorem stageR_tail {s : ℕ} (hs : N.kp ≤ s) : N.stageR s = N.stageR N.kp := by
  simp only [stageR, inp_tail hs]

theorem cS_nonneg (hN : N.Wf) (s : ℕ) : 0 ≤ N.cS s := (hN.pos s).c

theorem bLocS_tail {s : ℕ} (hs : N.kp ≤ s) : N.bLocS s = N.bLocS N.kp := by
  have h1 : N.cS (s + 1) = N.ctail := by simp [cS, show ¬ s + 1 < N.kp by omega]
  have h2 : N.cS (N.kp + 1) = N.ctail := by simp [cS]
  simp only [bLocS, inp_tail hs, h1, h2]

theorem CondR.down (hN : N.Wf) {bF x y : ℝ} {s : ℕ} (hxy : x ≤ y) (h : N.CondR bF s y) :
    N.CondR bF s x :=
  ⟨h.base.down (hN.pos s) hxy, (mul_le_mul_of_nonneg_left hxy
    ((hN.pos s).bLoc (cS_nonneg hN (s + 1)))).trans h.loc⟩

end NumA

/-- (J1)–(J3) with the torsion against the initial torus, at `X⋆`. -/
structure routeAOkR (N : NumA) (bF : ℝ) (σ m₀ : Fin 7 → ℝ) (Xs : ℝ) : Prop where
  Xs_nonneg : 0 ≤ Xs
  J1 : ∀ s < N.kp, N.CondR bF s (N.xS Xs s)
  J1t : N.CondR bF N.kp (N.xS Xs N.kp)
  J2 : 2 ^ (2 * (2 * N.τ)) * (N.stageR N.kp).CE * N.xS Xs N.kp ≤ 1
  J3 : ∀ i, m₀ i + sumA (2 * N.τ) 3 N.ρ N.ρinf N.γb (N.xS Xs) (fun s => (N.stageR s).rate i)
    (2 * N.τ + (jR i : ℝ)) N.kp ≤ σ i

/-- `routeAOkR` is the engine's `RunData`. -/
theorem routeAOkR.runData {N : NumA} (hN : N.Wf) {bF : ℝ} {σ m₀ : Fin 7 → ℝ} {Xs : ℝ}
    (h : routeAOkR N bF σ m₀ Xs) :
    RunData (2 * N.τ) 3 N.ρ N.ρinf N.γb N.stageR jR (fun s x => N.CondR bF s x) σ m₀ N.kp Xs where
  two_le_a := by linarith [hN.τ_ge]
  j_le := by intro i; fin_cases i <;> simp [jR]
  CE_nonneg := fun s => (hN.pos s).CE
  CD_nonneg := fun s => (hN.pos s).CDK
  Cp_nonneg := fun _ => le_rfl
  rate_nonneg := fun s i => NumA.rateR_nonneg (hN.pos s) i
  tail := fun _ hs => NumA.stageR_tail hs
  Xs_nonneg := h.Xs_nonneg
  down := fun _ _ _ _ hxy hc => hc.down hN hxy
  J1 := h.J1
  J1t := fun s hs => ⟨by rw [NumA.inp_tail hs]; exact h.J1t.base, by
    rw [NumA.bLocS_tail hs]; exact h.J1t.loc⟩
  J2 := h.J2
  J3 := h.J3

end KAM.Sharp2.RouteA

end
