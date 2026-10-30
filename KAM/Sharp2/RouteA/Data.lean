/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Arith
public import KAM.Sharp2.RouteA.Engine
public import KAM.Sharp2.SmallDiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# The numerical data of a run of route A

Audit finding F3: numerical data, object bounds and Fourier certificates are separate packages.

* `NumA`: the numbers of a run (caps, schedule, small-divisor constants);
* `NumA.inp`: the inputs of the step at stage `s` (from `kp` on, the tail inputs, valid for every
  bite
  `≤ δ_kp`);
* `NumA.stage`, `jA`: the stage constants of the engine and the eight rates (ball, `|DK|`, `|B|`,
  `|⟨T⟩⁻¹|`, `|Lᵀ|`, `|N|`, `|Nᵀ|`, `|T|`);
* `NumA.Wf`: well-formedness;
* `NumA.Cert`: the small-divisor certificates at the schedule, on a set of frequencies;
* `routeAOk`: (J1)–(J3) at `X⋆`, finitely many inequalities between explicit numbers.
-/

@[expose] public noncomputable section

open KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA

/-- The numbers of a run of route A. `c s`, `cbar s` are the small-divisor constants at the bites
`δ_s`, `r_s` of the prefix `s < kp`, `ctail` a constant valid at every bite `≤ δ_kp`. The last four
fields are the isoenergetic inputs. -/
structure NumA where
  n : ℕ
  τ : ℝ
  ρ : ℝ
  ρinf : ℝ
  M1 : ℝ
  M2 : ℝ
  sK : ℝ
  sB : ℝ
  sT : ℝ
  sLt : ℝ
  sN : ℝ
  sNt : ℝ
  t : ℝ
  th : ℝ
  γb : ℝ
  c : ℕ → ℝ
  cbar : ℕ → ℝ
  ctail : ℝ
  kp : ℕ
  iso : Bool := false
  Θ : ℝ := 0
  HY : ℝ := 0
  Mh2 : ℝ := 0

namespace NumA

variable (N : NumA)

/-- `δ_s = 2^{-s} δ₀`, `δ₀ = min {1, (ρ - ρ∞)/6}`. -/
def δ (s : ℕ) : ℝ := deltaSeq 3 N.ρ N.ρinf s
/-- `r_s = ρ - 6δ₀(1 - 2^{-s})`. -/
def r (s : ℕ) : ℝ := rSeq 3 N.ρ N.ρinf s
/-- `c(δ_s)` in the prefix, `c_∞` in the tail. -/
def cS (s : ℕ) : ℝ := if s < N.kp then N.c s else N.ctail
/-- The average constant: `c̄_s (δ_s/r_s)^τ` in the prefix (`bp:p2s2sd:avg`), `c_∞` in the tail. -/
def caS (s : ℕ) : ℝ :=
  if s < N.kp then N.cbar s * (N.δ s / N.r s) ^ N.τ else N.ctail
/-- The value of the bite in the constants: `δ_s` in the prefix, `δ_kp` in the tail. -/
def dS (s : ℕ) : ℝ := N.δ (min s N.kp)

/-- The inputs of the step at stage `s`. -/
def inp (s : ℕ) : StepInA :=
  { n := N.n, κ := N.τ, M1 := N.M1, M2 := N.M2, sK := N.sK, sB := N.sB, sT := N.sT, sLt := N.sLt,
    sN := N.sN, sNt := N.sNt, t := N.t, c := N.cS s, ca := N.caS s, γb := N.γb, δ := N.dS s,
    th := N.th, iso := N.iso, Θ := N.Θ, HY := N.HY, Mh2 := N.Mh2 }

/-- The eight rates of the fixed-frequency step. -/
def rateV (p : StepInA) : Fin 8 → ℝ :=
  ![p.CDK, p.n * p.CDK, p.CB * p.CDK, p.rT, 2 * p.n * p.CDK, p.CNd * p.CDK, p.CNtd * p.CDK, p.CDT]

/-- The constants of stage `s`. -/
def stage (s : ℕ) : StageA 8 where
  CE := (N.inp s).CE
  CD := (N.inp s).CDK
  Cp := 0
  rate := rateV (N.inp s)

/-- The recursion of the normalised error from `Xs`. -/
def xS (Xs : ℝ) : ℕ → ℝ := xA (2 * N.τ) (fun s => (N.stage s).CE) Xs

end NumA

/-- The weight exponents of the eight rates: `j = 0` for the ball, `1` for the frames. -/
def jA : Fin 8 → ℕ := ![0, 1, 1, 1, 1, 1, 1, 1]

/-- Well-formed numbers. -/
structure NumA.Wf (N : NumA) : Prop where
  two_le : 2 ≤ N.n
  τ_ge : 1 ≤ N.τ
  ρinf_pos : 0 < N.ρinf
  ρinf_lt : N.ρinf < N.ρ
  M1 : 0 ≤ N.M1
  M2 : 0 ≤ N.M2
  sK : 0 < N.sK
  sB : 0 < N.sB
  sT : 0 < N.sT
  sLt : 0 ≤ N.sLt
  sN : 0 ≤ N.sN
  sNt : 0 ≤ N.sNt
  t : 0 ≤ N.t
  th0 : 0 < N.th
  th1 : N.th < 1
  γb : 0 < N.γb
  c : ∀ s, 0 ≤ N.c s
  cbar : ∀ s, 0 ≤ N.cbar s
  ctail : 0 ≤ N.ctail
  Θ : 0 ≤ N.Θ
  HY : 0 ≤ N.HY
  Mh2 : 0 ≤ N.Mh2

/-- The small-divisor certificates at the schedule, on the set `Ω`: the data `(R4)`. These are
statements about the linear solver at explicit bites, not about the torus. -/
structure NumA.Cert (N : NumA) (γ : ℝ) (Ω : Set (Fin N.n → ℝ)) : Prop where
  stage : ∀ s < N.kp, SDConst N.n N.τ γ (N.δ s) (N.c s) Ω
  bar : ∀ s < N.kp, SDConst N.n N.τ γ (N.r s) (N.cbar s) Ω
  tail : ∀ δ, 0 < δ → δ ≤ N.δ N.kp → SDConst N.n N.τ γ δ N.ctail Ω

namespace NumA

variable {N : NumA}

theorem Wf.lam : (0 : ℝ) < 3 := by norm_num

theorem Wf.δ_pos (hN : N.Wf) (s : ℕ) : 0 < N.δ s :=
  ((schedule Wf.lam hN.ρinf_pos hN.ρinf_lt).2.2.2.2.2.1 s).1

theorem Wf.δ_le (hN : N.Wf) (s : ℕ) : N.δ s ≤ 1 :=
  ((schedule Wf.lam hN.ρinf_pos hN.ρinf_lt).2.2.2.2.2.1 s).2

theorem Wf.lam_δ_lt (hN : N.Wf) (s : ℕ) : 3 * N.δ s < N.r s :=
  (schedule Wf.lam hN.ρinf_pos hN.ρinf_lt).2.2.2.2.2.2 s

theorem Wf.ρinf_lt_r (hN : N.Wf) (s : ℕ) : N.ρinf < N.r s :=
  (schedule Wf.lam hN.ρinf_pos hN.ρinf_lt).2.2.2.2.1 s

theorem Wf.r_pos (hN : N.Wf) (s : ℕ) : 0 < N.r s := hN.ρinf_pos.trans (hN.ρinf_lt_r s)

theorem r_succ (s : ℕ) : N.r (s + 1) = N.r s - 3 * N.δ s := rSeq_succ s

theorem δ_succ (s : ℕ) : N.δ (s + 1) = N.δ s / 2 := deltaSeq_succ s

/-- `δ_s` is nonincreasing. -/
theorem Wf.δ_anti (hN : N.Wf) {j s : ℕ} (h : j ≤ s) : N.δ s ≤ N.δ j := by
  have hd : 0 < delta0 3 N.ρ N.ρinf := delta0_pos Wf.lam hN.ρinf_lt
  have h2 : (2 : ℝ)⁻¹ ^ s ≤ (2 : ℝ)⁻¹ ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  exact mul_le_mul_of_nonneg_right h2 hd.le

/-- The actual bite is at most the value of the bite in the constants. -/
theorem Wf.δ_le_dS (hN : N.Wf) (s : ℕ) : N.δ s ≤ N.dS s := hN.δ_anti (min_le_left _ _)

theorem Wf.pos (hN : N.Wf) (s : ℕ) : (N.inp s).Pos where
  n_pos := by have := hN.two_le; show 1 ≤ N.n; omega
  κ_ge := hN.τ_ge
  M1 := hN.M1
  M2 := hN.M2
  sK := hN.sK.le
  sB := hN.sB.le
  sT := hN.sT.le
  sLt := hN.sLt
  sN := hN.sN
  sNt := hN.sNt
  t := hN.t
  c := by
    show 0 ≤ N.cS s
    unfold cS
    split_ifs
    · exact hN.c s
    · exact hN.ctail
  ca := by
    show 0 ≤ N.caS s
    unfold caS
    split_ifs
    · exact mul_nonneg (hN.cbar s) (Real.rpow_nonneg (div_nonneg (hN.δ_pos s).le (hN.r_pos s).le) _)
    · exact hN.ctail
  γb := hN.γb
  δ := hN.δ_pos _
  δ1 := hN.δ_le _
  th0 := hN.th0
  th1 := hN.th1
  Θ := hN.Θ
  HY := hN.HY
  Mh2 := hN.Mh2

/-- The inputs are constant from `kp` on. -/
theorem inp_tail {s : ℕ} (hs : N.kp ≤ s) : N.inp s = N.inp N.kp := by
  have h1 : N.cS s = N.ctail := by simp [cS, Nat.not_lt.2 hs]
  have h2 : N.caS s = N.ctail := by simp [caS, Nat.not_lt.2 hs]
  have h3 : N.dS s = N.δ N.kp := by simp [dS, min_eq_right hs]
  have h1' : N.cS N.kp = N.ctail := by simp [cS]
  have h2' : N.caS N.kp = N.ctail := by simp [caS]
  have h3' : N.dS N.kp = N.δ N.kp := by simp [dS]
  simp only [inp, h1, h2, h3, h1', h2', h3']

theorem stage_tail {s : ℕ} (hs : N.kp ≤ s) : N.stage s = N.stage N.kp := by
  simp only [stage, inp_tail hs]

/-- The rates are nonnegative. -/
theorem rateV_nonneg {p : StepInA} (hp : p.Pos) (i : Fin 8) : 0 ≤ rateV p i := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hDK := hp.CDK
  fin_cases i
  · exact hDK
  · exact mul_nonneg hn hDK
  · exact mul_nonneg hp.CB hDK
  · exact hp.rT
  · exact mul_nonneg (mul_nonneg two_pos.le hn) hDK
  · exact mul_nonneg hp.CNd hDK
  · exact mul_nonneg hp.CNtd hDK
  · exact hp.CDT

end NumA

/-- The step conditions are downward closed on nonnegative errors. -/
theorem StepInA.Cond.down {p : StepInA} (hp : p.Pos) {x y : ℝ} (hxy : x ≤ y) (h : p.Cond y) :
    p.Cond x := by
  have hw : ∀ {a b : ℝ}, 0 ≤ a → a * y ≤ b → a * x ≤ b := fun ha h1 =>
    (mul_le_mul_of_nonneg_left hxy ha).trans h1
  have hδ := hp.δ
  have hγ := hp.γb
  have hD4 : 0 ≤ p.δ ^ (2 * (2 * p.κ) - 1) := Real.rpow_nonneg hδ.le _
  have hD3 : 0 ≤ p.δ ^ (3 * p.κ - 1) := Real.rpow_nonneg hδ.le _
  have hD2 : 0 ≤ p.δ ^ (2 * p.κ - 1) := Real.rpow_nonneg hδ.le _
  have h1 := hp.CSym
  have h2 := hp.CE
  have h3 := hp.sT
  have h4 := hp.CDT
  have h5 := hp.sB
  have h6 := hp.CGr
  have h7 := hp.CDK
  exact ⟨hw (by positivity) h.err, hw (by positivity) h.sym, hw h2 h.quad, hw (by positivity)
      h.twist,
    hw (by positivity) h.gram⟩

/-- (J1)–(J3) of `bp:p2s2:engine` for route A at `X⋆`, with initial cap values `m₀` and caps `σ`. -/
structure routeAOk (N : NumA) (σ m₀ : Fin 8 → ℝ) (Xs : ℝ) : Prop where
  Xs_nonneg : 0 ≤ Xs
  J1 : ∀ s < N.kp, (N.inp s).Cond (N.xS Xs s)
  J1t : (N.inp N.kp).Cond (N.xS Xs N.kp)
  J2 : 2 ^ (2 * (2 * N.τ)) * (N.stage N.kp).CE * N.xS Xs N.kp ≤ 1
  J3 : ∀ i, m₀ i + sumA (2 * N.τ) 3 N.ρ N.ρinf N.γb (N.xS Xs) (fun s => (N.stage s).rate i)
    (2 * N.τ + (jA i : ℝ)) N.kp ≤ σ i

/-- `routeAOk` is the engine's `RunData`. -/
theorem routeAOk.runData {N : NumA} (hN : N.Wf) {σ m₀ : Fin 8 → ℝ} {Xs : ℝ}
    (h : routeAOk N σ m₀ Xs) :
    RunData (2 * N.τ) 3 N.ρ N.ρinf N.γb N.stage jA (fun s x => (N.inp s).Cond x) σ m₀ N.kp Xs where
  two_le_a := by linarith [hN.τ_ge]
  j_le := by intro i; fin_cases i <;> simp [jA]
  CE_nonneg := fun s => (hN.pos s).CE
  CD_nonneg := fun s => (hN.pos s).CDK
  Cp_nonneg := fun _ => le_rfl
  rate_nonneg := fun s i => NumA.rateV_nonneg (hN.pos s) i
  tail := fun _ hs => NumA.stage_tail hs
  Xs_nonneg := h.Xs_nonneg
  down := fun s _ _ _ hxy hc => hc.down (hN.pos s) hxy
  J1 := h.J1
  J1t := fun s hs => by rw [NumA.inp_tail hs]; exact h.J1t
  J2 := h.J2
  J3 := h.J3

end KAM.Sharp2.RouteA

end
