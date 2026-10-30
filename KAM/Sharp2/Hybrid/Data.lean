/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Torsion
public import KAM.Sharp2.RouteA.Ref.G1

/-!
# The data of the hybrid theorem (`bp:p2s2hc:bounds`, `bp:p2s2hc:data`)

* `KData`: the certified data of `K`;
* `StepNum`, `StepBounds`: the step bounds `(S1)–(S7)`, each a bound on an explicit object;
* `StepNum.e1`, `frS`, `frR`, `lam0`, `lam1`, `t1`, `tA`, `init1`, `sK1`, `sB1`, `sT1`: the
  transferred values of Definition `bp:p2s2hc:data`, explicit functions of the step bounds and of
  the certified data of `K`;
* `RestartA`, `NumA.restart`, `HybOkR`: the restart numbers of route A with L8′ and the hybrid
  condition `HybOk_A'`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA

variable {n : ℕ}

/-- Certified data of `K` (Assumption `bp:p2s2hc:standing`(b)): `ℓ = σ_K - μ`, `β = σ_B - μ`,
`m = σ_T - μ`, and the refined initial values `ℓᵗ`, `ν`, `νᵗ`, `t`. -/
structure KData where
  ℓ : ℝ
  ℓt : ℝ
  β : ℝ
  ν : ℝ
  νt : ℝ
  t : ℝ
  m : ℝ

/-- The step bounds of Definition `bp:p2s2hc:bounds` (numbers). -/
structure StepNum where
  d0 : ℝ
  dinf : ℝ
  d1 : ℝ
  d1t : ℝ
  d0R : ℝ
  d1R : ℝ
  d1tR : ℝ
  lE : ℝ
  dE0 : ℝ
  o0 : ℝ
  dE0R : ℝ
  o0R : ℝ
  o1 : ℝ
  o1R : ℝ

/-- `(S1)–(S7)`: each a bound on an explicit object; `ρT` is the torsion strip `ρ₁ - δ₀'`; `ω` is
the frequency of `K`, `ω₁` that of `K₁` (`ω₁ = ω` at fixed frequency; `s ω*`, `s₁ ω*` in the iso
form, where `linNewError` at `s₁ ω*` is `Ẽ_s`). -/
structure StepBounds (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω ω₁ : Fin n → ℝ) (ρ₁ ρinf ρT : ℝ)
    (b : StepNum) : Prop where
  d0 : ∀ θ ∈ complexStrip n ρ₁, ‖ΔK θ‖ ≤ b.d0
  dinf : ∀ θ ∈ complexStrip n ρinf, ‖ΔK θ‖ ≤ b.dinf
  d1 : ∀ θ ∈ complexStrip n ρ₁, ‖tangentMat ΔK θ‖ ≤ b.d1 ∧ ‖(tangentMat ΔK θ)ᵀ‖ ≤ b.d1t
  real : ∀ θ : Fin n → ℝ, ‖ΔK fun l => (θ l : ℂ)‖ ≤ b.d0R ∧
    ‖tangentMat ΔK (fun l => (θ l : ℂ))‖ ≤ b.d1R ∧ ‖(tangentMat ΔK (fun l => (θ l : ℂ)))ᵀ‖ ≤ b.d1tR
  lin : ∀ θ ∈ complexStrip n ρ₁, ‖linNewError h K ΔK ω₁ θ‖ ≤ b.lE
  loc0 : ∀ θ ∈ complexStrip n ρT, ‖errDerivMat h K ω θ‖ ≤ b.dE0 ∧ ‖lagrangeMat K θ‖ ≤ b.o0
  loc0R : ∀ θ : Fin n → ℝ, ‖errDerivMat h K ω (fun l => (θ l : ℂ))‖ ≤ b.dE0R ∧
    ‖lagrangeMat K (fun l => (θ l : ℂ))‖ ≤ b.o0R
  loc1 : ∀ θ ∈ complexStrip n ρT, ‖lagrangeMat (K + ΔK) θ‖ ≤ b.o1
  loc1R : ∀ θ : Fin n → ℝ, ‖lagrangeMat (K + ΔK) (fun l => (θ l : ℂ))‖ ≤ b.o1R

namespace StepNum

variable (b : StepNum) (k : KData)

/-- `e₁ = ℓ_E + (M₂/2) d₀²` (Lemma `bp:p2s2hc:error`). -/
def e1 (M2 : ℝ) : ℝ := b.lE + M2 / 2 * b.d0 ^ 2
/-- The frame numbers on the strip. -/
def frS : FrameNum := ⟨k.ℓ, k.ℓt, k.β, k.ν, k.νt, b.d1, b.d1t⟩
/-- The frame numbers on the real torus. -/
def frR : FrameNum := ⟨k.ℓ, k.ℓt, k.β, k.ν, k.νt, b.d1R, b.d1tR⟩
/-- A bound of the matrix `W` of the local torsion part (`bp:p2s2hc:torsion`). -/
def wB (nn M1 ℓ ℓt dE : ℝ) : ℝ := ℓt * (4 * nn * M1) * ℓ + dE * (2 * nn * ℓ + ℓt)
/-- `λ₀`, the local part of `K`'s torsion, on the strip `T'` (`real = false`) or on `ℝⁿ`. -/
def lam0 (nn M1 : ℝ) (real : Bool) : ℝ :=
  let dE := if real then b.dE0R else b.dE0
  let o := if real then b.o0R else b.o0
  k.νt * k.β * dE + k.β ^ 3 * wB nn M1 k.ℓ k.ℓt dE * o
/-- `λ₁`, the local part of `K₁`'s torsion, with `ε₁' = n e₁/δ` (Cauchy). -/
def lam1 (nn M1 M2 δ : ℝ) (real : Bool) : ℝ :=
  let F := if real then b.frR k else b.frS k
  let dE := nn * δ⁻¹ * b.e1 M2
  let o := if real then b.o1R else b.o1
  (F.νt + F.nΔt) * F.β1 * dE + F.β1 ^ 3 * wB nn M1 (F.ℓ + F.d1) (F.ℓt + F.d1t) dE * o
/-- `t₁`, the torsion bound of `K₁` on `T'` (Lemma `bp:p2s2hc:torsion`(c)). -/
def t1 (nn M1 M2 δ cTh : ℝ) : ℝ :=
  min (k.t + dAB (b.frS k) cTh (2 * M2) b.d0 + b.lam0 k nn M1 false)
      (((b.frS k).νt + (b.frS k).nΔt) * cTh * ((b.frS k).ν + (b.frS k).nΔ)) +
    b.lam1 k nn M1 M2 δ false
/-- `t_A ≥ |⟨T₁⟩ - ⟨T⟩|` (Lemma `bp:p2s2hc:torsion`(d)). -/
def tA (nn M1 M2 δ cTh : ℝ) : ℝ :=
  dAB (b.frR k) cTh (2 * M2) b.d0R + b.lam0 k nn M1 true + b.lam1 k nn M1 M2 δ true
/-- The transferred initial values of `K₁` (Definition `bp:p2s2hc:data`). -/
def init1 (nn M1 M2 δ cTh : ℝ) : InitA :=
  ⟨k.ℓt + b.d1t, k.ν + (b.frS k).nΔ, k.νt + (b.frS k).nΔt, b.t1 k nn M1 M2 δ cTh⟩
/-- `σ_{K,1} = ℓ + d₁ + μ₁`. -/
def sK1 (μ₁ : ℝ) : ℝ := k.ℓ + b.d1 + μ₁
/-- `σ_{B,1} = β₁ + μ₁`. -/
def sB1 (μ₁ : ℝ) : ℝ := (b.frS k).β1 + μ₁
/-- `σ_{T,1} = m/(1 - m t_A) + μ₁`. -/
def sT1 (nn M1 M2 δ cTh μ₁ : ℝ) : ℝ := k.m / (1 - k.m * b.tA k nn M1 M2 δ cTh) + μ₁

end StepNum

/-- The restart numbers of route A: the strip `ρ₁`, the caps and the small-divisor data of the
schedule from `ρ₁` replace those of `N`; `(N.restart R).n = N.n` definitionally. -/
structure RestartA where
  ρ₁ : ℝ
  sK : ℝ
  sB : ℝ
  sT : ℝ
  sLt : ℝ
  sN : ℝ
  sNt : ℝ
  t : ℝ
  c : ℕ → ℝ
  cbar : ℕ → ℝ
  ctail : ℝ
  kp : ℕ
  bbar : ℕ → ℝ

/-- `NumA.restart` (Definition `bp:p2s2hc:data`). -/
def _root_.KAM.Sharp2.RouteA.NumA.restart (N : NumA) (R : RestartA) : NumA :=
  { N with
    ρ := R.ρ₁
    sK := R.sK
    sB := R.sB
    sT := R.sT
    sLt := R.sLt
    sN := R.sN
    sNt := R.sNt
    t := R.t
    c := R.c
    cbar := R.cbar
    ctail := R.ctail
    kp := R.kp
    bbar := R.bbar }

theorem restart_n (N : NumA) (R : RestartA) : (N.restart R).n = N.n := rfl

/-- The hybrid condition `HybOk_A'` of Definition `bp:p2s2hc:data` for `K` with the data `k`, the
step numbers `b`, the restart `N₁ = N.restart R`, margin `μ₁`, `X⋆`, budgets `bF`, `bT`. -/
structure HybOkR (N : NumA) (R : RestartA) (k : KData) (b : StepNum)
    (σK σB σT μ μ₁ γ Xs bF bT cTh : ℝ) : Prop where
  wf : (N.restart R).Wf
  μ₁_pos : 0 < μ₁
  ρ_le : R.ρ₁ ≤ N.ρ
  ℓ : k.ℓ = σK - μ
  β : k.β = σB - μ
  m : k.m = σT - μ
  sK : R.sK = b.sK1 k μ₁ - μ₁ / 2
  ok : routeAOkR (N.restart R) bF ((N.restart R).capR (μ₁ / 2) bT)
      (initR (b.init1 k N.n N.M1 N.M2 ((N.restart R).δ 0) cTh) (b.sK1 k μ₁) (b.sB1 k μ₁) μ₁) Xs
  budget : Ref.Budget (N.restart R) (b.sT1 k N.n N.M1 N.M2 ((N.restart R).δ 0) cTh μ₁ - μ₁)
      (b.init1 k N.n N.M1 N.M2 ((N.restart R).δ 0) cTh).iH bF bT
  Xs_pos : 0 < Xs
  m1 : b.d0 + μ₁ ≤ μ
  m2 : b.d1 + μ₁ / 2 ≤ μ / 2
  gS : k.β * (b.frS k).g < 1
  gR : k.β * (b.frR k).g < 1
  tA : k.m * b.tA k N.n N.M1 N.M2 ((N.restart R).δ 0) cTh < 1
  small : b.e1 N.M2 / (γ ^ 4 * delta0 3 R.ρ₁ N.ρinf ^ (2 * (2 * N.τ))) < Xs
  bud : b.dinf + c2A (N.restart R) Xs * b.e1 N.M2 / (γ ^ 2 * R.ρ₁ ^ (2 * N.τ)) ≤ μ / 2

end KAM.Sharp2.Hybrid

end
