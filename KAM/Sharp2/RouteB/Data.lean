/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModStepB
public import KAM.Sharp2.EngineRatio

/-!
# Route B: the numbers, certificates, initial values and the engine predicate

The declarations of `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt` (module
`KAM/Sharp2/RouteB/Data.lean`, SHARP2-FIX), verbatim (lines wrapped at 100 characters):

* `NumB`: the numbers of a run (caps, Hamiltonian data, budgets, ratios, schedule ratio `a`, decay
  bound `ȳ`, prefix length, certificates, option L10, stage-0 data); `NumB.inp s`, the inputs of
  stage `s` (the tail record from `kp` on); `NumB.stage s`, the engine's constants;
* `NumB.Wf`, `NumB.Cert` (the Fourier certificates on a set `Ω`), `InitB`, `InitB.Wf`, `RefHypB`
  (bounds on explicit objects of `h`, `K`), `NumB.Fits` (the stage-0 weights);
* `initB`, `capB` (the caps: `Tab` with the Neumann budget of `bp:p2s2:torsion-ref`),
  `routeBOk` ((J1)–(J4) at `X⋆`), `pN`, `c1B`, `c2B`, `c3B`, `defaultInitB`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2

/-- The numbers of a run of route B (`bp:p2s2:data-ok`): caps used in the constants, Hamiltonian
data, budgets, ratios, schedule ratio `a`, decay bound `ȳ`, prefix length `kp`, certificates of the
prefix (`c` at `δ_s`, `c'` at the split bite `τ/(τ+1) δ_s`, `cbar` at the full bite `min (r_s) 1`),
of the tail (`ctail` at every bite `≤ δ_kp`, `cbtail` at every full
bite `min (r_j) 1`, `j ≥ kp`), the option L10 and the stage-0 data. -/
structure NumB (n : ℕ) where
  τ : ℝ
  ρ : ℝ
  ρinf : ℝ
  γb : ℝ
  M1 : ℝ
  M2 : ℝ
  cTh : ℝ
  cDTh : ℝ
  sK : ℝ
  sLt : ℝ
  sB : ℝ
  sN : ℝ
  sNt : ℝ
  sT : ℝ
  ts : ℝ
  bF : ℝ
  θ : ℝ
  θξ : ℝ
  θΩ : ℝ
  q : ℝ
  θN : ℝ
  θω : ℝ
  a : ℝ
  ybar : ℝ
  kp : ℕ
  c : ℕ → ℝ
  c' : ℕ → ℝ
  cbar : ℕ → ℝ
  ctail : ℝ
  cbtail : ℝ
  selfcons : Bool := false
  lam0 : ℝ
  lamW0 : ℝ := 1
  ePer0 : ℝ
  iso : Bool := false
  Θ : ℝ := 0
  y0 : ℝ := 0
  Mh2 : ℝ := 0

namespace NumB

variable {n : ℕ} (N : NumB n)

/-- `δ₀`. -/
def δ0 : ℝ := bite0R N.a N.ρ N.ρinf
/-- `δ_s`. -/
def δ (s : ℕ) : ℝ := biteSR N.a N.ρ N.ρinf s
/-- `r_s`. -/
def r (s : ℕ) : ℝ := stripSR N.a N.ρ N.ρinf s
/-- The full bite of the averages, `min (r_s) 1`. -/
def bfull (s : ℕ) : ℝ := min (N.r s) 1
/-- The optimal Rüssmann-Cauchy split `τ/(τ+1)` and its factor `(τ+1)^{τ+1}/τ^τ`. -/
def split : ℝ := N.τ / (N.τ + 1)
/-- The Rüssmann-Cauchy factor. -/
def rcf : ℝ := (N.τ + 1) ^ (N.τ + 1) / N.τ ^ N.τ

/-- The inputs of stage `s` (the tail record for `s ≥ kp`, with the bite value `δ_kp`). -/
def inp (s : ℕ) : StepInB :=
  { n := n, κ := N.τ, M1 := N.M1, M2 := N.M2, cTh := N.cTh, cDTh := N.cDTh, sK := N.sK,
    sLt := N.sLt, sB := N.sB,
    sN := N.sN, sNt := N.sNt, sT := N.sT, ts := N.ts, bF := N.bF,
    c := if s < N.kp then N.c s else N.ctail,
    c1 := (if s < N.kp then N.c' s else N.ctail) * N.rcf,
    cavg := if s < N.kp then N.cbar s * (N.δ s / N.bfull s) ^ N.τ
      else N.cbtail * (N.δ N.kp / N.bfull N.kp) ^ N.τ,
    θ := N.θ, θξ := N.θξ, θΩ := N.θΩ, q := N.q, θN := N.θN, θω := N.θω, a := N.a,
    lam := if s = 0 then N.lam0 else 1, γb := N.γb, δ := N.δ (min s N.kp), selfcons := N.selfcons,
    stage0 := decide (s = 0), ePer := N.ePer0, iso := N.iso, Θ := N.Θ, y0 := N.y0, Mh2 := N.Mh2,
    lamW := if s = 0 then N.lamW0 else 1 }

/-- `Q_s`. -/
def Qs (s : ℕ) : ℝ := (stepConstsB (N.inp s)).Q
/-- The normalized errors from `X⋆`. -/
def xS (Xs : ℝ) : ℕ → ℝ := xSeqR N.a (N.τ + 1) N.Qs Xs
/-- The seven cap rates: `DK`, `Lᵀ`, `B`, `N`, `Nᵀ`, `Tab`, the frequency. -/
def rate (s : ℕ) : Fin 7 → ℝ :=
  ![n * (stepConstsB (N.inp s)).CDK, 2 * n * (stepConstsB (N.inp s)).CDK,
    (stepConstsB (N.inp s)).CBb,
    (stepConstsB (N.inp s)).CNb, (stepConstsB (N.inp s)).CNbT, (stepConstsB (N.inp s)).Cab,
    (stepConstsB (N.inp s)).Cnu]
/-- Their weights. -/
def wt (s : ℕ) : Fin 7 → ℝ := ![1, 1, 1, 1, 1, 1, N.γb * N.δ (min s N.kp) ^ (N.τ + 1)]
/-- The engine's constants of stage `s`. -/
def stage (s : ℕ) : StageConsts 7 where
  Q := N.Qs s
  cond := stepCondB (N.inp s)
  CDK := (stepConstsB (N.inp s)).CDK
  Cp := (stepConstsB (N.inp s)).Cnu
  rate := N.rate s
  wt := N.wt s
/-- The ball sum (J4), bounding `|K∞ - K|`. -/
def ballSum (Xs : ℝ) : ℝ :=
  (∑ s ∈ Finset.range N.kp, (stepConstsB (N.inp s)).CDK * N.δ s * N.xS Xs s) +
    (stepConstsB (N.inp N.kp)).CDK * N.δ N.kp * N.xS Xs N.kp / (1 - N.ybar)
/-- The frequency sum (iso), bounding `|s∞ ω* - s ω*|`. -/
def freqSum (Xs : ℝ) : ℝ :=
  (∑ s ∈ Finset.range N.kp, (stepConstsB (N.inp s)).Cnu * (N.γb * N.δ s ^ (N.τ + 1)) * N.xS Xs s) +
    (stepConstsB (N.inp N.kp)).Cnu * (N.γb * N.δ N.kp ^ (N.τ + 1)) * N.xS Xs N.kp / (1 - N.ybar)

end NumB

/-- Well-formed numbers (`bp:p2s2:data-ok`, audit F1). -/
structure NumB.Wf {n : ℕ} (N : NumB n) : Prop where
  two_le : 2 ≤ n
  τ_ge : 1 ≤ N.τ
  ρinf_pos : 0 < N.ρinf
  ρinf_lt : N.ρinf < N.ρ
  ρ_le : N.ρ ≤ 1
  nonneg : 0 ≤ N.M1 ∧ 0 ≤ N.M2 ∧ 0 ≤ N.cTh ∧ 0 ≤ N.cDTh ∧ 0 ≤ N.Θ ∧ 0 ≤ N.y0 ∧ 0 ≤ N.Mh2 ∧
    0 ≤ N.ePer0
  caps : 0 < N.sK ∧ 0 < N.sLt ∧ 0 < N.sB ∧ 0 < N.sN ∧ 0 < N.sNt ∧ 0 < N.sT
  budgets : 0 < N.ts ∧ 0 < N.bF
  ratios : 0 < N.θ ∧ N.θ < 1 ∧ 0 < N.θξ ∧ N.θξ < 1 ∧ 0 < N.θΩ ∧ N.θΩ < 1 ∧ 0 < N.q ∧ N.q < 1 ∧
    0 < N.θN ∧ N.θN < 1 ∧ 0 < N.θω ∧ N.θω < 1
  a_gt : 1 < N.a
  ybar : 0 < N.ybar ∧ N.ybar < 1
  kp_pos : 1 ≤ N.kp
  lam : 0 < N.lam0 ∧ N.lam0 ≤ 1 ∧ 0 < N.lamW0 ∧ N.lamW0 ≤ 1
  γb : 0 < N.γb
  sd : (∀ s, 0 < N.c s) ∧ (∀ s, 0 < N.c' s) ∧ (∀ s, 0 < N.cbar s) ∧ 0 < N.ctail ∧ 0 < N.cbtail

/-- The Fourier certificates (R4) on a set `Ω` at the scale `γ`: statements about the linear
solver at explicit bites. -/
structure NumB.Cert {n : ℕ} (N : NumB n) (γ : ℝ) (Ω : Set (Fin n → ℝ)) : Prop where
  stage : ∀ s < N.kp, SDConst n N.τ γ (N.δ s) (N.c s) Ω
  split : ∀ s < N.kp, SDConst n N.τ γ (N.split * N.δ s) (N.c' s) Ω
  bar : ∀ s < N.kp, SDConst n N.τ γ (N.bfull s) (N.cbar s) Ω
  tail : ∀ b, 0 < b → b ≤ N.δ N.kp → SDConst n N.τ γ b N.ctail Ω
  tailbar : ∀ j, N.kp ≤ j → SDConst n N.τ γ (N.bfull j) N.cbtail Ω

/-- The initial values of the refined data (R2) (route B derives the torsion cap, so no initial
torsion value). -/
structure InitB where
  iLt : ℝ
  iN : ℝ
  iNt : ℝ

/-- Positive initial values strictly below the caps (audit F1, F3). -/
structure InitB.Wf {n : ℕ} (I : InitB) (N : NumB n) (σT μ : ℝ) : Prop where
  pos : 0 < I.iLt ∧ 0 < I.iN ∧ 0 < I.iNt
  lt : I.iLt < N.sLt ∧ I.iN < N.sN ∧ I.iNt < N.sNt
  torsion : 0 < σT - μ ∧ σT - μ < N.sT

/-- The refined hypotheses (R1)–(R2) with initial values: bounds on explicit objects of `h` and
`K`. -/
structure RefHypB {n : ℕ} (N : NumB n) (I : InitB) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ρ : ℝ) :
    Prop where
  dX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1
  d2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2
  comm : ∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ N.cTh
  lip : ∀ z ∈ 𝔅, ∀ z' ∈ 𝔅, segment ℝ z z' ⊆ 𝔅 → ‖hamComm h z - hamComm h z'‖ ≤ N.cDTh * ‖z - z'‖
  tangentT : ∀ θ ∈ complexStrip n ρ, ‖(tangentMat K θ)ᵀ‖ ≤ I.iLt
  normal : ∀ θ ∈ complexStrip n ρ, ‖normalMat K θ‖ ≤ I.iN
  normalT : ∀ θ ∈ complexStrip n ρ, ‖(normalMat K θ)ᵀ‖ ≤ I.iNt

/-- The stage-0 weights fit every body scale `γ ≤ γ̄` (clipped weights, audit iso F4): with
`p̄ = max {σ_{Nᵀ}, σ_{Lᵀ}/(γ̄ δ₀^τ), 1 (iso)}`, `λ₀ ≥ σ_{Nᵀ}/p̄`, `λ_{ω,0} ≥ 1/p̄`,
`e/μ₀ ≤ 1/p̄`. -/
structure NumB.Fits {n : ℕ} (N : NumB n) (I : InitB) : Prop where
  lam0 : I.iNt / max (max I.iNt (I.iLt / (N.γb * N.δ0 ^ N.τ))) (if N.iso then 1 else 0) ≤ N.lam0
  lamW0 : N.iso = true → 1 / max (max I.iNt (I.iLt / (N.γb * N.δ0 ^ N.τ))) 1 ≤ N.lamW0
  ePer0 : 1 / max (max I.iNt (I.iLt / (N.γb * N.δ0 ^ N.τ))) (if N.iso then 1 else 0) ≤ N.ePer0

/-- The initial cap values. -/
def initB (I : InitB) (σK σB μ : ℝ) : Fin 7 → ℝ := ![σK - μ, I.iLt, σB - μ, I.iN, I.iNt, 0, 0]

/-- The caps: frames as in `N`, `Tab` with the Neumann budget `β_T - 2 b_F` (`bp:p2s2:torsion-ref`,
`β_T = (σ̂_T - m_T)/(σ̂_T m_T)`, `m_T = σ_T - μ`), the frequency with budget `ν/2`. -/
def capB {n : ℕ} (N : NumB n) (σT μ ν : ℝ) : Fin 7 → ℝ :=
  ![N.sK, N.sLt, N.sB, N.sN, N.sNt, (N.sT - (σT - μ)) / (N.sT * (σT - μ)) - 2 * N.bF, ν / 2]

/-- (J1)–(J4) of `bp:p2s2:engine` for route B at `X⋆` (all caps in J3, tail conditions on
`[0, X_kp]`). -/
structure routeBOk {n : ℕ} (N : NumB n) (σ m₀ : Fin 7 → ℝ) (β Xs : ℝ) : Prop where
  Xs_nonneg : 0 ≤ Xs
  J1 : ∀ s < N.kp, stepCondB (N.inp s) (N.xS Xs s)
  J1t : ∀ X, 0 ≤ X → X ≤ N.xS Xs N.kp → stepCondB (N.inp N.kp) X
  J2 : N.a ^ (N.τ + 1) * N.Qs N.kp * N.xS Xs N.kp ≤ N.ybar
  J3 : ∀ i, m₀ i + (∑ s ∈ Finset.range N.kp, N.rate s i * N.wt s i * N.xS Xs s) +
    N.rate N.kp i * N.wt N.kp i * N.xS Xs N.kp / (1 - N.ybar) ≤ σ i
  J4 : N.ballSum Xs < β

/-- The coefficient `p̄₀` of the stage-0 error in `X₀` (fixed: `σ_{Nᵀ}`, iso: `max {σ_{Nᵀ}, 1}`). -/
def pN {n : ℕ} (N : NumB n) (I : InitB) : ℝ := if N.iso then max I.iNt 1 else I.iNt

/-- `C₁` of route B (`bp:p2s2:frozen-form`). -/
def c1B {n : ℕ} (N : NumB n) (I : InitB) (Xs : ℝ) : ℝ :=
  N.ρ ^ (4 * N.τ) * max (I.iLt * N.γb ^ 2) (pN N I * N.γb ^ 3 * N.δ0 ^ N.τ) /
    (Xs * N.δ0 ^ (2 * N.τ + 1))

/-- `C₂` of route B: the ball sum, without `γ̄²` (audit F6). -/
def c2B {n : ℕ} (N : NumB n) (I : InitB) (Xs : ℝ) : ℝ :=
  N.ρ ^ (2 * N.τ) * max I.iLt (pN N I * N.γb * N.δ0 ^ N.τ) * N.ballSum Xs /
    (Xs * N.δ0 ^ (2 * N.τ + 1))

/-- `C₃` of route B (iso): the frequency sum, without `γ̄²` (audit iso F3). -/
def c3B {n : ℕ} (N : NumB n) (I : InitB) (Xs : ℝ) : ℝ :=
  N.ρ ^ (2 * N.τ) * max I.iLt (pN N I * N.γb * N.δ0 ^ N.τ) * N.freqSum Xs /
    (Xs * N.δ0 ^ (2 * N.τ + 1))

/-- The default initial values (`bp:p2s2:defaults`). -/
def defaultInitB (n : ℕ) (σK σB μ : ℝ) : InitB :=
  ⟨2 * n * (σK - μ), (σK - μ) * (σB - μ), 2 * n * (σK - μ) * (σB - μ)⟩

end KAM.Sharp2.RouteB

end
