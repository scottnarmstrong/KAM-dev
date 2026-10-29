/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.Setting
public import KAM.Iso.Charts.Inputs
public import KAM.Iso.Linear.Defs
public import KAM.Head.Data
public import KAM.Head.Defs

/-!
# Part 3 (local charts): constants, coordinates, patches, rays and torus outputs

Definitions only (the only proofs are the two `rfl` bridges to
`KAM.Head.domainD` and `KAM.Head.hbold`). `n = 2`, `τ = 2`. The Part 5 carriers `toC`, `realAct`,
`realPart`, `totalH`, `rhoInf`, `fractD`, `HeadData`, `PerturbData`, `EnergyPatch`, `TorusOutput`,
`ChartCover`, `ToriExistence` are those of `KAM.Iso.Confinement.Setting`.

* Bridges `fractD_eq_domainD`, `totalH_eq_hbold` (`rfl`).
* Constants of `bpI:p3:constants`: `rhoIso`, `dB`, `eta1`, `sSet`, `mhConst`, `MgConst`,
  `ShConst`, `nuConst`, `sigmaOmegaConst`, `sigmaKConst`, `sigmaTConst`, `epsT`.
* Coordinates of `bpI:p3:coordinates`: `perp`, `det2`, `aCoord`, `bCoord`, `slope`, `hessR`,
  `chartDom`, `chartM`, `chartPhi`, `jac2`.
* `IsPatch` (`bpI:p3:patch`) with `IsPatch.toEnergyPatch` into Part 5's `EnergyPatch`; `IsRay`
  (`bpI:p3:rays`); `flatRemainder` (`bpI:p3:torus`); `ToriSide` (`bpI:p3:tori`, (T1)-(T7) for
  one sign, on top of Part 5's `TorusOutput`).

Part 3 applies I-G1 and G3 only through the premises `IG1Statement` and `G3Statement` of
`KAM.Iso.Charts.Inputs` (imported here).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Set Metric

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement
open KAM.Head (muParam Fconst actionHessian)

theorem fractD_eq_domainD (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) :
    fractD B s₀ r₀ = KAM.Head.domainD 2 s₀ r₀ B := rfl

theorem totalH_eq_hbold (h : (Fin 2 → ℂ) → ℂ) (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) :
    totalH h f = KAM.Head.hbold h f := rfl

/-- `ρ = s/4` (`ρ_∞ = s/8` is `rhoInf`; `δ_*, μ, F_j, M, M_h, c̄` are K's `KAM.Head` constants). -/
def rhoIso (s₀ : ℝ) : ℝ := min s₀ 1 / 4

/-- `d_B = inf {|I - J| : I ∈ closure B', J ∉ B}`. -/
def dB (B B' : Set (Fin 2 → ℝ)) : ℝ :=
  sInf ((fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ‖p.1 - p.2‖) '' (closure B' ×ˢ Bᶜ))

def eta1 (η : ℝ) (B B' : Set (Fin 2 → ℝ)) : ℝ := min η (dB B B' / 2)
/-- `𝒮 = {I : dist(I, closure B') ≤ d_B/2}`. -/
def sSet (B B' : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) := Metric.cthickening (dB B B' / 2) (closure B')

def mhConst (h : (Fin 2 → ℂ) → ℂ) (B B' : Set (Fin 2 → ℝ)) : ℝ :=
  sInf ((fun I => ‖frequencyMap h I‖) '' sSet B B')
def MgConst (h : (Fin 2 → ℂ) → ℂ) (B B' : Set (Fin 2 → ℝ)) : ℝ :=
  sSup ((fun I => ‖frequencyMap h I‖) '' sSet B B')
/-- `S_h = max_𝒮 |𝖡_h⁻¹|` (row-sum norm of the real matrix). -/
def ShConst (h : (Fin 2 → ℂ) → ℂ) (B B' : Set (Fin 2 → ℝ)) : ℝ :=
  sSup ((fun I => ‖(KAM.Iso.borderedHessian h I)⁻¹‖) '' sSet B B')

def nuConst (h : (Fin 2 → ℂ) → ℂ) (B B' : Set (Fin 2 → ℝ)) : ℝ := mhConst h B B' / 4
def sigmaOmegaConst (h : (Fin 2 → ℂ) → ℂ) (B B' : Set (Fin 2 → ℝ)) : ℝ :=
  4 * MgConst h B B' / mhConst h B B' + 2
/-- `σ_K = σ_B = 1 + μ`. -/
def sigmaKConst (s₀ r₀ : ℝ) : ℝ := 1 + muParam s₀ r₀
def sigmaTConst (h : (Fin 2 → ℂ) → ℂ) (B B' : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) : ℝ :=
  2 * ShConst h B B' + muParam s₀ r₀
def epsT (h : (Fin 2 → ℂ) → ℂ) (B B' : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) : ℝ :=
  1 / (4 * ShConst h B B' * Fconst 2 s₀ r₀ 2)

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

def perp (g : Fin 2 → ℝ) : Fin 2 → ℝ := ![-g 1, g 0]
def det2 (g w : Fin 2 → ℝ) : ℝ := g 0 * w 1 - g 1 * w 0
def aCoord (g w : Fin 2 → ℝ) : ℝ := (g ⬝ᵥ w) / (g ⬝ᵥ g)
def bCoord (g w : Fin 2 → ℝ) : ℝ := det2 g w / (g ⬝ᵥ g)
def slope (g w : Fin 2 → ℝ) : ℝ := det2 g w / (g ⬝ᵥ w)
/-- `∇²h(I) = D(∇h)(I)`, the upper-left block of `𝖡_h(I)`. -/
def hessR (h : (Fin 2 → ℂ) → ℂ) (I : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a b => fderiv ℝ (frequencyMap h) I (Pi.single b 1) a
/-- `𝒰_c = {I ∈ U : a_c(∇h(I)) > 0}`. -/
def chartDom (h : (Fin 2 → ℂ) → ℂ) (B : Set (Fin 2 → ℝ)) (r₀ : ℝ) (c : Fin 2 → ℝ) :
    Set (Fin 2 → ℝ) :=
  {I | I ∈ realAct B r₀ ∧ 0 < aCoord (frequencyMap h c) (frequencyMap h I)}
def chartM (h : (Fin 2 → ℂ) → ℂ) (c I : Fin 2 → ℝ) : ℝ :=
  slope (frequencyMap h c) (frequencyMap h I)
def chartPhi (h : (Fin 2 → ℂ) → ℂ) (c I : Fin 2 → ℝ) : ℝ × ℝ := (realPart h I, chartM h c I)
/-- `det DF(x)` for `F : ℝ² → ℝ × ℝ`. -/
def jac2 (F : (Fin 2 → ℝ) → ℝ × ℝ) (x : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ (fun y => (F y).1) x (Pi.single 0 1) * fderiv ℝ (fun y => (F y).2) x (Pi.single 1 1) -
    fderiv ℝ (fun y => (F y).1) x (Pi.single 1 1) * fderiv ℝ (fun y => (F y).2) x (Pi.single 0 1)

/-- `bpI:p3:patch` (P1)–(P3), for the chart `Φ_c = (h, m_c)` with inverse `Ψ` on `W`. -/
structure IsPatch (h : (Fin 2 → ℂ) → ℂ) (B : Set (Fin 2 → ℝ)) (r₀ : ℝ) (B' : Set (Fin 2 → ℝ))
    (η₁ : ℝ) (c : Fin 2 → ℝ) (W : Set (Fin 2 → ℝ)) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (δE δm ρc : ℝ) :
    Prop where
  c_mem : c ∈ closure B'
  isOpen_W : IsOpen W
  W_dom : W ⊆ chartDom h B r₀ c
  W_subset_B : W ⊆ B
  W_subset_ball : W ⊆ ball c (η₁ / 4)
  hR_contDiffOn : ContDiffOn ℝ 1 (realPart h) W
  m_contDiffOn : ContDiffOn ℝ 1 (chartM h c) W
  isOpen_V : IsOpen (chartPhi h c '' W)
  Ψ_contDiffOn : ContDiffOn ℝ 1 Ψ (chartPhi h c '' W)
  Ψ_mem : ∀ v ∈ chartPhi h c '' W, Ψ v ∈ W
  Ψ_left : ∀ I ∈ W, Ψ (chartPhi h c I) = I
  Ψ_right : ∀ v ∈ chartPhi h c '' W, chartPhi h c (Ψ v) = v
  δE_pos : 0 < δE
  δm_pos : 0 < δm
  ρc_pos : 0 < ρc
  Q_subset : Icc (realPart h c - δE) (realPart h c + δE) ×ˢ Icc (-δm) δm ⊆ chartPhi h c '' W
  ρc_le : ρc ≤ η₁ / 4
  ball_subset : ball c ρc ⊆ W
  ball_h : ∀ I ∈ ball c ρc, |realPart h I - realPart h c| < δE / 2
  ball_m : ∀ I ∈ ball c ρc, |chartM h c I| < δm / 4

/-- A patch with two ray slopes is a Part 5 `EnergyPatch` (`hR = realPart h`, `m = m_c`). -/
def IsPatch.toEnergyPatch {r₀ η₁ δE δm ρc : ℝ} {c : Fin 2 → ℝ} {W : Set (Fin 2 → ℝ)}
    {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hp : IsPatch h B r₀ B' η₁ c W Ψ δE δm ρc) (mp mm : ℝ)
    (hmp : mp ∈ Ioo (δm / 2) δm) (hmm : mm ∈ Ioo (-δm) (-(δm / 2))) :
    EnergyPatch (realPart h) B η₁ :=
  ⟨c, W, chartM h c, Ψ, δE, δm, ρc, mp, mm, hp.δE_pos, hp.δm_pos, hp.ρc_pos, hp.isOpen_W,
    hp.W_subset_B, hp.W_subset_ball, hp.hR_contDiffOn, hp.m_contDiffOn, hp.isOpen_V,
    hp.Ψ_contDiffOn, hp.Ψ_mem, hp.Ψ_left, hp.Ψ_right, hp.Q_subset, hp.ρc_le, hp.ball_subset,
    hp.ball_h, hp.ball_m, hmp, hmm⟩

/-- `ω*` is a `(γ, 2)`-Diophantine ray of slope `m` at `c` with `m_h/4 < |ω*| < m_h/2`. -/
def IsRay (h : (Fin 2 → ℂ) → ℂ) (B B' : Set (Fin 2 → ℝ)) (c : Fin 2 → ℝ) (γ : ℝ)
    (ωs : Fin 2 → ℝ) (m : ℝ) : Prop :=
  0 < γ ∧ IsDiophantine γ 2 ωs ∧ 0 < aCoord (frequencyMap h c) ωs ∧
    slope (frequencyMap h c) ωs = m ∧ mhConst h B B' / 4 < ‖ωs‖ ∧ ‖ωs‖ < mhConst h B B' / 2

/-- `R(θ) = (∂²_I f  0; (∂_I f)ᵀ  0)` at `(θ, I)`. -/
def flatRemainder (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (I : Fin 2 → ℝ) (θ : Fin 2 → ℂ) :
    Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) ℂ :=
  KAM.Iso.Linear.bordMat (actionHessian f (θ, toC I)) 0
    (fun b => fderiv ℂ f (θ, toC I) (0, Pi.single b 1))

/-- (T1)–(T7) of `bpI:p3:tori` for one sign, on top of Part 5's `TorusOutput` (T1)–(T4). -/
structure ToriSide (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ) (B' : Set (Fin 2 → ℝ))
    (η η₁ : ℝ) (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε C_K E : ℝ) (I₀ : Fin 2 → ℝ)
    (Ψ : ℝ × ℝ → Fin 2 → ℝ) (m : ℝ) (K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ))
    (I ωt : Fin 2 → ℝ) : Prop extends TorusOutput h f ε C_K s₀ E K I ωt where
  base : I = Ψ (E, m)
  ray : ∃ (γ : ℝ) (ωs : Fin 2 → ℝ) (st sc : ℝ), 0 < γ ∧ IsDiophantine γ 2 ωs ∧ ωt = st • ωs ∧
    1 < st ∧ st < sigmaOmegaConst h B B' ∧ frequencyMap h I = sc • ωs ∧ 2 < sc ∧
    sc < 4 * MgConst h B B' / mhConst h B B' ∧ ‖ωt - frequencyMap h I‖ ≤ C_K * ε
  level : realPart h I = E
  near : I ∈ B ∧ ‖I - I₀‖ < η₁ / 2
  action : ∀ x : Fin 2 → ℝ, ‖(K (toC x)).2 - toC I₀‖ < η ∧ ∃ J ∈ sSet B B', (K (toC x)).2 = toC J
  margins : ∀ θ ∈ complexStrip 2 (rhoInf s₀),
    Metric.ball (K θ) (muParam s₀ r₀ / 2) ⊆ fractD B s₀ r₀ ∧
    ‖fderiv ℂ K θ‖ ≤ sigmaKConst s₀ r₀ - muParam s₀ r₀ / 2

end KAM.Iso.Charts

end
