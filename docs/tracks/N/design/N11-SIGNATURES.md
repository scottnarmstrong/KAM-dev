# N11 signature file (tracked copy)

Copy of the orchestrator's untracked `.drafts/design/N11Signatures.lean` as of 2026-10-28 21:59 UTC, published for the lane-N handoff. Every SIGNED N11 declaration must match this text exactly. Overnight amendments: line 213 `theorem ext_flow` (renamed from `flow`, ruling 20:50) and `canonical_map` gained `(hc : 0 < b.c)` (lines 301-302, ruling 21:15; see the N11-F2 audit for the open consumer question). Lane-N amendment (Zohar's team, 2026-10-28, ruling F2-C1 in `docs/campaign/LANE-N-LOG.md`): `iterative` gained `(hc : 0 < b.c)` after `hSL`.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.SupWeighted
public import KAM.Weighted.Algebra
public import KAM.ODE.Continuation
public import Mathlib.Analysis.Complex.ExponentialBounds
public import KAM.Weighted.Projections
public import KAM.Weighted.Cauchy
public import KAM.Canonical.Flow
public import KAM.ODE.Maximal
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Frozen.Nekhoroshev.Defs.HasDefiniteFastPart
public import KAM.Frozen.Nekhoroshev.Defs.IsPartialPerturbation
public import KAM.Frozen.Nekhoroshev.Defs.InnerCore
public import KAM.Frozen.Nekhoroshev.Defs.PartialTimeExponent
public import KAM.Frozen.Nekhoroshev.Defs.PartialDriftExponent
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Part 11 design signatures
All theorem bodies are deliberately `sorry`. Definitions have literal bodies.
No draft anchor or provider is imported. NF upstream definitions are copied
verbatim from NPart67Signatures until their implementation modules land.
-/
@[expose] public noncomputable section
open Set Metric
open scoped BigOperators

namespace KAM.NormalForm
open KAM.Weighted
variable {n : ℕ}
def zBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | KAM.Fourier.modeSize k ≤ K}
def freq (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℂ) : Fin n → ℂ := fun i => fderiv ℂ h I (Pi.single i 1)
def dotC (k : Fin n → ℤ) (v : Fin n → ℂ) : ℂ := ∑ i, (k i : ℂ) * v i
def conjExp (p : ℝ) : ℝ := p / (p - 1)
def IsNonresonant (D : Set (Fin n → ℂ)) (K α : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I ∈ D, ∀ k ∈ zBall n K \ Λ, α ≤ ‖dotC k (freq h I)‖
def FreqLipschitz (D : Set (Fin n → ℂ)) (r L : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I₀ ∈ D, ∀ I ∈ KAM.Weighted.polyNbhd D r, ‖I - I₀‖ < r → ‖freq h I - freq h I₀‖ ≤ L * ‖I - I₀‖
def DivisorBound (V : Set (Fin n → ℂ)) (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (c : ℝ) : Prop :=
  ∀ I ∈ V, ∀ k ∈ zBall n K \ Λ, c ≤ ‖dotC k (freq h I)‖
def homGenParam {m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (ω : (Fin m → ℂ) → Fin n → ℂ)
    (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  fun z => ∑' k, (zBall n K \ Λ).indicator (fun k =>
    coeff f z.2 k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (ω z.2)) * KAM.character k z.1) k

def homResParam {m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  projMode Λ (truncate K f)

def RealOnParam {m : ℕ} (U : Set ((Fin n → ℂ) × (Fin m → ℂ)))
    (u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : Prop :=
  ∀ x : (Fin n → ℝ) × (Fin m → ℝ), (KAM.realInclusion n x.1, KAM.realInclusion m x.2) ∈ U →
    (u (KAM.realInclusion n x.1, KAM.realInclusion m x.2)).im = 0
end KAM.NormalForm
open scoped ContDiff

namespace KAM.Nekhoroshev
open KAM.Weighted KAM.NormalForm
variable {n k : ℕ}

/-- Coordinates are θ, followed by I,q,p in a single weighted base. -/
abbrev Ext (n k : ℕ) (𝕜 : Type*) := (Fin n → 𝕜) × (Fin (n + (k + k)) → 𝕜)
abbrev EC (n k : ℕ) := Ext n k ℂ
abbrev ER (n k : ℕ) := Ext n k ℝ

def fastAction {𝕜 : Type*} (z : Ext n k 𝕜) : Fin n → 𝕜 := fun i => z.2 (Fin.castAdd (k+k) i)
def slowPair {𝕜 : Type*} (z : Ext n k 𝕜) : (Fin k → 𝕜) × (Fin k → 𝕜) :=
  (fun i => z.2 (Fin.natAdd n (Fin.castAdd k i)),
   fun i => z.2 (Fin.natAdd n (Fin.natAdd k i)))
def extCx (z : ER n k) : EC n k := (fun i => (z.1 i : ℂ), fun i => (z.2 i : ℂ))
def extRe (z : EC n k) : ER n k := (fun i => (z.1 i).re, fun i => (z.2 i).re)
abbrev extReal (U : Set (EC n k)) (f : EC n k → ℂ) : Prop :=
  KAM.NormalForm.RealOnParam U f

def wfield (c : ℝ) (H : EC n k → ℂ) (z : EC n k) : EC n k :=
  (fun i => fderiv ℂ H z (0, Pi.single (Fin.castAdd (k+k) i) 1),
   Fin.append (fun i => -fderiv ℂ H z (Pi.single i 1, 0))
    (Fin.append
      (fun i => (c : ℂ) * fderiv ℂ H z (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1))
      (fun i => -(c : ℂ) * fderiv ℂ H z (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1))))
def realWfield (c : ℝ) (H : ER n k → ℝ) (z : ER n k) : ER n k :=
  (fun i => fderiv ℝ H z (0, Pi.single (Fin.castAdd (k+k) i) 1),
   Fin.append (fun i => -fderiv ℝ H z (Pi.single i 1, 0))
    (Fin.append
      (fun i => c * fderiv ℝ H z (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1))
      (fun i => -c * fderiv ℝ H z (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1))))
def extBracket (c : ℝ) (u v : EC n k → ℂ) (z : EC n k) : ℂ :=
  fderiv ℂ u z (wfield c v z)
def extAd (c : ℝ) (φ : EC n k → ℂ) : ℕ → (EC n k → ℂ) → EC n k → ℂ
  | 0, u => u
  | j+1, u => extBracket c (extAd c φ j u) φ

def theta (z : KAM.Planetary.Phase (n+k)) : ER n k :=
  (fun i => KAM.Planetary.fast (b := k) z.1 i / (2*Real.pi),
   Fin.append (KAM.Planetary.fast (b := k) z.2)
     (Fin.append (KAM.Planetary.slow (a := n) z.1) (KAM.Planetary.slow (a := n) z.2)))
def thetaInv (z : ER n k) : KAM.Planetary.Phase (n+k) :=
  (Fin.append (fun i => 2*Real.pi*z.1 i) (slowPair z).1,
   Fin.append (fastAction z) (slowPair z).2)
def converted (H : KAM.Planetary.Phase (n+k) → ℝ) (z : ER n k) : ℝ :=
  H (thetaInv z) / (2*Real.pi)
theorem orbit (H : KAM.Planetary.Phase (n+k) → ℝ)
    (z : ℝ → KAM.Planetary.Phase (n+k)) (t : ℝ) (hh : DifferentiableAt ℝ H (z t)) :
    HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t ↔
    HasDerivAt (theta ∘ z) (realWfield (2*Real.pi) (converted H) (theta (z t))) t := sorry

theorem exponents (hn : 2 ≤ n) :
    0 < partialTimeExponent n ∧ partialTimeExponent n < partialDriftExponent n ∧
    2 * partialDriftExponent n < 1/(2*(n:ℝ)) := sorry

/-- Numerical data, no hypotheses or conclusions hidden in this carrier. -/
structure PartialConstants where
  n : ℕ
  ρ : ℝ
  g : ℝ
  m : ℝ
  Mc : ℝ
namespace PartialConstants
def s (a : PartialConstants) := a.ρ / (4*Real.pi)
def m1 (a : PartialConstants) := a.m / (2*Real.pi)
def M1 (a : PartialConstants) := a.Mc / (2*Real.pi)
def g1 (a : PartialConstants) := a.g / (2*Real.pi)
def r0 (a : PartialConstants) := min (a.ρ/2) (32*a.g/a.m)
def A (a : PartialConstants) := 40*a.Mc/a.m
def eps0 (a : PartialConstants) := a.m1*a.r0^2 / ((2:ℝ)^14*a.A^(2*a.n))
def R0 (a : PartialConstants) := a.r0/a.A
def kappaC (a : PartialConstants) := coth (Real.pi*a.s)^a.n
def cK (a : PartialConstants) := (2*Real.pi*a.eps0/a.kappaC) ^ (1/(2*(a.n:ℝ)))
def eps (a : PartialConstants) (μ : ℝ) := a.kappaC*μ/(2*Real.pi)
def K (a : PartialConstants) (μ : ℝ) := (a.eps0/a.eps μ) ^ (1/(2*(a.n:ℝ)))
def d (a : PartialConstants) (μ : ℝ) := μ ^ partialDriftExponent a.n
def kappa (a : PartialConstants) (μ : ℝ) := 2*Real.pi*a.K μ*a.s/Real.sqrt a.n
def rTheta (a : PartialConstants) (μ : ℝ) := a.r0/(a.A*a.K μ)^a.n
def blockTime (a : PartialConstants) (μ : ℝ) :=
  a.s*a.m1*a.rTheta μ/(240*a.M1*a.eps μ)*Real.exp (a.kappa μ/6)
end PartialConstants

/-- Fixed block geometry: λ and c are computed once, never from an iterated R. -/
structure PartialBlock (n k : ℕ) where
  Ic : Fin n → ℝ
  S : Set (KAM.Planetary.Phase k)
  rB : ℝ
  w : ℝ
namespace PartialBlock
def lam (b : PartialBlock n k) := b.w/b.rB
def c (b : PartialBlock n k) := 2*Real.pi/b.lam^2
def base (b : PartialBlock n k) : Set (Fin (n+(k+k)) → ℂ) :=
  {J | ∃ x ∈ b.S, J = Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((x.1 i/b.lam : ℝ) : ℂ)) (fun i => ((x.2 i/b.lam : ℝ) : ℂ)))}
def realDom (b : PartialBlock n k) (R : ℝ) : Set (ER n k) :=
  {z | extCx z ∈ Dom n b.base R 1}
def SL (b : PartialBlock n k) (s : ℝ) : Prop := 64*Real.pi*k*s*b.rB ≤ b.w^2
end PartialBlock

def ext_class (b : PartialBlock n k) (R s : ℝ) (u : EC n k → ℂ) : Prop :=
  InClass b.base R s u ∧ extReal (Dom n b.base R s) u
def slowLoss (c ρ σ : ℝ) (k : ℕ) : Prop := 16*k*c*σ ≤ ρ
def scaled (ρ σ : ℝ) (z : EC n k) : ℝ := max (‖z.1‖/σ) (‖z.2‖/ρ)
def liftFast (h : (Fin n → ℂ) → ℂ) (z : EC n k) : ℂ := h (fastAction z)
def realHamiltonianExt (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ) : ER n k → ℝ :=
  (b.realDom R).indicator (fun z => (H (extCx z)).re)
def ExtOrbit (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ)
    (J : Set ℝ) (y : ℝ → ER n k) : Prop :=
  KAM.ODE.IsSolutionIn (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R) J y

theorem ext_part4 (b : PartialBlock n k) {R s U : ℝ} {u : EC n k → ℂ}
    (hs : 0 < s) (hu : InClass b.base R s u) (hb : WBound b.base R s u U) :
    ∀ z ∈ Dom n b.base R s, ‖u z‖ ≤ U := sorry

theorem bracket (b : PartialBlock n k) {R0 s0 R s ρ σ U V : ℝ} {u v : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hR0 : R-ρ < R0) (hs0 : s-σ < s0)
    (hu : InClass b.base R0 s0 u) (hv : InClass b.base R s v)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hbu : WBound b.base R0 s0 u U) (hbv : WBound b.base R s v V) :
    InClass b.base (R-ρ) (s-σ) (extBracket b.c u v) ∧
    WBound b.base (R-ρ) (s-σ) (extBracket b.c u v)
      (((Real.exp 1)⁻¹*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ))+
        2*k*b.c/((R0-R+ρ)*ρ))*U*V) := sorry

theorem bracket_dominated {c ρ σ R0 R s0 s : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hσ : 0 < σ) (hR : R-ρ < R0) (hs : s-σ < s0) (hSL : slowLoss c ρ σ k) :
    (Real.exp 1)⁻¹*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ)) + 2*k*c/((R0-R+ρ)*ρ) ≤
      (1/2)*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ)) := sorry

/-- Decomposition is literal finite summation, as Part 6, with independent base dimension. -/
theorem bracket_g (b : PartialBlock n k) {N : ℕ} {R s ρ σ V : ℝ}
    (gj : Fin N → EC n k → ℂ) (Rj sj Uj : Fin N → ℝ) (φ : EC n k → ℂ)
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hSL : slowLoss b.c ρ σ k) (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j)
    (hU : ∀ j, 0 ≤ Uj j) (hV : 0 ≤ V)
    (hg : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j))
    (hφ : InClass b.base R s φ) (hφb : WBound b.base R s φ V) :
    WBound b.base (R-ρ) (s-σ) (extBracket b.c (fun z => ∑ j, gj j z) φ)
      ((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)*V/(ρ*σ)) := sorry

theorem vf (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ U : ℝ} {φ : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hSL : slowLoss b.c ρ σ k) (hU : 0 ≤ U)
    (hφ : InClass b.base R s φ) (hb : WBound b.base R s φ U) :
    ∀ z ∈ Dom n b.base (R-ρ) (s-σ), scaled ρ σ (wfield b.c φ z) ≤ U/(ρ*σ) ∧
      ‖slowPair (wfield b.c φ z)‖ ≤ b.c*U/ρ := sorry

/-- Generic Part 5 flow is consumed directly: no second choice of flow. -/
theorem ext_flow (W : EC n k ≃L[ℂ] EC n k) {Ω : Set (EC n k)} {F : EC n k → EC n k} {ε : ℝ}
    (hF : KAM.Canonical.SmallField W Ω F ε) {z : EC n k}
    (hz : z ∈ KAM.Canonical.gaugeInterior W Ω (1/2)) {t : ℝ} (ht : |t| ≤ 1) :
    KAM.Canonical.flow F Ω t z ∈ Ω ∧
    ‖W (KAM.Canonical.flow F Ω t z-z)‖ ≤ |t| *ε := sorry

/-- Basis-free expression of DΨ Ω DΨᵀ=Ω, for all linear functionals. -/
def ExtCanonical (c : ℝ) (U : Set (EC n k)) (Ψ : EC n k → EC n k) : Prop :=
  ∀ z ∈ U, ∀ u v : EC n k →L[ℂ] ℂ,
    extBracket c (fun x => u (Ψ x)) (fun x => v (Ψ x)) z =
      extBracket c (fun x => u x) (fun x => v x) (Ψ z)

theorem symplectic {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c ε : ℝ} (hc : 0 < c)
    (φ : EC n k → ℂ) (hφ : DifferentiableOn ℂ φ Ω) (W : EC n k ≃L[ℂ] EC n k)
    (hF : KAM.Canonical.SmallField W Ω (wfield c φ) ε) {t : ℝ} (ht : |t| ≤ 1) :
    ExtCanonical c (KAM.Canonical.gaugeInterior W Ω (1/2))
      (KAM.Canonical.flow (wfield c φ) Ω t) := sorry

theorem adjoint (b : PartialBlock n k) {R' s' R s ρ σ U V : ℝ} {φ u : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hRR : R+ρ ≤ R') (hss : s+σ ≤ s') (hSL : slowLoss b.c ρ σ k)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : InClass b.base R' s' φ) (hu : InClass b.base R s u)
    (hφb : WBound b.base R' s' φ V) (hub : WBound b.base R s u U) (j : ℕ) (hj : 1 ≤ j) :
    InClass b.base (R-ρ) (s-σ) (extAd b.c φ j u) ∧
    WBound b.base (R-ρ) (s-σ) (fun z => ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z)
      ((Real.exp 1^2*(2*V/(ρ*σ))/8)^j*U) := sorry

theorem ext_taylor {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ)
    (N : ℕ) (hN : 1 ≤ N) :
    u (γ 1) = (∑ j ∈ Finset.range N, ((j.factorial:ℂ)⁻¹)*extAd c φ j u (γ 0)) +
      ∫ t in (0:ℝ)..1, (((1-t)^(N-1)/(N-1).factorial:ℝ):ℂ)*extAd c φ N u (γ t) := sorry

/-- Source assumptions for B.5, including explicit norm bounds. -/
structure ExtCompose (b : PartialBlock n k) (R' s' R s ρ σ V : ℝ) (φ : EC n k → ℂ) : Prop where
  rho_pos : 0 < ρ
  rho_lt : ρ < R
  sig_pos : 0 < σ
  sig_lt : σ < s
  radii : R+ρ ≤ R'
  widths : s+σ ≤ s'
  bound_nonneg : 0 ≤ V
  hol : InClass b.base R' s' φ
  bound : WBound b.base R' s' φ V
  small : 2*V/(ρ*σ) ≤ 1/2
  slow : slowLoss b.c ρ σ k

def extFlow (b : PartialBlock n k) (R s ρ σ : ℝ) (φ : EC n k → ℂ) (t : ℝ) : EC n k → EC n k :=
  KAM.Canonical.flow (wfield b.c φ) (Dom n b.base (R-ρ) (s-σ)) t

theorem composition (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V U : ℝ}
    {φ u : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ)
    (hU : 0 ≤ U) (hu : InClass b.base R s u) (hub : WBound b.base R s u U) :
    let X := extFlow b R' s' ρ σ φ
    (∀ t : ℝ, |t| ≤ 1 → MapsTo (X t) (Dom n b.base (R-ρ) (s-σ)) (Dom n b.base R s)) ∧
    (∀ t : ℝ, |t| ≤ 1 → InClass b.base (R-ρ) (s-σ) (u ∘ X t) ∧
      WBound b.base (R-ρ) (s-σ) (u ∘ X t) ((1-|t| *(2*V/(ρ*σ)))⁻¹*U)) ∧
    (∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      HasSum (fun j : ℕ => ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z) (u (X 1 z))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N,
      WBound b.base (R-ρ) (s-σ)
        (fun z => u (X 1 z)-∑ j ∈ Finset.range N', ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z) ε) := sorry

theorem transform (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V U W : ℝ}
    {φ h f : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ)
    (hh : InClass b.base R s h) (hf : InClass b.base R s f)
    (hw : InClass b.base R s (extBracket b.c h φ)) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hfb : WBound b.base R s f U) (hwb : WBound b.base R s (extBracket b.c h φ) W) :
    let X := extFlow b R' s' ρ σ φ
    let rem := fun z => ∫ t in (0:ℝ)..1,
      extBracket b.c (fun x => ((1-t:ℝ):ℂ)*extBracket b.c h φ x+f x) φ (X t z)
    (∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      (h+f) (X 1 z) = h z+extBracket b.c h φ z+f z+rem z) ∧
    InClass b.base (R-ρ) (s-σ) rem ∧
    WBound b.base (R-ρ) (s-σ) rem ((2*V/(ρ*σ))/(1-2*V/(ρ*σ))*(W/2+U)) := sorry

/-- Separate statement retains joint continuity required by the integral clause. -/
theorem transform_integral (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V U : ℝ}
    {φ : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ) (v : ℝ → EC n k → ℂ)
    (hU : 0 ≤ U) (hv : ∀ t ∈ Icc (0:ℝ) 1, InClass b.base R s (v t))
    (hvb : ∀ t ∈ Icc (0:ℝ) 1, WBound b.base R s (v t) U)
    (hcont : ContinuousOn (fun p : ℝ × EC n k => v p.1 p.2) (Icc 0 1 ×ˢ Dom n b.base R s))
    (hdcont : ContinuousOn (fun p : ℝ × EC n k => fderiv ℂ (v p.1) p.2) (Icc 0 1 ×ˢ Dom n b.base R s)) :
    InClass b.base (R-ρ) (s-σ) (fun z => ∫ t in (0:ℝ)..1, v t (extFlow b R' s' ρ σ φ t z)) ∧
    WBound b.base (R-ρ) (s-σ) (fun z => ∫ t in (0:ℝ)..1, v t (extFlow b R' s' ρ σ φ t z))
      ((1-2*V/(ρ*σ))⁻¹*U) := sorry

theorem canonical_map (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ V : ℝ}
    {φ : EC n k → ℂ} (hc : 0 < b.c)
    (hρ : 0 < ρ) (hρR : ρ < R/2) (hσ : 0 < σ) (hσs : σ < s/2)
    (hSL : slowLoss b.c ρ σ k) (hV : 0 ≤ V) (hsmall : V/(ρ*σ) ≤ 1/2)
    (hφ : InClass b.base R s φ) (hb : WBound b.base R s φ V) :
    let Φ := extFlow b R s ρ σ φ 1
    let Ψ := extFlow b R s ρ σ φ (-1)
    let U := Dom n b.base (R-3*ρ/2) (s-3*σ/2)
    DifferentiableOn ℂ Φ U ∧ DifferentiableOn ℂ Ψ U ∧ MapsTo Φ U (Dom n b.base (R-ρ) (s-σ)) ∧
    MapsTo Ψ U (Dom n b.base (R-ρ) (s-σ)) ∧
    ExtCanonical b.c U Φ ∧
    (∀ z ∈ U, ‖(Φ z).1-z.1‖ ≤ V/ρ ∧ ‖fastAction (Φ z)-fastAction z‖ ≤ V/(Real.exp 1*σ) ∧
      ‖slowPair (Φ z)-slowPair z‖ ≤ b.c*V/ρ) ∧
    (∀ z ∈ U, ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)), z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), Ψ (Φ z) = z ∧ Φ (Ψ z) = z ∧ Φ z ∈ U) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), ∀ v : EC n k,
      scaled ρ σ (fderiv ℂ Φ z v-v) ≤ 2*(V/(ρ*σ))*scaled ρ σ v) ∧
    (extReal (Dom n b.base R s) φ → ∀ z : ER n k, extCx z ∈ U → extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := sorry

def homGenerator (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) : EC n k → ℂ :=
  KAM.NormalForm.homGenParam K Λ (fun J => freq h (fun i => J (Fin.castAdd (k+k) i))) f

theorem hom (b : PartialBlock n k) {R s K α q U : ℝ} (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (hR : 0 < R) (hs : 0 < s) (hK : 0 ≤ K) (hα : 0 < α) (hq : 1 ≤ q)
    (Λ : Set (Fin n → ℤ)) (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/q))
    (hU : 0 ≤ U) (hf : InClass b.base R s f) (hb : WBound b.base R s f U) :
    let ξ := projMode Λ (truncate K f)
    let φ := homGenerator K Λ h f
    InClass b.base R s ξ ∧ InClass b.base R s φ ∧
    WBound b.base R s ξ U ∧ WBound b.base R s (truncate K f) U ∧
    WBound b.base R s φ (q*U/(2*Real.pi*α)) ∧
    (∀ z ∈ Dom n b.base R s, extBracket b.c φ (liftFast h) z+ξ z = truncate K f z) ∧
    (∀ z ∈ Dom n b.base R s, projMode Λ φ z = 0) ∧
    ((∀ j, j ∈ Λ ↔ -j ∈ Λ) → extReal (Dom n b.base R s) f →
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      extReal (Dom n b.base R s) ξ ∧ extReal (Dom n b.base R s) φ) := sorry

/-- Source premises for a block normal form, not its conclusion. -/
structure ExtNFHyp (b : PartialBlock n k) (s K α L p ε : ℝ)
    (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) : Prop where
  n_pos : 1 ≤ n
  k_pos : 1 ≤ k
  radius_pos : 0 < b.rB
  slow_width_pos : 0 < b.w
  s_pos : 0 < s
  K_pos : 0 < K
  alpha_pos : 0 < α
  L_nonneg : 0 ≤ L
  p_gt : 1 < p
  eps_pos : 0 < ε
  symmetric : ∀ j, j ∈ Λ ↔ -j ∈ Λ
  hol : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} b.rB)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} b.rB →
    (h (KAM.realInclusion n I)).im = 0
  nr : IsNonresonant {KAM.realInclusion n b.Ic} K α Λ h
  lip : FreqLipschitz {KAM.realInclusion n b.Ic} b.rB L h
  divisor_size : K*L*b.rB ≤ α/p
  slow : b.SL s
  pert : ext_class b b.rB s f
  bound : WBound b.base b.rB s f ε
  cutoff : 6 ≤ 2*Real.pi*K*s

theorem iterative (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ K α p δ : ℝ}
    (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) (Λ : Set (Fin n → ℤ))
    (hR : 0 < ρ) (hR' : 2*ρ < R) (hs : 0 < σ) (hs' : 2*σ < s)
    (hSL : slowLoss b.c ρ σ k) (hc : 0 < b.c) (hα : 0 < α) (hp : 1 < p) (hK : 0 ≤ K)
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/conjExp p))
    (hδ : 0 ≤ δ) (hf : InClass b.base R s f) (hfb : WBound b.base R s f δ)
    (hsmall : δ ≤ 2*Real.pi*α*ρ*σ/(4*conjExp p))
    {N : ℕ} (gj : Fin N → EC n k → ℂ) (Rj sj Uj : Fin N → ℝ)
    (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j) (hUj : ∀ j, 0 ≤ Uj j)
    (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j)) :
    let q := conjExp p
    let φ := homGenerator K Λ h f
    let Φ := extFlow b R s ρ σ φ 1
    let g := fun z => ∑ j, gj j z
    let gp := g+projMode Λ (truncate K f)
    DifferentiableOn ℂ Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) ∧
    MapsTo Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) (Dom n b.base (R-ρ) (s-σ)) ∧
    (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2), ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), extFlow b R s ρ σ φ (-1) (Φ z) = z) ∧
    ∃ fp : EC n k → ℂ,
      InClass b.base (R-2*ρ) (s-2*σ) fp ∧
      (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), liftFast h (Φ z)+g (Φ z)+f (Φ z) = liftFast h z+gp z+fp z) ∧
      WBound b.base (R-2*ρ) (s-2*σ) fp
        ((1-2*q*δ/(2*Real.pi*α*ρ*σ))⁻¹*
          (q/(2*Real.pi*α*ρ*σ)*((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)+
            Real.exp (-2*Real.pi*K*σ))*δ) ∧
      ExtCanonical b.c (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) Φ ∧
      Set.InjOn Φ (Dom n b.base (R-2*ρ) (s-2*σ)) ∧
      WBound b.base (R-2*ρ) (s-2*σ) (gp-g) δ ∧
      (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2),
        ‖(Φ z).1-z.1‖ ≤ q*δ/(2*Real.pi*α*ρ) ∧
        ‖fastAction (Φ z)-fastAction z‖ ≤ q*δ/(Real.exp 1*2*Real.pi*α*σ) ∧
        ‖slowPair (Φ z)-slowPair z‖ ≤ q*δ/(16*k*2*Real.pi*α*σ)) ∧
      ((∀ j, j ∈ Λ ↔ -j ∈ Λ) →
        (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
          (h (KAM.realInclusion n I)).im = 0) →
        extReal (Dom n b.base R s) g → extReal (Dom n b.base R s) f →
        extReal (Dom n b.base R s) φ ∧ extReal (Dom n b.base (R-2*ρ) (s-2*σ)) gp ∧
        extReal (Dom n b.base (R-2*ρ) (s-2*σ)) fp ∧
        ∀ z : ER n k, extCx z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2) →
          extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := sorry

theorem nf (b : PartialBlock n k) {s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ} (ha : ExtNFHyp b s K α L p ε Λ h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K)) :
    ∃ Ψ : EC n k → EC n k, ∃ g fs : EC n k → ℂ,
      DifferentiableOn ℂ Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
      MapsTo Ψ (Dom n b.base (b.rB/2) (s/6)) (Dom n b.base b.rB s) ∧
      Set.InjOn Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
      ExtCanonical b.c (Dom n b.base (b.rB/2) (s/6)) Ψ ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6), ∀ ℓ : Fin n → ℤ,
        Ψ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Ψ z+((fun i => (ℓ i:ℂ)),0)) ∧
      (∀ z : ER n k, extCx z ∈ Dom n b.base (b.rB/2) (s/6) →
        extCx (extRe (Ψ (extCx z))) = Ψ (extCx z)) ∧
      ext_class b (b.rB/2) (s/6) g ∧ ext_class b (b.rB/2) (s/6) fs ∧
      (∀ J ∈ polyNbhd b.base (b.rB/2), ∀ j : Fin n → ℤ,
        j ∉ Λ ∩ zBall n K → coeff g J j = 0) ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6), liftFast h (Ψ z)+f (Ψ z) = liftFast h z+g z+fs z) ∧
      WBound b.base (b.rB/2) (s/6) (g-projMode Λ (truncate K f))
        (16*(2*conjExp p*K/(α*b.rB))*ε^2) ∧
      WBound b.base (b.rB/2) (s/6) fs (Real.exp (-(2*Real.pi*K*s)/6)*ε) ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6),
        ‖fastAction (Ψ z)-fastAction z‖ ≤ conjExp p*K*ε/α ∧
        ‖(Ψ z).1-z.1‖ ≤ 10*conjExp p*ε/(2*Real.pi*α*b.rB) ∧
        ‖slowPair (Ψ z)-slowPair z‖ ≤ conjExp p*K*ε/(8*α)) := sorry

/-- Literal real restriction and energy; finite norm is absent here. -/
theorem real_system (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hR : 0 < R) (hs : 0 < s) (hH : ext_class b R s H) :
    ContDiffOn ℝ ∞ (realHamiltonianExt b R H) (b.realDom R) ∧
    ContDiffOn ℝ 1 (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R) ∧
    (∀ z ∈ b.realDom R, extCx (realWfield b.c (realHamiltonianExt b R H) z) = wfield b.c H (extCx z)) ∧
    (∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom R,
      realHamiltonianExt b R H (z.1+(fun i => (ℓ i:ℝ)),z.2) = realHamiltonianExt b R H z) ∧
    (∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom R,
      realWfield b.c (realHamiltonianExt b R H) (z.1+(fun i => (ℓ i:ℝ)),z.2) =
        realWfield b.c (realHamiltonianExt b R H) z) ∧
    (∀ J : Set ℝ, J.OrdConnected → ∀ r, 0 < r → r ≤ R → ∀ y, ExtOrbit b r H J y →
      ∀ t ∈ J, ∀ u ∈ J, realHamiltonianExt b R H (y t) = realHamiltonianExt b R H (y u)) := sorry

theorem real_system_bounds (b : PartialBlock n k) {R s U : ℝ} {u : EC n k → ℂ}
    (hs : 0 < s) (hu : InClass b.base R s u) (hb : WBound b.base R s u U) :
    ∀ y ∈ b.realDom R, ‖u (extCx y)‖ ≤ U ∧
      ∑ j, ‖dtheta j u (extCx y)‖ ≤ U/(Real.exp 1*s) := sorry

def reExtMap (Ψ : EC n k → EC n k) (y : ER n k) : ER n k := extRe (Ψ (extCx y))
/-- Source hypotheses about the map; no orbit confinement in this structure. -/
structure ExtConjHyp (b : PartialBlock n k) (R s r t : ℝ) (H Ht : EC n k → ℂ)
    (Ψ : EC n k → EC n k) : Prop where
  R_pos : 0 < R
  r_pos : 0 < r
  s_pos : 0 < s
  t_pos : 0 < t
  r_le : r ≤ R
  t_le : t ≤ s
  outer : ext_class b R s H
  inner : ext_class b r t Ht
  hol : DifferentiableOn ℂ Ψ (Dom n b.base r t)
  maps : MapsTo Ψ (Dom n b.base r t) (Dom n b.base R s)
  real : ∀ z : ER n k, extCx z ∈ Dom n b.base r t → extCx (reExtMap Ψ z) = Ψ (extCx z)
  canon : ExtCanonical b.c (Dom n b.base r t) Ψ
  identity : ∀ z ∈ Dom n b.base r t, Ht z = H (Ψ z)

theorem conj (b : PartialBlock n k) {R s r t : ℝ} {H Ht : EC n k → ℂ} {Ψ : EC n k → EC n k}
    (hc : ExtConjHyp b R s r t H Ht Ψ) {J : Set ℝ} {y : ℝ → ER n k}
    (hy : ExtOrbit b r Ht J y) : ExtOrbit b R H J (reExtMap Ψ ∘ y) := sorry

theorem preimage (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w) {R s dθ dI dx ρ σ : ℝ} {Ψ : EC n k → EC n k}
    (hΨ : DifferentiableOn ℂ Ψ (Dom n b.base R s))
    (hr : ∀ y : ER n k, extCx y ∈ Dom n b.base R s → extCx (reExtMap Ψ y) = Ψ (extCx y))
    (hb : ∀ z ∈ Dom n b.base R s,
      ‖(Ψ z).1-z.1‖ ≤ dθ ∧ ‖fastAction (Ψ z)-fastAction z‖ ≤ dI ∧ ‖slowPair (Ψ z)-slowPair z‖ ≤ dx)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hσ : 0 < σ) (hσs : σ ≤ 2*s)
    (hsmall : max (dθ/σ) (max (dI/ρ) (dx/ρ)) ≤ 1/4) :
    ∀ y : ER n k, fastAction y = b.Ic → b.lam • slowPair y ∈ b.S →
      ∃ x ∈ b.realDom R, Ψ (extCx x) = extCx y ∧
        ‖x.1-y.1‖ ≤ dθ ∧ ‖fastAction x-b.Ic‖ ≤ dI ∧ ‖slowPair x-slowPair y‖ ≤ dx := sorry

theorem continuation {N : ℕ} {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    {F : (Fin n → ℝ) × (Fin N → ℝ) → (Fin n → ℝ) × (Fin N → ℝ)}
    (hF : ContDiffOn ℝ 1 F (univ ×ˢ U))
    (hper : ∀ ℓ : Fin n → ℤ, ∀ z ∈ (univ : Set (Fin n → ℝ)) ×ˢ U,
      F (z.1+(fun i => (ℓ i:ℝ)),z.2) = F z)
    {z0 : (Fin n → ℝ) × (Fin N → ℝ)} {Tm Tp : EReal} {z : ℝ → (Fin n → ℝ) × (Fin N → ℝ)}
    (hz : KAM.ODE.IsMaximalSolution F (univ ×ˢ U) z0 Tm Tp z)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hconf : ∃ t0 : ℝ, 0 ≤ t0 ∧ (t0:EReal) < Tp ∧
      ∀ t : ℝ, t0 ≤ t → (t:EReal) < Tp → (z t).2 ∈ K) : Tp = ⊤ := sorry

end KAM.Nekhoroshev

/-! Verbatim Part 7 definitions; delete these stubs when Stability/Gradient and Transfer land. -/
namespace KAM.Stability
variable {n : ℕ}
def resSpan (Λ : Set (Fin n → ℤ)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun k i => (k i : ℝ)) '' Λ)
structure IsActionNorm (N : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous N
  map_zero : N 0 = 0
  add_le : ∀ a b, N (a + b) ≤ N a + N b
  neg : ∀ a, N (-a) = N a
  smul : ∀ (c : ℝ) a, N (c • a) = |c| * N a
  norm_le : ∀ a, ‖a‖ ≤ N a
end KAM.Stability
namespace KAM.Nekhoroshev
open KAM.Weighted KAM.NormalForm
variable {n k : ℕ}

def slowTube (b : PartialBlock n k) (a : ℝ) (x : KAM.Planetary.Phase k) : Prop :=
  ∃ v ∈ b.S, ‖x-b.lam⁻¹ • v‖ ≤ a

theorem real_system_resonant (b : PartialBlock n k) {R s U : ℝ} {g : EC n k → ℂ}
    (hs : 0 < s) (hg : InClass b.base R s g) (hb : WBound b.base R s g U)
    {Λ : Set (Fin n → ℤ)}
    (hsupp : ∀ J ∈ polyNbhd b.base R, ∀ j : Fin n → ℤ, j ∉ Λ → coeff g J j = 0) :
    ∀ z ∈ b.realDom R,
      (fun i => (dtheta i g (extCx z)).re) ∈ KAM.Stability.resSpan Λ ∧
      (fun i => (dtheta i g (extCx z)).im) ∈ KAM.Stability.resSpan Λ := sorry

/-- Conditional helper only. T3 is proved by nonresonant integration or energy_free,
never forwarded as a premise of nonresonant, resonant, block or the provider. -/
theorem transfer_conditional (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w) {R s r t d dx a : ℝ} {T : ENNReal}
    {H Ht : EC n k → ℂ} {Ψ : EC n k → EC n k} (hc : ExtConjHyp b R s r t H Ht Ψ)
    (Nrm : (Fin n → ℝ) → ℝ) (hN : KAM.Stability.IsActionNorm Nrm)
    (hd : 0 ≤ d) (hdx : 0 ≤ dx) (hdxr : dx < r) (ha : 0 < a) (hgap : d+a < r) (hT : 0 < T)
    (hdisp : ∀ z ∈ b.realDom r, Nrm (fastAction (reExtMap Ψ z)-fastAction z) ≤ d ∧
      ‖slowPair (reExtMap Ψ z)-slowPair z‖ ≤ dx)
    (hpre : ∀ y : ER n k, fastAction y = b.Ic → b.lam • slowPair y ∈ b.S →
      ∃ x ∈ b.realDom r, reExtMap Ψ x = y ∧ Nrm (fastAction x-b.Ic) ≤ d)
    (hT3 : ∀ J : Set ℝ, J.OrdConnected → (0:ℝ) ∈ J → ∀ y : ℝ → ER n k,
      ExtOrbit b r Ht J y → Nrm (fastAction (y 0)-b.Ic) ≤ d →
      (∀ u ∈ J, slowTube b dx (slowPair (y u))) →
      ∀ u ∈ J, ENNReal.ofReal |u| ≤ T → Nrm (fastAction (y u)-fastAction (y 0)) ≤ a)
    (F : ER n k → ER n k) (hF : EqOn F (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hI : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (htT : ENNReal.ofReal |t1| ≤ T)
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, y u ∈ b.realDom R ∧ Nrm (fastAction (y u)-b.Ic) ≤ a+2*d := sorry

/-- Energy-source assumptions: the upper Hessian bound is only on real actions. -/
structure RealFastConvex (Ic : Fin n → ℝ) (R m M : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop where
  m_pos : 0 < m
  m_le : m ≤ M
  hol : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n Ic} R)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n Ic} R →
    (h (KAM.realInclusion n I)).im = 0
  convex : ∀ I : Fin n → ℝ, ‖I-Ic‖ < R → ∀ v : Fin n → ℝ,
    m*euclid v^2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I v v
  hessian_real : ∀ I : Fin n → ℝ, ‖I-Ic‖ < R → ∀ v : Fin n → ℝ,
    euclid (fun i => fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) v) ≤ M*euclid v


/-- Fast convexity and Hessian bound; the frequency need have no upper bound. -/
structure FastConvex (Ic : Fin n → ℝ) (R m M : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop where
  m_pos : 0 < m
  m_le : m ≤ M
  hol : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n Ic} R)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n Ic} R →
    (h (KAM.realInclusion n I)).im = 0
  convex : ∀ I : Fin n → ℝ, ‖I-Ic‖ < R → ∀ v : Fin n → ℝ,
    m*euclid v^2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I v v
  hessian : ∀ I ∈ polyNbhd {KAM.realInclusion n Ic} R, ∀ v : Fin n → ℂ,
    euclid (fun i => fderiv ℂ (fderiv ℂ h) I (Pi.single i 1) v) ≤ M*euclid v

/-- Restrict the complex Hessian bound to the real slice; no extra source premise. -/
theorem FastConvex.toRealFastConvex {Ic : Fin n → ℝ} {R m M : ℝ}
    {h : (Fin n → ℂ) → ℂ} (hh : FastConvex Ic R m M h) :
    RealFastConvex Ic R m M h := sorry

def NearResonance (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (Ic : Fin n → ℝ) (δ : ℝ) : Prop :=
  ∀ v ∈ KAM.Stability.resSpan Λ, |∑ i, KAM.frequencyMap h Ic i*v i| ≤ δ*euclid v

theorem energy_free (b : PartialBlock n k) {r s m M ε η ζ δ : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {g fs : EC n k → ℂ}
    (hr : 0 < r) (hs : 0 < s) (hh : RealFastConvex b.Ic r m M h)
    (hg : ext_class b r s g) (hf : ext_class b r s fs)
    (hgb : WBound b.base r s g (5*ε/4)) (hfb : WBound b.base r s fs η)
    (hsupp : ∀ J ∈ polyNbhd b.base r, ∀ j : Fin n → ℤ, j ∉ Λ → coeff g J j = 0)
    (hε : 0 < ε) (hη : 0 ≤ η) (hζ : 0 < ζ) (hηζ : η ≤ ζ) (hζε : ζ ≤ ε/Real.exp 1)
    (hsmall : ε ≤ m*r^2/2^12) (hSL : 16*k*b.c*s ≤ r)
    (hδ : 0 < δ) (hδr : δ ≤ m*r/16) (hnr : NearResonance Λ h b.Ic δ)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ExtOrbit b r (liftFast h+g+fs) J y)
    (hinit : euclid (fastAction (y 0)-b.Ic) < δ/(4*M))
    (hslow : ∀ u ∈ J, ∃ v ∈ b.S, ‖slowPair (y u)-b.lam⁻¹ • v‖ < r/2) :
    ∀ t ∈ J, |t| ≤ s*m*r/(20*M*ζ) → euclid (fastAction (y t)-fastAction (y 0)) ≤ r/4 := sorry

theorem nonresonant (b : PartialBlock n k) {s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α L p ε {0} h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, ‖fastAction (y u)-b.Ic‖ ≤ b.rB/2 := sorry

theorem resonant (b : PartialBlock n k) {s K α m M ε : ℝ}
    {Λ : AddSubgroup (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α (Real.sqrt n*M) (9/8) ε (Λ:Set (Fin n → ℤ)) h f)
    (hconv : FastConvex b.Ic b.rB m M h) (hne : NearResonance (Λ:Set (Fin n → ℤ)) h b.Ic (m*b.rB/32))
    (hsmall : ε ≤ m*b.rB^2/2^14)
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*m*b.rB/(240*M*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, euclid (fastAction (y u)-b.Ic) ≤ b.rB/2 := sorry

/-- Exactly the frozen source premises, bundled only for internal signatures. -/
structure PartialData (n k : ℕ) where
  G : Set (Fin n → ℝ)
  G' : Set (Fin n → ℝ)
  D : Set (KAM.Planetary.Phase k)
  ρ : ℝ
  g : ℝ
  m : ℝ
  Mc : ℝ
  h : (Fin n → ℂ) → ℂ
  hn : 2 ≤ n
  hk : 1 ≤ k
  hG : IsOpen G
  hGc : Convex ℝ G
  hG' : IsOpen G'
  hGc' : Convex ℝ G'
  hD : IsOpen D
  hρ : 0 < ρ
  hMc : 0 < Mc
  collar : ∀ I ∈ G, Metric.closedBall I ρ ⊆ G'
  hol : DifferentiableOn ℂ h (KAM.actionNbhd G' ρ)
  C2 : ContDiffOn ℂ 2 h (KAM.actionNbhd G' ρ)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd G' ρ →
    (h (KAM.realInclusion n I)).im = 0
  Hess : ∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mc
  definite : HasDefiniteFastPart G' ρ g m h

def constants (a : PartialData n k) : PartialConstants := ⟨n,a.ρ,a.g,a.m,a.Mc⟩
def block_setting (a : PartialData n k) (μ : ℝ) (Ic : Fin n → ℝ) (r : ℝ) : PartialBlock n k :=
  ⟨Ic, innerCore a.D (3*(constants a).d μ/4), r, (constants a).d μ/4⟩
def signedH (a : PartialData n k) (σ : ℝ) (I : Fin n → ℂ) : ℂ :=
  (σ:ℂ)*a.h I/(2*(Real.pi:ℂ))
def signedF (_a : PartialData n k) (σ μ : ℝ) (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ)
    (z : EC n k) : ℂ :=
  (σ*μ/(2*Real.pi):ℝ)*P (Fin.append (fun i => (2*Real.pi:ℂ)*z.1 i) (slowPair z).1,
    Fin.append (fastAction z) (slowPair z).2)
/-- Pull physical slow coordinates back by the fixed block scale. -/
def slowScale (lam : ℝ) (z : EC n k) : EC n k :=
  (z.1, Fin.append (fastAction z)
    (Fin.append (fun i => (lam:ℂ)*(slowPair z).1 i) (fun i => (lam:ℂ)*(slowPair z).2 i)))
def blockPert (a : PartialData n k) (μ σ : ℝ) (Ic : Fin n → ℝ) (r : ℝ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) : EC n k → ℂ :=
  signedF a σ μ P ∘ slowScale (block_setting a μ Ic r).lam

theorem hessian (a : PartialData n k) (hne : a.G.Nonempty) :
    a.m ≤ a.Mc ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ Ic ∈ a.G, ∀ R : ℝ, 0 < R → R ≤ (constants a).r0 →
        FastConvex Ic R (constants a).m1 (constants a).M1 (signedH a σ)) ∧
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd a.G' a.ρ →
        (constants a).g1 ≤ ‖KAM.frequencyMap (signedH a σ) I‖) := sorry

/-- Explicit selected sign is a source witness, not a convexity conclusion. -/
def DefiniteSign (a : PartialData n k) (σ : ℝ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd a.G' a.ρ →
    a.g ≤ ‖KAM.frequencyMap a.h I‖ ∧ ∀ v : Fin n → ℝ,
      a.m*(∑ i, (v i)^2) ≤ σ*fderiv ℝ (fderiv ℝ (realPart a.h)) I v v

theorem domain (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    polyNbhd {KAM.realInclusion n Ic} R ⊆ KAM.actionNbhd a.G' a.ρ ∧
    ext_class b R (constants a).s (blockPert a μ σ Ic R P) ∧
    WBound b.base R (constants a).s (blockPert a μ σ Ic R P) ((constants a).eps μ) := sorry

/-- The geometric output consumed by Part 11; covering itself is an upstream theorem.
No new representation of the Part 8 lattice enumeration is introduced. -/
theorem block_data (a : PartialData n k) (hne : a.G.Nonempty) {μ σ : ℝ} (hμ : 0 < μ)
    (hε : (constants a).eps μ ≤ (constants a).eps0) (hσ : DefiniteSign a σ)
    (hκ : 6 ≤ (constants a).kappa μ) {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G) :
    let c := constants a
    ∃ Λ : AddSubgroup (Fin n → ℤ), ∃ r : ℝ,
      Λ ≠ ⊤ ∧ c.rTheta μ ≤ r ∧ r ≤ c.R0/c.K μ ∧ 0 < r ∧
      IsNonresonant {KAM.realInclusion n Ic} (c.K μ/Real.sqrt n) ((9/8)*c.M1*c.K μ*r)
        (Λ:Set (Fin n → ℤ)) (signedH a σ) ∧
      (∃ δ : ℝ, 0 ≤ δ ∧ δ < c.m1*r/32 ∧ NearResonance (Λ:Set (Fin n → ℤ)) (signedH a σ) Ic δ) ∧
      FreqLipschitz {KAM.realInclusion n Ic} r (Real.sqrt n*c.M1) (signedH a σ) ∧
      c.eps μ ≤ c.m1*r^2/2^14 ∧
      c.eps μ ≤ ((9/8)*c.M1*c.K μ*r)*r/(2^7*9*(c.K μ/Real.sqrt n)) := sorry

/-- Physical period-one coordinates (no block-dependent coordinate scale). -/
def physicalDomain (Ic : Fin n → ℝ) (R w : ℝ) (S : Set (KAM.Planetary.Phase k)) : Set (ER n k) :=
  {z | ‖fastAction z-Ic‖ < R ∧ ∃ v ∈ S, ‖slowPair z-v‖ < w}

theorem domain_field (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    let H := KAM.Planetary.degenerateHamiltonian (realPart a.h) (fun _ w => (P (complexifyPhase w)).re) μ
    EqOn (fun z => σ • realWfield (2*Real.pi) (converted H) z)
      (realWfield (2*Real.pi) (fun z => (liftFast (signedH a σ) (extCx z)+signedF a σ μ P (extCx z)).re))
      (physicalDomain Ic R b.w b.S) := sorry

theorem block (a : PartialData n k) (hne : a.G.Nonempty) {μ σ : ℝ} (hμ : 0 < μ)
    (hσ : DefiniteSign a σ) (hε : (constants a).eps μ ≤ (constants a).eps0)
    (hd : (constants a).d μ ≤ a.ρ) (hκ : 6 ≤ (constants a).kappa μ)
    (hSL : 256*k*a.ρ*(constants a).R0/((constants a).d μ)^2 ≤ (constants a).K μ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P)
    {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G) (F : ER n k → ER n k)
    (hF : EqOn F (realWfield (2*Real.pi)
      (fun z => (liftFast (signedH a σ) (extCx z)+signedF a σ μ P (extCx z)).re))
      (physicalDomain Ic (constants a).r0 ((constants a).d μ/4)
        (innerCore a.D (3*(constants a).d μ/4))))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u) (hinit : fastAction (y 0) = Ic)
    (hx : slowPair (y 0) ∈ innerCore a.D (3*(constants a).d μ/4))
    {t1 : ℝ} (ht1 : t1 ∈ J) (htT : |t1| ≤ (constants a).blockTime μ)
    (hstop : ∀ u ∈ uIcc 0 t1, slowPair (y u) ∈ innerCore a.D ((constants a).d μ)) :
    ∀ u ∈ uIcc 0 t1, ‖fastAction (y u)-Ic‖ ≤ (constants a).R0/(2*(constants a).K μ) := sorry

theorem threshold (a : PartialData n k) (hne : a.G.Nonempty) :
    ∃ μ0 : ℝ, 0 < μ0 ∧ ∀ μ : ℝ, 0 < μ → μ < μ0 →
      let c := constants a
      c.eps μ ≤ c.eps0 ∧ c.d μ ≤ a.ρ ∧ 6 ≤ c.kappa μ ∧
      256*k*a.ρ*c.R0/(c.d μ)^2 ≤ c.K μ ∧ c.R0/(2*c.K μ) ≤ c.d μ/2 ∧
      μ⁻¹*Real.exp (μ^(-partialTimeExponent n)) ≤ c.blockTime μ := sorry


/-- The selected frozen definiteness witness is retained for assembly. -/
theorem hessian_at_sign (a : PartialData n k) (hne : a.G.Nonempty) {σ : ℝ}
    (hσ : DefiniteSign a σ) :
    a.m ≤ a.Mc ∧ ∀ Ic ∈ a.G, ∀ R : ℝ, 0 < R → R ≤ (constants a).r0 →
      FastConvex Ic R (constants a).m1 (constants a).M1 (signedH a σ) := sorry

/-- Generic real-preservation wrapper: Part 5 flow_e needs coordinate regrouping. -/
theorem flow_real (W : EC n k ≃L[ℂ] EC n k) {Ω : Set (EC n k)} {F : EC n k → EC n k} {ε : ℝ}
    (hF : KAM.Canonical.SmallField W Ω F ε)
    (hr : ∀ z : ER n k, extCx z ∈ Ω → extCx (extRe (F (extCx z))) = F (extCx z))
    {z : ER n k} (hz : extCx z ∈ KAM.Canonical.gaugeInterior W Ω (1/2)) {t : ℝ} (ht : |t| ≤ 1) :
    extCx (extRe (KAM.Canonical.flow F Ω t (extCx z))) = KAM.Canonical.flow F Ω t (extCx z) := sorry

/-- Taylor remainder bound, without choosing a maximum on an empty set. -/
theorem ext_taylor_bound {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ)
    (N : ℕ) (hN : 1 ≤ N) (B : ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖extAd c φ N u (γ t)‖ ≤ B) :
    ‖∫ t in (0:ℝ)..1, (((1-t)^(N-1)/(N-1).factorial:ℝ):ℂ)*extAd c φ N u (γ t)‖ ≤ B/N.factorial := sorry

/-- Arbitrary holomorphic observables inherit weighted bracket invariance. -/
theorem symplectic_bracket {c : ℝ} {U V : Set (EC n k)} (hU : IsOpen U) (hV : IsOpen V)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hm : MapsTo Ψ U V)
    (hc : ExtCanonical c U Ψ) {u v : EC n k → ℂ}
    (hu : DifferentiableOn ℂ u V) (hv : DifferentiableOn ℂ v V) :
    ∀ z ∈ U, extBracket c (u ∘ Ψ) (v ∘ Ψ) z = extBracket c u v (Ψ z) := sorry

theorem symplectic_det {c : ℝ} (hc : 0 < c) {U : Set (EC n k)} (hU : IsOpen U)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hcanon : ExtCanonical c U Ψ) :
    ∀ z ∈ U, (fderiv ℂ Ψ z).det = 1 ∨ (fderiv ℂ Ψ z).det = -1 := sorry


/-- B.5(i) keeps its smaller image tube, used by the integral remainder. -/
theorem composition_domain (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V : ℝ}
    {φ : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ) :
    (∀ z ∈ Dom n b.base (R'-ρ) (s'-σ), scaled ρ σ (wfield b.c φ z) ≤ V/(ρ*σ)) ∧
    (∀ t : ℝ, |t| ≤ 1 → MapsTo (extFlow b R' s' ρ σ φ t)
      (Dom n b.base (R-ρ) (s-σ))
      (Dom n b.base (R-(1-V/(ρ*σ))*ρ) (s-(1-V/(ρ*σ))*σ))) := sorry

theorem composition_real (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V : ℝ}
    {φ u : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ)
    (hφ : extReal (Dom n b.base R' s') φ) (hu : extReal (Dom n b.base R s) u) :
    extReal (Dom n b.base (R-ρ) (s-σ)) (u ∘ extFlow b R' s' ρ σ φ 1) := sorry

/-- Smoothness and the full derivative sequence in the source Taylor statement. -/
theorem ext_taylor_regular {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ) :
    ContDiffOn ℝ ∞ (u ∘ γ) (Icc 0 1) ∧
    ∀ j : ℕ, ∀ t ∈ Icc (0:ℝ) 1,
      iteratedDerivWithin j (u ∘ γ) (Icc 0 1) t = extAd c φ j u (γ t) := sorry

def extForm (c : ℝ) (v w : EC n k) : ℂ :=
  (∑ i, (fastAction v i*w.1 i-v.1 i*fastAction w i)) +
    (c:ℂ)⁻¹*(∑ i, ((slowPair v).2 i*(slowPair w).1 i-(slowPair v).1 i*(slowPair w).2 i))

theorem symplectic_form {c : ℝ} (hc : 0 < c) {U : Set (EC n k)} (hU : IsOpen U)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hcanon : ExtCanonical c U Ψ) :
    ∀ z ∈ U, ∀ v w : EC n k,
      extForm c (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = extForm c v w := sorry

end KAM.Nekhoroshev

namespace KAM.Provider.Nekhoroshev
open KAM.Nekhoroshev
theorem partialConvex_nekhoroshev
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (G G' : Set (Fin n → ℝ)) (D : Set (KAM.Planetary.Phase k))
    (hG : IsOpen G) (hGc : Convex ℝ G)
    (hG' : IsOpen G') (hGc' : Convex ℝ G') (hD : IsOpen D)
    (ρ g m Mcomplex : ℝ) (hρ : 0 < ρ) (hMc : 0 < Mcomplex)
    (hcollar : ∀ I ∈ G, Metric.closedBall I ρ ⊆ G')
    (h : (Fin n → ℂ) → ℂ)
    (hhol : DifferentiableOn ℂ h (KAM.actionNbhd G' ρ))
    (hC2 : ContDiffOn ℂ 2 h (KAM.actionNbhd G' ρ))
    (hreal : ∀ I : Fin n → ℝ,
      (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ → (h (fun i => (I i : ℂ))).im = 0)
    (hHess : ∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mcomplex)
    (hdef : HasDefiniteFastPart G' ρ g m h) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
      ∀ P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ,
      IsPartialPerturbation G' D ρ P → ∀ C : ℝ, 0 < C →
      ∀ z : ℝ → KAM.Planetary.Phase (n + k),
      IsSolutionOn
        (KAM.Planetary.degenerateHamiltonian (realPart h)
          (fun _ w => (P (complexifyPhase w)).re) μ)
        {I | KAM.Planetary.fast (b := k) I ∈ G} (Set.Icc 0 C) z →
      KAM.Planetary.fast (b := k) (z 0).2 ∈ innerCore G (μ ^ partialDriftExponent n) →
      ∀ t ∈ Set.Icc 0
        (min C (μ⁻¹ * Real.exp (μ ^ (-partialTimeExponent n)))),
      (∀ u ∈ Set.Icc 0 t,
        (KAM.Planetary.slow (a := n) (z u).1, KAM.Planetary.slow (a := n) (z u).2)
          ∈ innerCore D (μ ^ partialDriftExponent n)) →
      ‖KAM.Planetary.fast (b := k) (z t).2 - KAM.Planetary.fast (b := k) (z 0).2‖
        ≤ μ ^ partialDriftExponent n / 2 :=
  sorry

end KAM.Provider.Nekhoroshev
end
```
