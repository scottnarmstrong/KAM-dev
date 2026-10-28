/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Domains
public import KAM.Weighted.Norm
public import KAM.ODE.Basic
public import KAM.Canonical.Flow
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Nekhoroshev.NormalForm.Homological
public import KAM.Nekhoroshev.Stability.Gradient
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Frozen.Planetary.Defs.Phase

/-!
# Setting of the partial convex Nekhoroshev theorem (Part 11, package N11-A)

The extended phase space `Ext n k 𝕜 = 𝕜ⁿ × 𝕜^{n+(k+k)}` (angles, then fast actions and the slow
pair), its projections, the weighted vector field and bracket, the block geometry
`PartialBlock`, the classes `ext_class`, the source bundles `ExtNFHyp`, `ExtConjHyp`,
`FastConvex`, `RealFastConvex` and the closeness predicate `NearResonance`.
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

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
def liftFast (h : (Fin n → ℂ) → ℂ) (z : EC n k) : ℂ := h (fastAction z)
def realHamiltonianExt (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ) : ER n k → ℝ :=
  (b.realDom R).indicator (fun z => (H (extCx z)).re)
def ExtOrbit (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ)
    (J : Set ℝ) (y : ℝ → ER n k) : Prop :=
  KAM.ODE.IsSolutionIn (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R) J y

/-- Basis-free expression of DΨ Ω DΨᵀ=Ω, for all linear functionals. -/
def ExtCanonical (c : ℝ) (U : Set (EC n k)) (Ψ : EC n k → EC n k) : Prop :=
  ∀ z ∈ U, ∀ u v : EC n k →L[ℂ] ℂ,
    extBracket c (fun x => u (Ψ x)) (fun x => v (Ψ x)) z =
      extBracket c (fun x => u x) (fun x => v x) (Ψ z)

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

def NearResonance (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (Ic : Fin n → ℝ) (δ : ℝ) : Prop :=
  ∀ v ∈ KAM.Stability.resSpan Λ, |∑ i, KAM.frequencyMap h Ic i*v i| ≤ δ*euclid v

end KAM.Nekhoroshev

end
