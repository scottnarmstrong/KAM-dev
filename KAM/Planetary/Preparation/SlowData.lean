/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Fast
public import KAM.Planetary.Preparation.Polar
public import KAM.Planetary.Preparation.PolarAverage
public import KAM.Planetary.Preparation.RectangularBracket

/-!
# Slow averaging: data and specification (P11A-P7, `bpP:p11:sec-D#data`)

The signed parametric definitions `p11Rescale`, `p11PreparedBox`, `p11K2`, `p11s2`,
`P11SlowData`, `p11PartialVec` (verbatim), and the unsigned parametric copy `P11SlowSpecOf C Fast`
of the signed `P11SlowSpec`: its body is the signed body with the two lets
`C := p11SecularData D`, `Fast := p11FastData D eps` replaced by the parameters, so that
`P11SlowSpec D nu eps c A` unfolds to
`P11SlowSpecOf (p11SecularData D) (p11FastData D eps) nu eps c A` by `rfl`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Prepared chart rescaling, positions unchanged, both action blocks scaled by eps. -/
def p11Rescale {n : ℕ} (J0 : P11Vec n) (eps : ℝ) (z : P11Phase (n+n)) : P11Phase (n+n) :=
  (z.1, Fin.append (fun i : Fin n => (J0 i : ℂ)+eps*z.2 (Fin.castAdd n i))
    (fun i : Fin n => eps*(2*Real.pi+z.2 (Fin.natAdd n i))))
def p11PreparedBox (n : ℕ) : Set (P11Vec (n+n)) :=
  Set.pi univ (fun _ => Icc (-1/2 : ℝ) (1/2))
def p11K2 {n : ℕ} (C : P11SecularData n) (nu eps : ℝ) : ℝ :=
  3*nu/(Real.pi*(C.sigma/12))*Real.log (1/eps)
def p11s2 {n : ℕ} (C : P11SecularData n) (nu eps : ℝ) : ℝ :=
  min (p11s1 C eps/4) (C.gamma/(8*C.L*p11K2 C nu eps^(C.tau+1)))
structure P11SlowData (n : ℕ) where
  Psi : P11Phase (n+n) → P11Phase (n+n)
  h0 : P11CVec (n+n) → ℂ
  g2 : P11CVec (n+n) → ℂ
  Z : P11CVec (n+n) → ℂ
  f2 : P11Phase (n+n) → ℂ
  f3 : P11Phase (n+n) → ℂ
  deriving Inhabited
/-- Coordinate multi-index derivative on the existing Pi carrier, in fixed coordinate order. -/
def p11PartialVec {n m : ℕ} (alpha : Fin n → ℕ) (f : P11CVec n → P11CVec m) :
    P11CVec n → P11CVec m :=
  ((List.ofFn (fun i : Fin n => List.replicate (alpha i) i)).flatten).foldl
    (fun g i => fun x => fderiv ℂ g x (Pi.single i 1)) f
/-- Parametric copy of the signed `P11SlowSpec`. -/
def P11SlowSpecOf {n : ℕ} (C : P11SecularData n) (Fast : P11FastData n) (nu eps c : ℝ)
    (A : P11SlowData n) : Prop :=
  let center : P11CVec (n+n) := Fin.append (KAM.realInclusion n C.J0) (fun _ => 2*Real.pi*eps)
  let V := p11Box center (p11s2 C nu eps) (Real.pi*eps)
  let Vh := p11Box center (p11s2 C nu eps/2) (Real.pi*eps/2)
  let s := C.sigma/12
  let E := c*eps^(5/2 : ℝ)*Real.log (1/eps)^(2*C.tau+1)
  (∀ z ∈ KAM.complexStrip (n+n) s ×ˢ V,
    A.h0 z.2+A.f2 z=p11WorkingH C eps (Fast.map (p11PolarC z))) ∧
  (∀ I ∈ V, A.h0 I=C.h (fun i : Fin n => I (Fin.castAdd n i))+
    eps*p11PolarAverage Fast.G ((fun i : Fin n => I (Fin.castAdd n i)),
      fun i : Fin n => I (Fin.natAdd n i))) ∧
  (∀ I ∈ V, A.h0 I=C.h (fun i : Fin n => I (Fin.castAdd n i))+
    eps*(C.C (fun i : Fin n => I (Fin.castAdd n i))+
      (∑ i : Fin n, C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i/(2*Real.pi)*
        I (Fin.natAdd n i))+A.Z I)) ∧
  DifferentiableOn ℂ A.Z
    {I : P11CVec (n+n) |
      ‖(fun i : Fin n => I (Fin.castAdd n i))-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 ∧
      ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi*C.rz^2/16} ∧
  (∀ alpha : Fin n → ℕ, ∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/4 →
    ∀ rho : P11CVec n, ‖rho-(fun _ => (2*Real.pi*eps : ℂ))‖ < Real.pi*eps →
      ‖p11PartialVec alpha
        (fun J => fun i : Fin n =>
          fderiv ℂ (fun rho : P11CVec n => A.Z (Fin.append J rho)) rho (Pi.single i 1)) J‖ ≤
        c*(eps+p11eta1 C eps)*(∏ i, ((alpha i).factorial : ℝ))*(4/p11s1 C eps)^(∑ i, alpha i)) ∧
  (∀ I ∈ V, ∀ k : Fin (n+n) → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ p11K2 C nu eps →
    (if (fun i : Fin n => k (Fin.castAdd n i))=0 then eps else 1)*
      C.gamma/4*p11K2 C nu eps^(-C.tau) ≤
        ‖p11dotC k (fun i => fderiv ℂ A.h0 I (Pi.single i 1))‖) ∧
  DifferentiableOn ℂ A.h0 V ∧ DifferentiableOn ℂ A.g2 Vh ∧
  DifferentiableOn ℂ A.f2 (KAM.complexStrip (n+n) s ×ˢ V) ∧
  DifferentiableOn ℂ A.f3 (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
  KAM.Canonical.RealOn (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) A.f3 ∧
  KAM.Canonical.RealOn (KAM.complexStrip (n+n) s ×ˢ V) A.f2 ∧
  (∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈ Vh →
    (A.g2 (KAM.realInclusion (n+n) I)).im=0 ∧ (A.h0 (KAM.realInclusion (n+n) I)).im=0) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh →
    ∀ i, ((A.Psi (KAM.realInclusion₂ (n+n) z)).1 i).im=0 ∧
      ((A.Psi (KAM.realInclusion₂ (n+n) z)).2 i).im=0) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ i : Fin (n+n),
    A.f3 (z.1+Pi.single i 1,z.2)=A.f3 z) ∧
  DifferentiableOn ℂ A.Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ u v,
    KAM.Canonical.symplFormC (fderiv ℂ A.Psi z u) (fderiv ℂ A.Psi z v)=
      KAM.Canonical.symplFormC u v) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ k : Fin (n+n) → ℤ,
    A.Psi (z.1+(fun i => (k i : ℂ)),z.2)=A.Psi z+((fun i => (k i : ℂ)),0)) ∧
  InjOn A.Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
  MapsTo A.Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) (KAM.complexStrip (n+n) s ×ˢ V) ∧
  p11WBound V s A.f2 E ∧
  E ≤ (eps*C.gamma/4*p11K2 C nu eps^(-C.tau))*Real.pi*eps/(128*p11K2 C nu eps) ∧
  p11WBound Vh (s/6) A.f3 (eps^nu*E) ∧
  p11Bound Vh A.g2 (c*eps^3*Real.log (1/eps)^(5*C.tau+2)) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh,
    A.h0 (A.Psi z).2+A.f2 (A.Psi z)=A.h0 z.2+A.g2 z.2+A.f3 z) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh,
    ‖(fun i : Fin n => (A.Psi z).2 (Fin.natAdd n i)-z.2 (Fin.natAdd n i))‖ ≤
      c*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1) ∧
    ‖(fun i : Fin n => (A.Psi z).2 (Fin.castAdd n i)-z.2 (Fin.castAdd n i))‖ ≤
      c*eps^(5/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1) ∧
    ‖(A.Psi z).1-z.1‖ ≤ c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1))

end KAM.Planetary

end
