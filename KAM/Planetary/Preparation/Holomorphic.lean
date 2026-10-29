/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Working
public import KAM.Planetary.Preparation.Patch
public import KAM.Planetary.Preparation.AnalyticExtension
public import KAM.Planetary.Preparation.Schwarz
public import KAM.Planetary.Preparation.HolomorphicRotation
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.Hamiltonian.HolChart

/-!
# The holomorphic secular form (P11A-P2, `bpP:p11:holo-chart`)

The working carrier `p11WorkingDom`, the data package `P11SecularData` with its specification
`P11SecularSpec`/`P11SecularFullSpec`, and the theorem `holo_chart` selecting the data from the
physical data. The local steps `hc-rot`, `hc-lift`, `hc-strip`, `hc-F`, `hc-id`, `hc-lat` and
`hc-mean` are the named proof obligations of the construction.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Working chart carrier: ((theta,x),(J,y)), exactly the existing phase carrier. -/
def p11WorkingDom (n : ℕ) (J0 : P11Vec n) (s r rz : ℝ) : Set (P11Phase (n+n)) :=
  {z | (fun i : Fin n => z.1 (Fin.castAdd n i)) ∈ KAM.complexStrip n s ∧
    ‖(fun i : Fin n => z.2 (Fin.castAdd n i))-KAM.realInclusion n J0‖ < r ∧
    ‖(fun i : Fin n => z.1 (Fin.natAdd n i))‖ < rz ∧
    ‖(fun i : Fin n => z.2 (Fin.natAdd n i))‖ < rz}
/-- Only data, with all properties in P11SecularSpec. -/
structure P11SecularData (n : ℕ) where
  J0 : P11Vec n
  gamma : ℝ
  tau : ℝ
  rC : ℝ
  sigma : ℝ
  rz : ℝ
  MF : ℝ
  L : ℝ
  Brho : ℝ
  Bdrho : ℝ
  h : P11CVec n → ℂ
  C : P11CVec n → ℂ
  omega : P11CVec n → P11CVec n
  Omega : P11CVec n → P11CVec n
  F : P11Phase (n+n) → ℂ
  rho : P11CVec n → Matrix (Fin n) (Fin n) ℂ
  chart : Phase (n+n) → Phase (n*2)
/-- Literal P9 inverse lift after the canonical period conversion T1; positions and momenta keep
frozen order. -/
def p11ChartInput {n : ℕ} (C : P11SecularData n) (z : Phase (n+n)) : Phase (n+n) :=
  let L : P11Vec n := fun i => fast z.2 i/(2*Real.pi)
  let x := KAM.realInclusion n (slow z.1)
  let y := KAM.realInclusion n (slow z.2)
  let R := C.rho (KAM.realInclusion n L)
  assemble L
    (fun l => 2*Real.pi*fast z.1 l+
      (∑ i, ∑ j,
        y i*(R.transpose*fderiv ℂ C.rho (KAM.realInclusion n L) (Pi.single l 1)) i j*x j).re)
    (fun i => (R.mulVec y i).re) (fun i => (R.mulVec x i).re)
def p11WorkingH {n : ℕ} (C : P11SecularData n) (eps : ℝ) (z : P11Phase (n+n)) : ℂ :=
  C.h (fun i : Fin n => z.2 (Fin.castAdd n i))+eps*C.F z
def p11FastMean {n : ℕ} (F : P11Phase (n+n) → ℂ) (J : P11CVec n) (z : P11Phase n) : ℂ :=
  KAM.torusAverage (fun theta : P11Vec n =>
    F (Fin.append (KAM.realInclusion n theta) z.1,Fin.append J z.2))
def P11SecularSpec {n : ℕ} (D : P11Physical n) (C : P11SecularData n) : Prop :=
  (∀ J : P11Vec n, KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC) →
    J ∈ (p11PatchData D).V ∧
    (∀ i : Fin n,
      (C.omega (KAM.realInclusion n J) i).re=(p11PatchData D).varpi J (Fin.castAdd n i)) ∧
    (∀ i : Fin n, (C.Omega (KAM.realInclusion n J) i).re=
      2*Real.pi*(p11PatchData D).varpi J (Fin.natAdd n i))) ∧
  (∀ J : P11Vec n, ‖J-C.J0‖ < 2*C.rC →
    ((C.h (KAM.realInclusion n J)).re=
      -∑ i, (D.G*D.m0)^2*D.m i^3/(2*(J i/(2*Real.pi))^2)) ∧
    (C.h (KAM.realInclusion n J)).im = 0) ∧
  (DifferentiableOn ℂ C.omega (Metric.ball (KAM.realInclusion n C.J0) (2*C.rC)) ∧
   DifferentiableOn ℂ C.Omega (Metric.ball (KAM.realInclusion n C.J0) (2*C.rC))) ∧
  C.tau=max ((n : ℝ)*(p11PatchData D).mu) (2*n) ∧
  DifferentiableOn ℂ C.h (Metric.ball (KAM.realInclusion n C.J0) (2*C.rC)) ∧
  (∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC),
    C.omega J=fun i => fderiv ℂ C.h J (Pi.single i 1)) ∧
  (∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC), ∀ j ≤ (p11PatchData D).mu+1,
    ‖iteratedFDeriv ℂ j
      (fun J => Fin.append (C.omega J) ((2*Real.pi : ℂ)⁻¹ • C.Omega J)) J‖ ≤ C.L) ∧
  C.J0 ∈ interior (p11PatchData D).K ∧ 0 < C.gamma ∧ C.gamma ≤ 1 ∧
  KAM.IsDiophantine C.gamma C.tau ((p11PatchData D).varpi C.J0) ∧
  0 < C.rC ∧ C.rC ≤ 1 ∧ C.rC ≤ Real.pi*p11PhysicalDelta D/8 ∧ 0 < C.sigma ∧ C.sigma ≤ 1/4 ∧
  0 < C.rz ∧ C.rz ≤ 1 ∧ 1 ≤ C.MF ∧ 1 ≤ C.L ∧ 1 ≤ C.Brho ∧ 1 ≤ C.Bdrho ∧
  DifferentiableOn ℂ C.F (p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz) ∧
  p11Bound (p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz) C.F
    (C.MF/KAM.Weighted.coth (Real.pi*C.sigma)^n) ∧
  (∀ z ∈ p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz, ∀ j : Fin n,
    C.F (z.1+Pi.single (Fin.castAdd n j) 1,z.2)=C.F z) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz →
    (C.F (KAM.realInclusion₂ (n+n) z)).im=0) ∧
  (∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC),
    ∀ z : P11Phase n, ‖z‖ < C.rz →
      ‖p11FastMean C.F J z-C.C J-∑ i, C.Omega J i*(z.1 i^2+z.2 i^2)/2‖ ≤
        C.MF*(‖z‖/C.rz)^4) ∧
  (∀ L : P11Vec n, ‖L-(2*Real.pi)⁻¹ • C.J0‖ < C.rC/Real.pi →
    (∀ i j, (C.rho (KAM.realInclusion n L) i j).im=0) ∧
    (C.rho (KAM.realInclusion n L)).det=1 ∧
    (let R : Matrix (Fin n) (Fin n) ℝ := fun i j => (C.rho (KAM.realInclusion n L) i j).re
     R.transpose*p11SecularMatrix D L*R=
       Matrix.diagonal ((p11PatchData D).sigma ((2*Real.pi) • L)))) ∧
  (DifferentiableOn ℂ C.rho
    (Metric.ball ((2*Real.pi)⁻¹ • KAM.realInclusion n C.J0) (C.rC/Real.pi)) ∧
   ∀ J ∈ Metric.ball ((2*Real.pi)⁻¹ • KAM.realInclusion n C.J0) (C.rC/Real.pi),
     (C.rho J).transpose*C.rho J=1 ∧
     (∀ i, (∑ j, ‖C.rho J i j‖) ≤ C.Brho) ∧
     (∀ l : Fin n, ∀ i,
       (∑ j, ‖((C.rho J).transpose*fderiv ℂ C.rho J (Pi.single l 1)) i j‖) ≤ C.Bdrho)) ∧
  (let O := KAM.realInclusion₂ (n+n) ⁻¹' p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz
   AnalyticOnNhd ℝ C.chart O ∧ KAM.Kepler.IsSymplecticOn 1 C.chart O ∧
   (∀ z ∈ O, p11ChartInput C z ∈ poincareProdDom n ∧
     C.chart z=poincareProd D.m (D.G*D.m0) (p11ChartInput C z) ∧
       C.chart z ∈ collisionFreeDomain n) ∧
   (∀ z ∈ O, ∀ k : Fin n → ℤ,
     C.chart (z.1+Fin.append (fun i => (k i : ℝ)) 0,z.2)=C.chart z) ∧
   (∀ z ∈ O, ∀ z' ∈ O, C.chart z=C.chart z' →
     ∃ k : Fin n → ℤ, z'=(z.1+Fin.append (fun i => (k i : ℝ)) 0,z.2)) ∧
   (∀ eps : ℝ, ∀ z ∈ O, fixedHamiltonian D.G D.m0 D.m eps (C.chart z)=
      (p11WorkingH C eps (KAM.realInclusion₂ (n+n) z)).re))
/-- Part 11 A: this is constructed from physical data, not a standing chart hypothesis. -/
def P11SecularFullSpec {n : ℕ} (D : P11Physical n)
    (C : P11SecularData n) : Prop :=
  P11SecularSpec D C ∧
  ∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC),
    KAM.Nekhoroshev.euclid
      (Fin.append (C.omega J) ((2*Real.pi : ℂ)⁻¹ • C.Omega J)) ≤ C.L

end KAM.Planetary

end
