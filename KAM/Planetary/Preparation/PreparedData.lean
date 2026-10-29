/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowSigned
public import KAM.Planetary.Preparation.HoloAssembly
public import KAM.Planetary.Preparation.Patch
public import KAM.Planetary.WeakMeasure.Basic
public import KAM.Frozen.Planetary.Defs.FixedHamiltonian

/-!
# Prepared data and specifications (P11A-P8, `bpP:p11:sec-E#data`)

Verbatim signed `P11PreparedData`, `p11PreparedFreq`, `p11PreparedFreqR`, `P11PreparedSpec`,
`p11M0`, `p11SlowNormalizedFreq`, `P11PreparedFullSpec`, `p11PreparedData`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

structure P11PreparedData (n : ℕ) where
  N : P11CVec (n+n) → ℂ
  P : P11Phase (n+n) → ℂ
  chain : Phase (n+n) → Phase (n*2)
  checkW : P11Vec (n+n) → P11Vec (n+n)
  deriving Inhabited
def p11PreparedFreq {n : ℕ} (Q : P11PreparedData n) (I : P11CVec (n+n)) : P11CVec (n+n) :=
  fun i => fderiv ℂ Q.N I (Pi.single i 1)
def p11PreparedFreqR {n : ℕ} (Q : P11PreparedData n) (I : P11Vec (n+n)) : P11Vec (n+n) :=
  fun i => (p11PreparedFreq Q (KAM.realInclusion (n+n) I) i).re
def P11PreparedSpec {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) (Q : P11PreparedData n) : Prop :=
  let C := p11SecularData D
  let A := p11PatchData D
  let U := KAM.actionNbhd (p11PreparedBox n) 1
  let V := KAM.complexStrip (n+n) (C.sigma/72) ×ˢ U
  let smallV := KAM.actionNbhd (p11PreparedBox n) (3/4)
  let W := p11PreparedFreq Q
  let ell := Real.log (1/eps)
  let exponent := 5*C.tau+2+(C.tau+1)*(A.mu+1)
  (let A := p11SlowData D nu eps
   (∀ z ∈ V, let y := p11Rescale C.J0 eps z
     Q.N z.2=(A.h0 y.2+A.g2 y.2)/eps ∧ Q.P z=A.f3 y/eps) ∧
   ∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ V →
     let w := (p11FastData D eps).map
       (p11PolarC (A.Psi (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z))))
     Q.chain z=C.chart ((fun i => (w.1 i).re),fun i => (w.2 i).re)) ∧
  DifferentiableOn ℂ Q.N U ∧ DifferentiableOn ℂ Q.P V ∧
  (∀ z ∈ V, ∀ i : Fin (n+n), Q.P (z.1+Pi.single i 1,z.2)=Q.P z) ∧
  KAM.Canonical.RealOn V (fun z => Q.N z.2+Q.P z) ∧
  KAM.Canonical.RealOn V Q.P ∧
  (∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈ U → (Q.N (KAM.realInclusion (n+n) I)).im=0) ∧
  p11Bound V Q.P (c*eps^(nu+3/2)*ell^(2*C.tau+1)) ∧
  p11Bound smallV W (2*C.L+1) ∧
  (∀ I ∈ smallV, ‖fderiv ℂ W I‖ ≤ 2*C.L+1) ∧
  (∀ y : P11Vec (n+n), ‖y‖ ≤ 5/4 →
    p11PreparedFreqR Q y=Fin.append
      (fun i : Fin n => Q.checkW y (Fin.castAdd n i))
      (fun i : Fin n => eps*Q.checkW y (Fin.natAdd n i))) ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    let psi := fun J : P11Vec n => Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho)
    p11JetBound true A.mu {J | ‖J-C.J0‖ < p11s2 C nu eps/4} (psi-A.varpi) (c*eps*ell^exponent)) ∧
  (∀ direction, p11euclid direction=1 → ∀ j, 1 ≤ j → j ≤ A.mu+1 →
    ∀ y ∈ p11thick (p11PreparedBox n) (1/4),
      p11op (p11scalar 2 (p11PreparedFreqR Q) direction) j y ≤ (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ V →
    fixedHamiltonian D.G D.m0 D.m eps (Q.chain z)=eps*(Q.N (KAM.realInclusion (n+n) z.2)+
      Q.P (KAM.realInclusion₂ (n+n) z)).re)
def p11M0 (n mu : ℕ) (L : ℝ) : ℝ :=
  (2*n+1 : ℝ)^(mu+1)*(2*L+1)
def p11SlowNormalizedFreq {n : ℕ} (D : P11Physical n)
    (nu eps : ℝ) (J rho : P11Vec n) : P11Vec (n+n) :=
  let A := p11SlowData D nu eps
  let I := Fin.append (KAM.realInclusion n J)
    (fun i : Fin n => (eps*(2*Real.pi+rho i) : ℂ))
  let W : P11CVec (n+n) :=
    fun i => fderiv ℂ (A.h0+A.g2) I (Pi.single i 1)
  Fin.append (fun i : Fin n => (W (Fin.castAdd n i)).re)
    (fun i : Fin n => (W (Fin.natAdd n i)).re/eps)
def P11PreparedFullSpec {n : ℕ} (D : P11Physical n)
    (nu eps c : ℝ) (Q : P11PreparedData n) : Prop :=
  let C := p11SecularData D
  let A := p11PatchData D
  let ell := Real.log (1/eps)
  let exponent := 5*C.tau+2+(C.tau+1)*(A.mu+1)
  P11PreparedSpec D nu eps c Q ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    ∀ J : P11Vec n, ‖J-C.J0‖ < p11s2 C nu eps/4 →
      Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho) =
        p11SlowNormalizedFreq D nu eps J rho) ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    p11JetBound true A.mu {J | ‖J-C.J0‖ < p11s2 C nu eps/4}
      ((fun J => Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho))-A.varpi)
      (c*eps*ell^exponent)) ∧
  p11JetBound true A.mu (p11thick (p11PreparedBox n) (1/4))
    (p11PreparedFreqR Q) (p11M0 n A.mu C.L) ∧
  (∀ direction, p11euclid direction=1 →
    ∀ y ∈ p11thick (p11PreparedBox n) (1/4),
      p11op (p11scalar 2 (p11PreparedFreqR Q) direction) 0 y ≤
        (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2)
open Classical in
def p11PreparedData {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) : P11PreparedData n :=
  if h : ∃ Q, P11PreparedFullSpec D nu eps c Q then h.choose else default

end KAM.Planetary

end
