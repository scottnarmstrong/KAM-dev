/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.FastBridge
public import KAM.Planetary.Preparation.FastParams

/-!
# Fast averaging (P11A-P5, `bpP:p11:avg-fast`, `bpP:p11:sec-C#data`)

The exact CP09 preparation parameters `p11K1, p11Alpha1, p11s1, p11d1, p11eta1` (`ν₁ = 3`), the
fast data `P11FastData` with its specification `P11FastSpec`, and the exported core theorem
`avg_fast_of_spec`: for an arbitrary `C : P11SecularData n` with `P11SecularSpec D C` the
conclusion of `avg_fast` holds. The signed `avg_fast` and `p11FastData` (which select
`C = p11SecularData D` through `holo_chart`) are one-line wrappers of it. The proof is the
application of `osc_averaging` (`af-apply`), the divisor bound (`af-o1`), the smallness (S1)
(`af-o2`, via `e4`) and the bookkeeping of the conclusion (`af-concl`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Exact CP09 preparation parameters; nu1 is fixed at 3. -/
def p11K1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) : ℝ :=
  6/(Real.pi*C.sigma)*Real.log (1/(eps*C.MF))
def p11Alpha1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := C.gamma/2*p11K1 C eps^(-C.tau)
def p11s1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  min C.rC (C.gamma/(4*C.L*p11K1 C eps^(C.tau+1)))
def p11d1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := min (p11s1 C eps*C.sigma) C.rz^2
def p11eta1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  400*(1+n)*eps*C.MF^2/(2*Real.pi*p11Alpha1 C eps*p11d1 C eps)
structure P11FastData (n : ℕ) where
  map : P11Phase (n+n) → P11Phase (n+n)
  G : P11CVec n × P11Phase n → ℂ
  f1 : P11Phase (n+n) → ℂ
  deriving Inhabited
def P11FastSpec {n : ℕ} (C : P11SecularData n) (eps : ℝ) (A : P11FastData n) : Prop :=
  let U := p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2)
  DifferentiableOn ℂ A.map U ∧ InjOn A.map U ∧
  DifferentiableOn ℂ A.f1 U ∧ KAM.Canonical.RealOn U A.f1 ∧
  DifferentiableOn ℂ A.G
    (Metric.ball (KAM.realInclusion n C.J0) (p11s1 C eps/2) ×ˢ Metric.ball 0 (C.rz/2)) ∧
  (∀ J : P11Vec n, ‖J-C.J0‖ < p11s1 C eps/2 → ∀ z : Phase n, ‖z‖ < C.rz/2 →
    (A.G (KAM.realInclusion n J,KAM.realInclusion₂ n z)).im=0) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ U → ∀ i,
    ((A.map (KAM.realInclusion₂ (n+n) z)).1 i).im=0 ∧
    ((A.map (KAM.realInclusion₂ (n+n) z)).2 i).im=0) ∧
  (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ A.map z u) (fderiv ℂ A.map z v)=
    KAM.Canonical.symplFormC u v) ∧
  (∀ z ∈ U, ∀ k : Fin n → ℤ, A.map (z.1+Fin.append (fun i => (k i : ℂ)) 0,z.2)=
    A.map z+(Fin.append (fun i => (k i : ℂ)) 0,0)) ∧
  MapsTo A.map U (p11WorkingDom n C.J0 C.sigma (p11s1 C eps) C.rz) ∧
  (∀ z ∈ U, p11WorkingH C eps (A.map z)=
    C.h (fun i : Fin n => z.2 (Fin.castAdd n i))+
    eps*A.G ((fun i : Fin n => z.2 (Fin.castAdd n i)),
      ((fun i : Fin n => z.1 (Fin.natAdd n i)),fun i : Fin n => z.2 (Fin.natAdd n i)))+A.f1 z) ∧
  p11Bound U A.f1 ((eps*C.MF)^3) ∧
  (∀ z : P11Phase n, ‖z‖ < C.rz/2 → ∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 →
    let f := fun u : P11CVec n × P11CVec n => A.f1 (Fin.append u.1 z.1,Fin.append u.2 z.2)
    KAM.Weighted.WSummable f (C.sigma/6) J ∧ KAM.Weighted.wsum f (C.sigma/6) J ≤ (eps*C.MF)^3) ∧
  (∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 → ∀ z : P11Phase n, ‖z‖ < C.rz/2 →
    ‖A.G (J,z)-p11FastMean C.F J z‖ ≤ p11eta1 C eps) ∧
  ∀ z ∈ U,
    2*Real.pi*p11Alpha1 C eps*C.sigma*
      ‖(fun i : Fin n => (A.map z).2 (Fin.castAdd n i)-z.2 (Fin.castAdd n i))‖ ≤ 3*eps*C.MF ∧
    2*Real.pi*p11Alpha1 C eps*p11s1 C eps*
      ‖(fun i : Fin n => (A.map z).1 (Fin.castAdd n i)-z.1 (Fin.castAdd n i))‖ ≤ 9*eps*C.MF ∧
    2*Real.pi*p11Alpha1 C eps*C.rz*
      max (‖(fun i : Fin n => (A.map z).1 (Fin.natAdd n i)-z.1 (Fin.natAdd n i))‖)
        (‖(fun i : Fin n => (A.map z).2 (Fin.natAdd n i)-z.2 (Fin.natAdd n i))‖) ≤ 9*eps*C.MF

end KAM.Planetary

end
