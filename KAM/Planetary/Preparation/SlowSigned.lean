/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAssembly
public import KAM.Planetary.Preparation.SlowData
public import KAM.Planetary.Preparation.FastSigned

/-!
# Signed `P11SlowSpec`, `avg_slow`, `p11SlowConstant`, `p11SlowData` (P11A-P7d)

Verbatim signed statements (long lines re-wrapped); `avg_slow` is a wrapper over the core
`avg_slow_of_spec` at `p11SecularData D` (from `holo_chart`) and `p11FastData D` (from the
signed `avg_fast`), `P11SlowSpec` unfolding to `P11SlowSpecOf` by `rfl`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

def P11SlowSpec {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) (A : P11SlowData n) : Prop :=
  let C := p11SecularData D
  let Fast := p11FastData D eps
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

theorem avg_slow {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ eps2 c2 : ℝ, 0 < eps2 ∧ eps2 < 1 ∧ 1 ≤ c2 ∧
      ∀ eps, 0 < eps → eps ≤ eps2 → ∃ A, P11SlowSpec D nu eps c2 A := by
  obtain ⟨eps1, h0, h1, hfast⟩ := avg_fast D
  have hF : ∀ eps, 0 < eps → eps ≤ eps1 → P11FastSpec (p11SecularData D) eps (p11FastData D eps) :=
    fun eps he hle => by
      have h := (hfast eps he hle).2
      unfold p11FastData
      rw [dif_pos h]
      exact h.choose_spec
  exact avg_slow_of_spec (holo_chart D).choose_spec.1 hnu h0 (fun eps => p11FastData D eps) hF
open Classical in
def p11SlowConstant {n : ℕ} (D : P11Physical n) (nu : ℝ) : ℝ :=
  if h : 1 ≤ nu then ((avg_slow D h).choose_spec).choose else 1
open Classical in
def p11SlowData {n : ℕ} (D : P11Physical n) (nu eps : ℝ) : P11SlowData n :=
  if h : ∃ A, P11SlowSpec D nu eps (p11SlowConstant D nu) A then h.choose else default

end KAM.Planetary

end
