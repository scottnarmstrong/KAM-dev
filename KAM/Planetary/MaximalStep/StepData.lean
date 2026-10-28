/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Homological
public import KAM.Planetary.MaximalStep.AffineFlow
public import KAM.Planetary.MaximalStep.Cutoff
public import KAM.Canonical.Symplectic
public import KAM.Frozen.Planetary.Defs.CircularTube

/-!
# Canonical-step data (P11A-C8)

The step parameters `P11Step`, the explicit output functions and the hypotheses `P11StepHyp` of
`bpP:p11a:canonical-step`, copied verbatim from the design signatures. No conclusion is a field.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Canonical-step source parameters; no conclusions are fields. -/
structure P11Step (n : ℕ) where
  E : Set (P11Vec n)
  t : ℝ
  r : ℝ
  s : ℝ
  T : ℝ
  d : ℝ
  delta : ℝ
  sigma : ℝ
  q : ℝ
  D : ℝ
  L : ℝ
  eps : ℝ
  n_pos : 1 ≤ n
  t_pos : 0 < t
  s_pos : 0 < s
  T_pos : 0 < T
  d_pos : 0 < d
  delta_pos : 0 < delta
  sigma_pos : 0 < sigma
  radius : 0 < r-d-delta-2*sigma
  q_pos : 0 < q
  q_le : q ≤ 1/2
  D_pos : 0 < D
  L_nonneg : 0 ≤ L
  eps_nonneg : 0 ≤ eps
  cutoff_error : p11Error n T d ≤ 1
  divisor_small : t*T*L ≤ D/2
  flow_small : 4*(n+1)*p11Lambda n delta*(1+p11Error n T d)*eps ≤ Real.pi*D*s*sigma
def p11StepA {n : ℕ} (S : P11Step n) : ℝ :=
  p11Lambda n S.delta*(1+p11Error n S.T S.d)*S.eps/(Real.pi*S.D*S.s)
def p11StepKappa {n : ℕ} (S : P11Step n) : ℝ := 2*(n+1)*p11StepA S/S.sigma
def p11StepRem {n : ℕ} (S : P11Step n) : ℝ :=
  S.eps*(S.q^2/(1-S.q)+2*p11Error n S.T S.d)+
    n*(4*n+5)*(5+4*p11Error n S.T S.d)*(1+p11Error n S.T S.d)*
      p11Lambda n S.delta*S.eps^2/(Real.pi*S.D*S.s*S.sigma)
def p11R0 {n : ℕ} (T : ℝ) (R : P11Family n → ℂ) (z : P11CVec n × P11CVec n) : ℂ :=
  p11Cutoff T R ((z.1,0),z.2)
def p11R1 {n : ℕ} (T : ℝ) (R : P11Family n → ℂ) (z : P11CVec n × P11CVec n) : P11CVec n :=
  fun i => fderiv ℂ (fun eta => p11Cutoff T R ((z.1,eta),z.2)) 0 (Pi.single i 1)
def p11DeltaH {n : ℕ} (T : ℝ) (R : P11Family n → ℂ) := p11AngleAverage (p11R0 T R)
def p11DeltaW {n : ℕ} (T : ℝ) (R : P11Family n → ℂ) (b : P11CVec n) : P11CVec n :=
  fun i => p11AngleAverage (fun z => p11R1 T R z i) b
def p11StepPhi {n : ℕ} (S : P11Step n) (w : P11CVec n → P11CVec n)
    (R : P11Family n → ℂ) (b : P11CVec n) : P11Phase n → ℂ :=
  p11Affine (fun theta => p11Solve S.T w (p11R0 S.T R) theta b)
    (fun theta i => p11Solve S.T w (fun z => p11R1 S.T R z i) theta b)
def p11StepMap {n : ℕ} (S : P11Step n) (w : P11CVec n → P11CVec n)
    (R : P11Family n → ℂ) (z : P11Family n) : P11Phase n :=
  p11Flow (p11StepPhi S w R z.2) (S.r-S.d-S.delta) S.s S.sigma 1 z.1
def p11Normal {n : ℕ} (h : P11CVec n → ℂ) (w : P11CVec n → P11CVec n)
    (z : P11Family n) : ℂ := h z.2+∑ i, w z.2 i*z.1.2 i
def p11StepRemainder {n : ℕ} (S : P11Step n) (h : P11CVec n → ℂ)
    (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ) (z : P11Family n) : ℂ :=
  (p11Normal h w+R) (p11StepMap S w R z,z.2)-
    p11Normal (h+p11DeltaH S.T R) (w+p11DeltaW S.T R) z
structure P11StepHyp {n : ℕ} (S : P11Step n) (h : P11CVec n → ℂ)
    (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ) : Prop where
  holh : DifferentiableOn ℂ h (KAM.actionNbhd S.E S.t)
  holw : DifferentiableOn ℂ w (KAM.actionNbhd S.E S.t)
  realh : ∀ b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t →
    (h (KAM.realInclusion n b)).im=0
  realw : ∀ b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t →
    ∀ i, (w (KAM.realInclusion n b) i).im=0
  admissible : p11Admissible S.r S.s (KAM.actionNbhd S.E S.t) R
  bound : p11Bound (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R S.eps
  derivative : ∀ b ∈ KAM.actionNbhd S.E S.t, ‖fderiv ℂ w b‖ ≤ S.L
  divisor : ∀ b ∈ S.E, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ S.T →
    S.D ≤ ‖p11dotC k (w (KAM.realInclusion n b))‖

end KAM.Planetary

end
