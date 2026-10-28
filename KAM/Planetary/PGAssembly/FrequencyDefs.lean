/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Norm
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Planetary.Defs.FastFrequency
public import KAM.Planetary.PGAssembly.Jets
public import KAM.Planetary.PGAssembly.FastComplex

/-!
# P Part 5: the analytic constants (`bpP:p5:freq-data`), definitions

`PGAnalytic` (numeric carriers), the complex domains, `complexIntegrable`, `complexFrequency` and
the specification `PGAnalyticSpec` of the constants. The specification is produced from `PGData`
by `freq_data` (see `KAM.Planetary.PGAssembly.FrequencyBounds`); every clause is proved there.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FD.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- Numeric carriers selected before r and mu. The specification is produced below. -/
structure PGAnalytic where
  rho : ℝ
  c0 : ℝ
  M0 : ℝ
  AN : ℝ
  LN : ℝ
  LB : ℝ
  muStar : ℝ
  LP : ℝ
  CQ : ℝ
  r1 : ℝ
  Cdio : ℝ

def analyticDomain (d : PGData a b) (p : PGAnalytic) : Set (Fin (a+b) → ℂ) :=
  {J | blockFast J ∈ KAM.actionNbhd (closure d.V) p.rho ∧ ‖blockSlow J‖ < 1}

def analyticBoundDomain (d : PGData a b) (p : PGAnalytic) :
    Set (Fin (a+b) → ℂ) :=
  {J | blockFast J ∈ KAM.actionNbhd (closure d.V) p.rho ∧
    ‖blockSlow J‖ < 2}


def complexIntegrable (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) : ℂ :=
  (pgExtension d).H0 (blockFast J)+mu*jetPolynomial d mu J

def complexFrequency (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) (i : Fin (a+b)) : ℂ :=
  fderiv ℂ (complexIntegrable d mu) J (Pi.single i 1)

/-- All clauses are proved from d. None is an assumed inverse or assumed KAM family. -/
def PGAnalyticSpec (d : PGData a b) (p : PGAnalytic) : Prop :=
  0 < p.rho ∧ p.rho < (pgExtension d).delta/16 ∧ 0 < p.c0 ∧
  1 ≤ p.M0 ∧ 1 ≤ p.AN ∧ 1 ≤ p.LN ∧ 1 ≤ p.LB ∧ 0 < p.muStar ∧ p.muStar ≤ 1 ∧ p.muStar ≤ d.mu0 ∧
  1 ≤ p.LP ∧ (pgExtension d).MP * KAM.Weighted.coth ((pgExtension d).delta/4)^a ≤ p.LP ∧ 0 < p.CQ ∧ 0 < p.r1 ∧ p.r1 ≤ pgOscRadius d ∧ 0 < p.Cdio ∧
  p.muStar*p.AN ≤ p.c0/2 ∧ 4*p.muStar*p.AN^2*p.LB ≤ p.c0 ∧
  2*p.muStar*p.LN^2*p.LB < p.c0 ∧ p.LN ≤ p.AN ∧
  (∀ gamma : ℝ, 0 < gamma →
    volume {I ∈ d.V | ¬ KAM.IsDiophantine gamma ((a+b:ℕ)+1) (fastFrequency d.H0 I)} ≤
      ENNReal.ofReal (p.Cdio*gamma)) ∧
  (∀ z ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ z' ∈ KAM.actionNbhd (closure d.V) p.rho,
    p.c0*‖z-z'‖ ≤ ‖complexFast d z-complexFast d z'‖) ∧
  (∀ z ∈ KAM.actionNbhd (closure d.V) (2*p.rho), ‖fderiv ℂ (complexFast d) z‖ ≤ p.M0) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho,
    ∀ I' ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ xi : Fin b → ℂ, ‖xi‖ ≤ 1 →
      ‖(fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I (Pi.single i 1)) -
        (fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I' (Pi.single i 1))‖ ≤ p.LN*‖I-I'‖ ∧
      ‖(jetOmega d mu I+(jetBeta d mu I).mulVec xi) -
        (jetOmega d mu I'+(jetBeta d mu I').mulVec xi)‖ ≤ p.LN*‖I-I'‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho,
    ∀ xi xi' : Fin b → ℂ, ‖xi‖ ≤ 1 → ‖xi'‖ ≤ 1 →
      ‖(fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I (Pi.single i 1)) -
        (fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi')) I (Pi.single i 1))‖ ≤ p.LN*‖xi-xi'‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ J ∈ analyticBoundDomain d p,
    ‖jetPolynomial d mu J‖ ≤ p.AN ∧ ‖fderiv ℂ (jetPolynomial d mu) J‖ ≤ p.AN ∧
      ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J‖ ≤ p.AN) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ v : Fin b → ℂ,
    ‖v‖ ≤ p.LB*‖(jetBeta d mu I).mulVec v‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/4),
    ∀ x : PGComplexPhase b, ‖x‖ ≤ p.r1 → ‖pgRemainder d mu I x‖ ≤ p.CQ*‖x‖^5)


end KAM.Planetary

end
