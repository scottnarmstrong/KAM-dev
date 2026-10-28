/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Threshold
public import KAM.Planetary.PGMeasure.OneScale

/-!
# P Part 5: the explicit budget constants (`bpP:p5:budget#constant`)

`kamMeasureConstant` is the constant `c_n` of `bpP:p3:two-scale-kam`, `pgMeasureUpper1/2` the
data-only upper bounds of the two P4 measure constants, and `pgBudget` the explicit data-only sum
`C_b` of `bpP:p5:budget`, chosen before `r` and `mu`. Declarations are copied verbatim from
`P45Signatures.lean`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-BU.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

def kamMeasureConstant (n : ℕ) : ℝ := 1+(1+2^n)*(1+(4/3:ℝ)^n)

def pgMeasureUpper1 (d : PGData a b) : ℝ :=
  let p := pgAnalytic d
  let t := pgTau a b
  (pgInverseL d)^(a+b)/((volume d.V).toReal/2) *
    max (4*(2*pgInverseR d)^(a-1)*latticeS (a+b) t)
      (4*b^2*p.LB*(2*pgInverseR d)^a *
        (2*3^(a+b-1)/(t+1-(a+b:ℕ))) *
        (4*p.LN*pgInverseL d)^(t+1-(a+b:ℕ)))

def pgMeasureUpper2 (d : PGData a b) : ℝ :=
  b*(pgAnalytic d).LB*latticeS b (pgTau a b+1)

def pgBudget (d : PGData a b) : ℝ :=
  4^(b+1)*2*Real.pi*(pgScales d).k0 *
    (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d) +
    8*(pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/
      (volume d.V).toReal + b*(pgScales d).k1/16

end KAM.Planetary

end
