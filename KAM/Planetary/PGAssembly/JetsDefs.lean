/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Extension

/-!
# P Part 5: the Birkhoff jets of the complex average (`bpP:p5:birkhoff-ext`, definitions)

`jetP0`, `jetOmega`, `jetBeta` are derivatives of `complexAverage` at `0` (constructed from the
average, not from arbitrary boundary values), `jetPolynomial` is the degree-four polynomial they
define and `pgRemainder` the average minus that polynomial. Declarations as in the design
signature file. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

/-- Jets are constructed from the average, not from arbitrary total boundary values. -/
def jetP0 (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) : ℂ := complexAverage d mu I 0

def jetOmega (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) (j : Fin b) : ℂ :=
  iteratedFDeriv ℂ 2 (complexAverage d mu I) 0 (fun _ => (0,Pi.single j 1))

def jetBeta (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) : Matrix (Fin b) (Fin b) ℂ :=
  fun i j => if i=j then (1/3:ℂ)*iteratedFDeriv ℂ 4 (complexAverage d mu I) 0 (fun _ => (0,Pi.single i 1))
  else iteratedFDeriv ℂ 4 (complexAverage d mu I) 0
    (fun k : Fin 4 => if k.val < 2 then (0,Pi.single i 1) else (0,Pi.single j 1))

def jetPolynomial (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) : ℂ :=
  jetP0 d mu (blockFast J) + ∑ j, jetOmega d mu (blockFast J) j * blockSlow J j +
    (1/2:ℂ)*∑ i, ∑ j, jetBeta d mu (blockFast J) i j*blockSlow J i*blockSlow J j

def pgRemainder (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) (x : PGComplexPhase b) : ℂ :=
  complexAverage d mu I x - jetPolynomial d mu
    (Fin.append I (fun j => (x.1 j^2+x.2 j^2)/2))

end KAM.Planetary

end
