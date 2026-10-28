/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Threshold
public import KAM.Planetary.PGAssembly.JetsDefs
public import KAM.Planetary.PGAssembly.FrequencyDefs
public import KAM.Planetary.Averaging.OscillatorFinite
public import KAM.Planetary.Hamiltonian.Chart

/-!
# P Part 5: averaging, definitions (`bpP:p5:avg`)

The produced averaging record `PGAveraging`, its specification `AveragingSpec`, the conformally
symplectic oscillator normalization `pgOscNormalize` and the data supplied to the P2 theorem
`averaged_remainder` (`pgOscP`, `pgOscH`, `pgOscE`, `pgOscEpsilon`, `pgOscWidth`, `pgOscAlpha`).
Declarations are copied verbatim from `P45Signatures.lean`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ}

structure PGAveraging (n : ℕ) where
  Psi : PGComplexPhase n → PGComplexPhase n
  remainder : PGComplexPhase n → ℂ

def averagingDomain (d : PGData a b) (r mu : ℝ) : Set (PGComplexPhase (a+b)) :=
  {z | blockFast z.2 ∈ KAM.actionNbhd (checkedCore d r mu) ((params d r mu).rhoBar/2) ∧
    blockFast z.1 ∈ KAM.complexStrip a (pgWidth d/6) ∧ ‖(blockSlow z.2,blockSlow z.1)‖ < pgOscRadius d/2}

def realAverageMap (A : PGAveraging n) (z : Phase n) : Phase n :=
  ((fun i => (A.Psi (KAM.realInclusion₂ n z)).1 i |>.re),
    (fun i => (A.Psi (KAM.realInclusion₂ n z)).2 i |>.re))

def AveragingSpec (d : PGData a b) (r mu : ℝ) (A : PGAveraging (a+b)) : Prop :=
  DifferentiableOn ℂ A.Psi (averagingDomain d r mu) ∧
  InjOn A.Psi (averagingDomain d r mu) ∧
  MapsTo A.Psi (averagingDomain d r mu) (extensionDomain d (pgExtension d).delta) ∧
  (∀ z ∈ averagingDomain d r mu,
    (pgExtension d).H0 (blockFast (A.Psi z).2)+mu*(pgExtension d).P mu (A.Psi z) =
      complexIntegrable d mu (Fin.append (blockFast z.2)
        (fun j => ((blockSlow z.1 j)^2+(blockSlow z.2 j)^2)/2)) +
      mu*pgRemainder d mu (blockFast z.2) (blockSlow z.1,blockSlow z.2)+A.remainder z) ∧
  DifferentiableOn ℂ A.remainder (averagingDomain d r mu) ∧
  (∀ z ∈ averagingDomain d r mu, ‖A.remainder z‖ ≤ 2*(pgAnalytic d).LP*mu*r^5) ∧
  (∀ I ∈ KAM.actionNbhd (checkedCore d r mu) ((params d r mu).rhoBar/2),
    ∀ x : PGComplexPhase b, ‖x‖ < pgOscRadius d/2 →
      KAM.Fourier.SummableWeighted (pgWidth d/6)
        (KAM.torusCoeff (fun theta => A.remainder
          (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a theta) x.2 x.1))) ∧
      KAM.Fourier.weightedNorm (pgWidth d/6)
        (KAM.torusCoeff (fun theta => A.remainder
          (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a theta) x.2 x.1))) ≤
        2*(pgAnalytic d).LP*mu*r^5) ∧
  (∀ z ∈ averagingDomain d r mu, ∀ k : Fin a → ℤ,
    A.Psi (z+KAM.realInclusion₂ (a+b) (fastShift k)) =
      A.Psi z+KAM.realInclusion₂ (a+b) (fastShift k)) ∧
  (∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ averagingDomain d r mu →
    A.Psi (KAM.realInclusion₂ (a+b) z) = KAM.realInclusion₂ (a+b) (realAverageMap A z)) ∧
  IsChart 1 (realAverageMap A) ((KAM.realInclusion₂ (a+b)) ⁻¹' averagingDomain d r mu) ∧
  (∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ averagingDomain d r mu →
    ‖blockFast (realAverageMap A z).2-blockFast z.2‖ ≤
      12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/(pgWidth d*(params d r mu).gammaBar) ∧
    ‖(blockSlow (realAverageMap A z).2-blockSlow z.2,blockSlow (realAverageMap A z).1-blockSlow z.1)‖ ≤
      18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/(pgOscRadius d*(params d r mu).gammaBar))

/-- Mixed fast-angle/oscillator normalization, conformally symplectic with factor 2*pi. -/
def pgOscNormalize (z : CPhase (a+b)) : CPhase (a+b) :=
  (Fin.append ((2*Real.pi:ℂ) • blockFast z.1)
    ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1),
   Fin.append (blockFast z.2) ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2))
def pgOscUnnormalize (z : CPhase (a+b)) : CPhase (a+b) :=
  (Fin.append ((2*Real.pi:ℂ)⁻¹ • blockFast z.1)
    ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • blockSlow z.1),
   Fin.append (blockFast z.2) ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • blockSlow z.2))
def pgOscP (d : PGData a b) (mu : ℝ) (z : CPhase (a+b)) : ℂ :=
  (pgExtension d).P mu (pgOscNormalize z)/(pgAnalytic d).LP
def pgOscH (d : PGData a b) (I : Fin a → ℂ) : ℂ := (pgExtension d).H0 I/(2*Real.pi)
def pgOscE (d : PGData a b) (mu : ℝ) : ℝ := (pgAnalytic d).LP*mu/(2*Real.pi)
def pgOscEpsilon (d : PGData a b) : ℝ := pgOscRadius d/Real.sqrt (2*Real.pi)
def pgOscWidth (d : PGData a b) : ℝ := pgWidth d/(2*Real.pi)
/-- Cutoff divisor after neighbourhood loss and conformal Hamiltonian scaling. -/
def pgOscAlpha (d : PGData a b) (r mu : ℝ) : ℝ :=
  (params d r mu).gammaBar / (4*Real.pi*(params d r mu).Kbar^(pgTau a b))

end KAM.Planetary

end
