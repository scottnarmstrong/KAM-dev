/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Averaging
public import KAM.Planetary.PGMeasure.Polar

/-!
# P Part 5: the chart `phi`, definitions (`bpP:p5:phi`)

`phi` composes the real averaging map with the oscillator polar chart, `phiDomain` is its
domain and `oscillatorPolarComplex` the complexification of the polar chart. Declarations are
copied verbatim from `P45Signatures.lean`; the membership and periodicity lemmas used by
`phi_chart` and `location` follow.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CH.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

def phi (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) : Phase (a+b) → Phase (a+b) :=
  realAverageMap (pgAvg d r mu h) ∘ oscillatorPolar

def phiDomain (d : PGData a b) (r mu : ℝ) : Set (Phase (a+b)) :=
  {z | KAM.realInclusion a (blockFast z.2) ∈ KAM.actionNbhd (checkedCore d r mu) ((params d r mu).rhoBar/2) ∧
    blockSlow z.2 ∈ actionShell b ((params d r mu).l1/2) (2*(params d r mu).l2)}

def oscillatorPolarComplex (z : PGComplexPhase (a+b)) : PGComplexPhase (a+b) :=
  assembleComplex (blockFast z.2) (blockFast z.1)
    (fun j => (2*blockSlow z.2 j)^(1/2:ℂ)*Complex.cos (blockSlow z.1 j))
    (fun j => (2*blockSlow z.2 j)^(1/2:ℂ)*Complex.sin (blockSlow z.1 j))

theorem oscillatorPolarComplex_real (z : Phase (a+b))
    (hz : ∀ j : Fin b, 0 < blockSlow z.2 j) :
    oscillatorPolarComplex (KAM.realInclusion₂ (a+b) z) =
      KAM.realInclusion₂ (a+b) (oscillatorPolar z) := by
  have hs : ∀ j : Fin b, ((2*blockSlow z.2 j : ℝ) : ℂ)^(1/2:ℂ) =
      ((Real.sqrt (2*blockSlow z.2 j) : ℝ) : ℂ) := fun j => by
    have h0 : 0 ≤ 2*blockSlow z.2 j := by have := hz j; positivity
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h0]
    norm_num
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [oscillatorPolarComplex, assembleComplex, blockFast, oscillatorPolar, assemble,
        Fin.append_left]
    · have := hs j
      simp only [oscillatorPolarComplex, assembleComplex, blockSlow, Fin.append_right,
        KAM.realInclusion₂_apply, KAM.realInclusion_apply, oscillatorPolar_fst_natAdd] at this ⊢
      push_cast at this ⊢
      rw [this]
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [oscillatorPolarComplex, assembleComplex, blockFast, oscillatorPolar, assemble,
        Fin.append_left]
    · have := hs j
      simp only [oscillatorPolarComplex, assembleComplex, blockSlow, Fin.append_right,
        KAM.realInclusion₂_apply, KAM.realInclusion_apply, oscillatorPolar_snd_natAdd] at this ⊢
      push_cast at this ⊢
      rw [this]

end KAM.Planetary

end
