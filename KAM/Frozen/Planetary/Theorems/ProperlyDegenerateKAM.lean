/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Defs.Cylinder
public import KAM.Frozen.Planetary.Defs.CylinderCell
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm
public import KAM.Frozen.Planetary.Defs.HasFastDiffeomorphism
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Frozen.Planetary.Defs.IsCylinderKolmogorovSet
import KAM.Provider.Planetary.ProperlyDegenerateKAM

/-!
# Frozen theorem `KAM.Planetary.properlyDegenerateKAM`

Owner-approved on 2026-10-27 (decision D20). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.properlyDegenerateKAM` when the provider
`KAM.Provider.Planetary.ProperlyDegenerateKAM` is complete (sealing).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

/-- P-G v0.2: corrected specialization of CP11 Theorem 11.1 / CP10 Theorem 1.3.
Audit P1-P3: oscillator discs, a fast diffeomorphism near closure V, and a boundary collar.
These corrected hypotheses and joint analyticity await owner approval; see statement.md.
All geometric and analytic data precede the two small parameters. -/
theorem properlyDegenerateKAM {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (V : Set (Fin a → ℝ)) (hV : IsOpen V) (hVc : IsConnected V)
    (hVb : Bornology.IsBounded V)
    (W : Set (Fin a → ℝ)) (hW : IsOpen W) (hVW : closure V ⊆ W)
    (hboundary : ∃ A d : ℝ, 0 < A ∧ 0 < d ∧
      ∀ t : ℝ, 0 < t → t < d →
        volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < t} ≤
          ENNReal.ofReal (A * t))
    (r0 mu0 B : ℝ)
    (hr0 : 0 < r0) (hmu0 : 0 < mu0) (hB : 0 < B)
    (H0 : (Fin a → ℝ) → ℝ) (P : ℝ → Phase (a + b) → ℝ)
    (P0 : ℝ → (Fin a → ℝ) → ℝ)
    (Omega : ℝ → (Fin a → ℝ) → (Fin b → ℝ))
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (hP : AnalyticOnNhd ℝ (fun z : ℝ × Phase (a + b) => P z.1 z.2)
      (Set.Icc 0 mu0 ×ˢ closure (cylinder V r0)))
    (hperiod : ∀ mu ∈ Set.Icc 0 mu0, ∀ z ∈ cylinder V r0,
      ∀ k : Fin a → ℤ, P mu (z + fastShift k) = P mu z)
    (hfreq : HasFastDiffeomorphism H0 W)
    (hBNF : HasSecularBirkhoffForm P V r0 mu0 P0 Omega beta)
    (htorsion : ∀ mu ∈ Set.Icc 0 mu0, ∀ I ∈ V, B ≤ |(beta mu I).det|)
    (hsymm : ∀ mu ∈ Set.Icc 0 mu0, ∀ I ∈ V, (beta mu I).IsSymm) :
    ∃ rStar C c : ℝ, 0 < rStar ∧ rStar < r0 ∧ rStar < 1 ∧ 0 < C ∧ 0 < c ∧
      ∀ r mu : ℝ, 0 < r → r < rStar → 0 < mu → mu < mu0 →
        mu < r ^ 6 / (Real.log (1 / r)) ^ c →
        ∃ S : Set (Phase (a + b)),
          IsCylinderKolmogorovSet (degenerateHamiltonian H0 P mu) V r mu C S ∧
          0 < volume (S ∩ cylinderCell V r) ∧
          ENNReal.ofReal (1 - C * Real.sqrt r) * volume (cylinderCell (b := b) V r) <
            volume (S ∩ cylinderCell V r) ∧
          volume (S ∩ cylinderCell V r) < volume (cylinderCell (b := b) V r) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.properlyDegenerateKAM ha hb V hV hVc hVb W hW hVW hboundary r0 mu0
      B hr0 hmu0 hB H0 P P0 Omega beta hP hperiod hfreq hBNF htorsion hsymm
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary

end
-- FROZEN_ANCHOR_SUFFIX_END
