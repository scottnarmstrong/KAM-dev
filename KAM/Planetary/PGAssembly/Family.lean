/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FamilySigma
public import KAM.Planetary.PGAssembly.FamilyFreq

/-!
# P Part 5: the torus family (`bpP:p5:kset`, `bpP:p5:torus-conv`)

`torus_conv` assembles the family of whole tori from the single joint output of `two_scale_kam`
applied to the exact P3 record `pg_kam_hyp`, transports it through the chart `phi` with the
P1 `cyl_pipeline`, and retains the quantitative data (Lipschitz bound, lattice periodicity,
injectivity in the parameter, location, measure of the missed set) as `PGFamilySpec`.
`pgFamily` chooses the witness; `kset` and `rawUnion` are unions of whole ranges over a parameter
set. Declarations are copied verbatim from `P45Signatures.lean`; `frequency_bounds` lives in
`FamilyFreq` and the auxiliary lemmas in `FamilyAux` and `FamilySigma`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FAM.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- Parameter actions J0; raw output is in frozen angle/action order. -/
structure PGFamily (n : ℕ) where
  raw : (Fin n → ℝ) → (Fin n → ℝ) → Phase n

def physicalTorus (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (F : PGFamily (a+b)) (J : Fin (a+b) → ℝ) : (Fin (a+b) → ℝ) → Phase (a+b) :=
  phi d r mu h ∘ angleScale (2*Real.pi) ∘ F.raw J

def PGFamilySpec (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (F : PGFamily (a+b)) : Prop :=
  IsSigmaCompact (pgD0 d r mu) ∧
  (∃ L : ℝ, 0 < L ∧ ∀ z ∈ pgD0 d r mu ×ˢ unitCube (a+b),
    ∀ z' ∈ pgD0 d r mu ×ˢ unitCube (a+b),
      ‖F.raw z.1 z.2-F.raw z'.1 z'.2‖ ≤ L*‖z-z'‖) ∧
  (∀ J ∈ pgD0 d r mu, ∀ theta, ∀ k : Fin (a+b) → ℤ,
    F.raw J (theta+fun i => (k i:ℝ)) = F.raw J theta+((fun i => (k i:ℝ)),0)) ∧
  (∀ J ∈ pgD0 d r mu, ∀ J' ∈ pgD0 d r mu, ∀ theta theta',
    physicalTorus d r mu h F J theta = physicalTorus d r mu h F J' theta' → J=J') ∧
  (∀ J ∈ pgD0 d r mu, ∀ theta,
    (F.raw J theta).2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK) ∧
  (volume (({z : Phase (a+b) | z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK ∧
      z.1 ∈ unitCube (a+b)}) \ (⋃ J ∈ pgD0 d r mu, range (F.raw J))) ≤
    ENNReal.ofReal (1+(1+2^(a+b))*(1+(4/3:ℝ)^(a+b))) *
      (volume (pgActionDomain d r mu \ pgD0 d r mu) +
        volume (realNbhd (pgActionDomain d r mu) (params d r mu).rK \ pgActionDomain d r mu))) ∧
  (∀ J ∈ pgD0 d r mu,
    IsCylinderTorus (degenerateHamiltonian d.H0 d.P mu) (cylinder d.V r)
      ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) (physicalTorus d r mu h F J))

/-- Assembly from the single joint two_scale_kam output, via P1 cyl_pipeline. -/
theorem torus_conv (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    ∃ F : PGFamily (a+b), PGFamilySpec d r mu h F := by
  sorry

def pgFamily (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) : PGFamily (a+b) :=
  (torus_conv d r mu h).choose

def kset (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) : Set (Phase (a+b)) :=
  ⋃ J ∈ B, range (physicalTorus d r mu h (pgFamily d r mu h) J)

def rawUnion (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) : Set (Phase (a+b)) :=
  ⋃ J ∈ B, range ((pgFamily d r mu h).raw J)

end KAM.Planetary

end
