/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm
public import KAM.Frozen.Planetary.Defs.HasFastDiffeomorphism
public import KAM.Frozen.Planetary.Defs.Cylinder
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.Slow

/-!
# P Parts 4-5: the P-G setting (`bpP:p4:conv#data`, `bpP:p4:conv#shell`)

Scalar-generic block extensions `blockFast`, `blockSlow` (identified with the frozen `fast`,
`slow` on real vectors), the source-data structure `PGData` (the frozen P-G binders and
nothing else), the boundary-constant extractors, and the plain coordinate carriers
`realNbhd`, `innerCore`, `actionShell`, `joinedActions`, `unitCube`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P45-S. This module contains only
source and coordinate data, no chosen witnesses that depend on downstream existence lemmas.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {a b n : ℕ}

/-- Scalar-generic extension; real specializations are identified with the frozen projections. -/
def blockFast {a b : ℕ} {F : Type*} (v : Fin (a+b) → F) : Fin a → F := fun i => v (Fin.castAdd b i)

def blockSlow {a b : ℕ} {F : Type*} (v : Fin (a+b) → F) : Fin b → F := fun i => v (Fin.natAdd a i)

theorem blockFast_real (v : Fin (a+b) → ℝ) : blockFast v = fast v := rfl

theorem blockSlow_real (v : Fin (a+b) → ℝ) : blockSlow v = slow v := rfl

/-- Source data only: the frozen P-G binders, without extra hypotheses. -/
structure PGData (a b : ℕ) where
  ha : 0 < a
  hb : 0 < b
  V : Set (Fin a → ℝ)
  hV : IsOpen V
  hVc : IsConnected V
  hVb : Bornology.IsBounded V
  W : Set (Fin a → ℝ)
  hW : IsOpen W
  hVW : closure V ⊆ W
  hboundary : ∃ A d : ℝ, 0 < A ∧ 0 < d ∧ ∀ t : ℝ, 0 < t → t < d →
    volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < t} ≤ ENNReal.ofReal (A * t)
  r0 : ℝ
  mu0 : ℝ
  B : ℝ
  hr0 : 0 < r0
  hmu0 : 0 < mu0
  hB : 0 < B
  H0 : (Fin a → ℝ) → ℝ
  P : ℝ → Phase (a + b) → ℝ
  P0 : ℝ → (Fin a → ℝ) → ℝ
  Omega : ℝ → (Fin a → ℝ) → (Fin b → ℝ)
  beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ
  hP : AnalyticOnNhd ℝ (fun z : ℝ × Phase (a + b) => P z.1 z.2)
    (Icc 0 mu0 ×ˢ closure (cylinder V r0))
  hperiod : ∀ mu ∈ Icc 0 mu0, ∀ z ∈ cylinder V r0, ∀ k : Fin a → ℤ,
    P mu (z + fastShift k) = P mu z
  hfreq : HasFastDiffeomorphism H0 W
  hBNF : HasSecularBirkhoffForm P V r0 mu0 P0 Omega beta
  htorsion : ∀ mu ∈ Icc 0 mu0, ∀ I ∈ V, B ≤ |(beta mu I).det|
  hsymm : ∀ mu ∈ Icc 0 mu0, ∀ I ∈ V, (beta mu I).IsSymm

def pgBoundaryA (d : PGData a b) : ℝ := d.hboundary.choose

def pgBoundaryD (d : PGData a b) : ℝ := d.hboundary.choose_spec.choose

/-- Real neighbourhood, expressed by witnesses to avoid empty-set infDist totality. -/
def realNbhd (X : Set (Fin n → ℝ)) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ y ∈ X, dist x y < s}

def innerCore (V : Set (Fin a → ℝ)) (t : ℝ) : Set (Fin a → ℝ) :=
  {I ∈ V | ∀ J ∈ frontier V, t ≤ dist I J}

def actionShell (b : ℕ) (l u : ℝ) : Set (Fin b → ℝ) := pi univ fun _ => Ioo l u

def joinedActions (X : Set (Fin a → ℝ)) (Y : Set (Fin b → ℝ)) : Set (Fin (a+b) → ℝ) :=
  {J | blockFast J ∈ X ∧ blockSlow J ∈ Y}

def unitCube (n : ℕ) : Set (Fin n → ℝ) := pi univ fun _ => Ico (0 : ℝ) 1

end KAM.Planetary

end
