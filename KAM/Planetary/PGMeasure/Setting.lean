/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PG.Setting
public import KAM.Frozen.Planetary.Defs.HasFastDiffeomorphism
public import KAM.Frozen.Planetary.Defs.FastFrequency

/-!
# P Parts 4-5: the measure setting (`bpP:p4:freq`, `bpP:p4:data`)

The actual frequency map `freq`, its secular ingredients `secularPolynomial` and
`slowFrequency`, the literal S4 standing hypotheses `MeasureData`, and the resonance union
helper `resonanceBad`. `joinedActions` (`bpP:p4:conv#shell`) is owned by `KAM.Planetary.PG.Setting`
and is reused, not redeclared. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-S.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {a b n : ℕ}

/-- Polynomial uses the frozen coefficients themselves on V. -/
def secularPolynomial (P0 : ℝ → (Fin a → ℝ) → ℝ)
    (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (mu : ℝ) (I : Fin a → ℝ) (xi : Fin b → ℝ) : ℝ :=
  P0 mu I + ∑ j, Omega mu I j * xi j + (1/2:ℝ)*∑ i, ∑ j, beta mu I i j*xi i*xi j

def slowFrequency (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (mu : ℝ) (I : Fin a → ℝ) (xi : Fin b → ℝ) : Fin b → ℝ :=
  Omega mu I + (beta mu I).mulVec xi

def freq (H0 : (Fin a → ℝ) → ℝ) (P0 : ℝ → (Fin a → ℝ) → ℝ)
    (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (mu : ℝ) (J : Fin (a+b) → ℝ) : Fin (a+b) → ℝ :=
  Fin.append (fastFrequency H0 (blockFast J) + mu •
    fun i => fderiv ℝ (fun I => secularPolynomial P0 Omega beta mu I (blockSlow J)) (blockFast J)
      (Pi.single i 1))
    (mu • slowFrequency Omega beta mu (blockFast J) (blockSlow J))

/-- S4 source premises. The two-scale set is owned by P1 and is not redeclared here. -/
structure MeasureData (a b : ℕ) where
  H0 : (Fin a → ℝ) → ℝ
  W : Set (Fin a → ℝ)
  V : Set (Fin a → ℝ)
  core : Set (Fin a → ℝ)
  hW : IsOpen W
  hVb : Bornology.IsBounded V
  hVW : closure V ⊆ W
  hfreq : HasFastDiffeomorphism H0 W
  hcore : IsCompact core
  hcoreV : core ⊆ V
  hvol : 0 < volume core
  P0 : ℝ → (Fin a → ℝ) → ℝ
  Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ
  beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ
  tau : ℝ
  lambda0 : ℝ
  mu1 : ℝ
  LN : ℝ
  LB : ℝ
  Lg : ℝ
  Ry : ℝ
  hRy : 0 < Ry
  hRybound : ∀ y ∈ fastFrequency H0 '' closure V, ‖y‖ ≤ Ry
  ha : 0 < a
  hb : 0 < b
  htau : (a+b:ℕ) < tau
  hlambda0 : 0 < lambda0
  hmu1 : 0 < mu1
  hLN : 1 ≤ LN
  hLB : 1 ≤ LB
  hLg : 1 ≤ Lg
  g : (Fin a → ℝ) → Fin a → ℝ
  hinv : ∀ I ∈ W, g (fastFrequency H0 I) = I
  hglip : ∀ y ∈ fastFrequency H0 '' closure V, ∀ y' ∈ fastFrequency H0 '' closure V,
    ‖g y-g y'‖ ≤ Lg*‖y-y'‖
  small : mu1 ≤ (2*(1+2*b*LN*LB)*a*LN*Lg)⁻¹
  N1 : ∀ mu ∈ Ioc 0 mu1, ∀ I ∈ core, ∀ I' ∈ core, ∀ xi : Fin b → ℝ, ‖xi‖ ≤ lambda0 →
    ‖blockFast (freq H0 P0 Omega beta mu (Fin.append I xi)) - fastFrequency H0 I -
      (blockFast (freq H0 P0 Omega beta mu (Fin.append I' xi)) - fastFrequency H0 I')‖
      ≤ mu*LN*‖I-I'‖ ∧
    ‖slowFrequency Omega beta mu I xi - slowFrequency Omega beta mu I' xi‖ ≤ LN*‖I-I'‖
  N2 : ∀ mu ∈ Ioc 0 mu1, ∀ I ∈ core, ∀ xi xi' : Fin b → ℝ,
    ‖xi‖ ≤ lambda0 → ‖xi'‖ ≤ lambda0 →
    ‖blockFast (freq H0 P0 Omega beta mu (Fin.append I xi)) -
      blockFast (freq H0 P0 Omega beta mu (Fin.append I xi'))‖ ≤ mu*LN*‖xi-xi'‖
  N3 : ∀ mu ∈ Ioc 0 mu1, ∀ I ∈ core, ∀ v : Fin b → ℝ, ‖v‖ ≤ LB*‖(beta mu I).transpose.mulVec v‖


/-- Resonance union helper; `resonanceBad_eq` identifies it with the exact P1 predicate. -/
def resonanceBad (F : (Fin (a+b) → ℝ) → Fin (a+b) → ℝ)
    (D : Set (Fin (a+b) → ℝ)) (alpha1 alpha2 tau : ℝ) : Set (Fin (a+b) → ℝ) :=
  {J ∈ D | ∃ k : Fin (a+b) → ℤ, k ≠ 0 ∧
    |∑ i, (k i : ℝ)*F J i| <
      (if (blockFast k : Fin a → ℤ) = 0 then alpha2 else alpha1)/(∑ i, |(k i : ℝ)|)^tau}

end KAM.Planetary

end
