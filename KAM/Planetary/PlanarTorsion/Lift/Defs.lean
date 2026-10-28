/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.Assemble
public import KAM.Planetary.Hamiltonian.Chart
public import KAM.Planetary.PlanarTorsion.QuarticFlow
public import KAM.Planetary.PlanarTorsion.RealFlow.Variational

/-!
# Planar quartic torsion: the lifted slow flow, definitions and coordinates (package T11)

Blueprint P, Part 11b (`bpP:p11b:lift-map`).  The signed definitions `p11c_liftFlow` and
`p11c_tube` (verbatim from the signature file) and the coordinate API of the assembled
`(φ, q; I, p)` phase space `Phase (2 + 2)`: the action, angle and slow components of a point, the
Hamiltonian `p11cL_ham chi w = chi (I w) (z w)` of the full lift, and its Hamiltonian field in
terms of the partial derivatives of `chi`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

/-- Slow flow lifted in the frozen (phi,q;I,p) coordinate order. -/
def p11c_liftFlow (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (w : Phase (2 + 2)) : Phase (2 + 2) :=
  let I : Fin 2 → ℝ := fun i => w.2 (Fin.castAdd 2 i)
  let lam : Fin 2 → ℝ := fun i => w.1 (Fin.castAdd 2 i)
  let z : Phase 2 := (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i))
  let Y := p11c_flow chi I 1 z
  let g : Fin 2 → ℝ := fun i => ∫ t in (0 : ℝ)..1,
    fderiv ℝ (fun J => chi J (p11c_flow chi I t z)) I (Pi.single i 1)
  assemble I (lam + g) Y.2 Y.1

def p11c_tube (O : Set (Fin 2 → ℝ)) (r : ℝ) : Set (Phase (2 + 2)) :=
  {w | (fun i => w.2 (Fin.castAdd 2 i)) ∈ O ∧
    p11c_slowLength (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i)) < r}

/-- The action component of a point of `Phase (2 + 2)`. -/
def p11cL_act (w : Phase (2 + 2)) : Fin 2 → ℝ := fun i => w.2 (Fin.castAdd 2 i)

/-- The angle component of a point of `Phase (2 + 2)`. -/
def p11cL_ang (w : Phase (2 + 2)) : Fin 2 → ℝ := fun i => w.1 (Fin.castAdd 2 i)

/-- The slow component of a point of `Phase (2 + 2)`. -/
def p11cL_slow (w : Phase (2 + 2)) : Phase 2 :=
  (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i))

/-- The Hamiltonian of the full lift: only the actions and the slow variables enter. -/
def p11cL_ham {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) (w : Phase (2 + 2)) : ℝ :=
  chi.eval (p11cL_act w) (p11cL_slow w)

/-- The open set where the lifted Hamiltonian is analytic. -/
def p11cL_dom (O : Set (Fin 2 → ℝ)) : Set (Phase (2 + 2)) := {w | p11cL_act w ∈ O}

/-- The partial derivative of `chi` in the action direction `i`, at fixed slow variable. -/
def p11cL_dI {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) (u : (Fin 2 → ℝ) × Phase 2)
    (i : Fin 2) : ℝ :=
  fderiv ℝ (fun v : (Fin 2 → ℝ) × Phase 2 => chi.eval v.1 v.2) u (Pi.single i 1, 0)

theorem p11cL_act_assemble (I lam : Fin 2 → ℝ) (z : Phase 2) :
    p11cL_act (assemble I lam z.2 z.1) = I := by
  funext i; simp [p11cL_act, assemble]

theorem p11cL_ang_assemble (I lam : Fin 2 → ℝ) (z : Phase 2) :
    p11cL_ang (assemble I lam z.2 z.1) = lam := by
  funext i; simp [p11cL_ang, assemble]

theorem p11cL_slow_assemble (I lam : Fin 2 → ℝ) (z : Phase 2) :
    p11cL_slow (assemble I lam z.2 z.1) = z := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [p11cL_slow, assemble]

theorem p11cL_assemble_eq (w : Phase (2 + 2)) :
    assemble (p11cL_act w) (p11cL_ang w) (p11cL_slow w).2 (p11cL_slow w).1 = w := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> refine Fin.addCases ?_ ?_ j <;>
    intro i <;> simp [assemble, p11cL_act, p11cL_ang, p11cL_slow]

theorem p11cL_tube_iff (O : Set (Fin 2 → ℝ)) (r : ℝ) (w : Phase (2 + 2)) :
    w ∈ p11c_tube O r ↔ p11cL_act w ∈ O ∧ p11c_slowLength (p11cL_slow w) < r := Iff.rfl

theorem p11cL_liftFlow_eq (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (w : Phase (2 + 2)) :
    p11c_liftFlow chi w =
      assemble (p11cL_act w)
        (p11cL_ang w + fun i => ∫ t in (0 : ℝ)..1,
          fderiv ℝ (fun J => chi J (p11c_flow chi (p11cL_act w) t (p11cL_slow w)))
            (p11cL_act w) (Pi.single i 1))
        (p11c_flow chi (p11cL_act w) 1 (p11cL_slow w)).2
        (p11c_flow chi (p11cL_act w) 1 (p11cL_slow w)).1 := rfl

end KAM.Planetary

end
