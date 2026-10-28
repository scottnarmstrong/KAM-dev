/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Frozen.Planetary.Defs.SecularAverage
public import KAM.Frozen.Planetary.Defs.Assemble
public import KAM.Frozen.Planetary.Defs.PlaneLength

/-!
# Secular form: carriers, data and domains

Blueprint P, Part 8 (`bpP:p8:conv#data`, `bpP:p8:rho`, `bpP:p8:quartic`): the standing physical
data `Data n`, the axes/action domains, the perturbation of the two matched Newtonian models,
the literal secular average (the frozen `secularAverage` at `(I,p,q) = (Λ,η,ξ)`), the torus average `avg`, the
radius `rho`, the polydisc and real inclusion, and the pair secular function `pairSlowSecular`.
All definitions; no theorem is stated here.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev CVec (n : ℕ) := Fin n → ℂ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Slow (n : ℕ) := Vec n × Vec n × Vec n
abbrev CSlow (n : ℕ) := CVec n × CVec n × CVec n
/-- Source standing physical data; no spectral or analytic conclusions. -/
structure Data (n : ℕ) where
  G : ℝ
  m0 : ℝ
  m : Vec n
  hG : 0 < G
  hm0 : 0 < m0
  hm : ∀ i, 0 < m i
  hn : 0 < n
variable {n : ℕ}
def axes (n : ℕ) : Set (Vec n) := {a | (∀ i, 0 < a i) ∧ StrictMono a}
def action (D : Data n) (a : Vec n) : Vec n := fun i => D.m i * √(D.G * D.m0 * a i)
def axis (D : Data n) (I : Vec n) : Vec n := fun i => I i ^ 2 / (D.m i ^ 2 * (D.G * D.m0))
def actionDomain (D : Data n) : Set (Vec n) := action D '' axes n
def nu (D : Data n) (I : Vec n) : Vec n := fun i => (D.G * D.m0) ^ 2 * D.m i ^ 3 / I i ^ 3
def perturbation (D : Data n) (moving : Bool) (w : Phase (n+n)) : ℝ :=
  if moving then fMov D.G D.m0 D.m (poincareProd D.m (D.G * D.m0) w)
  else fFix D.G D.m (poincareProd D.m (D.G * D.m0) w)
/-- Literally the frozen average: slow order is (xi,Lambda,eta). -/
def secular (D : Data n) (moving : Bool) (x : Slow n) : ℝ :=
  secularAverage (fun _ => perturbation D moving) 0 x.2.1 x.2.2 x.1
def slowSecular (D : Data n) (moving : Bool) (I : Vec n) (u : Vec n × Vec n) : ℝ :=
  secular D moving (u.1,I,u.2)
def slowDom (_D : Data n) : Set (Slow n) :=
  {x | assemble x.2.1 0 x.2.2 x.1 ∈ poincareProdDom n}
def cell (n : ℕ) : Set (Vec n) := Set.pi univ (fun _ => Icc 0 (2 * π))
def avg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec n → E) : E := (2 * π) ^ (-(n : ℤ)) • ∫ t in cell n, f t
def rho (D : Data n) (a : Vec n) : ℝ :=
  ⨅ i, min (action D a i / 2) (√(action D a i) / 16)
def polydisc (D : Data n) (a : Vec n) (r : ℝ) : Set (CSlow n) :=
  {x | ∀ i, ‖x.1 i‖ < r ∧ ‖x.2.1 i - (action D a i : ℂ)‖ < r ∧ ‖x.2.2 i‖ < r}
def inclusion (x : Slow n) : CSlow n :=
  (fun i => (x.1 i : ℂ), fun i => (x.2.1 i : ℂ), fun i => (x.2.2 i : ℂ))
def realDisc (D : Data n) (a : Vec n) (r : ℝ) : Set (Slow n) := inclusion ⁻¹' polydisc D a r

/-- Pair coefficient functions are functions of their two actions only. -/
def pairSlowSecular (D : Data n) (i j : Fin n) (I J : ℝ)
    (u : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  (2*π)⁻¹ * ∫ s in (0:ℝ)..2*π, (2*π)⁻¹ * ∫ t in (0:ℝ)..2*π,
    -D.G*D.m i*D.m j / planeLength
      ((poincare (D.m i) (D.G*D.m0) (![s,u.1 0], ![I,u.1 1])).1 -
       (poincare (D.m j) (D.G*D.m0) (![t,u.2 0], ![J,u.2 1])).1)
end SecularForm

end KAM.Planetary
