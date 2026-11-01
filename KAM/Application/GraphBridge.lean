/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.AngleGraph
public import KAM.Application.ClockGraph
public import KAM.Application.RealTorus
public import KAM.Application.Confinement.TwoTorus

/-!
# From the graph adapters to the confinement's `GraphTorus`

The confinement between two invariant tori (`KAM.Application.Confinement.twoTorus_confinement`)
takes its tori as `Confinement.GraphTorus V H E lo hi`: an embedding `k : ℝ² → ℝ² × ℝ²` with a
continuous two-sided inverse `Θ` of its angle map, whose lines `s ↦ k(θ + s ν)` solve `ż = V z`,
on the level `H = E`, with actions in `[lo, hi]`. Both graph adapters produce that data:

* `IsAnalyticAngleGraph.toGraphTorus`: an analytic angle graph (two degrees of freedom) with a
  linear flow of `V`, on the level, with actions in the box, is a `GraphTorus` with
  `Θ = A⁻¹ = invFun (torusAngle k)` (continuous: `IsAnalyticAngleGraph.continuous_angleInv`);
  `IsAnalyticAngleGraph.toGraphTorusOfModel`: the same for a real model torus
  (`IsRealModelTorus H ω E k`, `V = X_H`, `ν = ω`);
* the near-identity adapter: `IsAngleGraph.toGraphTorus`, `IsAngleGraph.toGraphTorusOfModel`
  (through `IsAngleGraph.isAnalyticAngleGraph`; for a model torus analyticity comes from
  `IsRealModelTorus.analytic`);
* the clock-triangular adapter: `IsClockAngleGraph.toGraphTorusOfModel` (through the parent
  `IsClockAngleGraph.toIsAnalyticAngleGraph`).

So a certified torus reaches the confinement in three steps: the graph
(`CertifiedTorus.exists_realGraph_of_checks` or `CertifiedTorus.exists_clockGraph_of_checks`, which
also give the real model torus), the action box (`CertifiedTorusAt.abs_action_sub_ctr_le_real`
with `checkActionRangeReal`), and this bridge; `Tests/GraphBridge.lean` runs it on the certified
toy T2 and feeds `twoTorus_confinement` with one torus from each adapter.

**Scope of the clock adapter.** Its certified hypotheses (every angle `l ≠ i` a clock of the same
slope `a`, `ω*` Diophantine) are satisfiable only for `n = 2`: for `n ≥ 3` two clocks `l ≠ l'`
give `s∞ ω*_l = s∞ ω*_{l'} = a`, so `s∞ ω*` is resonant at `e_l - e_{l'}` and the Diophantine
hypothesis fails. The confinement is two-dimensional, which is exactly the case of interest.
-/

@[expose] public noncomputable section

open Set Function

namespace KAM.Application

open Confinement

section Analytic

variable {k : (Fin 2 → ℝ) → Phase} (hG : IsAnalyticAngleGraph k) {V : Phase → Phase}
  {H : Phase → ℝ} {E : ℝ} {lo hi : Fin 2 → ℝ} (ν : Fin 2 → ℝ)
  (hflow : ∀ θ t, HasDerivAt (fun s : ℝ => k (θ + s • ν)) (V (k (θ + t • ν))) t)
  (henergy : ∀ θ, H (k θ) = E) (hIcc : ∀ θ, (k θ).2 ∈ Icc lo hi)

/-- **An analytic angle graph with a linear flow is a confinement `GraphTorus`**, with
`Θ = A⁻¹ = invFun (torusAngle k)`. -/
def IsAnalyticAngleGraph.toGraphTorus : GraphTorus V H E lo hi where
  k := k
  Θ := invFun (torusAngle k)
  ν := ν
  continuous_k := hG.continuous
  continuous_Θ := hG.continuous_angleInv
  angle_Θ := hG.apply_invFun
  Θ_angle := hG.invFun_apply
  hasDerivAt_orbit := hflow
  energy := henergy
  mem_Icc := hIcc

@[simp] theorem IsAnalyticAngleGraph.toGraphTorus_k :
    (hG.toGraphTorus ν hflow henergy hIcc).k = k := rfl

@[simp] theorem IsAnalyticAngleGraph.toGraphTorus_Θ :
    (hG.toGraphTorus ν hflow henergy hIcc).Θ = invFun (torusAngle k) := rfl

@[simp] theorem IsAnalyticAngleGraph.toGraphTorus_ν :
    (hG.toGraphTorus ν hflow henergy hIcc).ν = ν := rfl

/-- The torus's first action over the angle `φ` is the first component of the graph function. -/
theorem IsAnalyticAngleGraph.toGraphTorus_graph₁ (φ : Fin 2 → ℝ) :
    (hG.toGraphTorus ν hflow henergy hIcc).graph₁ φ = torusGraph k φ 0 := rfl

end Analytic

/-- **A real model torus that is an analytic angle graph is a confinement `GraphTorus`** for the
Hamiltonian field `V = X_H` (`ν = ω`). -/
def IsAnalyticAngleGraph.toGraphTorusOfModel {k : (Fin 2 → ℝ) → Phase}
    (hG : IsAnalyticAngleGraph k) {H : Phase → ℝ} {ω : Fin 2 → ℝ} {E : ℝ}
    (hT : IsRealModelTorus H ω E k) {lo hi : Fin 2 → ℝ} (hIcc : ∀ θ, (k θ).2 ∈ Icc lo hi) :
    GraphTorus (hamiltonianVectorField H) H E lo hi :=
  hG.toGraphTorus ω hT.flow hT.energy hIcc

/-- **The near-identity graph adapter feeds the confinement**: `IsAngleGraph k L` of an analytic
`k` with a linear flow of `V`, on the level, with actions in the box, is a `GraphTorus`. -/
def IsAngleGraph.toGraphTorus {k : (Fin 2 → ℝ) → Phase} {L : ℝ} (h : IsAngleGraph k L)
    (hk : AnalyticOnNhd ℝ k univ) {V : Phase → Phase} {H : Phase → ℝ} {E : ℝ}
    {lo hi : Fin 2 → ℝ} (ν : Fin 2 → ℝ)
    (hflow : ∀ θ t, HasDerivAt (fun s : ℝ => k (θ + s • ν)) (V (k (θ + t • ν))) t)
    (henergy : ∀ θ, H (k θ) = E) (hIcc : ∀ θ, (k θ).2 ∈ Icc lo hi) : GraphTorus V H E lo hi :=
  (h.isAnalyticAngleGraph hk).toGraphTorus ν hflow henergy hIcc

/-- The near-identity adapter for a real model torus (`V = X_H`, `ν = ω`; `k` is analytic as a
model torus). -/
def IsAngleGraph.toGraphTorusOfModel {k : (Fin 2 → ℝ) → Phase} {L : ℝ} (h : IsAngleGraph k L)
    {H : Phase → ℝ} {ω : Fin 2 → ℝ} {E : ℝ} (hT : IsRealModelTorus H ω E k)
    {lo hi : Fin 2 → ℝ} (hIcc : ∀ θ, (k θ).2 ∈ Icc lo hi) :
    GraphTorus (hamiltonianVectorField H) H E lo hi :=
  (h.isAnalyticAngleGraph hT.analytic).toGraphTorusOfModel hT hIcc

/-- **The clock-triangular graph adapter feeds the confinement** (real model torus, `V = X_H`,
`ν = ω`). -/
def IsClockAngleGraph.toGraphTorusOfModel {k : (Fin 2 → ℝ) → Phase} {i : Fin 2}
    {c : Fin 2 → ℝ} {m : ℝ} (h : IsClockAngleGraph k i c m) {H : Phase → ℝ} {ω : Fin 2 → ℝ}
    {E : ℝ} (hT : IsRealModelTorus H ω E k) {lo hi : Fin 2 → ℝ}
    (hIcc : ∀ θ, (k θ).2 ∈ Icc lo hi) : GraphTorus (hamiltonianVectorField H) H E lo hi :=
  h.toIsAnalyticAngleGraph.toGraphTorusOfModel hT hIcc

end KAM.Application
