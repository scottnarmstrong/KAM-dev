/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Confinement.GlobalODE
public import KAM.Application.Confinement.Level
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Confinement between two invariant tori in two degrees of freedom

"A trajectory cannot cross an invariant torus": on the universal cover `ℝ² × ℝ²` of a chart
`(θ, a)` of a two-degree-of-freedom system, the solution through a point of an energy level that
lies strictly between two invariant tori of that level stays between them for all times (the
topological confinement argument of Arnold; used e.g. by Celletti–Chierchia for the restricted
three-body problem and by Locatelli–Giorgilli, Celest. Mech. Dyn. Astron. 78 (2000) 47–74,
Sect. 1 and 4.3, for the secular Sun–Jupiter–Saturn model). The statement is for a general field
`V` and first integral `H` (typically `V = X_H`); the second action `a₂` is the one the energy
level solves for (`∂H/∂a₂ < 0`), the first action `a₁` the one in which the tori are ordered.

* `InvariantGraph`: an invariant graph over the angles: `k : ℝ² → ℝ² × ℝ²` with a continuous
  two-sided inverse `Θ` of its angle map `θ ↦ (k θ).1`, invariant for the field `V` (through each
  of its points a global solution of `V` stays on it), on the energy level `H = E`, with actions
  in `[lo, hi]`. Its first action over the angle `φ` is `graph₁ φ = (k (Θ φ)).2 0`.
* `GraphTorus`: the same with invariance given by a linear flow `t ↦ k (θ + t ν)` of `V` (a KAM
  torus); `GraphTorus.toInvariantGraph` forgets the flow. (For a certified torus the graph
  property comes from `KAM.Application.CertifiedTorusAt.isAngleGraph`.)
* `twoTorus_confinement_of_invariant`: let `V` be Lipschitz and bounded on the action box
  `ℝ² × [α, β]`, `H` differentiable there, a first integral of `V` with `∂H/∂a₂ ≤ -m < 0`, both
  graphs inside the box, the faces `a₂ = α₂, β₂` off the level `H = E` over the strip between the
  graphs (e.g. by `face_of_cone`), and an initial point `w₀` of the level strictly between the
  two graphs. Then the solution of `V` through `w₀` exists for all times, stays strictly inside
  the box and strictly between the graphs, and every global solution through `w₀` is this one.
  No hypothesis on `H` outside the box is needed (chart Hamiltonians defined only on positive
  actions fit).
* `twoTorus_confinement`: the same for two `GraphTorus`es.

The proof: the field clamped to the box is globally Lipschitz and bounded
(`lipschitzWith_clamped`), so its solution `w` is global (`exists_global_solution`). The set of
times at which `w` is inside the open box, on the level, and strictly between the graphs is open
(energy is conserved inside the box) and closed: a limit point lies in the closed region, which
is inside the open box by the faces, and is off both graphs, since an orbit through a graph
point stays on the graph (invariance and uniqueness for the clamped field), whereas `w₀` is on
neither graph. Uniqueness: `w` stays in the open box, where `V` is Lipschitz
(`eq_of_lipschitzOnWith_of_mem_open`).
-/

public section

open Set Filter
open scoped NNReal Topology

namespace KAM.Application.Confinement

/-- **An invariant graph over the angles**: `k : ℝ² → ℝ² × ℝ²` with a continuous two-sided inverse
`Θ` of its angle map `θ ↦ (k θ).1`, invariant for the field `V` (through every point of it a global
solution of `V` stays on it), on the energy level `H = E`, with actions in `[lo, hi]`. -/
structure InvariantGraph (V : Phase → Phase) (H : Phase → ℝ) (E : ℝ) (lo hi : Fin 2 → ℝ) where
  /-- the embedding, on the universal cover -/
  k : (Fin 2 → ℝ) → Phase
  /-- the inverse of the angle map `θ ↦ (k θ).1` -/
  Θ : (Fin 2 → ℝ) → Fin 2 → ℝ
  continuous_k : Continuous k
  continuous_Θ : Continuous Θ
  angle_Θ : ∀ φ, (k (Θ φ)).1 = φ
  Θ_angle : ∀ θ, Θ (k θ).1 = θ
  invariant : ∀ θ, ∃ γ : ℝ → Phase, γ 0 = k θ ∧
    ∀ s, HasDerivAt γ (V (γ s)) s ∧ γ s ∈ Set.range k
  energy : ∀ θ, H (k θ) = E
  mem_Icc : ∀ θ, (k θ).2 ∈ Icc lo hi

namespace InvariantGraph

variable {V : Phase → Phase} {H : Phase → ℝ} {E : ℝ} {lo hi : Fin 2 → ℝ}
  (T : InvariantGraph V H E lo hi)

/-- The graph's first action over the angle `φ`. -/
@[expose] def graph₁ (φ : Fin 2 → ℝ) : ℝ := (T.k (T.Θ φ)).2 0

theorem continuous_graph₁ : Continuous T.graph₁ :=
  ((continuous_apply 0).comp continuous_snd).comp (T.continuous_k.comp T.continuous_Θ)

theorem graph₁_k (θ : Fin 2 → ℝ) : T.graph₁ (T.k θ).1 = (T.k θ).2 0 := by
  simp [graph₁, T.Θ_angle]

/-- A point of the level set in the box whose first action is the graph's is on the graph. -/
theorem eq_k_of_graph₁ {α β : Fin 2 → ℝ}
    (hHd : ∀ q ∈ boxSet α β, DifferentiableAt ℝ H q)
    (hHm : ∀ q ∈ boxSet α β, fderiv ℝ H q ((0 : Fin 2 → ℝ), Pi.single 1 1) < 0)
    (hlo : α ≤ lo) (hhi : hi ≤ β) {p : Phase} (hp : p ∈ boxSet α β) (hE : H p = E)
    (hg : p.2 0 = T.graph₁ p.1) : p = T.k (T.Θ p.1) :=
  eq_of_energy_eq hHd hHm hp
    ⟨le_trans hlo (T.mem_Icc _).1, le_trans (T.mem_Icc _).2 hhi⟩
    (T.angle_Θ p.1).symm hg (hE.trans (T.energy _).symm)

end InvariantGraph

/-- **An invariant torus with a linear flow that is a graph over the angles**: as
`InvariantGraph`, with invariance given by the linear flow `t ↦ k (θ + t ν)` of `V`. -/
structure GraphTorus (V : Phase → Phase) (H : Phase → ℝ) (E : ℝ) (lo hi : Fin 2 → ℝ) where
  /-- the embedding, on the universal cover -/
  k : (Fin 2 → ℝ) → Phase
  /-- the inverse of the angle map `θ ↦ (k θ).1` -/
  Θ : (Fin 2 → ℝ) → Fin 2 → ℝ
  /-- the frequency of the linear flow on the torus -/
  ν : Fin 2 → ℝ
  continuous_k : Continuous k
  continuous_Θ : Continuous Θ
  angle_Θ : ∀ φ, (k (Θ φ)).1 = φ
  Θ_angle : ∀ θ, Θ (k θ).1 = θ
  hasDerivAt_orbit : ∀ θ t, HasDerivAt (fun s : ℝ => k (θ + s • ν)) (V (k (θ + t • ν))) t
  energy : ∀ θ, H (k θ) = E
  mem_Icc : ∀ θ, (k θ).2 ∈ Icc lo hi

namespace GraphTorus

variable {V : Phase → Phase} {H : Phase → ℝ} {E : ℝ} {lo hi : Fin 2 → ℝ}
  (T : GraphTorus V H E lo hi)

/-- The torus as an invariant graph: the lines `s ↦ k (θ + s ν)` are the invariant solutions. -/
@[expose] def toInvariantGraph : InvariantGraph V H E lo hi where
  k := T.k
  Θ := T.Θ
  continuous_k := T.continuous_k
  continuous_Θ := T.continuous_Θ
  angle_Θ := T.angle_Θ
  Θ_angle := T.Θ_angle
  invariant θ := ⟨fun s => T.k (θ + s • T.ν), by simp, fun s => ⟨T.hasDerivAt_orbit θ s, ⟨_, rfl⟩⟩⟩
  energy := T.energy
  mem_Icc := T.mem_Icc

/-- The torus's first action over the angle `φ`. -/
@[expose] def graph₁ (φ : Fin 2 → ℝ) : ℝ := (T.k (T.Θ φ)).2 0

theorem toInvariantGraph_graph₁ : T.toInvariantGraph.graph₁ = T.graph₁ := rfl

theorem continuous_graph₁ : Continuous T.graph₁ := T.toInvariantGraph.continuous_graph₁

theorem graph₁_k (θ : Fin 2 → ℝ) : T.graph₁ (T.k θ).1 = (T.k θ).2 0 :=
  T.toInvariantGraph.graph₁_k θ

end GraphTorus

/-- The open action box `ℝⁿ × (α, β)`. -/
@[expose] def openBoxSet {n m : ℕ} (α β : Fin m → ℝ) : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {p | ∀ j, α j < p.2 j ∧ p.2 j < β j}

theorem isOpen_openBoxSet {n m : ℕ} (α β : Fin m → ℝ) :
    IsOpen (openBoxSet α β : Set ((Fin n → ℝ) × (Fin m → ℝ))) := by
  have : (openBoxSet α β : Set ((Fin n → ℝ) × (Fin m → ℝ))) = ⋂ j : Fin m,
      ({p : (Fin n → ℝ) × (Fin m → ℝ) | α j < p.2 j} ∩
        {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 j < β j}) := by
    ext p
    simp [openBoxSet, forall_and]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    (isOpen_lt continuous_const ((continuous_apply j).comp continuous_snd)).inter
      (isOpen_lt ((continuous_apply j).comp continuous_snd) continuous_const)

theorem openBoxSet_subset {n m : ℕ} (α β : Fin m → ℝ) :
    (openBoxSet α β : Set ((Fin n → ℝ) × (Fin m → ℝ))) ⊆ boxSet α β :=
  fun _ hp => ⟨fun j => (hp j).1.le, fun j => (hp j).2.le⟩

/-- **Confinement between two invariant graphs** (two degrees of freedom, chart level): the
solution through `w₀` exists for all times, stays strictly inside the box, on the level and
strictly between the graphs, and every global solution through `w₀` is this one. -/
theorem twoTorus_confinement_of_invariant {V : Phase → Phase} {H : Phase → ℝ} {E : ℝ}
    {α β lo₁ hi₁ lo₂ hi₂ : Fin 2 → ℝ} {K : ℝ≥0} {C m : ℝ}
    (T₁ : InvariantGraph V H E lo₁ hi₁) (T₂ : InvariantGraph V H E lo₂ hi₂)
    (hV : LipschitzOnWith K V (boxSet α β)) (hVC : ∀ p ∈ boxSet α β, ‖V p‖ ≤ C)
    (hHd : ∀ p ∈ boxSet α β, DifferentiableAt ℝ H p)
    (hHV : ∀ p ∈ boxSet α β, fderiv ℝ H p (V p) = 0)
    (hm : 0 < m) (hHm : ∀ p ∈ boxSet α β, fderiv ℝ H p ((0 : Fin 2 → ℝ), Pi.single 1 1) ≤ -m)
    (hlo₁ : α ≤ lo₁) (hhi₁ : hi₁ ≤ β) (hlo₂ : α ≤ lo₂) (hhi₂ : hi₂ ≤ β)
    (hα₀ : α 0 < lo₁ 0) (hβ₀ : hi₂ 0 < β 0)
    (hface : ∀ θ a, lo₁ 0 ≤ a 0 → a 0 ≤ hi₂ 0 →
      (a 1 = β 1 → H (θ, a) < E) ∧ (a 1 = α 1 → E < H (θ, a)))
    {w₀ : Phase} (hw₀ : w₀ ∈ boxSet α β) (hw₀E : H w₀ = E)
    (hw₀₁ : T₁.graph₁ w₀.1 < w₀.2 0) (hw₀₂ : w₀.2 0 < T₂.graph₁ w₀.1) :
    ∃ w : ℝ → Phase, w 0 = w₀ ∧
      (∀ t, HasDerivAt w (V (w t)) t ∧
        (∀ j, α j < (w t).2 j ∧ (w t).2 j < β j) ∧ H (w t) = E ∧
        T₁.graph₁ (w t).1 < (w t).2 0 ∧ (w t).2 0 < T₂.graph₁ (w t).1) ∧
      ∀ w' : ℝ → Phase, w' 0 = w₀ → (∀ t, HasDerivAt w' (V (w' t)) t) → w' = w := by
  have hHm' : ∀ p ∈ boxSet α β, fderiv ℝ H p ((0 : Fin 2 → ℝ), Pi.single 1 1) < 0 :=
    fun p hp => (hHm p hp).trans_lt (neg_lt_zero.mpr hm)
  have hαβ : α ≤ β := fun j =>
    ((hlo₁ j).trans (((T₁.mem_Icc 0).1 j).trans ((T₁.mem_Icc 0).2 j))).trans (hhi₁ j)
  have hHc : ContinuousOn H (boxSet α β) := fun p hp =>
    (hHd p hp).continuousAt.continuousWithinAt
  /- the clamped field -/
  set W : Phase → Phase := fun p => V (p.1, clampBox α β p.2) with hWdef
  have hWV : ∀ p ∈ boxSet α β, W p = V p := fun p hp => by
    simp only [hWdef, clampBox_of_mem hp]
  have hWlip : LipschitzWith K W := lipschitzWith_clamped hαβ hV
  have hWC : ∀ p, ‖W p‖ ≤ C := fun p => hVC _ (clampBox_mem hαβ p.2)
  obtain ⟨w, hw0, hw⟩ := exists_global_solution hWlip hWC w₀
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun t => (hw t).continuousAt
  /- the barriers and the regions -/
  set g₁ : Phase → ℝ := fun p => p.2 0 - T₁.graph₁ p.1 with hg₁
  set g₂ : Phase → ℝ := fun p => T₂.graph₁ p.1 - p.2 0 with hg₂
  have hg₁c : Continuous g₁ :=
    ((continuous_apply 0).comp continuous_snd).sub (T₁.continuous_graph₁.comp continuous_fst)
  have hg₂c : Continuous g₂ :=
    (T₂.continuous_graph₁.comp continuous_fst).sub ((continuous_apply 0).comp continuous_snd)
  set O := openBoxSet α β
  have hCO : ∀ p ∈ boxSet α β, H p = E → 0 ≤ g₁ p → 0 ≤ g₂ p → p ∈ O := by
    intro p hp hE h1 h2
    have hlo : lo₁ 0 ≤ p.2 0 := by
      have := (T₁.mem_Icc (T₁.Θ p.1)).1 0
      simp only [hg₁, InvariantGraph.graph₁] at h1
      linarith
    have hhi : p.2 0 ≤ hi₂ 0 := by
      have := (T₂.mem_Icc (T₂.Θ p.1)).2 0
      simp only [hg₂, InvariantGraph.graph₁] at h2
      linarith
    have hf := hface p.1 p.2 hlo hhi
    intro j
    fin_cases j
    · exact ⟨by simp; linarith, by simp; linarith⟩
    · refine ⟨lt_of_le_of_ne (hp.1 1) fun h => ?_, lt_of_le_of_ne (hp.2 1) fun h => ?_⟩
      · have := hf.2 h.symm
        simp only [Prod.mk.eta] at this
        linarith
      · have := hf.1 h
        simp only [Prod.mk.eta] at this
        linarith
  /- an orbit of the clamped field through a graph point stays on the graph -/
  have horbit : ∀ {lo hi : Fin 2 → ℝ} (T : InvariantGraph V H E lo hi), α ≤ lo → hi ≤ β →
      ∀ t θ, w t = T.k θ → w 0 ∈ Set.range T.k := by
    intro lo hi T hlo hhi t θ hwt
    have hTbox : ∀ θ, T.k θ ∈ boxSet α β := fun θ =>
      ⟨le_trans hlo (T.mem_Icc θ).1, le_trans (T.mem_Icc θ).2 hhi⟩
    obtain ⟨γ, hγ0, hγ⟩ := T.invariant θ
    have hγbox : ∀ s, γ s ∈ boxSet α β := fun s => by
      obtain ⟨θ', hθ'⟩ := (hγ s).2
      rw [← hθ']
      exact hTbox θ'
    set γ' : ℝ → Phase := fun s => γ (s - t) with hγ'
    have hγ'd : ∀ s, HasDerivAt γ' (W (γ' s)) s := fun s => by
      rw [hWV _ (hγbox _)]
      exact ((hγ (s - t)).1).comp_sub_const s t
    have heq : w = γ' := ODE_solution_unique_univ (v := fun _ => W) (s := fun _ => univ)
      (K := K) (t₀ := t) (fun _ => hWlip.lipschitzOnWith) (fun s => ⟨hw s, trivial⟩)
      (fun s => ⟨hγ'd s, trivial⟩) (by simp [hγ', hγ0, hwt])
    rw [heq]
    exact (hγ (0 - t)).2
  have hnot₁ : ∀ t, w t ∈ boxSet α β → H (w t) = E → g₁ (w t) ≠ 0 := by
    intro t hb hE h0
    have hk := T₁.eq_k_of_graph₁ hHd hHm' hlo₁ hhi₁ hb hE (by simp only [hg₁] at h0; linarith)
    obtain ⟨θ', hθ'⟩ := horbit T₁ hlo₁ hhi₁ t _ hk
    have : g₁ (w 0) = 0 := by
      simp only [hg₁, ← hθ', T₁.graph₁_k, sub_self]
    rw [hw0] at this
    simp only [hg₁] at this
    linarith
  have hnot₂ : ∀ t, w t ∈ boxSet α β → H (w t) = E → g₂ (w t) ≠ 0 := by
    intro t hb hE h0
    have hk := T₂.eq_k_of_graph₁ hHd hHm' hlo₂ hhi₂ hb hE (by simp only [hg₂] at h0; linarith)
    obtain ⟨θ', hθ'⟩ := horbit T₂ hlo₂ hhi₂ t _ hk
    have : g₂ (w 0) = 0 := by
      simp only [hg₂, ← hθ', T₂.graph₁_k, sub_self]
    rw [hw0] at this
    simp only [hg₂] at this
    linarith
  /- the good times -/
  set S : Set ℝ := {t | w t ∈ O ∧ H (w t) = E ∧ 0 < g₁ (w t) ∧ 0 < g₂ (w t)} with hS
  set Cl : Set Phase :=
    (boxSet α β ∩ H ⁻¹' {E}) ∩ {p | 0 ≤ g₁ p} ∩ {p | 0 ≤ g₂ p} with hCl
  have hClc : IsClosed Cl :=
    ((hHc.preimage_isClosed_of_isClosed (isClosed_boxSet α β) isClosed_singleton).inter
      (isClosed_le continuous_const hg₁c)).inter (isClosed_le continuous_const hg₂c)
  have hSeq : S = w ⁻¹' Cl := by
    ext t
    constructor
    · rintro ⟨hO, hE, h1, h2⟩
      exact ⟨⟨⟨openBoxSet_subset α β hO, hE⟩, h1.le⟩, h2.le⟩
    · rintro ⟨⟨⟨hb, hE⟩, h1⟩, h2⟩
      have hE' : H (w t) = E := hE
      exact ⟨hCO _ hb hE' h1 h2, hE', lt_of_le_of_ne h1 (hnot₁ t hb hE').symm,
        lt_of_le_of_ne h2 (hnot₂ t hb hE').symm⟩
  have hSclosed : IsClosed S := hSeq ▸ hClc.preimage hwc
  have hSopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro t ht
    have hU : IsOpen (w ⁻¹' (O ∩ {p | 0 < g₁ p} ∩ {p | 0 < g₂ p})) :=
      (((isOpen_openBoxSet α β).inter (isOpen_lt continuous_const hg₁c)).inter
        (isOpen_lt continuous_const hg₂c)).preimage hwc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t ⟨⟨ht.1, ht.2.2.1⟩, ht.2.2.2⟩
    refine ⟨ε, hε, fun s hs => ?_⟩
    obtain ⟨⟨hsO, hs1⟩, hs2⟩ := hball hs
    refine ⟨hsO, ?_, hs1, hs2⟩
    -- energy is constant on the ball
    have hder : ∀ u ∈ Metric.ball t ε, HasDerivAt (fun u => H (w u)) 0 u := by
      intro u hu
      obtain ⟨⟨huO, -⟩, -⟩ := hball hu
      have hub := openBoxSet_subset α β huO
      have h := (hHd _ hub).hasFDerivAt.comp_hasDerivAt u (hw u)
      rwa [hWV _ hub, hHV _ hub] at h
    have hconst := (Metric.isOpen_ball (x := t) (ε := ε)).is_const_of_deriv_eq_zero
      (convex_ball t ε).isPreconnected
      (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hder u hu).deriv) hs (Metric.mem_ball_self hε)
    exact hconst.trans ht.2.1
  have hS0 : (0 : ℝ) ∈ S := by
    rw [hSeq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp only [Set.mem_preimage, hw0]
    · exact hw₀
    · exact hw₀E
    · simp only [hg₁, Set.mem_ofPred_eq]; linarith
    · simp only [hg₂, Set.mem_ofPred_eq]; linarith
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨0, hS0⟩
  have hmemS : ∀ t, t ∈ S := fun t => hSuniv ▸ mem_univ t
  have hwV : ∀ t, HasDerivAt w (V (w t)) t := fun t => by
    rw [← hWV _ (openBoxSet_subset α β (hmemS t).1)]
    exact hw t
  refine ⟨w, hw0, fun t => ?_, fun w' hw'0 hw' => ?_⟩
  · obtain ⟨hO, hE, h1, h2⟩ := hmemS t
    refine ⟨hwV t, hO, hE, ?_, ?_⟩
    · simp only [hg₁] at h1; linarith
    · simp only [hg₂] at h2; linarith
  · exact eq_of_lipschitzOnWith_of_mem_open hV (isOpen_openBoxSet α β) (openBoxSet_subset α β)
      hwV (fun t => (hmemS t).1) hw' (hw'0.trans hw0.symm)

/-- **Confinement between two invariant tori with linear flows**:
`twoTorus_confinement_of_invariant` for two `GraphTorus`es. -/
theorem twoTorus_confinement {V : Phase → Phase} {H : Phase → ℝ} {E : ℝ}
    {α β lo₁ hi₁ lo₂ hi₂ : Fin 2 → ℝ} {K : ℝ≥0} {C m : ℝ}
    (T₁ : GraphTorus V H E lo₁ hi₁) (T₂ : GraphTorus V H E lo₂ hi₂)
    (hV : LipschitzOnWith K V (boxSet α β)) (hVC : ∀ p ∈ boxSet α β, ‖V p‖ ≤ C)
    (hHd : ∀ p ∈ boxSet α β, DifferentiableAt ℝ H p)
    (hHV : ∀ p ∈ boxSet α β, fderiv ℝ H p (V p) = 0)
    (hm : 0 < m) (hHm : ∀ p ∈ boxSet α β, fderiv ℝ H p ((0 : Fin 2 → ℝ), Pi.single 1 1) ≤ -m)
    (hlo₁ : α ≤ lo₁) (hhi₁ : hi₁ ≤ β) (hlo₂ : α ≤ lo₂) (hhi₂ : hi₂ ≤ β)
    (hα₀ : α 0 < lo₁ 0) (hβ₀ : hi₂ 0 < β 0)
    (hface : ∀ θ a, lo₁ 0 ≤ a 0 → a 0 ≤ hi₂ 0 →
      (a 1 = β 1 → H (θ, a) < E) ∧ (a 1 = α 1 → E < H (θ, a)))
    {w₀ : Phase} (hw₀ : w₀ ∈ boxSet α β) (hw₀E : H w₀ = E)
    (hw₀₁ : T₁.graph₁ w₀.1 < w₀.2 0) (hw₀₂ : w₀.2 0 < T₂.graph₁ w₀.1) :
    ∃ w : ℝ → Phase, w 0 = w₀ ∧
      (∀ t, HasDerivAt w (V (w t)) t ∧
        (∀ j, α j < (w t).2 j ∧ (w t).2 j < β j) ∧ H (w t) = E ∧
        T₁.graph₁ (w t).1 < (w t).2 0 ∧ (w t).2 0 < T₂.graph₁ (w t).1) ∧
      ∀ w' : ℝ → Phase, w' 0 = w₀ → (∀ t, HasDerivAt w' (V (w' t)) t) → w' = w :=
  twoTorus_confinement_of_invariant T₁.toInvariantGraph T₂.toInvariantGraph hV hVC hHd hHV hm
    hHm hlo₁ hhi₁ hlo₂ hhi₂ hα₀ hβ₀ hface hw₀ hw₀E hw₀₁ hw₀₂

end KAM.Application.Confinement
