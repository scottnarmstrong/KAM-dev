/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Confinement: the energy level over an action box

A chart of a Hamiltonian system with phase points `(θ, a)` (angles `θ`, actions `a`), an action box
`ℝⁿ × [α, β]` (`boxSet α β`, any `n`, `m`), and, in two degrees of freedom (`Phase = ℝ² × ℝ²`), a
function `H` (the Hamiltonian in the chart) with `∂H/∂a₂ ≤ -m < 0` on the box. Typical charts:
action–angle charts of a two-degree-of-freedom system (e.g. LG00's secular Sun–Jupiter–Saturn
model), or the extended phase space `(θ, t; p, E)` of a periodically forced one-degree-of-freedom
system (e.g. the Moon's spin), where `H̃ = H(θ, t, p) + E` and `∂H̃/∂E = 1`.

* `eq_of_energy_eq`: on the box, a point of a level set of `H` is determined by its angle and its
  first action `a₁` (the level set is a graph `a₂ = f(θ, a₁)`).
* `face_of_cone`: if moreover `|∂H/∂a₁| ≤ M` and over every angle there is a point of the level
  `H = E` with actions in `[lo, hi]`, then the level misses the faces `a₂ = β₂` and `a₂ = α₂` over a
  strip of `a₁`, provided the cone inequalities `M·W < m(β₂ − hi₂)` and `M·W < m(lo₂ − α₂)` hold.
-/

public section

open Set

namespace KAM.Application.Confinement

/-- Phase points of a two-degree-of-freedom chart: angles `θ` and actions `a`. -/
abbrev Phase : Type := (Fin 2 → ℝ) × (Fin 2 → ℝ)

/-- The action box `ℝⁿ × [α, β]` of a chart `(Fin n → ℝ) × (Fin m → ℝ)`. -/
@[expose] def boxSet {n m : ℕ} (α β : Fin m → ℝ) : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {p | p.2 ∈ Icc α β}

theorem mem_boxSet {n m : ℕ} {α β : Fin m → ℝ} {p : (Fin n → ℝ) × (Fin m → ℝ)} :
    p ∈ boxSet α β ↔ p.2 ∈ Icc α β := Iff.rfl

theorem isClosed_boxSet {n m : ℕ} (α β : Fin m → ℝ) :
    IsClosed (boxSet α β : Set ((Fin n → ℝ) × (Fin m → ℝ))) :=
  isClosed_Icc.preimage continuous_snd

/-- Moving one action: `(θ, a) ↦ (θ, a with aⱼ := s)`. -/
@[expose] def actLine (p : Phase) (j : Fin 2) (s : ℝ) : Phase := (p.1, Function.update p.2 j s)

theorem hasDerivAt_actLine (p : Phase) (j : Fin 2) (s : ℝ) :
    HasDerivAt (actLine p j) (((0 : Fin 2 → ℝ), Pi.single j 1) : Phase) s :=
  (hasDerivAt_const s p.1).prodMk (hasDerivAt_update p.2 j s)

theorem actLine_self (p : Phase) (j : Fin 2) : actLine p j (p.2 j) = p := by
  simp [actLine]

theorem actLine_mem_boxSet {α β : Fin 2 → ℝ} {p : Phase} (hp : p ∈ boxSet α β) {j : Fin 2}
    {s : ℝ} (hs : s ∈ Icc (α j) (β j)) : actLine p j s ∈ boxSet α β := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> by_cases h : i = j
  · subst h; simpa [actLine] using hs.1
  · simpa [actLine, Function.update_of_ne h] using hp.1 i
  · subst h; simpa [actLine] using hs.2
  · simpa [actLine, Function.update_of_ne h] using hp.2 i

variable {H : Phase → ℝ} {α β : Fin 2 → ℝ}

/-- The derivative of `H` along an action line. -/
theorem hasDerivAt_comp_actLine {p : Phase} {j : Fin 2} {s : ℝ}
    (hd : DifferentiableAt ℝ H (actLine p j s)) :
    HasDerivAt (fun u => H (actLine p j u))
      (fderiv ℝ H (actLine p j s) ((0 : Fin 2 → ℝ), Pi.single j 1)) s :=
  hd.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_actLine p j s)

/-- On the box, `H` is strictly antitone along `a₂` when `∂H/∂a₂ < 0`. -/
theorem strictAntiOn_actLine (hHd : ∀ q ∈ boxSet α β, DifferentiableAt ℝ H q)
    (hHm : ∀ q ∈ boxSet α β, fderiv ℝ H q ((0 : Fin 2 → ℝ), Pi.single 1 1) < 0)
    {p : Phase} (hp : p ∈ boxSet α β) :
    StrictAntiOn (fun s => H (actLine p 1 s)) (Icc (α 1) (β 1)) := by
  have hder : ∀ s ∈ Icc (α 1) (β 1), HasDerivAt (fun u => H (actLine p 1 u))
      (fderiv ℝ H (actLine p 1 s) ((0 : Fin 2 → ℝ), Pi.single 1 1)) s := fun s hs =>
    hasDerivAt_comp_actLine (hHd _ (actLine_mem_boxSet hp hs))
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt) fun s hs => ?_
  have hs' := interior_subset hs
  rw [(hder s hs').deriv]
  exact hHm _ (actLine_mem_boxSet hp hs')

/-- **The level set is a graph over `(θ, a₁)` on the box**: two points of the box with the same
angle, the same first action and the same energy coincide. -/
theorem eq_of_energy_eq (hHd : ∀ q ∈ boxSet α β, DifferentiableAt ℝ H q)
    (hHm : ∀ q ∈ boxSet α β, fderiv ℝ H q ((0 : Fin 2 → ℝ), Pi.single 1 1) < 0)
    {p q : Phase} (hp : p ∈ boxSet α β) (hq : q ∈ boxSet α β) (h1 : p.1 = q.1)
    (h0 : p.2 0 = q.2 0) (hE : H p = H q) : p = q := by
  have hqp : actLine p 1 (q.2 1) = q := by
    refine Prod.ext h1 (funext fun i => ?_)
    fin_cases i
    · simpa [actLine] using h0
    · simp [actLine]
  have hinj := (strictAntiOn_actLine hHd hHm hp).injOn
  have h21 : p.2 1 = q.2 1 := by
    refine hinj ⟨hp.1 1, hp.2 1⟩ ⟨hq.1 1, hq.2 1⟩ ?_
    simp only
    rw [actLine_self, hqp, hE]
  rw [← hqp, ← h21, actLine_self]

/-- **The faces of the box are off the level set** over the strip `a₁ ∈ [x₀, x₁]`, from the cone
inequalities and a reference point of the level set over every angle (actions in `[lo, hi]`). -/
theorem face_of_cone {E m M Wd x₀ x₁ : ℝ} {lo hi : Fin 2 → ℝ}
    (hHd : ∀ q ∈ boxSet α β, DifferentiableAt ℝ H q)
    (hHm : ∀ q ∈ boxSet α β, fderiv ℝ H q ((0 : Fin 2 → ℝ), Pi.single 1 1) ≤ -m)
    (hHM : ∀ q ∈ boxSet α β, |fderiv ℝ H q ((0 : Fin 2 → ℝ), Pi.single 0 1)| ≤ M)
    (hm : 0 ≤ m) (href : ∀ θ, ∃ q : Phase, q.1 = θ ∧ q.2 ∈ Icc lo hi ∧ H q = E)
    (hlo : α ≤ lo) (hhi : hi ≤ β) (hx₀ : α 0 ≤ x₀) (hx₁ : x₁ ≤ β 0)
    (hW₀ : hi 0 - x₀ ≤ Wd) (hW₁ : x₁ - lo 0 ≤ Wd)
    (hup : M * Wd < m * (β 1 - hi 1)) (hdn : M * Wd < m * (lo 1 - α 1)) :
    ∀ θ a, x₀ ≤ a 0 → a 0 ≤ x₁ →
      (a 1 = β 1 → H (θ, a) < E) ∧ (a 1 = α 1 → E < H (θ, a)) := by
  intro θ a ha₀ ha₁
  obtain ⟨q, rfl, hqI, hqE⟩ := href θ
  have hq : q ∈ boxSet α β := ⟨le_trans hlo hqI.1, le_trans hqI.2 hhi⟩
  -- step 1: along `a₁` from `q` to `P₁ = actLine q 0 (a 0)`
  set P₁ := actLine q 0 (a 0) with hP₁
  have hD0 : ∀ s ∈ Icc (α 0) (β 0), HasDerivAt (fun u => H (actLine q 0 u))
      (fderiv ℝ H (actLine q 0 s) ((0 : Fin 2 → ℝ), Pi.single 0 1)) s := fun s hs =>
    hasDerivAt_comp_actLine (hHd _ (actLine_mem_boxSet hq hs))
  have hstep1 : |H P₁ - E| ≤ M * Wd := by
    have hmv := (convex_Icc (α 0) (β 0)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => H (actLine q 0 u)) (fun s hs => (hD0 s hs).hasDerivWithinAt)
      (fun s hs => by
        rw [Real.norm_eq_abs]; exact hHM _ (actLine_mem_boxSet hq hs))
      (x := q.2 0) (y := a 0) ⟨hq.1 0, hq.2 0⟩ ⟨le_trans hx₀ ha₀, le_trans ha₁ hx₁⟩
    rw [actLine_self, hqE, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have hM : 0 ≤ M := (abs_nonneg _).trans (hHM q hq)
    have hd : |a 0 - q.2 0| ≤ Wd := abs_le.mpr
      ⟨by linarith [hqI.2 0], by linarith [hqI.1 0]⟩
    exact hmv.trans (mul_le_mul_of_nonneg_left hd hM)
  have hP₁box : P₁ ∈ boxSet α β := actLine_mem_boxSet hq ⟨le_trans hx₀ ha₀, le_trans ha₁ hx₁⟩
  have hP₁1 : P₁.2 1 = q.2 1 := by simp [hP₁, actLine]
  -- step 2: along `a₂` from `P₁`; `s ↦ H (actLine P₁ 1 s) + m s` is antitone on `[α₁, β₁]`
  have hD1 : ∀ s ∈ Icc (α 1) (β 1), HasDerivAt (fun u => H (actLine P₁ 1 u) + m * u)
      (fderiv ℝ H (actLine P₁ 1 s) ((0 : Fin 2 → ℝ), Pi.single 1 1) + m) s := fun s hs => by
    have h := (hasDerivAt_comp_actLine (hHd _ (actLine_mem_boxSet hP₁box hs))).add
      ((hasDerivAt_id' s).const_mul m)
    rwa [mul_one] at h
  have hanti : AntitoneOn (fun u => H (actLine P₁ 1 u) + m * u) (Icc (α 1) (β 1)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun s hs => (hD1 s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hD1 s (interior_subset hs)).differentiableAt.differentiableWithinAt)
      fun s hs => ?_
    rw [(hD1 s (interior_subset hs)).deriv]
    linarith [hHm _ (actLine_mem_boxSet hP₁box (interior_subset hs))]
  have hq1 : q.2 1 ∈ Icc (α 1) (β 1) := ⟨hq.1 1, hq.2 1⟩
  have hP2 : ∀ c, a 1 = c → actLine P₁ 1 c = (q.1, a) := by
    intro c hc
    refine Prod.ext rfl (funext fun i => ?_)
    fin_cases i
    · simp [hP₁, actLine]
    · simp [actLine, hc]
  have hself : H (actLine P₁ 1 (q.2 1)) = H P₁ := by rw [← hP₁1, actLine_self]
  have hαβ : α 1 ≤ β 1 := (hq.1 1).trans (hq.2 1)
  have hst := abs_le.mp hstep1
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have h := hanti hq1 ⟨hαβ, le_rfl⟩ (hq.2 1)
    simp only at h
    rw [hP2 _ hb, hself] at h
    have : m * (β 1 - hi 1) ≤ m * (β 1 - q.2 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hqI.2 1]) hm
    nlinarith
  · have h := hanti ⟨le_rfl, hαβ⟩ hq1 (hq.1 1)
    simp only at h
    rw [hP2 _ hb, hself] at h
    have : m * (lo 1 - α 1) ≤ m * (q.2 1 - α 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hqI.1 1]) hm
    nlinarith

end KAM.Application.Confinement
