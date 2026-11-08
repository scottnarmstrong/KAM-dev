/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.Observable

/-!
# The tube domain in phase space: `W`, the action deviations and the compact `K` (T2-CONF, N5b)

The phase-space sets of the tube checker, through the chart `tubeChart V B` of N2
(`x ↦ (u, φ)`, `u = I - B(φ)`):

* `modesPos V`: all rotated modes nonzero, `(Vᵀη)_j² + (Vᵀξ)_j² > 0` (the open set `W`);
* `tubeU V B x = (tubeChart V B x).1`: the action deviations `u_j(x) = I_j(x) - B_j(φ(x))`;
* `tubeK V B ρ = {x ∈ W | ∀ j, |u_j x| ≤ ρ}`: the closed tube.

Main results:
* `isOpen_modesPos`; `continuousOn_tubeU` (for a `2π`-periodic differentiable `B`: the branch cut of
  `arg` is invisible);
* `isCompact_tubeK`: if `bmin_j ≤ B_j ≤ bmax_j` and `ρ < bmin_j`, the tube `K` is compact (its
  actions lie in `[bmin_j - ρ, bmax_j + ρ]`, bounded away from `0`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Set Filter Topology Matrix Real

/-- `B` is `2π`-periodic in both reduced angles. -/
abbrev ShiftPeriodic (B : (Fin 2 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∀ (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ), B (φ + fun a => 2 * π * m a) = B φ

/-- A function of `(u, φ)` is `2π`-periodic in both reduced angles. -/
abbrev ObsPeriodic (f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ), f (u, φ + fun a => 2 * π * m a) = f (u, φ)

/-- The squared modulus `(Vᵀη)_j² + (Vᵀξ)_j²` of the rotated mode `j` (twice its action). -/
def modeSq (V : Matrix (Fin 3) (Fin 3) ℝ) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (j : Fin 3) : ℝ :=
  (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2

/-- The open set `W`: all rotated modes nonzero. -/
def modesPos (V : Matrix (Fin 3) (Fin 3) ℝ) : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  {x | ∀ j, 0 < modeSq V x j}

/-- The action deviations `u_j(x) = I_j(x) - B_j(φ(x))`. -/
def tubeU (V : Matrix (Fin 3) (Fin 3) ℝ) (B : (Fin 2 → ℝ) → (Fin 3 → ℝ))
    (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  (tubeChart V B x).1

/-- The closed tube `K = {x ∈ W | ∀ j, |u_j x| ≤ ρ}`. -/
def tubeK (V : Matrix (Fin 3) (Fin 3) ℝ) (B : (Fin 2 → ℝ) → (Fin 3 → ℝ)) (ρ : ℝ) :
    Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  {x | x ∈ modesPos V ∧ ∀ j, |tubeU V B x j| ≤ ρ}

theorem continuous_rotMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Continuous (rotMap A) :=
  (differentiable_rotMap A).continuous

theorem continuous_modeSq (V : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    Continuous fun x => modeSq V x j := by
  have h := continuous_rotMap Vᵀ
  unfold modeSq
  fun_prop

theorem isOpen_modesPos (V : Matrix (Fin 3) (Fin 3) ℝ) : IsOpen (modesPos V) := by
  have : modesPos V = ⋂ j, {x | 0 < modeSq V x j} := by ext x; simp [modesPos]
  rw [this]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_modeSq V j)

theorem mem_modesPos_iff {V : Matrix (Fin 3) (Fin 3) ℝ} {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} :
    x ∈ modesPos V ↔ ∀ j, 0 < (rotMap Vᵀ x).1 j ^ 2 + (rotMap Vᵀ x).2 j ^ 2 := Iff.rfl

/-- The action of the rotated mode `j` is `modeSq / 2`, and `u_j = modeSq / 2 - B_j(φ)`. -/
theorem tubeU_apply (V : Matrix (Fin 3) (Fin 3) ℝ) (B : (Fin 2 → ℝ) → (Fin 3 → ℝ))
    (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (j : Fin 3) :
    tubeU V B x j = modeSq V x j / 2 - B (tubeChart V B x).2 j := rfl

theorem differentiableAt_tubeU {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} (hBper : ShiftPeriodic B) (hB : Differentiable ℝ B)
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ modesPos V) (j : Fin 3) :
    DifferentiableAt ℝ (fun x => tubeU V B x j) x :=
  differentiableAt_comp_tubeChart (f := fun p => p.1 j) hV hBper (fun _ _ _ => rfl) hx
    (by fun_prop) (hB _)

theorem continuousOn_tubeU {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} (hBper : ShiftPeriodic B) (hB : Differentiable ℝ B)
    (j : Fin 3) : ContinuousOn (fun x => tubeU V B x j) (modesPos V) := fun _ hx =>
  (differentiableAt_tubeU hV hBper hB hx j).continuousAt.continuousWithinAt

private theorem abs_le_one_add_sq (a : ℝ) : |a| ≤ 1 + a ^ 2 := by
  nlinarith [sq_abs a, sq_nonneg (|a| - 1)]

/-- **Compactness of the tube.** If `bmin_j ≤ B_j(φ) ≤ bmax_j` for all `φ` and `ρ < bmin_j`, then
`K = tubeK V B ρ` is compact. -/
theorem isCompact_tubeK {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} (hBper : ShiftPeriodic B) (hB : Differentiable ℝ B)
    {bmin bmax : Fin 3 → ℝ} {ρ : ℝ} (hρ : ∀ j, ρ < bmin j) (hmin : ∀ φ j, bmin j ≤ B φ j)
    (hmax : ∀ φ j, B φ j ≤ bmax j) : IsCompact (tubeK V B ρ) := by
  set S := {x : (Fin 3 → ℝ) × (Fin 3 → ℝ) | ∀ j, 2 * (bmin j - ρ) ≤ modeSq V x j}
  have hSW : S ⊆ modesPos V := fun x hx j => by
    have := hx j
    have := hρ j
    linarith
  have hSc : IsClosed S := by
    have : S = ⋂ j, {x | 2 * (bmin j - ρ) ≤ modeSq V x j} := by ext x; simp [S]
    rw [this]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_modeSq V j)
  have hlow : ∀ x, (∀ j, |tubeU V B x j| ≤ ρ) → x ∈ S := fun x hx j => by
    have h1 := (abs_le.1 (hx j)).1
    rw [tubeU_apply] at h1
    have := hmin (tubeChart V B x).2 j
    linarith
  have hKeq : tubeK V B ρ = S ∩ (tubeU V B) ⁻¹' {v | ∀ j, |v j| ≤ ρ} := by
    ext x
    exact ⟨fun hx => ⟨hlow x hx.2, hx.2⟩, fun hx => ⟨hSW hx.1, hx.2⟩⟩
  have hclosed : IsClosed (tubeK V B ρ) := by
    rw [hKeq]
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ hSc ?_
    · exact continuousOn_pi.2 fun j => (continuousOn_tubeU hV hBper hB j).mono hSW
    · have : {v : Fin 3 → ℝ | ∀ j, |v j| ≤ ρ} = ⋂ j, {v | |v j| ≤ ρ} := by ext v; simp
      rw [this]
      exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  -- boundedness: `K ⊆ rotMap V '' closedBall 0 M`
  set M : ℝ := 1 + ∑ j, 2 * (bmax j + ρ)
  have hbd : ∀ x ∈ tubeK V B ρ, ∀ j, modeSq V x j ≤ 2 * (bmax j + ρ) := fun x hx j => by
    have h1 := (abs_le.1 (hx.2 j)).2
    rw [tubeU_apply] at h1
    have := hmax (tubeChart V B x).2 j
    linarith
  have hM : ∀ x ∈ tubeK V B ρ, ∀ j, |(rotMap Vᵀ x).1 j| ≤ M ∧ |(rotMap Vᵀ x).2 j| ≤ M := by
    intro x hx j
    have hsum : 2 * (bmax j + ρ) ≤ ∑ k, 2 * (bmax k + ρ) :=
      Finset.single_le_sum (f := fun k => 2 * (bmax k + ρ))
        (fun k _ => by
          have := hmin 0 k; have := hmax 0 k; have := hρ k
          have : 0 ≤ ρ := (abs_nonneg _).trans (hx.2 k)
          linarith)
        (Finset.mem_univ j)
    have h1 := hbd x hx j
    unfold modeSq at h1
    constructor
    · nlinarith [abs_le_one_add_sq ((rotMap Vᵀ x).1 j), sq_nonneg ((rotMap Vᵀ x).2 j)]
    · nlinarith [abs_le_one_add_sq ((rotMap Vᵀ x).2 j), sq_nonneg ((rotMap Vᵀ x).1 j)]
  have hsub : tubeK V B ρ ⊆ rotMap V '' Metric.closedBall 0 M := by
    intro x hx
    refine ⟨rotMap Vᵀ x, ?_, rotMap_rotMap_transpose hV x⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx 0).1
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    constructor
    · exact (pi_norm_le_iff_of_nonneg hM0).2 fun j => by
        rw [Real.norm_eq_abs]; exact (hM x hx j).1
    · exact (pi_norm_le_iff_of_nonneg hM0).2 fun j => by
        rw [Real.norm_eq_abs]; exact (hM x hx j).2
  exact ((isCompact_closedBall _ _).image (continuous_rotMap V)).of_isClosed_subset hclosed hsub

end KAM.EffectiveStability.Tube

end
