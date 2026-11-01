/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Confinement.TwoTorus
public import KAM.Application.Confinement.Periodic

/-!
# Tests of the confinement lemmas on a toy system

The toy two-degree-of-freedom system `H(θ, a) = −a₂` in a chart `(θ, a) ∈ ℝ² × ℝ²`: its field is
`X_H = (∂_a H, −∂_θ H) = ((0, −1), 0)` (constant), and every flat torus `a = (c, e)` is invariant,
a graph over the angles, on the level `H = −e`.

* `toy_clampBox`, `toy_lipschitz`: the clamp and the periodic Lipschitz lemma on small inputs;
* `toy_confined`: `twoTorus_confinement` with the flat tori `a = (∓1/2, 0)` on the level `H = 0`,
  the box `[−1, 1]²` and the initial point `(0, (0, 0))`: the solution exists for all times and
  stays strictly between the tori, `−1/2 < a₁ < 1/2`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Application.Tests.Confinement

open KAM.Application.Confinement

/-- The clamp of `(2, −3)` to `[0, 1]²` is `(1, 0)`. -/
theorem toy_clampBox : clampBox ![0, 0] ![1, 1] ![2, -3] = (![1, 0] : Fin 2 → ℝ) := by
  funext j
  fin_cases j <;> norm_num [clampBox]

/-- The toy Hamiltonian `H(θ, a) = −a₂`. -/
def toyH (p : Phase) : ℝ := -p.2 1

/-- Its Hamiltonian field `((0, −1), 0)`. -/
def toyV (_ : Phase) : Phase := (![0, -1], 0)

/-- A constant field is Lipschitz and bounded on any action box (the periodic lemma). -/
theorem toy_lipschitz (α β : Fin 2 → ℝ) :
    ∃ K, ∃ C : ℝ, LipschitzOnWith K toyV (boxSet α β) ∧ ∀ p ∈ boxSet α β, ‖toyV p‖ ≤ C :=
  exists_lipschitzOnWith_of_periodic isOpen_univ (subset_univ _) contDiffOn_const
    fun _ _ => rfl

theorem hasFDerivAt_toyH (p : Phase) :
    HasFDerivAt toyH (-((ContinuousLinearMap.proj (1 : Fin 2)).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)))) p :=
  ((ContinuousLinearMap.proj (1 : Fin 2)).comp
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).hasFDerivAt.neg

theorem fderiv_toyH (p v : Phase) : fderiv ℝ toyH p v = -v.2 1 := by
  rw [(hasFDerivAt_toyH p).fderiv]
  rfl

/-- The flat torus `a = (c, 0)`: a graph torus of the toy field on the level `H = 0`. -/
def flatTorus (c : ℝ) : GraphTorus toyV toyH 0 ![c, 0] ![c, 0] where
  k θ := (θ, ![c, 0])
  Θ := id
  ν := ![0, -1]
  continuous_k := continuous_id.prodMk continuous_const
  continuous_Θ := continuous_id
  angle_Θ _ := rfl
  Θ_angle _ := rfl
  hasDerivAt_orbit θ t := by
    have h := (((hasDerivAt_id t).smul_const (![0, -1] : Fin 2 → ℝ)).const_add θ).prodMk
      (hasDerivAt_const t (![c, 0] : Fin 2 → ℝ))
    simpa [toyV] using h
  energy _ := by simp [toyH]
  mem_Icc _ := ⟨le_rfl, le_rfl⟩

/-- **The toy confinement**: the solution of the toy field through `(0, (0, 0))` exists for all
times and stays strictly between the flat tori `a₁ = −1/2` and `a₁ = 1/2`. -/
theorem toy_confined :
    ∃ w : ℝ → Phase, w 0 = (0, ![0, 0]) ∧ ∀ t, HasDerivAt w (toyV (w t)) t ∧
      -1 / 2 < (w t).2 0 ∧ (w t).2 0 < 1 / 2 := by
  obtain ⟨K, C, hV, hVC⟩ := toy_lipschitz ![-1, -1] ![1, 1]
  have hd : ∀ p : Phase, DifferentiableAt ℝ toyH p := fun p =>
    (hasFDerivAt_toyH p).differentiableAt
  obtain ⟨w, hw0, hw⟩ := twoTorus_confinement (flatTorus (-1 / 2)) (flatTorus (1 / 2)) hV hVC
    (by unfold toyH; fun_prop) (fun p _ => hd p) (fun p _ => by simp [fderiv_toyH, toyV])
    (m := 1) one_pos (fun p _ => by simp [fderiv_toyH])
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (by norm_num) (by norm_num)
    (fun θ a _ _ => ⟨fun h => by simp [toyH, h], fun h => by simp [toyH, h]⟩)
    (w₀ := (0, ![0, 0]))
    ⟨fun j => by fin_cases j <;> norm_num, fun j => by fin_cases j <;> norm_num⟩
    (by simp [toyH]) (by norm_num [GraphTorus.graph₁, flatTorus])
    (by norm_num [GraphTorus.graph₁, flatTorus])
  refine ⟨w, hw0, fun t => ⟨(hw t).1, ?_, ?_⟩⟩
  · simpa [GraphTorus.graph₁, flatTorus] using (hw t).2.2.2.1
  · simpa [GraphTorus.graph₁, flatTorus] using (hw t).2.2.2.2

end KAM.Application.Tests.Confinement
