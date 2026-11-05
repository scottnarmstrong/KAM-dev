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
  stays strictly between the tori, `−1/2 < a₁ < 1/2`, and it is the only global solution.
* `tilt_confined`: the tilted toy `H(θ, a) = −a₂ + a₁/4` (field `((1/4, −1), 0)`), whose level
  `H = 0` is the tilted plane `a₂ = a₁/4`, with the flat tori `a = ∓(1/2, 1/8)` on it; the faces
  `a₂ = ±1` of the box `[−1, 1]²` are kept off the level by `face_of_cone` (`M = 1/4`, `m = 1`).
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
times, stays strictly between the flat tori `a₁ = −1/2` and `a₁ = 1/2`, and is the only global
solution through that point. -/
theorem toy_confined :
    ∃ w : ℝ → Phase, w 0 = (0, ![0, 0]) ∧ (∀ t, HasDerivAt w (toyV (w t)) t ∧
      -1 / 2 < (w t).2 0 ∧ (w t).2 0 < 1 / 2) ∧
      ∀ w' : ℝ → Phase, w' 0 = (0, ![0, 0]) → (∀ t, HasDerivAt w' (toyV (w' t)) t) → w' = w := by
  obtain ⟨K, C, hV, hVC⟩ := toy_lipschitz ![-1, -1] ![1, 1]
  have hd : ∀ p : Phase, DifferentiableAt ℝ toyH p := fun p =>
    (hasFDerivAt_toyH p).differentiableAt
  obtain ⟨w, hw0, hw, huniq⟩ := twoTorus_confinement (flatTorus (-1 / 2)) (flatTorus (1 / 2))
    hV hVC (fun p _ => hd p) (fun p _ => by simp [fderiv_toyH, toyV])
    (m := 1) one_pos (fun p _ => by simp [fderiv_toyH])
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (by norm_num) (by norm_num)
    (fun θ a _ _ => ⟨fun h => by simp [toyH, h], fun h => by simp [toyH, h]⟩)
    (w₀ := (0, ![0, 0]))
    ⟨fun j => by fin_cases j <;> norm_num, fun j => by fin_cases j <;> norm_num⟩
    (by simp [toyH]) (by norm_num [GraphTorus.graph₁, flatTorus])
    (by norm_num [GraphTorus.graph₁, flatTorus])
  refine ⟨w, hw0, fun t => ⟨(hw t).1, ?_, ?_⟩, huniq⟩
  · simpa [GraphTorus.graph₁, flatTorus] using (hw t).2.2.2.1
  · simpa [GraphTorus.graph₁, flatTorus] using (hw t).2.2.2.2

/-- The tilted toy Hamiltonian `H(θ, a) = −a₂ + a₁/4`. -/
def tiltH (p : Phase) : ℝ := -p.2 1 + p.2 0 / 4

/-- Its Hamiltonian field `((1/4, −1), 0)`. -/
def tiltV (_ : Phase) : Phase := (![1 / 4, -1], 0)

/-- The linear map `(θ, a) ↦ −a₂ + a₁/4`. -/
def tiltL : Phase →L[ℝ] ℝ :=
  -((ContinuousLinearMap.proj (1 : Fin 2)).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))) +
    (1 / 4 : ℝ) • (ContinuousLinearMap.proj (0 : Fin 2)).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

theorem tiltH_eq : tiltH = ⇑tiltL := by
  funext p
  simp [tiltH, tiltL]
  ring

theorem fderiv_tiltH (p v : Phase) : fderiv ℝ tiltH p v = -v.2 1 + v.2 0 / 4 := by
  rw [tiltH_eq, tiltL.fderiv]
  simp [tiltL]
  ring

theorem differentiableAt_tiltH (p : Phase) : DifferentiableAt ℝ tiltH p := by
  rw [tiltH_eq]
  exact tiltL.differentiableAt

/-- The flat torus `a = (c, c/4)`: a graph torus of the tilted field on the level `H = 0`. -/
def tiltTorus (c : ℝ) : GraphTorus tiltV tiltH 0 ![c, c / 4] ![c, c / 4] where
  k θ := (θ, ![c, c / 4])
  Θ := id
  ν := ![1 / 4, -1]
  continuous_k := continuous_id.prodMk continuous_const
  continuous_Θ := continuous_id
  angle_Θ _ := rfl
  Θ_angle _ := rfl
  hasDerivAt_orbit θ t := by
    have h := (((hasDerivAt_id t).smul_const (![1 / 4, -1] : Fin 2 → ℝ)).const_add θ).prodMk
      (hasDerivAt_const t (![c, c / 4] : Fin 2 → ℝ))
    simpa [tiltV] using h
  energy _ := by simp [tiltH]
  mem_Icc _ := ⟨le_rfl, le_rfl⟩

/-- **The tilted toy confinement**: the solution of the tilted field through `(0, (0, 0))` exists
for all times, stays strictly between the flat tori `a = −(1/2, 1/8)` and `a = (1/2, 1/8)` and
strictly inside the box `[−1, 1]²`, and is the only global solution through that point; the faces
`a₂ = ±1` come from `face_of_cone`. -/
theorem tilt_confined :
    ∃ w : ℝ → Phase, w 0 = (0, ![0, 0]) ∧ (∀ t, HasDerivAt w (tiltV (w t)) t ∧
      -1 / 2 < (w t).2 0 ∧ (w t).2 0 < 1 / 2 ∧ -1 < (w t).2 1 ∧ (w t).2 1 < 1) ∧
      ∀ w' : ℝ → Phase, w' 0 = (0, ![0, 0]) → (∀ t, HasDerivAt w' (tiltV (w' t)) t) →
        w' = w := by
  obtain ⟨K, C, hV, hVC⟩ : ∃ K, ∃ C : ℝ, LipschitzOnWith K tiltV (boxSet ![-1, -1] ![1, 1]) ∧
      ∀ p ∈ boxSet ![-1, -1] ![1, 1], ‖tiltV p‖ ≤ C :=
    exists_lipschitzOnWith_of_periodic isOpen_univ (subset_univ _) contDiffOn_const
      fun _ _ => rfl
  have hHd : ∀ p ∈ boxSet (![-1, -1] : Fin 2 → ℝ) ![1, 1], DifferentiableAt ℝ tiltH p :=
    fun p _ => differentiableAt_tiltH p
  have hHm : ∀ p ∈ boxSet (![-1, -1] : Fin 2 → ℝ) ![1, 1],
      fderiv ℝ tiltH p ((0 : Fin 2 → ℝ), Pi.single 1 1) ≤ -1 :=
    fun p _ => by simp [fderiv_tiltH]
  have hface := face_of_cone (E := 0) (m := 1) (M := 1 / 4) (Wd := 1 / 2) (x₀ := -1 / 2)
    (x₁ := 1 / 2) (lo := 0) (hi := 0) hHd hHm
    (fun p _ => by norm_num [fderiv_tiltH, abs_of_pos]) zero_le_one
    (fun θ => ⟨(θ, 0), rfl, ⟨le_rfl, le_rfl⟩, by simp [tiltH]⟩)
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨w, hw0, hw, huniq⟩ := twoTorus_confinement (tiltTorus (-1 / 2)) (tiltTorus (1 / 2))
    hV hVC hHd (fun p _ => by simp [fderiv_tiltH, tiltV]) one_pos hHm
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (by norm_num) (by norm_num)
    (fun θ a h₀ h₁ => hface θ a (by simpa using h₀) (by simpa using h₁))
    (w₀ := (0, ![0, 0]))
    ⟨fun j => by fin_cases j <;> norm_num, fun j => by fin_cases j <;> norm_num⟩
    (by simp [tiltH]) (by norm_num [GraphTorus.graph₁, tiltTorus])
    (by norm_num [GraphTorus.graph₁, tiltTorus])
  refine ⟨w, hw0, fun t => ⟨(hw t).1, ?_, ?_, ?_, ?_⟩, huniq⟩
  · simpa [GraphTorus.graph₁, tiltTorus] using (hw t).2.2.2.1
  · simpa [GraphTorus.graph₁, tiltTorus] using (hw t).2.2.2.2
  · simpa using ((hw t).2.1 1).1
  · simpa using ((hw t).2.1 1).2

end KAM.Application.Tests.Confinement
