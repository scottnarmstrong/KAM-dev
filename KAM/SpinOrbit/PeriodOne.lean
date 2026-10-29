/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Model

/-!
# The period-one normalization of the lunar model (track SO, package SO-MODEL)

Proposal §2.2. With `x = 2π q`, `f = 2π φ` and time `s = 2π t` (orbital mean motion one radian per
unit time), the period-one system `q̇ = p`, `ṗ = -∂_q V`, `φ̇ = 1` is equivalent to the radian
system `dx/ds = y`, `dy/ds = -∂_x V_rad(x, f)`, `df/ds = 1`, where
`V_rad(x, f) = -ε Σ A_m cos (2x - m f)` and `y = p` (the momentum is the same number in both
conventions).

* `soV_eq_soVrad`: `V(q, φ) = V_rad(2π q, 2π φ)`.
* `soVq_eq_two_pi_mul_soVradx`: `∂_q V(q, φ) = 2π ∂_x V_rad(2π q, 2π φ)`; this is the force
  scaling: the force is divided by `2π` when time is rescaled by `2π` (`dp/ds = (1/2π) dp/dt`).
* `soToRad`/`soFromRad` and `isSoRadSolution_iff`: the change of variables, both directions.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit

/-- The potential in the radian convention, `V_rad(x, f) = -ε Σ A_m cos (2x - m f)`. -/
def soVrad (x f : ℝ) : ℝ :=
  -soEps * ∑ m ∈ soModes, soA m * Real.cos (2 * x - m * f)

/-- `∂_x V_rad = 2ε Σ A_m sin (2x - m f)`. -/
def soVradx (x f : ℝ) : ℝ :=
  2 * soEps * ∑ m ∈ soModes, soA m * Real.sin (2 * x - m * f)

theorem soV_eq_soVrad (q φ : ℝ) : soV q φ = soVrad (2 * π * q) (2 * π * φ) := by
  unfold soV soVrad
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 2; ring

theorem soVq_eq_two_pi_mul_soVradx (q φ : ℝ) :
    soVq q φ = 2 * π * soVradx (2 * π * q) (2 * π * φ) := by
  unfold soVq soVradx
  have : ∀ m : ℕ, 2 * π * (2 * q - m * φ) = 2 * (2 * π * q) - m * (2 * π * φ) := fun m => by ring
  simp only [this]
  ring

theorem soVrad_eq_soV (x f : ℝ) : soVrad x f = soV (x / (2 * π)) (f / (2 * π)) := by
  rw [soV_eq_soVrad]
  have h : (2 * π) ≠ 0 := by positivity
  congr 1 <;> field_simp

theorem hasDerivAt_soVrad_x (x f : ℝ) : HasDerivAt (fun y => soVrad y f) (soVradx x f) x := by
  have h2 : (2 * π) ≠ 0 := by positivity
  have hd := hasDerivAt_soV_comp (a := fun y : ℝ => y / (2 * π)) (b := fun _ => f / (2 * π))
    ((hasDerivAt_id x).div_const (2 * π)) (hasDerivAt_const x (f / (2 * π)))
  have hv : soVq (x / (2 * π)) (f / (2 * π)) = 2 * π * soVradx x f := by
    rw [soVq_eq_two_pi_mul_soVradx]; congr 3 <;> field_simp
  simp only [soVrad_eq_soV]
  convert hd using 1
  rw [hv]; simp; field_simp

/-! ### The radian system and the change of variables -/

/-- `(x, y, f)` solves the radian-convention system on `ℝ` (time `s`, orbital mean motion one
radian per unit time): `x' = y`, `y' = -∂_x V_rad(x, f)`, `f' = 1`. -/
def IsSoRadSolution (x y f : ℝ → ℝ) : Prop :=
  ∀ s, HasDerivAt x (y s) s ∧ HasDerivAt y (-soVradx (x s) (f s)) s ∧ HasDerivAt f 1 s

/-- A period-one solution rescaled to the radian convention: `x(s) = 2π q(s/2π)`,
`y(s) = p(s/2π)`, `f(s) = 2π φ(s/2π)`. -/
def soToRad (q p φ : ℝ → ℝ) : (ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ) :=
  (fun s => 2 * π * q (s / (2 * π)), fun s => p (s / (2 * π)), fun s => 2 * π * φ (s / (2 * π)))

/-- A radian solution rescaled to period one: `q(t) = x(2πt)/2π`, `p(t) = y(2πt)`,
`φ(t) = f(2πt)/2π`. -/
def soFromRad (x y f : ℝ → ℝ) : (ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ) :=
  (fun t => x (2 * π * t) / (2 * π), fun t => y (2 * π * t), fun t => f (2 * π * t) / (2 * π))

theorem soFromRad_soToRad (q p φ : ℝ → ℝ) :
    soFromRad (soToRad q p φ).1 (soToRad q p φ).2.1 (soToRad q p φ).2.2 = (q, p, φ) := by
  have h : (2 * π) ≠ 0 := by positivity
  have e : ∀ t : ℝ, 2 * π * t / (2 * π) = t := fun t => by field_simp
  simp only [soFromRad, soToRad, e]

theorem soToRad_soFromRad (x y f : ℝ → ℝ) :
    soToRad (soFromRad x y f).1 (soFromRad x y f).2.1 (soFromRad x y f).2.2 = (x, y, f) := by
  have h : (2 * π) ≠ 0 := by positivity
  have e : ∀ t : ℝ, 2 * π * (t / (2 * π)) = t := fun t => by field_simp
  simp only [soFromRad, soToRad, e]

theorem hasDerivAt_comp_div {g : ℝ → ℝ} {d s c : ℝ} (h : HasDerivAt g d (s / c)) :
    HasDerivAt (fun s => g (s / c)) (d / c) s := by
  have := h.comp s ((hasDerivAt_id s).div_const c)
  simpa [Function.comp_def, div_eq_mul_inv] using this

theorem hasDerivAt_comp_mul {g : ℝ → ℝ} {d t c : ℝ} (h : HasDerivAt g d (c * t)) :
    HasDerivAt (fun t => g (c * t)) (d * c) t := by
  have := h.comp t ((hasDerivAt_id t).const_mul c)
  simpa [Function.comp_def] using this

theorem isSoRadSolution_soToRad {q p φ : ℝ → ℝ} (h : IsSoSolution q p φ) :
    IsSoRadSolution (soToRad q p φ).1 (soToRad q p φ).2.1 (soToRad q p φ).2.2 := by
  rw [isSoSolution_iff] at h
  have h2 : (2 * π) ≠ 0 := by positivity
  intro s
  obtain ⟨h1, h2', h3⟩ := h (s / (2 * π))
  simp only [soToRad]
  refine ⟨?_, ?_, ?_⟩
  · exact ((hasDerivAt_comp_div h1).const_mul (2 * π)).congr_deriv (by field_simp)
  · refine (hasDerivAt_comp_div h2').congr_deriv ?_
    rw [soVq_eq_two_pi_mul_soVradx]
    field_simp
  · exact ((hasDerivAt_comp_div h3).const_mul (2 * π)).congr_deriv (by field_simp)

theorem isSoSolution_soFromRad {x y f : ℝ → ℝ} (h : IsSoRadSolution x y f) :
    IsSoSolution (soFromRad x y f).1 (soFromRad x y f).2.1 (soFromRad x y f).2.2 := by
  rw [isSoSolution_iff]
  have h2 : (2 * π) ≠ 0 := by positivity
  intro t
  obtain ⟨h1, h2', h3⟩ := h (2 * π * t)
  simp only [soFromRad]
  refine ⟨?_, ?_, ?_⟩
  · exact ((hasDerivAt_comp_mul h1).div_const (2 * π)).congr_deriv (by field_simp)
  · refine (hasDerivAt_comp_mul h2').congr_deriv ?_
    rw [soVq_eq_two_pi_mul_soVradx]
    have e1 : 2 * π * (x (2 * π * t) / (2 * π)) = x (2 * π * t) := by field_simp
    have e2 : 2 * π * (f (2 * π * t) / (2 * π)) = f (2 * π * t) := by field_simp
    rw [e1, e2]; ring
  · exact ((hasDerivAt_comp_mul h3).div_const (2 * π)).congr_deriv (by field_simp)

/-- The change of variables of proposal §2.2, including the force scaling: a triple solves the
period-one system iff its rescaling solves the radian system. -/
theorem isSoRadSolution_iff (q p φ : ℝ → ℝ) :
    IsSoSolution q p φ ↔
      IsSoRadSolution (soToRad q p φ).1 (soToRad q p φ).2.1 (soToRad q p φ).2.2 := by
  refine ⟨isSoRadSolution_soToRad, fun h => ?_⟩
  have := isSoSolution_soFromRad h
  rwa [soFromRad_soToRad] at this

end KAM.SpinOrbit

end
