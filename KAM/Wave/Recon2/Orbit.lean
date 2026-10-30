/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Coordinatewise
public import KAM.Frozen.Wave.Defs.IsAnalyticTorusEmbedding
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Analytic coefficient solutions and torus orbits (blueprint `bpW:w2:coeffsol`, `bpW:w2:orbit`,
`bpW:w2:curve-deriv`)

Infrastructure used by several nodes; the dependency graph is still being built. Blueprint labels
`bpW:w2:coeffsol`, `bpW:w2:orbit`, `bpW:w2:curve-deriv` (milestone W2).

* `KAM.Wave.IsAnalyticCoeffSolution m hm Y` (Definition `bpW:w2:coeffsol`): `Y : ℝ → WaveSpace` is
  analytic and its coefficients solve the system `κ(Y₁)' = λ κ(Y₂)`,
  `κ(Y₂)' = -λ κ(Y₁) - 𝒢(Y₁)` pointwise (`HasDerivAt`);
* `KAM.Wave.isAnalyticCoeffSolution_orbit` (Lemma `bpW:w2:orbit`): the orbit
  `t ↦ K (θ₀ + t ν)` of an analytic `K` satisfying the frozen clause (4) is one;
* `KAM.Wave.hasDerivAt_coeffSol_fst`, `KAM.Wave.coeff_deriv_coeffSol_fst`, … (Lemma
  `bpW:w2:curve-deriv`): the curve derivatives and their coefficients.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- **Analytic coefficient solution** (blueprint `bpW:w2:coeffsol`): `Y` is real analytic at every
`t`, and the coefficient curves have the derivatives prescribed by the system `bpW:w0:coeffsys`. -/
def IsAnalyticCoeffSolution (m : ℝ) (hm : 0 < m) (Y : ℝ → WaveSpace) : Prop :=
  (∀ t : ℝ, AnalyticAt ℝ Y t) ∧
  ∀ (t : ℝ) (j : ℕ+),
    HasDerivAt (fun s : ℝ => coeff (Y s).1 j) (lam m hm j * coeff (Y t).2 j) t ∧
    HasDerivAt (fun s : ℝ => coeff (Y s).2 j)
      (-(lam m hm j * coeff (Y t).1 j) - cubicGrad m hm (Y t).1 j) t

/-- **Torus orbits are analytic coefficient solutions** (blueprint `bpW:w2:orbit`). The invariance
hypothesis is the frozen clause (4) of `KAM.Wave.nlw2` for one torus. -/
theorem isAnalyticCoeffSolution_orbit {m : ℝ} (hm : 0 < m) {K : (Fin 2 → ℝ) → WaveSpace}
    {ν : Fin 2 → ℝ} (hK : AnalyticOnNhd ℝ K Set.univ)
    (hinv : ∀ (θ : Fin 2 → ℝ) (j : ℕ+),
      HasDerivAt (fun t : ℝ => coeff (K (θ + t • ν)).1 j)
        (lam m hm j * coeff (K θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (K (θ + t • ν)).2 j)
        (-(lam m hm j * coeff (K θ).1 j) - cubicGrad m hm (K θ).1 j) 0)
    (θ₀ : Fin 2 → ℝ) :
    IsAnalyticCoeffSolution m hm (fun t : ℝ => K (θ₀ + t • ν)) := by
  refine ⟨fun t => ?_, fun t j => ?_⟩
  · have hlin : AnalyticAt ℝ (fun t : ℝ => θ₀ + t • ν) t :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    exact AnalyticAt.comp (g := K) (f := fun t : ℝ => θ₀ + t • ν) (hK (θ₀ + t • ν) trivial) hlin
  · have hs : ∀ s : ℝ, θ₀ + t • ν + (s - t) • ν = θ₀ + s • ν := fun s => by
      rw [add_assoc, ← add_smul]; congr 2; ring
    obtain ⟨h1, h2⟩ := hinv (θ₀ + t • ν) j
    have g1 := HasDerivAt.comp_sub_const t t
      (f := fun h : ℝ => coeff (K (θ₀ + t • ν + h • ν)).1 j) (by rw [sub_self]; exact h1)
    have g2 := HasDerivAt.comp_sub_const t t
      (f := fun h : ℝ => coeff (K (θ₀ + t • ν + h • ν)).2 j) (by rw [sub_self]; exact h2)
    simp only [hs] at g1 g2
    exact ⟨g1, g2⟩

section Curve

variable {m : ℝ} {hm : 0 < m} {Y : ℝ → WaveSpace}

lemma hasDerivAt_coeffSol (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) :
    HasDerivAt Y (deriv Y t) t :=
  (hY.1 t).differentiableAt.hasDerivAt

/-- `Y₁ = (Y ·).1` is differentiable at `t` with derivative `deriv (fun s => (Y s).1) t`
(blueprint `bpW:w2:curve-deriv`). -/
lemma hasDerivAt_coeffSol_fst (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) :
    HasDerivAt (fun s => (Y s).1) (deriv (fun s => (Y s).1) t) t :=
  ((ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2)
    (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt (Y t) |>.comp (hY.1 t)).differentiableAt.hasDerivAt

lemma hasDerivAt_coeffSol_snd (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) :
    HasDerivAt (fun s => (Y s).2) (deriv (fun s => (Y s).2) t) t :=
  ((ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2)
    (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt (Y t) |>.comp (hY.1 t)).differentiableAt.hasDerivAt

/-- `κ(Y₁'(t))_j = λ_j κ(Y₂(t))_j` (blueprint `bpW:w2:curve-deriv`). -/
theorem coeff_deriv_coeffSol_fst (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) (j : ℕ+) :
    coeff (deriv (fun s => (Y s).1) t) j = lam m hm j * coeff (Y t).2 j := by
  have h := hasDerivAt_coeffW (hasDerivAt_coeffSol_fst hY t) 1 1 j
  have e : ∀ z : lp (fun _ : ℕ+ => ℝ) 2, coeffW 1 1 z j = coeff z j := fun z => by
    rw [coeffW_one_one]
  simp only [e] at h
  exact h.unique (hY.2 t j).1

/-- `κ(Y₂'(t))_j = -λ_j κ(Y₁(t))_j - 𝒢(Y₁(t))_j` (blueprint `bpW:w2:curve-deriv`). -/
theorem coeff_deriv_coeffSol_snd (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) (j : ℕ+) :
    coeff (deriv (fun s => (Y s).2) t) j =
      -(lam m hm j * coeff (Y t).1 j) - cubicGrad m hm (Y t).1 j := by
  have h := hasDerivAt_coeffW (hasDerivAt_coeffSol_snd hY t) 1 1 j
  have e : ∀ z : lp (fun _ : ℕ+ => ℝ) 2, coeffW 1 1 z j = coeff z j := fun z => by
    rw [coeffW_one_one]
  simp only [e] at h
  exact h.unique (hY.2 t j).2

end Curve

end KAM.Wave

end
