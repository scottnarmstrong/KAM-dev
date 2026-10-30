/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Recon2.Curve

/-!
# PDE solutions on invariant tori (blueprint `bpW:w2:main`, `bpW:w2:clause5`)

Infrastructure used by several nodes; the dependency graph is still being built. Blueprint labels
`bpW:w2:main`, `bpW:w2:clause5` (milestone W2).

* `KAM.Wave.reconWave_main` (Theorem `bpW:w2:main`): for `K : ℝ² → WaveSpace` with
  `IsAnalyticTorusEmbedding K` (only `.2.1` is used), the frozen clause (4) along `ν`, and
  `‖K θ‖ ≤ B`, every `θ₀` gives the four conjuncts of the frozen clause (5) of `KAM.Wave.nlw2`
  (for `K I := K`, `ν I := ν`), the last with bound `M_m B` (`KAM.Wave.reconWaveBound`).
  `KAM.Wave.reconWave_main_le` is the same with an arbitrary bound `R ≥ M_m B` in the last
  conjunct, so that `R = C * Real.sqrt (I 0 + I 1)` gives the frozen text verbatim.
* `KAM.Wave.reconWave_clause5` (Corollary `bpW:w2:clause5`): the common constant
  `C = max 1 M_m * C₃`, with the bound in clause (3) and the clause (5) of `nlw2` verbatim.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

lemma reconWaveBound_nonneg (m : ℝ) : 0 ≤ reconWaveBound m := by
  unfold reconWaveBound
  have := reconWaveC0_nonneg
  positivity

/-- **PDE solutions on invariant tori** (blueprint `bpW:w2:main`). The conclusions are the four
conjuncts of the frozen clause (5) of `KAM.Wave.nlw2`, for `K I := K` and `ν I := ν`, with the last
bound `M_m B` in place of `C * Real.sqrt (I 0 + I 1)`. -/
theorem reconWave_main {m : ℝ} (hm : 0 < m) {K : (Fin 2 → ℝ) → WaveSpace} {ν : Fin 2 → ℝ}
    {B : ℝ} (hemb : IsAnalyticTorusEmbedding K)
    (hinv : ∀ (θ : Fin 2 → ℝ) (j : ℕ+),
      HasDerivAt (fun t : ℝ => coeff (K (θ + t • ν)).1 j)
        (lam m hm j * coeff (K θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (K (θ + t • ν)).2 j)
        (-(lam m hm j * coeff (K θ).1 j) - cubicGrad m hm (K θ).1 j) 0)
    (hbd : ∀ θ : Fin 2 → ℝ, ‖K θ‖ ≤ B) (θ₀ : Fin 2 → ℝ) :
    (∀ z ∈ Set.univ ×ˢ Set.Icc 0 Real.pi,
      AnalyticAt ℝ (fun z : ℝ × ℝ => reconU m hm (K (θ₀ + z.1 • ν)).1 z.2) z) ∧
    IsClassicalSolution m hm (fun t x => reconU m hm (K (θ₀ + t • ν)).1 x) ∧
    (∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
      HasDerivAt (fun s => reconU m hm (K (θ₀ + s • ν)).1 x)
        (reconV m hm (K (θ₀ + t • ν)).2 x) t) ∧
    ∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
      |reconU m hm (K (θ₀ + t • ν)).1 x| +
        |derivWithin (reconU m hm (K (θ₀ + t • ν)).1) (Set.Icc 0 Real.pi) x| +
        |reconV m hm (K (θ₀ + t • ν)).2 x| ≤ reconWaveBound m * B := by
  have hY := isAnalyticCoeffSolution_orbit hm hemb.2.1 hinv θ₀
  refine ⟨fun z _ => analyticAt_reconWave_u hY z, isClassicalSolution_reconWave hY,
    fun t x _ => hasDerivAt_reconWave_ut hY t x, fun t x hx => ?_⟩
  refine (reconWave_bound (fun t : ℝ => K (θ₀ + t • ν)) t hx).2.trans ?_
  exact mul_le_mul_of_nonneg_left (hbd _) (reconWaveBound_nonneg m)

/-- `KAM.Wave.reconWave_main` with the last bound relaxed to any `R ≥ M_m B`. -/
theorem reconWave_main_le {m : ℝ} (hm : 0 < m) {K : (Fin 2 → ℝ) → WaveSpace} {ν : Fin 2 → ℝ}
    {B R : ℝ} (hemb : IsAnalyticTorusEmbedding K)
    (hinv : ∀ (θ : Fin 2 → ℝ) (j : ℕ+),
      HasDerivAt (fun t : ℝ => coeff (K (θ + t • ν)).1 j)
        (lam m hm j * coeff (K θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (K (θ + t • ν)).2 j)
        (-(lam m hm j * coeff (K θ).1 j) - cubicGrad m hm (K θ).1 j) 0)
    (hbd : ∀ θ : Fin 2 → ℝ, ‖K θ‖ ≤ B) (hR : reconWaveBound m * B ≤ R)
    (θ₀ : Fin 2 → ℝ) :
    (∀ z ∈ Set.univ ×ˢ Set.Icc 0 Real.pi,
      AnalyticAt ℝ (fun z : ℝ × ℝ => reconU m hm (K (θ₀ + z.1 • ν)).1 z.2) z) ∧
    IsClassicalSolution m hm (fun t x => reconU m hm (K (θ₀ + t • ν)).1 x) ∧
    (∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
      HasDerivAt (fun s => reconU m hm (K (θ₀ + s • ν)).1 x)
        (reconV m hm (K (θ₀ + t • ν)).2 x) t) ∧
    ∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
      |reconU m hm (K (θ₀ + t • ν)).1 x| +
        |derivWithin (reconU m hm (K (θ₀ + t • ν)).1) (Set.Icc 0 Real.pi) x| +
        |reconV m hm (K (θ₀ + t • ν)).2 x| ≤ R := by
  obtain ⟨a, b, c, d⟩ := reconWave_main hm hemb hinv hbd θ₀
  exact ⟨a, b, c, fun t x hx => (d t x hx).trans hR⟩

/-- **Clause (5) with the common constant** (blueprint `bpW:w2:clause5`): with
`C = max 1 M_m * C₃`, the bound of the frozen clause (3) holds with `C`, and the frozen clause (5)
of `KAM.Wave.nlw2` holds verbatim with the same `C`. -/
theorem reconWave_clause5 {m : ℝ} (hm : 0 < m) {C₃ : ℝ} (hC₃ : 0 < C₃)
    {Γ : Set (Fin 2 → ℝ)} {ν : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace}
    (hemb : ∀ I ∈ Γ, IsAnalyticTorusEmbedding (K I))
    (hbd : ∀ I ∈ Γ, ∀ θ : Fin 2 → ℝ, ‖K I θ‖ ≤ C₃ * Real.sqrt (I 0 + I 1))
    (hinv : ∀ I ∈ Γ, ∀ θ : Fin 2 → ℝ, ∀ j : ℕ+,
      HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).1 j)
        (lam m hm j * coeff (K I θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).2 j)
        (-(lam m hm j * coeff (K I θ).1 j) - cubicGrad m hm (K I θ).1 j) 0) :
    ∃ C : ℝ, C = max 1 (reconWaveBound m) * C₃ ∧ 0 < C ∧ C₃ ≤ C ∧
      (∀ I ∈ Γ, ∀ θ : Fin 2 → ℝ, ‖K I θ‖ ≤ C * Real.sqrt (I 0 + I 1)) ∧
      (∀ I ∈ Γ, ∀ θ₀ : Fin 2 → ℝ,
        (∀ z ∈ Set.univ ×ˢ Set.Icc 0 Real.pi,
          AnalyticAt ℝ (fun z : ℝ × ℝ => reconU m hm (K I (θ₀ + z.1 • ν I)).1 z.2) z) ∧
        IsClassicalSolution m hm (fun t x => reconU m hm (K I (θ₀ + t • ν I)).1 x) ∧
        (∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
          HasDerivAt (fun s => reconU m hm (K I (θ₀ + s • ν I)).1 x)
            (reconV m hm (K I (θ₀ + t • ν I)).2 x) t) ∧
        ∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
          |reconU m hm (K I (θ₀ + t • ν I)).1 x| +
            |derivWithin (reconU m hm (K I (θ₀ + t • ν I)).1) (Set.Icc 0 Real.pi) x| +
            |reconV m hm (K I (θ₀ + t • ν I)).2 x| ≤ C * Real.sqrt (I 0 + I 1)) := by
  have hmax : 1 ≤ max 1 (reconWaveBound m) := le_max_left _ _
  have hC₃C : C₃ ≤ max 1 (reconWaveBound m) * C₃ := by nlinarith
  refine ⟨max 1 (reconWaveBound m) * C₃, rfl, by linarith, hC₃C, fun I hI θ => ?_,
    fun I hI θ₀ => ?_⟩
  · exact (hbd I hI θ).trans (mul_le_mul_of_nonneg_right hC₃C (Real.sqrt_nonneg _))
  · refine reconWave_main_le hm (hemb I hI) (hinv I hI) (hbd I hI) ?_ θ₀
    have h1 : reconWaveBound m * C₃ ≤ max 1 (reconWaveBound m) * C₃ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hC₃.le
    calc reconWaveBound m * (C₃ * Real.sqrt (I 0 + I 1))
        = (reconWaveBound m * C₃) * Real.sqrt (I 0 + I 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)

end KAM.Wave

end
