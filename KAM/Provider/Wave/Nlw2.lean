/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Wave.Defs.CubicGrad
public import KAM.Frozen.Wave.Defs.IsAnalyticTorusEmbedding
public import KAM.Frozen.Wave.Defs.IsClassicalSolution
public import KAM.Frozen.Wave.Defs.LinearTorus
public import KAM.Frozen.Wave.Defs.ReconV
import KAM.Wave.Assembly.Nlw2Proof

/-!
# Provider for the frozen theorem `KAM.Wave.nlw2`

The proof of `KAM.Wave.nlw2` is assembled here as `KAM.Provider.Wave.nlw2`, from graph predecessors
and approved external inputs only. While the frozen anchor is `DRAFT_SORRY`, this module is
quarantined: no module other than the anchor may import it.

* `KAM.Provider.Wave.nlw2` has exactly the type of the frozen `KAM.Wave.nlw2` (statement copied
  verbatim from `KAM/Frozen/Wave/Theorems/Nlw2.lean`). It is `KAM.Wave.nlw2_proof`
  (`KAM/Wave/Assembly/Nlw2Proof.lean`, blueprint `bpW:w8:nlw2-proof`). This module does not import
  the frozen theorem.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace KAM.Provider.Wave

open KAM KAM.Wave

/-- **W-NLW2.** The provider of the frozen `KAM.Wave.nlw2`, with exactly its type. -/
theorem nlw2 {m : ℝ} (hm : 0 < m) :
    ∃ (r₀ C τ : ℝ) (η : ℝ → ℝ) (Γ : Set (Fin 2 → ℝ)) (ν : (Fin 2 → ℝ) → Fin 2 → ℝ)
      (K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace),
      0 < r₀ ∧ 0 < C ∧ 1 < τ ∧
      (∀ r ∈ Set.Ioo 0 r₀, 0 ≤ η r) ∧ Tendsto η (𝓝[>] 0) (𝓝 0) ∧
      MeasurableSet Γ ∧ Γ ⊆ {I | (∀ i, 0 < I i) ∧ Real.sqrt (I 0 + I 1) < r₀} ∧
      ContinuousOn ν Γ ∧ ContinuousOn (Function.uncurry K) (Γ ×ˢ Set.univ) ∧
      -- (1) density one in actions
      Tendsto (fun h : ℝ => volume (Γ ∩ Metric.ball 0 h) /
          volume ({I : Fin 2 → ℝ | ∀ i, 0 < I i} ∩ Metric.ball 0 h)) (𝓝[>] 0) (𝓝 1) ∧
      -- (2) two independent frequencies
      (∀ I ∈ Γ, ∃ γ : ℝ, 0 < γ ∧ KAM.IsDiophantine γ τ (ν I)) ∧
      Tendsto ν (𝓝[Γ] 0) (𝓝 fun i => lam m hm (i : ℕ).succPNat / (2 * Real.pi)) ∧
      -- (3) small embedded tori
      (∀ (I : Fin 2 → ℝ) (hI : ∀ i, 0 < I i), I ∈ Γ → IsAnalyticTorusEmbedding (K I) ∧
        (∀ θ, ‖K I θ - linearTorus I hI θ‖ ≤
          η (Real.sqrt (I 0 + I 1)) * Real.sqrt (I 0 + I 1)) ∧
        ∀ θ, ‖K I θ‖ ≤ C * Real.sqrt (I 0 + I 1)) ∧
      -- (4) exact invariance
      (∀ I ∈ Γ, ∀ θ : Fin 2 → ℝ, ∀ j : ℕ+,
        HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).1 j)
          (lam m hm j * coeff (K I θ).2 j) 0 ∧
        HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).2 j)
          (-(lam m hm j * coeff (K I θ).1 j) - cubicGrad m hm (K I θ).1 j) 0) ∧
      -- (5) PDE solutions
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
            |reconV m hm (K I (θ₀ + t • ν I)).2 x| ≤ C * Real.sqrt (I 0 + I 1)) ∧
      -- (6) family injectivity
      ∀ I ∈ Γ, ∀ I' ∈ Γ, ∀ θ θ' : Fin 2 → ℝ, K I θ = K I' θ' →
        I = I' ∧ ∃ k : Fin 2 → ℤ, θ - θ' = fun i => (k i : ℝ) :=
  KAM.Wave.nlw2_proof hm

end KAM.Provider.Wave

end
