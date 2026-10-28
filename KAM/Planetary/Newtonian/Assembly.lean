/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Newtonian.Reconstruction
public import KAM.Planetary.Newtonian.Tube
public import KAM.Frozen.Planetary.Defs.MovingKolmogorovSet
public import KAM.Frozen.Planetary.Defs.FixedKolmogorovSet

/-!
# Assembly of the Kolmogorov sets from the tube

Blueprint P, Part 6 (`bpP:p6:measure-positive` (a), `bpP:p6:movkol-assembly`,
`bpP:p6:fixkol-assembly`): the circular tube is bounded, so its measurable subsets have finite
volume; and the frozen predicates `MovingKolmogorovSet`, `FixedKolmogorovSet` follow from the
tube inclusion together with the torus predicate on each point's torus (the confinement to the
tube gives no collision, the pair bounds, and, through the orbit transfer, the Newton and
fixed-Sun solutions).

`bpP:p6:measure-positive` (b) is Part 1's `KAM.Planetary.measure_chart_image`
(`KAM/Planetary/Hamiltonian/Liouville.lean`), which is not re-declared here.
-/

public section

open MeasureTheory

namespace KAM.Planetary

open KAM KAM.Kepler

section Assembly

variable {n : ℕ}

/-- `bpP:p6:measure-positive` (a): the tube is bounded. -/
theorem circularTube_norm_lt {G m0 : ℝ} {m a : Fin n → ℝ} {η : ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (ha : ∀ i, 0 < a i) {z : Phase (n * 2)} (hz : z ∈ circularTube G m0 m a η) :
    ‖z.1‖ < (⨆ i, a i) + η ∧ ‖z.2‖ < (⨆ i, |m i| * √(G * m0 / a i)) + η := by
  have _ := hG
  have _ := hm0
  obtain ⟨φ, hφ⟩ := hz
  have h1 : ‖z.1 - (circularPoint G m0 m a φ).1‖ < η :=
    lt_of_le_of_lt (norm_fst_le (z - circularPoint G m0 m a φ)) hφ
  have h2 : ‖z.2 - (circularPoint G m0 m a φ).2‖ < η :=
    lt_of_le_of_lt (norm_snd_le (z - circularPoint G m0 m a φ)) hφ
  have hS1 : 0 ≤ ⨆ i, a i := Real.iSup_nonneg fun i => (ha i).le
  have hS2 : 0 ≤ ⨆ i, |m i| * √(G * m0 / a i) :=
    Real.iSup_nonneg fun i => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hq : ‖(circularPoint G m0 m a φ).1‖ ≤ ⨆ i, a i := by
    refine (pi_norm_le_iff_of_nonneg hS1).mpr fun k => ?_
    have hk : (circularPoint G m0 m a φ).1 k =
        a (finProdFinEquiv.symm k).1 * (![Real.cos (2 * Real.pi * φ (finProdFinEquiv.symm k).1),
          Real.sin (2 * Real.pi * φ (finProdFinEquiv.symm k).1)] : Fin 2 → ℝ)
            (finProdFinEquiv.symm k).2 := rfl
    rw [hk, Real.norm_eq_abs, abs_mul, abs_of_pos (ha _)]
    refine (le_ciSup (Set.finite_range a).bddAbove (finProdFinEquiv.symm k).1).trans' ?_
    have : |(![Real.cos (2 * Real.pi * φ (finProdFinEquiv.symm k).1),
          Real.sin (2 * Real.pi * φ (finProdFinEquiv.symm k).1)] : Fin 2 → ℝ)
            (finProdFinEquiv.symm k).2| ≤ 1 := by
      generalize (finProdFinEquiv.symm k).2 = c
      fin_cases c
      · exact Real.abs_cos_le_one _
      · exact Real.abs_sin_le_one _
    calc a _ * |_| ≤ a _ * 1 := mul_le_mul_of_nonneg_left this (ha _).le
      _ = a _ := mul_one _
  have hp : ‖(circularPoint G m0 m a φ).2‖ ≤ ⨆ i, |m i| * √(G * m0 / a i) := by
    refine (pi_norm_le_iff_of_nonneg hS2).mpr fun k => ?_
    have hk : (circularPoint G m0 m a φ).2 k =
        m (finProdFinEquiv.symm k).1 * √(G * m0 / a (finProdFinEquiv.symm k).1) *
          (![-Real.sin (2 * Real.pi * φ (finProdFinEquiv.symm k).1),
            Real.cos (2 * Real.pi * φ (finProdFinEquiv.symm k).1)] : Fin 2 → ℝ)
              (finProdFinEquiv.symm k).2 := rfl
    rw [hk, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine (le_ciSup (f := fun i => |m i| * √(G * m0 / a i)) (Set.finite_range _).bddAbove
      (finProdFinEquiv.symm k).1).trans' ?_
    have : |(![-Real.sin (2 * Real.pi * φ (finProdFinEquiv.symm k).1),
          Real.cos (2 * Real.pi * φ (finProdFinEquiv.symm k).1)] : Fin 2 → ℝ)
            (finProdFinEquiv.symm k).2| ≤ 1 := by
      generalize (finProdFinEquiv.symm k).2 = c
      fin_cases c
      · simpa using Real.abs_sin_le_one _
      · exact Real.abs_cos_le_one _
    calc |m _| * √(G * m0 / a _) * |_| ≤ |m _| * √(G * m0 / a _) * 1 :=
          mul_le_mul_of_nonneg_left this (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      _ = _ := mul_one _
  constructor
  · calc ‖z.1‖ = ‖(circularPoint G m0 m a φ).1 + (z.1 - (circularPoint G m0 m a φ).1)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖(circularPoint G m0 m a φ).1‖ + ‖z.1 - (circularPoint G m0 m a φ).1‖ := norm_add_le _ _
      _ < (⨆ i, a i) + η := by linarith
  · calc ‖z.2‖ = ‖(circularPoint G m0 m a φ).2 + (z.2 - (circularPoint G m0 m a φ).2)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖(circularPoint G m0 m a φ).2‖ + ‖z.2 - (circularPoint G m0 m a φ).2‖ := norm_add_le _ _
      _ < (⨆ i, |m i| * √(G * m0 / a i)) + η := by linarith

theorem volume_lt_top_of_subset_circularTube {G m0 : ℝ} {m a : Fin n → ℝ} {η : ℝ} (hG : 0 < G)
    (hm0 : 0 < m0) (ha : ∀ i, 0 < a i) {S : Set (Phase (n * 2))}
    (hS : S ⊆ circularTube G m0 m a η) : MeasureTheory.volume S < ⊤ := by
  refine Bornology.IsBounded.measure_lt_top ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max ((⨆ i, a i) + η) ((⨆ i, |m i| * √(G * m0 / a i)) + η), fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := circularTube_norm_lt hG hm0 ha (hS hz)
  rw [Prod.norm_def]
  exact max_le_max h1.le h2.le

/-! ### `bpP:p6:movkol-assembly`, `bpP:p6:fixkol-assembly` -/

theorem movingKolmogorovSet_of_tube {G m0 μ : ℝ} {m a : Fin n → ℝ} {γ A η : ℝ}
    (h : AxisData a γ A) (hη : 0 < η) (hn : 0 < n) (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) {S : Set (Phase (n * 2))} (hS : MeasurableSet S)
    (hSt : S ⊆ circularTube G m0 m a (tubeRadius η γ))
    (hS2 : ∀ z ∈ S, ∃ (w : Fin (n * 2) → ℝ) (K : (Fin (n * 2) → ℝ) → Phase (n * 2))
      (θ : Fin (n * 2) → ℝ), K θ = z ∧ Set.range K ⊆ S ∧
        IsPhysicalTorus (movingHamiltonian G m0 m μ) w K) :
    MovingKolmogorovSet G m0 m a μ η (tubeD γ) (tubeBigD γ A) S := by
  have _ := hn
  have hζ := tubeRadius_pos hη h.gap_pos
  have hζ' : tubeRadius η γ ≤ γ / 6 := min_le_right _ _
  refine ⟨hS, hSt.trans (circularTube_mono (min_le_left _ _)), fun z hz => ?_⟩
  obtain ⟨w, K, θ, hKz, hKS, hK⟩ := hS2 z hz
  have hmem : ∀ φ, K φ ∈ circularTube G m0 m a (tubeRadius η γ) := fun φ =>
    hSt (hKS ⟨φ, rfl⟩)
  have hnc : ∀ φ, NoCollision (K φ).1 := fun φ =>
    (circularTube_pair_bounds h hζ hζ' (hmem φ)).2.2
  exact ⟨w, K, θ, hKz, hKS, hK, hnc, orbit_transfer_moving hG hm0 hm hμ hK hnc,
    fun φ => circularTube_pairBounds_barycentric h hζ hζ' hm0 hm hμ (hmem φ)⟩

theorem fixedKolmogorovSet_of_tube {G m0 ε : ℝ} {m a : Fin n → ℝ} {γ A η : ℝ}
    (h : AxisData a γ A) (hη : 0 < η) (hn : 0 < n) (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) {S : Set (Phase (n * 2))} (hS : MeasurableSet S)
    (hSt : S ⊆ circularTube G m0 m a (tubeRadius η γ))
    (hS2 : ∀ z ∈ S, ∃ (w : Fin (n * 2) → ℝ) (K : (Fin (n * 2) → ℝ) → Phase (n * 2))
      (θ : Fin (n * 2) → ℝ), K θ = z ∧ Set.range K ⊆ S ∧
        IsPhysicalTorus (fixedHamiltonian G m0 m ε) w K) :
    FixedKolmogorovSet G m0 m a ε η (tubeD γ) (tubeBigD γ A) S := by
  have _ := hn
  have _ := hG
  have hζ := tubeRadius_pos hη h.gap_pos
  have hζ' : tubeRadius η γ ≤ γ / 6 := min_le_right _ _
  refine ⟨hS, hSt.trans (circularTube_mono (min_le_left _ _)), fun z hz => ?_⟩
  obtain ⟨w, K, θ, hKz, hKS, hK⟩ := hS2 z hz
  have hmem : ∀ φ, K φ ∈ circularTube G m0 m a (tubeRadius η γ) := fun φ =>
    hSt (hKS ⟨φ, rfl⟩)
  have hnc : ∀ φ, NoCollision (K φ).1 := fun φ =>
    (circularTube_pair_bounds h hζ hζ' (hmem φ)).2.2
  exact ⟨w, K, θ, hKz, hKS, hK, hnc, orbit_transfer_fixed hm0 hm hK hnc,
    fun φ => circularTube_pairBounds_fixed h hζ hζ' (hmem φ)⟩

end Assembly

end KAM.Planetary
