/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Hamiltonian.Liouville
public import KAM.Planetary.Newtonian.Assembly
public import KAM.Frozen.Planetary.Defs.IsCylinderKolmogorovSet
public import KAM.Frozen.Planetary.Defs.CylinderCell
public import KAM.Frozen.Planetary.Defs.CircularTube
public import KAM.Frozen.Planetary.Defs.FastShift

/-!
# Part 12: image measure of a cylinder Kolmogorov set

`bpP:p12:measure` (`stepP:p12:me-inv`, `me-cell`, `me-meas`, `me-tube`): fast-lattice invariance
of a frozen union-of-whole-tori set (`cylinder_set_shift`), the reduction of the image to the
half-open fast cell, the Borel image and the exact volume through `chart_measure_image` at
factor one (`measure`), and the tube consequences (`measure_in_tube`). `V` is arbitrary;
Borelness of the cell intersection comes from `S ⊆ cylinder V r`.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler

namespace PlanarAssembly

private theorem fast_fst_add_fastShift {a b : ℕ} (z : Phase (a + b)) (k : Fin a → ℤ) (i : Fin a) :
    fast (z + fastShift k).1 i = fast z.1 i + 2 * π * (k i : ℝ) := by
  simp [fast, fastShift]

private theorem fastShift_neg {a b : ℕ} (k : Fin a → ℤ) :
    (fastShift (-k) : Phase (a + b)) = -fastShift k := by
  refine Prod.ext (funext fun i => ?_) (by simp [fastShift])
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [fastShift]
  · simp [fastShift]

private theorem fastShift_zero {a b : ℕ} : (fastShift (0 : Fin a → ℤ) : Phase (a + b)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (by simp [fastShift])
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [fastShift]
  · simp [fastShift]

private theorem shift_mem {a b : ℕ} {H : Phase (a + b) → ℝ}
    {V : Set (Fin a → ℝ)} {r μ C : ℝ} {S : Set (Phase (a + b))}
    (hS : IsCylinderKolmogorovSet H V r μ C S) (k : Fin a → ℤ) {z : Phase (a + b)} (hz : z ∈ S) :
    z + fastShift k ∈ S := by
  obtain ⟨-, -, hS3⟩ := hS
  obtain ⟨w, K, θ, hKz, hKS, hK, -⟩ := hS3 z hz
  have h4 := hK.2.2.1 θ (Fin.append k (0 : Fin b → ℤ))
  have hk : (fun i : Fin a => (Fin.append k (0 : Fin b → ℤ)) (Fin.castAdd b i)) = k := by
    funext i; simp
  rw [hk, hKz] at h4
  exact hKS ⟨_, h4⟩

/-- Invariance under the fast lattice follows from the frozen union-of-whole-tori predicate. -/
theorem cylinder_set_shift {a b : ℕ} {H : Phase (a + b) → ℝ}
    {V : Set (Fin a → ℝ)} {r μ C : ℝ} {S : Set (Phase (a + b))}
    (hS : IsCylinderKolmogorovSet H V r μ C S) (k : Fin a → ℤ) :
    (fun z => z + fastShift k) '' S = S := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact shift_mem hS k hz
  · intro z hz
    refine ⟨z + fastShift (-k), shift_mem hS (-k) hz, ?_⟩
    simp [fastShift_neg]

private theorem measurableSet_fastCell (a b : ℕ) :
    MeasurableSet {z : Phase (a + b) | ∀ i : Fin a, fast z.1 i ∈ Ico (0 : ℝ) (2 * π)} := by
  have : {z : Phase (a + b) | ∀ i : Fin a, fast z.1 i ∈ Ico (0 : ℝ) (2 * π)} =
      ⋂ i : Fin a, (fun z : Phase (a + b) => fast z.1 i) ⁻¹' Ico (0 : ℝ) (2 * π) := by
    ext z; simp
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ico.preimage ((measurable_pi_apply (Fin.castAdd b i)).comp measurable_fst)

private theorem cell_inter_eq {a b : ℕ} {V : Set (Fin a → ℝ)} {r : ℝ} {S : Set (Phase (a + b))}
    (hSc : S ⊆ cylinder V r) :
    S ∩ cylinderCell V r =
      S ∩ {z : Phase (a + b) | ∀ i : Fin a, fast z.1 i ∈ Ico (0 : ℝ) (2 * π)} := by
  ext z
  simp only [mem_inter_iff, cylinderCell, mem_ofPred_eq, mem_Ico]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hSc h.1, h.2⟩⟩

/-- Borel image and exact volume through the half-open fast cell.
V is arbitrary: use S subset cylinder V r to rewrite the cell intersection as S
intersected with just the Borel fast-angle bounds; do not assume V measurable. -/
theorem measure {a b : ℕ} {O : Set (Phase (a + b))} (hO : IsOpen O)
    {Ψ : Phase (a + b) → Phase (a + b)}
    (hΨa : AnalyticOnNhd ℝ Ψ O) (hΨs : IsSymplecticOn 1 Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin a → ℤ, z + fastShift k ∈ O ∧ Ψ (z + fastShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin a → ℤ, z' = z + fastShift k)
    {H : Phase (a + b) → ℝ} {V : Set (Fin a → ℝ)} {r μ C : ℝ}
    {S : Set (Phase (a + b))} (hS : IsCylinderKolmogorovSet H V r μ C S)
    (hSO : S ⊆ O) :
    Ψ '' S = Ψ '' (S ∩ cylinderCell V r) ∧
    InjOn Ψ (S ∩ cylinderCell V r) ∧ MeasurableSet (Ψ '' S) ∧
    volume (Ψ '' S) = volume (S ∩ cylinderCell V r) := by
  have hch : IsChart 1 Ψ O := ⟨hΨa, hΨs⟩
  have hSm : MeasurableSet S := hS.1
  have hSc : S ⊆ cylinder V r := hS.2.1
  have hpi : 0 < 2 * π := by positivity
  have himg : Ψ '' S = Ψ '' (S ∩ cylinderCell V r) := by
    refine Subset.antisymm ?_ (image_mono inter_subset_left)
    rintro _ ⟨z, hz, rfl⟩
    set k : Fin a → ℤ := fun i => -⌊fast z.1 i / (2 * π)⌋ with hk
    have hz' : z + fastShift k ∈ S := shift_mem hS k hz
    refine ⟨z + fastShift k, ⟨hz', hSc hz', fun i => ?_⟩, (hQ1 z (hSO hz) k).2⟩
    rw [fast_fst_add_fastShift]
    have h1 := Int.floor_le (fast z.1 i / (2 * π))
    have h2 := Int.lt_floor_add_one (fast z.1 i / (2 * π))
    rw [le_div_iff₀ hpi] at h1
    rw [div_lt_iff₀ hpi] at h2
    simp only [hk, Int.cast_neg]
    constructor <;> nlinarith
  have hinj : InjOn Ψ (S ∩ cylinderCell V r) := by
    rintro z ⟨hzS, hzc⟩ z' ⟨hz'S, hz'c⟩ h
    obtain ⟨k, hkz⟩ := hQ2 z (hSO hzS) z' (hSO hz'S) h.symm
    have hk0 : k = 0 := by
      funext i
      have h1 := fast_fst_add_fastShift z k i
      rw [← hkz] at h1
      have a1 := hzc.2 i
      have a2 := hz'c.2 i
      have h2 : ((k i : ℤ) : ℝ) < 1 := by
        have : 2 * π * ((k i : ℤ) : ℝ) < 2 * π * 1 := by linarith [a1.1, a2.2]
        exact lt_of_mul_lt_mul_left this hpi.le
      have h3 : (-1 : ℝ) < ((k i : ℤ) : ℝ) := by
        have : 2 * π * (-1 : ℝ) < 2 * π * ((k i : ℤ) : ℝ) := by linarith [a1.2, a2.1]
        exact lt_of_mul_lt_mul_left this hpi.le
      have h4 : k i < 1 := by exact_mod_cast h2
      have h5 : -1 < k i := by exact_mod_cast h3
      simp only [Pi.zero_apply]; omega
    subst hk0
    rw [fastShift_zero, add_zero] at hkz
    exact hkz.symm
  have hAm : MeasurableSet (S ∩ cylinderCell V r) := by
    rw [cell_inter_eq hSc]
    exact hSm.inter (measurableSet_fastCell a b)
  have hAO : S ∩ cylinderCell V r ⊆ O := inter_subset_left.trans hSO
  refine ⟨himg, hinj, ?_, ?_⟩
  · rw [himg]
    exact measurableSet_chart_image one_pos hO hch hAO hAm
  · rw [himg]
    have := (chart_measure_image one_pos hO hch hAO hAm.nullMeasurableSet).2.2 hinj
    simpa using this

/-- Tube, positivity and finiteness after the measure theorem; no lattice strengthening. -/
theorem measure_in_tube {G m0 : ℝ} {m a : Fin 2 → ℝ} {ζ r μ C : ℝ}
    (hG : 0 < G) (hm0 : 0 < m0) (ha : ∀ i, 0 < a i)
    {Ψ : Phase 4 → Phase 4} {H : Phase 4 → ℝ} {V : Set (Fin 2 → ℝ)}
    {S : Set (Phase 4)} (hS : IsCylinderKolmogorovSet (a := 2) (b := 2) H V r μ C S)
    (hvol : volume (Ψ '' S) = volume (S ∩ cylinderCell (b := 2) V r))
    (hpos : 0 < volume (S ∩ cylinderCell (b := 2) V r))
    (hmap : MapsTo Ψ (cylinder (b := 2) V r) (circularTube G m0 m a ζ)) :
    Ψ '' S ⊆ circularTube G m0 m a ζ ∧
    0 < volume (Ψ '' S) ∧ volume (Ψ '' S) < ⊤ := by
  have hsub : Ψ '' S ⊆ circularTube G m0 m a ζ := (hmap.mono_left hS.2.1).image_subset
  exact ⟨hsub, hvol ▸ hpos, volume_lt_top_of_subset_circularTube hG hm0 ha hsub⟩

end PlanarAssembly

end KAM.Planetary

end
