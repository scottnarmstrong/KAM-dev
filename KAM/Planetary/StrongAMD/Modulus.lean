/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Threshold

/-!
# The modulus of continuity of the strong threshold, and the shared compact `U`

Source: `LP:MAIN L6 (177–189)` with amendment N2 (one shared compact `U`); track LP,
non-frozen.

* M1 `strongThresholdModulus` and its properties (nonnegative, monotone, bounded, the defining
  inequality, `Ω_B(r) → 0` as `r ↓ 0`), for any compact `U ⊆ chamber ν` given as data.
* M2 `exists_cthickening_compact`: for compact `L ⊆ chamber ν` some closed thickening
  `cthickening ρ L` is a compact subset of `chamber ν`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open Filter Topology

variable {n : ℕ}

/-- `Ω_B(r) = sup {|B(I) - B(J)| : I, J ∈ U, ‖I - J‖_∞ ≤ r}` (`LP:MAIN L6 (179)`). -/
def strongThresholdModulus (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (r : ℝ) : ℝ :=
  sSup {x | ∃ I ∈ U, ∃ J ∈ U, ‖I - J‖ ≤ r ∧ x = |strongThreshold ν I - strongThreshold ν J|}

section Modulus

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)}

/-- The set defining `Ω_B(r)` is bounded above (`B` is bounded on the compact `U`). -/
theorem bddAbove_strongThresholdModulus_set (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hUc : IsCompact U) (hUch : U ⊆ chamber ν) (r : ℝ) :
    BddAbove {x | ∃ I ∈ U, ∃ J ∈ U, ‖I - J‖ ≤ r ∧
      x = |strongThreshold ν I - strongThreshold ν J|} := by
  obtain ⟨C, hC⟩ := hUc.exists_bound_of_continuousOn
    ((continuousOn_strongThreshold hν hn).mono hUch)
  refine ⟨2 * C, ?_⟩
  rintro x ⟨I, hI, J, hJ, -, rfl⟩
  have h1 := hC I hI
  have h2 := hC J hJ
  rw [Real.norm_eq_abs] at h1 h2
  exact (abs_sub _ _).trans (by linarith)

theorem strongThresholdModulus_nonneg (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (r : ℝ) :
    0 ≤ strongThresholdModulus ν U r :=
  Real.sSup_nonneg (by rintro x ⟨I, -, J, -, -, rfl⟩; exact abs_nonneg _)

/-- The defining inequality `|B I - B J| ≤ Ω_B(r)` for `I, J ∈ U` with `‖I - J‖ ≤ r`. -/
theorem abs_strongThreshold_sub_le_modulus (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {I J : Fin n → ℝ} (hI : I ∈ U) (hJ : J ∈ U)
    {r : ℝ} (hIJ : ‖I - J‖ ≤ r) :
    |strongThreshold ν I - strongThreshold ν J| ≤ strongThresholdModulus ν U r :=
  le_csSup (bddAbove_strongThresholdModulus_set hν hn hUc hUch r) ⟨I, hI, J, hJ, hIJ, rfl⟩

theorem strongThresholdModulus_mono (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {r s : ℝ} (hrs : r ≤ s) :
    strongThresholdModulus ν U r ≤ strongThresholdModulus ν U s := by
  refine Real.sSup_le ?_ (strongThresholdModulus_nonneg ν U s)
  rintro x ⟨I, hI, J, hJ, hIJ, rfl⟩
  exact abs_strongThreshold_sub_le_modulus hν hn hUc hUch hI hJ (hIJ.trans hrs)

/-- `Ω_B(r) → 0` as `r ↓ 0` (uniform continuity of `B` on the compact `U`). -/
theorem tendsto_strongThresholdModulus (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hUc : IsCompact U) (hUch : U ⊆ chamber ν) :
    Tendsto (strongThresholdModulus ν U) (𝓝[>] 0) (𝓝 0) := by
  have huc := hUc.uniformContinuousOn_of_continuous
    ((continuousOn_strongThreshold hν hn).mono hUch)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
  have hr' : r < δ := by
    have := (Real.dist_eq r 0 ▸ hrδ : |r - 0| < δ)
    rw [sub_zero, abs_of_pos hr] at this
    exact this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (strongThresholdModulus_nonneg ν U r)]
  have : strongThresholdModulus ν U r ≤ ε / 2 := by
    refine Real.sSup_le ?_ (half_pos hε).le
    rintro x ⟨I, hI, J, hJ, hIJ, rfl⟩
    have hd : dist I J < δ := by rw [dist_eq_norm]; exact lt_of_le_of_lt hIJ hr'
    have := hδ' I hI J hJ hd
    rw [Real.dist_eq] at this
    exact this.le
  linarith

end Modulus

/-- M2 (amendment N2): a compact `L ⊆ chamber ν` has a closed thickening that is a compact
subset of `chamber ν`; later packages take `U := cthickening (4 r_g) L` with `4 r_g ≤ ρ`. -/
theorem exists_cthickening_compact (ν : Fin n → ℝ) {L : Set (Fin n → ℝ)} (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) :
    ∃ ρ : ℝ, 0 < ρ ∧ IsCompact (Metric.cthickening ρ L) ∧
      Metric.cthickening ρ L ⊆ chamber ν := by
  obtain ⟨ρ, hρ, hsub⟩ := hL.exists_cthickening_subset_open (isOpen_chamber ν) hLch
  exact ⟨ρ, hρ, hL.cthickening, hsub⟩

end KAM.Planetary.StrongAMD
