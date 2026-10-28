/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.Setting
public import KAM.Weighted.Projections
import KAM.Strip.Cohomological
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The homological equation (`bpN:p6:homological`)

For `f ∈ O(r,s)` with `|f|_{r,s} ≤ δ` the generating function
`φ = ∑_{k ∈ Z_K \ Λ} f̂ₖ(I)/(2πi k·ω(I)) χₖ(θ)` and the resonant part `ξ = P_Λ T_K f` solve
`∂_ω φ + ξ = T_K f` with the bounds of the source.

The core `homological_param` has an independent parameter dimension `m` and an arbitrary
holomorphic frequency field `ω : ℂᵐ → ℂⁿ` (the bracket is stated as the directional derivative
`∑ᵢ ∂_{θᵢ}φ · ωᵢ`); `homological_direct` is its `m = n`, `ω = freq h` specialization and
`homological` follows from it and `divisor`. Design
`docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-2.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-- The generating function `φ = ∑_{k ∈ Z_K \ Λ} f̂ₖ(I)/(2πi k·ω(I)) χₖ(θ)`. -/
def homGen (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun z => ∑' k, (zBall n K \ Λ).indicator (fun k =>
    coeff f z.2 k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (freq h z.2)) *
      KAM.character k z.1) k

/-- The resonant part `ξ = P_Λ T_K f`. -/
def homRes (K : ℝ) (Λ : Set (Fin n → ℤ)) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  projMode Λ (truncate K f)

/-- `φ = ∑_{k ∈ Z_K \ Λ} f̂ₖ(y)/(2πi k·ω(y)) χₖ(θ)` with an independent parameter carrier. -/
def homGenParam {m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (ω : (Fin m → ℂ) → Fin n → ℂ)
    (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  fun z => ∑' k, (zBall n K \ Λ).indicator (fun k =>
    coeff f z.2 k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (ω z.2)) *
      KAM.character k z.1) k

/-- `ξ = P_Λ T_K f` with an independent parameter carrier. -/
def homResParam {m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  projMode Λ (truncate K f)

/-- Reality on the real points of `U ⊆ ℂⁿ × ℂᵐ` (the `m ≠ n` analogue of `RealOn`). -/
def RealOnParam {m : ℕ} (U : Set ((Fin n → ℂ) × (Fin m → ℂ)))
    (u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : Prop :=
  ∀ x : (Fin n → ℝ) × (Fin m → ℝ), (KAM.realInclusion n x.1, KAM.realInclusion m x.2) ∈ U →
    (u (KAM.realInclusion n x.1, KAM.realInclusion m x.2)).im = 0

/-- Bridge: for `m = n` the two reality predicates agree. -/
theorem realOnParam_iff_realOn (U : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : RealOnParam U u ↔ RealOn U u := Iff.rfl

/-- Bridge: the canonical generator is the `m = n`, `ω = freq h` specialization. -/
theorem homGen_eq_homGenParam (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : homGen K Λ h f = homGenParam K Λ (freq h) f := rfl

/-- Bridge: the canonical resonant part is the `m = n` specialization. -/
theorem homRes_eq_homResParam (K : ℝ) (Λ : Set (Fin n → ℤ))
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : homRes K Λ f = homResParam K Λ f := rfl

section Core

variable {m : ℕ}

private theorem finite_zBall (K : ℝ) : (zBall n K).Finite := by
  refine (KAM.modeCutoff n ⌈K⌉₊).finite_toSet.subset fun k hk => ?_
  have hk' : KAM.Fourier.modeSize k ≤ K := hk
  exact KAM.mem_modeCutoff.2 (hk'.trans (Nat.le_ceil K))

/-- The finite set of modes `Z_K`. -/
private def zFin (n : ℕ) (K : ℝ) : Finset (Fin n → ℤ) := (finite_zBall (n := n) K).toFinset

private theorem mem_zFin {K : ℝ} {k : Fin n → ℤ} : k ∈ zFin n K ↔ k ∈ zBall n K :=
  Set.Finite.mem_toFinset _

/-- A series over a set of modes inside `Z_K` is the finite sum over `Z_K`. -/
private theorem tsum_indicator_zBall (K : ℝ) (S : Set (Fin n → ℤ)) (g : (Fin n → ℤ) → ℂ)
    (hS : S ⊆ zBall n K) : ∑' k, S.indicator g k = ∑ k ∈ zFin n K, S.indicator g k := by
  refine tsum_eq_sum fun k hk => ?_
  exact Set.indicator_of_notMem (fun h => hk (mem_zFin.2 (hS h))) _

/-- The coefficient `aₖ(I) = 1_{Z_K \ Λ}(k) f̂ₖ(I)/(2πi k·ω(I))` of the generator. -/
private def genCoeff (K : ℝ) (Λ : Set (Fin n → ℤ)) (ω : (Fin m → ℂ) → Fin n → ℂ)
    (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) (k : Fin n → ℤ) (I : Fin m → ℂ) : ℂ :=
  (zBall n K \ Λ).indicator
    (fun k => coeff f I k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (ω I))) k

private theorem homGenParam_eq_fourierSeries (K : ℝ) (Λ : Set (Fin n → ℤ))
    (ω : (Fin m → ℂ) → Fin n → ℂ) (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) :
    homGenParam K Λ ω f = fourierSeries (genCoeff K Λ ω f) := by
  funext z
  unfold homGenParam fourierSeries genCoeff
  refine tsum_congr fun k => ?_
  by_cases hk : k ∈ zBall n K \ Λ <;> simp [hk]

/-- The generator is a finite sum over `Z_K`. -/
private theorem homGenParam_eq_sum (K : ℝ) (Λ : Set (Fin n → ℤ))
    (ω : (Fin m → ℂ) → Fin n → ℂ) (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin m → ℂ)) :
    homGenParam K Λ ω f z = ∑ k ∈ zFin n K, genCoeff K Λ ω f k z.2 * KAM.character k z.1 := by
  unfold homGenParam genCoeff
  rw [tsum_indicator_zBall K _ _ Set.sdiff_subset]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k ∈ zBall n K \ Λ <;> simp [hk]

section Hyp

variable {D : Set (Fin m → ℂ)} {r s K α q δ : ℝ} {Λ : Set (Fin n → ℤ)}
  {ω : (Fin m → ℂ) → Fin n → ℂ} {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}

private theorem divisor_ne_zero (hq : 1 ≤ q) (hα : 0 < α)
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ, α / q ≤ ‖dotC k (ω I)‖)
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) {k : Fin n → ℤ} (hk : k ∈ zBall n K \ Λ) :
    2 * (Real.pi : ℂ) * Complex.I * dotC k (ω I) ≠ 0 := by
  have h1 : 0 < α / q := div_pos hα (by linarith)
  have h2 : dotC k (ω I) ≠ 0 := fun h => by
    have := hdir I hI k hk
    rw [h, norm_zero] at this
    linarith
  have h3 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  exact mul_ne_zero h3 h2

private theorem differentiableOn_dotC (hω : DifferentiableOn ℂ ω (polyNbhd D r))
    (k : Fin n → ℤ) : DifferentiableOn ℂ (fun I => dotC k (ω I)) (polyNbhd D r) := by
  unfold dotC
  refine DifferentiableOn.fun_sum fun i _ => ?_
  exact (differentiableOn_const _).mul (differentiableOn_pi.1 hω i)

private theorem genCoeff_differentiableOn (hq : 1 ≤ q) (hα : 0 < α) (hs : 0 < s)
    (hω : DifferentiableOn ℂ ω (polyNbhd D r))
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ, α / q ≤ ‖dotC k (ω I)‖)
    (hf : InClass D r s f) (k : Fin n → ℤ) :
    DifferentiableOn ℂ (genCoeff K Λ ω f k) (polyNbhd D r) := by
  by_cases hk : k ∈ zBall n K \ Λ
  · have e : genCoeff K Λ ω f k =
        fun I => coeff f I k * (2 * (Real.pi : ℂ) * Complex.I * dotC k (ω I))⁻¹ := by
      funext I
      simp [genCoeff, hk, div_eq_mul_inv]
    rw [e]
    refine (coeff_differentiableOn hs hf k).mul (DifferentiableOn.inv ?_ ?_)
    · exact (differentiableOn_const _).mul (differentiableOn_dotC hω k)
    · intro I hI
      exact divisor_ne_zero hq hα hdir hI hk
  · have e : genCoeff K Λ ω f k = fun _ => 0 := by
      funext I
      simp [genCoeff, hk]
    rw [e]
    exact differentiableOn_const _

/-- The pointwise bound `|aₖ| ≤ q |f̂ₖ|/(2πα)`. -/
private theorem norm_genCoeff_le (hq : 1 ≤ q) (hα : 0 < α)
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ, α / q ≤ ‖dotC k (ω I)‖)
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) (k : Fin n → ℤ) :
    ‖genCoeff K Λ ω f k I‖ ≤ q / (2 * Real.pi * α) * ‖coeff f I k‖ := by
  have hq0 : 0 < q := by linarith
  have hc : 0 ≤ q / (2 * Real.pi * α) := by positivity
  by_cases hk : k ∈ zBall n K \ Λ
  · simp only [genCoeff, Set.indicator_of_mem hk, norm_div, norm_mul]
    have hd := hdir I hI k hk
    have hd0 : 0 < ‖dotC k (ω I)‖ := lt_of_lt_of_le (div_pos hα hq0) hd
    have hn : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [hn, div_le_iff₀ (by positivity)]
    have : q / (2 * Real.pi * α) * ‖coeff f I k‖ * (2 * Real.pi * ‖dotC k (ω I)‖) =
        ‖coeff f I k‖ * (q * ‖dotC k (ω I)‖ / α) := by
      field_simp
    rw [this]
    have h5 : 1 ≤ q * ‖dotC k (ω I)‖ / α := by
      rw [le_div_iff₀ hα]
      have := (div_le_iff₀ hq0).1 hd
      linarith
    nlinarith [norm_nonneg (coeff f I k)]
  · simp only [genCoeff, Set.indicator_of_notMem hk, norm_zero]
    positivity

end Hyp

end Core

end KAM.NormalForm

end
