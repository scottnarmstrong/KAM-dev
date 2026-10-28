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

/-! ### Truncation, the resonant part and the derivative of the generator -/

private theorem zBall_neg {K : ℝ} {k : Fin n → ℤ} : -k ∈ zBall n K ↔ k ∈ zBall n K := by
  simp [zBall, KAM.Fourier.modeSize]

private theorem truncate_eq_sum (K : ℝ) (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin m → ℂ)) :
    truncate K f z = ∑ k ∈ zFin n K, coeff f z.2 k * KAM.character k z.1 := by
  unfold truncate projMode
  have := tsum_indicator_zBall K (zBall n K) (fun k => coeff f z.2 k * KAM.character k z.1)
    subset_rfl
  refine this.trans (Finset.sum_congr rfl fun k hk => ?_)
  exact Set.indicator_of_mem (mem_zFin.1 hk) _

private theorem projMode_inter_eq_sum (K : ℝ) (Λ : Set (Fin n → ℤ))
    (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) (z : (Fin n → ℂ) × (Fin m → ℂ)) :
    projMode (Λ ∩ zBall n K) f z =
      ∑ k ∈ zFin n K, Λ.indicator (fun k => coeff f z.2 k * KAM.character k z.1) k := by
  unfold projMode
  rw [tsum_indicator_zBall K _ _ Set.inter_subset_right]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := mem_zFin.1 hk
  by_cases hΛ : k ∈ Λ <;> simp [hΛ, hk']

private theorem homResParam_eq_projMode {D : Set (Fin m → ℂ)} {r s K δ : ℝ} {Λ : Set (Fin n → ℤ)}
    {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hs : 0 < s) (hf : InClass D r s f)
    (hδ : WBound D r s f δ) {z : (Fin n → ℂ) × (Fin m → ℂ)} (hz : z ∈ Dom n D r s) :
    homResParam K Λ f z = projMode (Λ ∩ zBall n K) f z := by
  have hc := (projections hs hf hδ (zBall n K)).2.1 z.2 hz.2
  unfold homResParam projMode
  refine tsum_congr fun k => ?_
  have hck : coeff (truncate K f) z.2 k = (zBall n K).indicator (coeff f z.2) k := hc k
  by_cases hΛ : k ∈ Λ <;> by_cases hZ : k ∈ zBall n K <;> simp [hΛ, hZ, hck]

private theorem hasFDerivAt_genTerm {D : Set (Fin m → ℂ)} {r s K α q : ℝ} {Λ : Set (Fin n → ℤ)}
    {ω : (Fin m → ℂ) → Fin n → ℂ} {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hq : 1 ≤ q) (hα : 0 < α) (hs : 0 < s) (hω : DifferentiableOn ℂ ω (polyNbhd D r))
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ, α / q ≤ ‖dotC k (ω I)‖)
    (hf : InClass D r s f) {z : (Fin n → ℂ) × (Fin m → ℂ)} (hz : z ∈ Dom n D r s)
    (k : Fin n → ℤ) :
    HasFDerivAt (fun w : (Fin n → ℂ) × (Fin m → ℂ) => genCoeff K Λ ω f k w.2 *
        KAM.character k w.1)
      (genCoeff K Λ ω f k z.2 • ((KAM.character k z.1 • ((2 * Real.pi * Complex.I : ℂ) •
          KAM.modeForm k)).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin m → ℂ))) +
        KAM.character k z.1 • (fderiv ℂ (genCoeff K Λ ω f k) z.2).comp
          (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin m → ℂ))) z := by
  have hda : DifferentiableAt ℂ (genCoeff K Λ ω f k) z.2 :=
    (genCoeff_differentiableOn hq hα hs hω hdir hf k).differentiableAt
      ((isOpen_polyNbhd D r).mem_nhds hz.2)
  have h1 := hda.hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℂ) (p := z))
  have h2 := (KAM.hasFDerivAt_character k z.1).comp z (hasFDerivAt_fst (𝕜 := ℂ) (p := z))
  exact h1.mul h2

private theorem fderiv_homGenParam {D : Set (Fin m → ℂ)} {r s K α q : ℝ} {Λ : Set (Fin n → ℤ)}
    {ω : (Fin m → ℂ) → Fin n → ℂ} {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hq : 1 ≤ q) (hα : 0 < α) (hs : 0 < s) (hω : DifferentiableOn ℂ ω (polyNbhd D r))
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ, α / q ≤ ‖dotC k (ω I)‖)
    (hf : InClass D r s f) {z : (Fin n → ℂ) × (Fin m → ℂ)} (hz : z ∈ Dom n D r s) (i : Fin n) :
    fderiv ℂ (homGenParam K Λ ω f) z (Pi.single i 1, 0) =
      ∑ k ∈ zFin n K, genCoeff K Λ ω f k z.2 *
        (KAM.character k z.1 * (2 * Real.pi * Complex.I * (k i : ℂ))) := by
  have hsum := HasFDerivAt.fun_sum (u := zFin n K) fun k _ =>
    hasFDerivAt_genTerm hq hα hs hω hdir hf hz k
  have hfun : homGenParam K Λ ω f = fun w => ∑ k ∈ zFin n K,
      genCoeff K Λ ω f k w.2 * KAM.character k w.1 := funext fun w => homGenParam_eq_sum K Λ ω f w
  rw [hfun, hsum.fderiv, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hm : (KAM.modeForm k) (Pi.single i 1) = (k i : ℂ) := by
    simp [KAM.modeForm_apply, Pi.single_apply]
  simp [hm]

private theorem dotC_eq_sum (k : Fin n → ℤ) (w : Fin n → ℂ) (c : ℂ) :
    ∑ i, c * (k i : ℂ) * w i = c * dotC k w := by
  unfold dotC
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The directional derivative of the generator plus the resonant part. -/
private theorem directional_homGenParam {D : Set (Fin m → ℂ)} {r s K α q : ℝ}
    {Λ : Set (Fin n → ℤ)} {ω : (Fin m → ℂ) → Fin n → ℂ} {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hq : 1 ≤ q) (hα : 0 < α) (hs : 0 < s) (hω : DifferentiableOn ℂ ω (polyNbhd D r))
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ, α / q ≤ ‖dotC k (ω I)‖)
    (hf : InClass D r s f) {z : (Fin n → ℂ) × (Fin m → ℂ)} (hz : z ∈ Dom n D r s) :
    ∑ i, fderiv ℂ (homGenParam K Λ ω f) z (Pi.single i 1, 0) * ω z.2 i =
      ∑ k ∈ zFin n K, (zBall n K \ Λ).indicator
        (fun k => coeff f z.2 k * KAM.character k z.1) k := by
  simp_rw [fderiv_homGenParam hq hα hs hω hdir hf hz, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ i, genCoeff K Λ ω f k z.2 * (KAM.character k z.1 *
      (2 * Real.pi * Complex.I * (k i : ℂ))) * ω z.2 i =
      genCoeff K Λ ω f k z.2 * KAM.character k z.1 *
        (2 * Real.pi * Complex.I * (k i : ℂ) * ω z.2 i) := fun i => by ring
  simp_rw [e]
  rw [← Finset.mul_sum, dotC_eq_sum]
  by_cases hk : k ∈ zBall n K \ Λ
  · have hne := divisor_ne_zero hq hα hdir hz.2 hk
    have hd0 : dotC k (ω z.2) ≠ 0 := fun h => hne (by simp [h])
    simp only [genCoeff, Set.indicator_of_mem hk]
    field_simp
  · simp [genCoeff, hk]

/-! ### Reality -/

private theorem im_tsum_indicator_eq_zero (S : Set (Fin n → ℤ)) (hS : ∀ k, -k ∈ S ↔ k ∈ S)
    (g : (Fin n → ℤ) → ℂ) (hg : ∀ k, starRingEnd ℂ (g k) = g (-k)) :
    (∑' k, S.indicator g k).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have hstar : ∀ f : (Fin n → ℤ) → ℂ, (starRingEnd ℂ) (∑' k, f k) = ∑' k, (starRingEnd ℂ) (f k) :=
    fun f => by
      simp only [starRingEnd_apply]
      exact tsum_star
  rw [hstar]
  conv_rhs => rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq]
  refine tsum_congr fun k => ?_
  show (starRingEnd ℂ) (S.indicator g k) = S.indicator g (-k)
  by_cases hk : k ∈ S
  · have : -k ∈ S := (hS k).2 hk
    simp [hk, this, hg k]
  · have : -k ∉ S := fun h => hk ((hS k).1 h)
    simp [hk, this]

private theorem conj_dotC {w : Fin n → ℂ} (hw : ∀ i, (w i).im = 0) (k : Fin n → ℤ) :
    starRingEnd ℂ (dotC k w) = dotC k w := by
  have : ∀ i, starRingEnd ℂ (w i) = w i := fun i => Complex.conj_eq_iff_im.mpr (hw i)
  simp [dotC, this]

private theorem dotC_neg (k : Fin n → ℤ) (w : Fin n → ℂ) : dotC (-k) w = -dotC k w := by
  simp [dotC, Finset.sum_neg_distrib]

private theorem conj_coeff {D : Set (Fin m → ℂ)} {r s : ℝ} {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hs : 0 < s) (hf : RealOnParam (Dom n D r s) f) {y : Fin m → ℝ}
    (hy : KAM.realInclusion m y ∈ polyNbhd D r) (k : Fin n → ℤ) :
    starRingEnd ℂ (coeff f (KAM.realInclusion m y) k) = coeff f (KAM.realInclusion m y) (-k) := by
  have hv : ∀ x : Fin n → ℝ, (f (fun j => (x j : ℂ), KAM.realInclusion m y)).im = 0 := fun x =>
    hf (x, y) ⟨KAM.ofReal_mem_complexStrip hs x, hy⟩
  exact (KAM.torusCoeff_conjugateSymmetric hv k).symm



/-- The homological solve with independent angle/parameter dimensions (core of
`homological_direct`; consumed by `bpN:p11:hom`). -/
theorem homological_param {D : Set (Fin m → ℂ)} {r s K α q δ : ℝ}
    {Λ : Set (Fin n → ℤ)} {ω : (Fin m → ℂ) → Fin n → ℂ} {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hq : 1 ≤ q) (hα : 0 < α) (hs : 0 < s) (hK : 0 ≤ K)
    (hω : DifferentiableOn ℂ ω (polyNbhd D r))
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ, α / q ≤ ‖dotC k (ω I)‖)
    (hf : InClass D r s f) (hδ : WBound D r s f δ) :
    InClass D r s (homGenParam K Λ ω f) ∧ InClass D r s (homResParam K Λ f) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, k ∉ zBall n K \ Λ → coeff (homGenParam K Λ ω f) I k = 0) ∧
    (∀ z ∈ Dom n D r s,
      (∑ i, fderiv ℂ (homGenParam K Λ ω f) z (Pi.single i 1, 0) * ω z.2 i) +
        homResParam K Λ f z = truncate K f z) ∧
    (∀ I ∈ polyNbhd D r, ∀ k ∈ Λ, coeff (homGenParam K Λ ω f) I k = 0) ∧
    (∀ z ∈ Dom n D r s, homResParam K Λ f z = projMode (Λ ∩ zBall n K) f z) ∧
    WBound D r s (homResParam K Λ f) δ ∧ WBound D r s (truncate K f) δ ∧
    WBound D r s (homGenParam K Λ ω f) (q * δ / (2 * Real.pi * α)) ∧
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOnParam (Dom n D r s) f →
      (∀ I : Fin m → ℝ, KAM.realInclusion m I ∈ polyNbhd D r →
        ∀ i, (ω (KAM.realInclusion m I) i).im = 0) →
      RealOnParam (Dom n D r s) (homGenParam K Λ ω f) ∧
        RealOnParam (Dom n D r s) (homResParam K Λ f)) := by
  have _ := hK
  have hq0 : 0 < q := by linarith
  have ha := genCoeff_differentiableOn hq hα hs hω hdir hf
  have hc0 : 0 ≤ q / (2 * Real.pi * α) := by positivity
  have hS : ∀ I ∈ polyNbhd D r,
      Summable (fun k => ‖genCoeff K Λ ω f k I‖ * modeWeight s k) ∧
        ∑' k, ‖genCoeff K Λ ω f k I‖ * modeWeight s k ≤ q * δ / (2 * Real.pi * α) := by
    intro I hI
    obtain ⟨h1, h2⟩ := hδ I hI
    have hle : ∀ k, ‖genCoeff K Λ ω f k I‖ * modeWeight s k ≤
        q / (2 * Real.pi * α) * (‖coeff f I k‖ * modeWeight s k) := fun k => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (norm_genCoeff_le hq hα hdir hI k)
        (Real.exp_pos _).le
    have h1' : Summable fun k => q / (2 * Real.pi * α) * (‖coeff f I k‖ * modeWeight s k) :=
      h1.mul_left _
    have hs' : Summable (fun k => ‖genCoeff K Λ ω f k I‖ * modeWeight s k) :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hle h1'
    refine ⟨hs', (hs'.tsum_le_tsum hle h1').trans ?_⟩
    rw [tsum_mul_left]
    calc q / (2 * Real.pi * α) * ∑' k, ‖coeff f I k‖ * modeWeight s k
        ≤ q / (2 * Real.pi * α) * δ := mul_le_mul_of_nonneg_left h2 hc0
      _ = q * δ / (2 * Real.pi * α) := by ring
  obtain ⟨-, hcls, hcoef, hwb⟩ := coefficients_series (D := D) (r := r) (s := s)
    (S := q * δ / (2 * Real.pi * α)) hs ha hS
  rw [← homGenParam_eq_fourierSeries K Λ ω f] at hcls hwb
  have hcoef' : ∀ I ∈ polyNbhd D r, ∀ k,
      coeff (homGenParam K Λ ω f) I k = genCoeff K Λ ω f k I := by
    rw [homGenParam_eq_fourierSeries]; exact hcoef
  obtain ⟨hT1, -, hT3, -, -⟩ := projections hs hf hδ (zBall n K)
  have hT1' : InClass D r s (truncate K f) := hT1
  have hT3' : WBound D r s (truncate K f) δ := hT3
  obtain ⟨hR1, -, hR3, -, -⟩ := projections hs hT1' hT3' Λ
  have hres := fun z (hz : z ∈ Dom n D r s) => homResParam_eq_projMode (K := K) (Λ := Λ) hs hf hδ hz
  refine ⟨hcls, hR1, ?_, ?_, ?_, hres, hR3, hT3', hwb, ?_⟩
  · intro I hI k hk
    rw [hcoef' I hI k]
    simp [genCoeff, hk]
  · intro z hz
    rw [directional_homGenParam hq hα hs hω hdir hf hz, hres z hz, projMode_inter_eq_sum,
      truncate_eq_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := mem_zFin.1 hk
    by_cases hΛ : k ∈ Λ <;> simp [hΛ, hk']
  · intro I hI k hk
    rw [hcoef' I hI k]
    have : k ∉ zBall n K \ Λ := fun h => h.2 hk
    simp [genCoeff, this]
  · intro hΛ hfr hωr
    have hFs : ∀ k, -k ∈ zBall n K \ Λ ↔ k ∈ zBall n K \ Λ := fun k => by
      refine and_congr zBall_neg ?_
      refine not_congr ⟨fun h => ?_, hΛ k⟩
      simpa using hΛ _ h
    have hΛs : ∀ k, -k ∈ Λ ∩ zBall n K ↔ k ∈ Λ ∩ zBall n K := fun k =>
      and_congr ⟨fun h => by simpa using hΛ _ h, hΛ k⟩ zBall_neg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hw : ∀ i, (ω (KAM.realInclusion m x.2) i).im = 0 := hωr x.2 hx.2
      show (homGenParam K Λ ω f (KAM.realInclusion n x.1, KAM.realInclusion m x.2)).im = 0
      unfold homGenParam
      refine im_tsum_indicator_eq_zero _ hFs _ fun k => ?_
      have e1 : starRingEnd ℂ (2 * (Real.pi : ℂ) * Complex.I *
          dotC k (ω (KAM.realInclusion m x.2))) =
          2 * (Real.pi : ℂ) * Complex.I * dotC (-k) (ω (KAM.realInclusion m x.2)) := by
        rw [map_mul, conj_dotC hw, dotC_neg]
        simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
        ring
      have hχ : KAM.realInclusion n x.1 = fun j => ((x.1 j : ℝ) : ℂ) := rfl
      simp only
      rw [map_mul, map_div₀, e1, conj_coeff hs hfr hx.2, hχ, KAM.conj_character_real]
    · show (homResParam K Λ f (KAM.realInclusion n x.1, KAM.realInclusion m x.2)).im = 0
      rw [hres _ hx]
      unfold projMode
      refine im_tsum_indicator_eq_zero _ hΛs _ fun k => ?_
      have hχ : KAM.realInclusion n x.1 = fun j => ((x.1 j : ℝ) : ℂ) := rfl
      simp only
      rw [map_mul, conj_coeff hs hfr hx.2, hχ, KAM.conj_character_real]

/-- `bpN:p6:homological` under `(N-dir)` (the form all proofs use; `bpN:p6:iterative-direct`). -/
theorem homological_direct {D : Set (Fin n → ℂ)} {r s K α p δ : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α)
    (hs : 0 < s) (hK : 0 ≤ K) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hdir : DivisorBound (polyNbhd D r) K Λ h (α / conjExp p))
    (hf : InClass D r s f) (hδ : WBound D r s f δ) :
    -- finite sums of characters of degree `≤ K`, in the class
    InClass D r s (homGen K Λ h f) ∧ InClass D r s (homRes K Λ f) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, k ∉ zBall n K \ Λ → coeff (homGen K Λ h f) I k = 0) ∧
    -- (a)
    (∀ z ∈ Dom n D r s, poissonBracket (homGen K Λ h f) (fun w => h w.2) z + homRes K Λ f z =
      truncate K f z) ∧
    (∀ I ∈ polyNbhd D r, ∀ k ∈ Λ, coeff (homGen K Λ h f) I k = 0) ∧
    (∀ z ∈ Dom n D r s, homRes K Λ f z = projMode (Λ ∩ zBall n K) f z) ∧
    -- (b)
    WBound D r s (homRes K Λ f) δ ∧ WBound D r s (truncate K f) δ ∧
    WBound D r s (homGen K Λ h f) (conjExp p * δ / (2 * Real.pi * α)) ∧
    -- (c)
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) f →
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd D r →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      RealOn (Dom n D r s) (homGen K Λ h f) ∧ RealOn (Dom n D r s) (homRes K Λ f)) := by
  have hq : 1 ≤ conjExp p := by
    unfold conjExp
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hω : DifferentiableOn ℂ (freq h) (polyNbhd D r) := fun I hI =>
    (differentiableAt_freq (isOpen_polyNbhd D r) hh hI).differentiableWithinAt
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
    homological_param (ω := freq h) (q := conjExp p) hq hα hs hK hω
      (fun I hI k hk => hdir I hI k hk) hf hδ
  have hbr : ∀ z ∈ Dom n D r s, poissonBracket (homGen K Λ h f) (fun w => h w.2) z =
      ∑ i, fderiv ℂ (homGenParam K Λ (freq h) f) z (Pi.single i 1, 0) * freq h z.2 i := by
    intro z hz
    have hda : DifferentiableAt ℂ h z.2 :=
      hh.differentiableAt ((isOpen_polyNbhd D r).mem_nhds hz.2)
    have hd := hda.hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℂ) (p := z))
    unfold poissonBracket
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2) =
        h ∘ (Prod.snd : (Fin n → ℂ) × (Fin n → ℂ) → Fin n → ℂ) := rfl
    have h1 : ((fderiv ℂ h z.2).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ)))
        (0, Pi.single i 1) = freq h z.2 i := by simp [freq]
    have h2 : ((fderiv ℂ h z.2).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ)))
        (Pi.single i 1, 0) = 0 := by simp
    rw [e, hd.fderiv, h1, h2, mul_zero, sub_zero]
    rfl
  exact ⟨c1, c2, c3, fun z hz => by rw [hbr z hz]; exact c4 z hz, c5, c6, c7, c8, c9, c10⟩

/-- `bpN:p6:homological` (source hypotheses `(N1)`, `(N2)`, `KLr ≤ α/p`); from the direct form and
`divisor`. -/
theorem homological {D : Set (Fin n → ℂ)} {r s K α L p δ : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α)
    (hs : 0 < s) (hK : 0 ≤ K) (hL : 0 ≤ L) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p)
    (hf : InClass D r s f) (hδ : WBound D r s f δ) :
    InClass D r s (homGen K Λ h f) ∧ InClass D r s (homRes K Λ f) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, k ∉ zBall n K \ Λ → coeff (homGen K Λ h f) I k = 0) ∧
    (∀ z ∈ Dom n D r s, poissonBracket (homGen K Λ h f) (fun w => h w.2) z + homRes K Λ f z =
      truncate K f z) ∧
    (∀ I ∈ polyNbhd D r, ∀ k ∈ Λ, coeff (homGen K Λ h f) I k = 0) ∧
    (∀ z ∈ Dom n D r s, homRes K Λ f z = projMode (Λ ∩ zBall n K) f z) ∧
    WBound D r s (homRes K Λ f) δ ∧ WBound D r s (truncate K f) δ ∧
    WBound D r s (homGen K Λ h f) (conjExp p * δ / (2 * Real.pi * α)) ∧
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) f →
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd D r →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      RealOn (Dom n D r s) (homGen K Λ h f) ∧ RealOn (Dom n D r s) (homRes K Λ f)) :=
  homological_direct hp hα hs hK hh (divisor hp hα hK hL hnr hlip hrad).2 hf hδ


end Core

end KAM.NormalForm

end
