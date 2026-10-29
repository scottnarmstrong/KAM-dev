/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.PhaseBasis
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Strip.Cohomological
public import KAM.Strip.FourierSeries

/-!
# The clock lemma

If `∂_{I_j} H ≡ 1` on `D` and the exact torus `K_∞` is invariant at `s_∞ ω*`, then the `j`-th
angle component is a clock: averaging the `j`-th angle equation gives `s_∞ ω*_j = 1`
(`clock_frequency`), and nonresonance of `s_∞ ω*` makes `K_∞,j(x) - x_j` constant on the reals
(its Fourier coefficients satisfy `2πi (k · ω) ŵ_k = 0`).
-/

@[expose] public section

namespace KAM.Certificate

open KAM

variable {n : ℕ}

private theorem torusAverage_const_complex (c : ℂ) :
    torusAverage (fun _ : Fin n → ℝ => c) = c := by
  rw [torusAverage, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    volume_unitCube, ENNReal.toReal_one, one_smul]

private theorem torusCoeff_const_complex (c : ℂ) (k : Fin n → ℤ) :
    torusCoeff (fun _ : Fin n → ℝ => c) k = if k = 0 then c else 0 := by
  have h : torusCoeff (fun _ : Fin n → ℝ => c) k =
      torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ))) * c := by
    simp only [torusCoeff, torusAverage]
    exact MeasureTheory.integral_mul_const c _
  rw [h, torusAverage_character]
  by_cases hk : k = 0 <;> simp [hk]

private theorem coord_hasFDerivAt {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} (hK : DifferentiableAt ℂ Kinf θ) (j : Fin n) :
    HasFDerivAt (fun θ => (Kinf θ).1 j)
      ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.fst ℂ _ _).comp (fderiv ℂ Kinf θ)))
      θ :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ))).hasFDerivAt.comp θ hK.hasFDerivAt

private theorem periodic_clock {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}
    (hprim : IsPrimaryOnStrip Kinf ρ) (j : Fin n) (i : Fin n) (z : Fin n → ℂ)
    (hz : z ∈ complexStrip n ρ) :
    (Kinf (z + Pi.single i 1)).1 j - (z + Pi.single i 1 : Fin n → ℂ) j = (Kinf z).1 j - z j := by
  have h := hprim z hz (Pi.single i 1)
  have hc : (fun l => (((Pi.single i 1 : Fin n → ℤ) l : ℤ) : ℂ)) = Pi.single i 1 := by
    funext l
    by_cases hl : l = i <;> simp [hl]
  rw [hc] at h
  rw [h]
  simp only [Prod.fst_add, Pi.add_apply]
  ring

/-- If `∂_{I_j} H ≡ 1` on `D` and the exact torus is invariant at `s_∞ ω*`, the clock
coordinate is exact: `s_∞ ω*_j = 1`, and `K_∞,j(θ) = θ_j + c` on reals (nonresonance). -/
theorem clock_frequency {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ρ sinf γ τ : ℝ} {ωstar : Fin n → ℝ} (j : Fin n) (hρ : 0 < ρ)
    (hH1 : ∀ z ∈ D, fderiv ℂ H z (phaseBasis (.inr j)) = 1)
    (hKD : ∀ θ ∈ complexStrip n ρ, Kinf θ ∈ D)
    (hholo : DifferentiableOn ℂ Kinf (complexStrip n ρ)) (hprim : IsPrimaryOnStrip Kinf ρ)
    (hreal : IsRealOnReals Kinf)
    (hinv : ∀ θ ∈ complexStrip n ρ, invarianceError H Kinf (sinf • ωstar) θ = 0)
    (hγ : 0 < γ) (hdio : IsDiophantine γ τ (sinf • ωstar)) :
    sinf * ωstar j = 1 ∧
      ∃ c : ℝ, ∀ x : Fin n → ℝ, (Kinf fun i => (x i : ℂ)).1 j = ((x j + c : ℝ) : ℂ) := by
  have hopen := isOpen_complexStrip n ρ
  set ω : Fin n → ℂ := fun i => ((sinf • ωstar) i : ℂ) with hω
  -- the `j`-th angle equation
  have hf' : ∀ θ ∈ complexStrip n ρ,
      fderiv ℂ (fun θ => (Kinf θ).1 j) θ ω = 1 := by
    intro θ hθ
    have hK := (hholo.differentiableAt (hopen.mem_nhds hθ))
    rw [(coord_hasFDerivAt hK j).fderiv]
    have h1 := congrArg (fun u => u.1 j) (hinv θ hθ)
    simp only [invarianceError, hamiltonianVectorFieldℂ, Prod.fst_sub, Pi.sub_apply,
      Prod.fst_zero, Pi.zero_apply] at h1
    have h2 := hH1 _ (hKD θ hθ)
    rw [phaseBasis_inr] at h2
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_fst']
    rw [← sub_eq_zero.mp h1, h2]
  -- `w = K_j - θ_j`
  set w : (Fin n → ℂ) → ℂ := fun θ => (Kinf θ).1 j - θ j with hw
  have hwdiff : DifferentiableOn ℂ w (complexStrip n ρ) := by
    refine DifferentiableOn.sub ?_ (differentiable_apply j |>.differentiableOn)
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
      (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ))).differentiable.comp_differentiableOn
      hholo
  have hwper : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → w (z + Pi.single i 1) = w z :=
    fun i z hz => periodic_clock hprim j i z hz
  have hwd : ∀ θ ∈ complexStrip n ρ, fderiv ℂ w θ ω = 1 - ω j := by
    intro θ hθ
    have hK := (hholo.differentiableAt (hopen.mem_nhds hθ))
    have hsub := (coord_hasFDerivAt hK j).sub
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).hasFDerivAt (x := θ))
    have e := hf' θ hθ
    rw [(coord_hasFDerivAt hK j).fderiv] at e
    rw [show w = (fun θ => (Kinf θ).1 j) - ⇑(ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin n => ℂ) j) from rfl, hsub.fderiv, sub_apply, e]
    rfl
  -- averaging
  have hone : sinf * ωstar j = 1 := by
    have h0 := torusAverage_complex_direction_eq_zero hρ hwdiff hwper ω
    have : (fun x : Fin n → ℝ => fderiv ℂ w (fun i => (x i : ℂ)) ω) =
        fun _ => 1 - ω j := funext fun x => hwd _ (ofReal_mem_complexStrip hρ x)
    rw [this, torusAverage_const_complex] at h0
    have h1 : ω j = 1 := by linear_combination -h0
    have h2 := congrArg Complex.re h1
    simpa [hω] using h2
  refine ⟨hone, ?_⟩
  -- the Fourier coefficients of `w` on the reals vanish off zero
  have hωj : ω j = 1 := by
    simp only [hω, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast hone
  have hzero : ∀ θ ∈ complexStrip n ρ, fderiv ℂ w θ ω = 0 := by
    intro θ hθ
    rw [hwd θ hθ, hωj]; ring
  set v : (Fin n → ℝ) → ℂ := fun x => w fun i => (x i : ℂ) with hv
  have hcoef : ∀ k : Fin n → ℤ, k ≠ 0 → torusCoeff v k = 0 := by
    intro k hk
    have h := torusCoeff_fderiv hρ hwdiff hwper ω k
    have hl : torusCoeff (fun x : Fin n → ℝ => fderiv ℂ w (fun j => (x j : ℂ)) ω) k = 0 := by
      have : (fun x : Fin n → ℝ => fderiv ℂ w (fun j => (x j : ℂ)) ω) = fun _ => 0 :=
        funext fun x => hzero _ (ofReal_mem_complexStrip hρ x)
      rw [this, torusCoeff_const_complex]
      simp
    rw [hl] at h
    have hne : (2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * ω j) ≠ 0 := by
      have hsum : (∑ j, (k j : ℂ) * ω j) =
          ((∑ i, (k i : ℝ) * (sinf • ωstar) i : ℝ) : ℂ) := by
        push_cast [hω]
        rfl
      rw [hsum]
      have hpos : 0 < ∑ i, |(k i : ℝ)| := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
        exact lt_of_lt_of_le (by simpa using hi)
          (Finset.single_le_sum (f := fun i => |(k i : ℝ)|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)) |>.trans_le' le_rfl
      have hd := hdio k hk
      have hlow : 0 < γ / (∑ i, |(k i : ℝ)|) ^ τ := by positivity
      have habs : (∑ i, (k i : ℝ) * (sinf • ωstar) i) ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hd
        linarith
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr habs)
      exact_mod_cast Real.pi_ne_zero
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  have hvc : Continuous v :=
    hwdiff.continuousOn.comp_continuous
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
      (fun x => ofReal_mem_complexStrip hρ x)
  have hvp : ∀ (i : Fin n) x, v (x + Pi.single i 1) = v x := by
    intro i x
    have : (fun j => (((x + Pi.single i (1 : ℝ) : Fin n → ℝ) j : ℝ) : ℂ)) =
        (fun j => (x j : ℂ)) + Pi.single i 1 := by
      funext l
      by_cases hl : l = i <;> simp [hl]
    simp only [hv, this]
    exact hwper i _ (ofReal_mem_complexStrip hρ x)
  have hconst : ∀ x, v x = torusAverage v := by
    intro x
    have hu := eq_zero_of_torusCoeff_eq_zero (v := fun y => v y - torusAverage v)
      (hvc.sub continuous_const) (fun i y => by simp only [hvp i y]) (fun k => by
        rw [torusCoeff_sub hvc continuous_const, torusCoeff_const_complex]
        by_cases hk : k = 0
        · subst hk
          rw [torusCoeff_zero]
          simp
        · rw [hcoef k hk]
          simp [hk]) x
    exact sub_eq_zero.mp hu
  -- realness
  obtain ⟨z, hz⟩ := hreal 0
  refine ⟨z.1 j, fun x => ?_⟩
  have h0 : v 0 = (z.1 j : ℂ) := by
    show (Kinf fun i => (((0 : Fin n → ℝ) i : ℝ) : ℂ)).1 j -
      ((((0 : Fin n → ℝ) j : ℝ)) : ℂ) = _
    rw [hz]
    simp
  have hx := hconst x
  have hx0 := hconst 0
  have : (Kinf fun i => (x i : ℂ)).1 j - (x j : ℂ) = (z.1 j : ℂ) := by
    show v x = _
    exact (hx.trans hx0.symm).trans h0
  push_cast
  linear_combination this

end KAM.Certificate
