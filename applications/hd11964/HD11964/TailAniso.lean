/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.TailBound

/-!
# HD 11964: the tails on an anisotropic strip (HD11964-ROT, piece 2, anisotropic)

The isotropic bounds of `HD11964.TailBound` weigh the model's remainder by `e^{-2πρ|k|₁}` with one
width `ρ` for both angles. For HD 11964 the Fourier decay is very different in the two angles
(`e^{-0.30|k_c|}` against `0.116^{|k_b|}`, HD11964-PROD), and the Taylor remainder of a cell model
does not decay in `k` by itself, so an isotropic `ρ` loses the fast `k_b` decay (HD11964-ROT,
part 3: the isotropic tail bound is `10⁻⁴` or worse on the worst cell). Here the strip is
anisotropic,
`stripA ρ = {θ : |Im θ_j| < ρ_j}`, and the decay is `e^{-2π(σ₀|k_0| + σ₁|k_1|)}` for `σ_j < ρ_j`.

* `intervalIntegral_shift_im`: the contour shift of a `1`-periodic holomorphic function on a
  horizontal strip (Cauchy's theorem on a rectangle; the vertical sides cancel by periodicity).
* `iint_swap`: Fubini on `[0, 1]²` for continuous integrands.
* `norm_iint_coeff_le_aniso`: anisotropic coefficient decay (one shift per angle).
* `abs_dirDeriv_sub_projS_le_aniso`, `abs_dirDeriv_sub_projS_le_of_cell_aniso`,
  `tails_HD_of_cell_aniso`: the tail bounds of `HD11964.TailBound` on `stripA`, with the weight
  `tailWeightA` and, for HD 11964, the closed form `boxTailBoundA 80 20`.
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory KAM.Planetary KAM.Application.LambdaDrift
open scoped Real ContDiff

namespace HD11964.Cover

/-- The anisotropic strip `{θ : |Im θ_j| < ρ_j}`. -/
def stripA (ρ : Fin 2 → ℝ) : Set (Fin 2 → ℂ) := {θ | ∀ j, |(θ j).im| < ρ j}

theorem ofReal_mem_stripA {ρ : Fin 2 → ℝ} (hρ : ∀ j, 0 < ρ j) (x : Fin 2 → ℝ) :
    (fun j => (x j : ℂ)) ∈ stripA ρ := fun j => by simpa using hρ j

theorem isOpen_stripA (ρ : Fin 2 → ℝ) : IsOpen (stripA ρ) := by
  have e : stripA ρ = ⋂ j, {θ : Fin 2 → ℂ | |(θ j).im| < ρ j} := by
    ext θ; simp [stripA]
  rw [e]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp (continuous_apply j)))
      continuous_const

/-! ### The contour shift and Fubini -/

/-- **The contour shift** of a `1`-periodic holomorphic function on the strip `|Im z| < r`:
`∫₀¹ f(x + iτ) dx = ∫₀¹ f(x) dx` for `|τ| < r`. -/
theorem intervalIntegral_shift_im {f : ℂ → ℂ} {r τ : ℝ}
    (hf : DifferentiableOn ℂ f {z | |z.im| < r}) (hp : ∀ z : ℂ, |z.im| < r → f (z + 1) = f z)
    (hτ : |τ| < r) :
    ∫ x in (0 : ℝ)..1, f (x + τ * Complex.I) = ∫ x in (0 : ℝ)..1, f x := by
  have hy : ∀ y ∈ Set.uIcc (0 : ℝ) τ, |y| < r := by
    intro y hy
    rw [Set.mem_uIcc] at hy
    refine lt_of_le_of_lt ?_ hτ
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
    · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
  have hR : Set.uIcc (0 : ℂ).re (1 + τ * Complex.I).re ×ℂ Set.uIcc (0 : ℂ).im (1 + τ * Complex.I).im
      ⊆ {z | |z.im| < r} := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    have h2 : z.im ∈ Set.uIcc (0 : ℝ) τ := by simpa using hz.2
    exact hy _ h2
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f 0 (1 + τ * Complex.I)
    (hf.mono hR)
  have e1 : (1 + (τ : ℂ) * Complex.I).re = 1 := by simp
  have e2 : (1 + (τ : ℂ) * Complex.I).im = τ := by simp
  rw [e1, e2] at h
  simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_zero, zero_mul, add_zero,
    Complex.ofReal_one, zero_add, smul_eq_mul] at h
  have hv : ∫ y in (0 : ℝ)..τ, f (1 + y * Complex.I) = ∫ y in (0 : ℝ)..τ, f (y * Complex.I) := by
    refine intervalIntegral.integral_congr fun y hy' => ?_
    have him : |((y : ℂ) * Complex.I).im| < r := by simpa using hy y hy'
    rw [add_comm]
    exact hp _ him
  rw [hv] at h
  linear_combination -h

/-- **Fubini on `[0, 1]²`** for a continuous integrand. -/
theorem iint_swap {F : ℝ → ℝ → ℂ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F x y := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact MeasureTheory.integral_integral_swap hint

/-! ### Anisotropic coefficient decay -/

theorem differentiable_vec2_right (c : ℂ) : Differentiable ℂ fun z : ℂ => (![c, z] : Fin 2 → ℂ) :=
  differentiable_pi.2 fun j => by fin_cases j <;> simp

theorem differentiable_vec2_left (c : ℂ) : Differentiable ℂ fun z : ℂ => (![z, c] : Fin 2 → ℂ) :=
  differentiable_pi.2 fun j => by fin_cases j <;> simp

theorem vec2_mem_stripA {ρ : Fin 2 → ℝ} {z₀ z₁ : ℂ} (h₀ : |z₀.im| < ρ 0) (h₁ : |z₁.im| < ρ 1) :
    (![z₀, z₁] : Fin 2 → ℂ) ∈ stripA ρ := fun j => by fin_cases j <;> simpa

theorem vec2_add_single_one (z₀ z₁ : ℂ) :
    (![z₀, z₁ + 1] : Fin 2 → ℂ) = ![z₀, z₁] + Pi.single 1 1 := by
  funext j; fin_cases j <;> simp

theorem vec2_add_single_zero (z₀ z₁ : ℂ) :
    (![z₀ + 1, z₁] : Fin 2 → ℂ) = ![z₀, z₁] + Pi.single 0 1 := by
  funext j; fin_cases j <;> simp

theorem norm_charE_neg_vec2 (k : Fin 2 → ℤ) (z₀ z₁ : ℂ) :
    ‖charE (-k) ![z₀, z₁]‖ = Real.exp (2 * π * ((k 0 : ℝ) * z₀.im + (k 1 : ℝ) * z₁.im)) := by
  rw [charE_eq_character, KAM.norm_character]
  congr 1
  simp [Fin.sum_univ_two]
  ring

/-- **Anisotropic coefficient decay**: for `f` holomorphic, `1`-periodic and bounded by `A` on
`stripA ρ`, `|f̂_k| ≤ e^{-2π(σ₀|k_0| + σ₁|k_1|)} A` for `0 ≤ σ_j < ρ_j` (one contour shift per
angle). -/
theorem norm_iint_coeff_le_aniso {ρ σ : Fin 2 → ℝ} {A : ℝ} {f : (Fin 2 → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (stripA ρ))
    (hp : ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ → f (θ + Pi.single j 1) = f θ)
    (hA : ∀ θ ∈ stripA ρ, ‖f θ‖ ≤ A) (k : Fin 2 → ℤ) (hσ0 : ∀ j, 0 ≤ σ j) (hσ : ∀ j, σ j < ρ j) :
    ‖∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
        f ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]‖ ≤
      Real.exp (-(2 * π * (σ 0 * |(k 0 : ℝ)| + σ 1 * |(k 1 : ℝ)|))) * A := by
  have hρ : ∀ j, 0 < ρ j := fun j => (hσ0 j).trans_lt (hσ j)
  set F : ℂ → ℂ → ℂ := fun z₀ z₁ => f ![z₀, z₁] * charE (-k) ![z₀, z₁] with hFdef
  set τ : Fin 2 → ℝ := fun j => if 0 ≤ k j then -σ j else σ j with hτdef
  have hτ : ∀ j, |τ j| = σ j := fun j => by
    simp only [hτdef]; split_ifs <;> simp [abs_of_nonneg (hσ0 j)]
  have hτρ : ∀ j, |τ j| < ρ j := fun j => (hτ j).symm ▸ hσ j
  have hF : ∀ z₀ z₁ : ℂ, |z₀.im| < ρ 0 → |z₁.im| < ρ 1 →
      DifferentiableAt ℂ (fun θ : Fin 2 → ℂ => f θ * charE (-k) θ) ![z₀, z₁] := fun z₀ z₁ h₀ h₁ =>
    ((hf _ (vec2_mem_stripA h₀ h₁)).differentiableAt
      (isOpen_stripA ρ |>.mem_nhds (vec2_mem_stripA h₀ h₁))).mul
      ((differentiable_charE _) _)
  -- holomorphy and periodicity in each variable
  have hd1 : ∀ z₀ : ℂ, |z₀.im| < ρ 0 → DifferentiableOn ℂ (F z₀) {z | |z.im| < ρ 1} :=
    fun z₀ h₀ z hz => by
      have h := (hF z₀ z h₀ hz).comp z (differentiable_vec2_right z₀ z)
      exact h.differentiableWithinAt
  have hd0 : ∀ z₁ : ℂ, |z₁.im| < ρ 1 → DifferentiableOn ℂ (fun z => F z z₁) {z | |z.im| < ρ 0} :=
    fun z₁ h₁ z hz => by
      have h := (hF z z₁ hz h₁).comp z (differentiable_vec2_left z₁ z)
      exact h.differentiableWithinAt
  have hp1 : ∀ z₀ : ℂ, |z₀.im| < ρ 0 → ∀ z : ℂ, |z.im| < ρ 1 → F z₀ (z + 1) = F z₀ z := by
    intro z₀ h₀ z hz
    simp only [hFdef, vec2_add_single_one, hp 1 _ (vec2_mem_stripA h₀ hz), charE_add_single]
  have hp0 : ∀ z₁ : ℂ, |z₁.im| < ρ 1 → ∀ z : ℂ, |z.im| < ρ 0 → F (z + 1) z₁ = F z z₁ := by
    intro z₁ h₁ z hz
    simp only [hFdef, vec2_add_single_zero, hp 0 _ (vec2_mem_stripA hz h₁), charE_add_single]
  have hre : ∀ t : ℝ, |((t : ℂ)).im| = 0 := fun t => by simp
  -- step 1: shift the inner variable
  have s1 : ∀ t₀ : ℝ, ∫ t₁ in (0 : ℝ)..1, F t₀ t₁ =
      ∫ t₁ in (0 : ℝ)..1, F t₀ (t₁ + τ 1 * Complex.I) := fun t₀ =>
    (intervalIntegral_shift_im (hd1 t₀ (by rw [hre]; exact hρ 0)) (hp1 t₀ (by rw [hre]; exact hρ 0))
      (hτρ 1)).symm
  -- continuity on the shifted torus
  have hcont : Continuous fun p : ℝ × ℝ => F p.1 (p.2 + τ 1 * Complex.I) := by
    have hm : ∀ p : ℝ × ℝ, (![(p.1 : ℂ), (p.2 : ℂ) + τ 1 * Complex.I] : Fin 2 → ℂ) ∈ stripA ρ :=
      fun p => vec2_mem_stripA (by rw [hre]; exact hρ 0) (by simpa using hτρ 1)
    have hv : Continuous fun p : ℝ × ℝ => (![(p.1 : ℂ), (p.2 : ℂ) + τ 1 * Complex.I] : Fin 2 → ℂ) :=
      continuous_pi fun j => by fin_cases j <;> simp <;> fun_prop
    exact (hf.continuousOn.comp_continuous hv hm).mul ((differentiable_charE _).continuous.comp hv)
  -- step 2: Fubini; step 3: shift the other variable
  have s3 : ∀ t₁ : ℝ, ∫ t₀ in (0 : ℝ)..1, F t₀ (t₁ + τ 1 * Complex.I) =
      ∫ t₀ in (0 : ℝ)..1, F (t₀ + τ 0 * Complex.I) (t₁ + τ 1 * Complex.I) := by
    intro t₁
    have h₁ : |((t₁ : ℂ) + τ 1 * Complex.I).im| < ρ 1 := by simpa using hτρ 1
    exact (intervalIntegral_shift_im (hd0 _ h₁) (hp0 _ h₁) (hτρ 0)).symm
  have e : (∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
      f ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]) =
      ∫ t₁ in (0 : ℝ)..1, ∫ t₀ in (0 : ℝ)..1,
        F (t₀ + τ 0 * Complex.I) (t₁ + τ 1 * Complex.I) := by
    rw [show (∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
        f ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]) =
        ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1, F t₀ t₁ from rfl]
    simp only [s1]
    rw [iint_swap (F := fun t₀ t₁ => F t₀ (t₁ + τ 1 * Complex.I)) hcont]
    simp only [s3]
  rw [e]
  refine norm_iint_le fun t₁ t₀ => ?_
  have h₀ : |((t₀ : ℂ) + τ 0 * Complex.I).im| < ρ 0 := by simpa using hτρ 0
  have h₁ : |((t₁ : ℂ) + τ 1 * Complex.I).im| < ρ 1 := by simpa using hτρ 1
  simp only [hFdef]
  rw [norm_mul, mul_comm]
  refine mul_le_mul (le_of_eq ?_) (hA _ (vec2_mem_stripA h₀ h₁)) (norm_nonneg _)
    (Real.exp_pos _).le
  rw [norm_charE_neg_vec2]
  congr 1
  have hk : ∀ j, (k j : ℝ) * τ j = -(σ j * |(k j : ℝ)|) := by
    intro j
    simp only [hτdef]
    split_ifs with h
    · rw [abs_of_nonneg (by exact_mod_cast h)]; ring
    · rw [abs_of_neg (by exact_mod_cast not_le.mp h)]; ring
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [hk 0, hk 1]
  ring

/-! ### The tails on the anisotropic strip -/

/-- **The tail bound at a point, anisotropic**: `abs_dirDeriv_sub_projS_le` with the slice's
extension holomorphic, periodic and within `r` of `Σ_{k ∈ T} a_k e(k·θ)` on `stripA ρ`, and the
weight `tailWeightA S i σ₀ σ₁` for `0 < σ_j < ρ_j`. -/
theorem abs_dirDeriv_sub_projS_le_aniso {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) {Q : Phase (2 + 2) → ℝ} (hQ : ContDiffOn ℝ ∞ Q U)
    (S T : Finset (Fin 2 → ℤ)) (i : Fin 2) {w : Phase (2 + 2)} (hw : w ∈ U)
    {ρ σ : Fin 2 → ℝ} {r : ℝ} (hσ0 : ∀ j, 0 < σ j) (hσ : ∀ j, σ j < ρ j)
    {Qc : (Fin 2 → ℂ) → ℂ} (hQc : DifferentiableOn ℂ Qc (stripA ρ))
    (hper : ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ → Qc (θ + Pi.single j 1) = Qc θ)
    (hlink : ∀ t : Fin 2 → ℝ, Qc (fun j => (t j : ℂ)) = (Q (withAngles w fun j => 2 * π * t j) : ℂ))
    (a : (Fin 2 → ℤ) → ℂ) (hrem : ∀ θ ∈ stripA ρ, ‖Qc θ - ∑ k ∈ T, a k * charE k θ‖ ≤ r) :
    |dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => Q y - projS S Q y) w| ≤
      ∑ k ∈ T \ S, |(k i : ℝ)| * ‖a k‖ + r * tailWeightA S i (σ 0) (σ 1) := by
  have hρ : ∀ j, 0 < ρ j := fun j => (hσ0 j).trans (hσ j)
  have hcQ : Continuous fun x : Fin 2 → ℝ => Qc (fun j => (x j : ℂ)) :=
    hQc.continuousOn.comp_continuous continuous_ofRealVec fun x => ofReal_mem_stripA hρ x
  have hgQ : (fun x : Fin 2 → ℝ => (Q (withAngles w fun j => 2 * π * x j) : ℂ)) =
      fun x => Qc (fun j => (x j : ℂ)) := funext fun x => (hlink x).symm
  have hpers : ∀ (j : Fin 2) (x : Fin 2 → ℝ),
      Q (withAngles w fun l => 2 * π * (x + Pi.single j 1 : Fin 2 → ℝ) l) =
        Q (withAngles w fun l => 2 * π * x l) := by
    intro j x
    apply Complex.ofReal_injective
    rw [← hlink, ← hlink, ofReal_add_single, hper j _ (ofReal_mem_stripA hρ x)]
  have htrig : Differentiable ℂ fun θ : Fin 2 → ℂ => ∑ k ∈ T, a k * charE k θ :=
    Differentiable.fun_sum fun k _ => (differentiable_const _).mul (differentiable_charE k)
  have hcoef : ∀ k, ‖chartCoeff Q k w - (if k ∈ T then a k else 0)‖ ≤
      Real.exp (-(2 * π * (σ 0 * |(k 0 : ℝ)| + σ 1 * |(k 1 : ℝ)|))) * r := by
    intro k
    have hf : DifferentiableOn ℂ (fun θ => Qc θ - ∑ k ∈ T, a k * charE k θ) (stripA ρ) :=
      hQc.sub htrig.differentiableOn
    have hfp : ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
        Qc (θ + Pi.single j 1) - ∑ k ∈ T, a k * charE k (θ + Pi.single j 1) =
          Qc θ - ∑ k ∈ T, a k * charE k θ := by
      intro j θ hθ
      simp only [hper j θ hθ, charE_add_single]
    have h := norm_iint_coeff_le_aniso (f := fun θ => Qc θ - ∑ k ∈ T, a k * charE k θ) hf hfp
      hrem k (fun j => (hσ0 j).le) hσ
    have hvc : Continuous fun x : Fin 2 → ℝ =>
        Qc (fun j => (x j : ℂ)) - ∑ k' ∈ T, a k' * charE k' (fun j => (x j : ℂ)) :=
      hcQ.sub (htrig.continuous.comp continuous_ofRealVec)
    rw [chartCoeff_eq_torusCoeff Q w (hgQ ▸ hcQ) k, hgQ, ← torusCoeff_sub_trig hcQ T a k,
      torusCoeff_eq_iint hvc k]
    refine (le_of_eq ?_).trans h
    congr 1
    refine intervalIntegral.integral_congr fun t₀ _ =>
      intervalIntegral.integral_congr fun t₁ _ => ?_
    show (_ - _) * _ = (_ - _) * _
    rw [vec2_ofReal]
  have h := abs_dirDeriv_sub_projS_le_of_coeff hU hsat hQ S T i hw hpers a _ hcoef
    (((summable_absMul_expA i (hσ0 0) (hσ0 1)).mul_right r).congr fun k => by ring)
  refine h.trans (le_of_eq ?_)
  rw [tailWeightA, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  split_ifs <;> ring

/-- The cell form of `abs_dirDeriv_sub_projS_le_aniso` (the cell data's form). -/
theorem abs_dirDeriv_sub_projS_le_of_cell_aniso {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) {Q : Phase (2 + 2) → ℝ} (hQ : ContDiffOn ℝ ∞ Q U)
    (S : Finset (Fin 2 → ℤ)) (i : Fin 2) (cell : AffineCell) (hcell : cell.wf = true)
    {ρ σ : Fin 2 → ℝ} {r : ℝ} (hσ0 : ∀ j, 0 < σ j) (hσ : ∀ j, σ j < ρ j)
    {Qc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {p : TFPoly}
    (hQd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Qc θ u) (stripA ρ))
    (hQp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
      Qc (θ + Pi.single j 1) u = Qc θ u)
    (hQm : ∀ θ ∈ stripA ρ, ∀ u ∈ polyDiscC 6 1, ‖Qc θ u - p.eval θ u‖ ≤ r)
    (hlink : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Qc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (Q (withAngles w (fun i => 2 * π * t i)) : ℂ))
    {w : Phase (2 + 2)} (hw : w ∈ cell.toSet) (hwU : w ∈ U) :
    |dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => Q y - projS S Q y) w| ≤
      ∑ k ∈ p.support \ S, |(k i : ℝ)| * l1 (p k) + r * tailWeightA S i (σ 0) (σ 1) := by
  obtain ⟨u, hu, hx⟩ := hw
  have hw' : w ∈ cell.toSet := ⟨u, hu, hx⟩
  set uc : Fin 6 → ℂ := fun j => (cell.coord (cellCoord w) j : ℂ) with huc
  have hU' : uc ∈ polyDiscC 6 1 := by
    intro j
    rw [huc, hx, AffineCell.coord_map cell hcell u, Complex.norm_real, Real.norm_eq_abs]
    exact hu j
  have hrem : ∀ θ ∈ stripA ρ, ‖Qc θ uc -
      ∑ k ∈ p.support, MvPolynomial.eval uc (p k) * charE k θ‖ ≤ r := fun θ hθ => by
    have h := hQm θ hθ uc hU'
    unfold TFPoly.eval Finsupp.sum at h
    exact h
  have h := abs_dirDeriv_sub_projS_le_aniso hU hsat hQ S p.support i hwU hσ0 hσ (hQd uc hU')
    (fun j θ hθ => hQp uc hU' j θ hθ) (fun t => hlink w hw' t)
    (fun k => MvPolynomial.eval uc (p k)) hrem
  refine h.trans (add_le_add (Finset.sum_le_sum fun k _ => ?_) le_rfl)
  exact mul_le_mul_of_nonneg_left (norm_eval_le_l1 _ hU') (abs_nonneg _)

/-- **The tails `T₁`, `T₂` on a cell, anisotropic** (`abs_tails_le_of_cell` on `stripA ρ`). -/
theorem abs_tails_le_of_cell_aniso {ν : Fin 2 → ℝ} {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) (hdom : U ⊆ poincareProdDom 2) {S : Finset (Fin 2 → ℤ)}
    {P : Phase (2 + 2) → ℝ} (hP : ContDiffOn ℝ ∞ P U) (hS : IsModeSet S (keplerFreq ν) U)
    (cell : AffineCell) (hcell : cell.wf = true) (i : Fin 2) {ρ σ : Fin 2 → ℝ} {rP rG : ℝ}
    (hσ0 : ∀ j, 0 < σ j) (hσ : ∀ j, σ j < ρ j)
    {Pc Gc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {p g : TFPoly}
    (hPd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Pc θ u) (stripA ρ))
    (hPp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
      Pc (θ + Pi.single j 1) u = Pc θ u)
    (hPm : ∀ θ ∈ stripA ρ, ∀ u ∈ polyDiscC 6 1, ‖Pc θ u - p.eval θ u‖ ≤ rP)
    (hPl : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Pc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (P (withAngles w (fun i => 2 * π * t i)) : ℂ))
    (hGd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Gc θ u) (stripA ρ))
    (hGp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
      Gc (θ + Pi.single j 1) u = Gc θ u)
    (hGm : ∀ θ ∈ stripA ρ, ∀ u ∈ polyDiscC 6 1, ‖Gc θ u - g.eval θ u‖ ≤ rG)
    (hGl : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Gc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (pb (fun y => P y - projS S P y / 2) (chiStar S (keplerFreq ν) P)
          (withAngles w (fun i => 2 * π * t i)) : ℂ))
    {w : Phase (2 + 2)} (hw : w ∈ cell.toSet) (hwU : w ∈ U) :
    |dirDeriv (angleDir (Fin.castAdd 2 i))
        (residual₁ (hProd 1 ν) P (chiStar S (keplerFreq ν) P)) w| ≤
      ∑ k ∈ p.support \ S, |(k i : ℝ)| * l1 (p k) + rP * tailWeightA S i (σ 0) (σ 1) ∧
    |dirDeriv (angleDir (Fin.castAdd 2 i)) (residual₂ (hProd 1 ν) P (chiStar S (keplerFreq ν) P)
        (chiStar S (keplerFreq ν) (pb (fun y => P y - projS S P y / 2)
          (chiStar S (keplerFreq ν) P)))) w| ≤
      ∑ k ∈ g.support \ S, |(k i : ℝ)| * l1 (g k) + rG * tailWeightA S i (σ 0) (σ 1) := by
  set χ₁ := chiStar S (keplerFreq ν) P
  set G₂ := pb (fun y => P y - projS S P y / 2) χ₁
  have hfrq : ∀ w ∈ U, ContDiffAt ℝ ∞ (keplerFreq ν) (fast w.2) := fun w hw =>
    contDiffAt_keplerFreq ν (fast_ne_zero_of_mem_dom (hdom hw))
  have hχ₁ : ContDiffOn ℝ ∞ χ₁ U := contDiffOn_chiStar hU hsat hP hfrq hS
  have hA : ContDiffOn ℝ ∞ (fun y => P y - projS S P y / 2) U :=
    hP.sub ((contDiffOn_projS hU hsat S hP).div_const 2)
  have hG₂ : ContDiffOn ℝ ∞ G₂ U := fun y hy =>
    (contDiffAt_pb (hA.contDiffAt (hU.mem_nhds hy))
      (hχ₁.contDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hn : U ∈ 𝓝 w := hU.mem_nhds hwU
  have e₁ : dirDeriv (angleDir (Fin.castAdd 2 i)) (residual₁ (hProd 1 ν) P χ₁) w =
      dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => P y - projS S P y) w := by
    unfold dirDeriv
    rw [Filter.EventuallyEq.fderiv_eq (Filter.mem_of_superset hn fun y hy =>
      (residual₁_tail hU hsat hdom hP hS).1 y hy)]
  have e₂ : dirDeriv (angleDir (Fin.castAdd 2 i))
      (residual₂ (hProd 1 ν) P χ₁ (chiStar S (keplerFreq ν) G₂)) w =
      dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => G₂ y - projS S G₂ y) w := by
    unfold dirDeriv
    rw [Filter.EventuallyEq.fderiv_eq (Filter.mem_of_superset hn fun y hy =>
      (residual₂_tail hU hsat hdom hP hS).1 y hy)]
  refine ⟨?_, ?_⟩
  · rw [e₁]
    exact abs_dirDeriv_sub_projS_le_of_cell_aniso hU hsat hP S i cell hcell hσ0 hσ hPd hPp hPm
      hPl hw hwU
  · rw [e₂]
    exact abs_dirDeriv_sub_projS_le_of_cell_aniso hU hsat hG₂ S i cell hcell hσ0 hσ hGd hGp hGm
      hGl hw hwU

/-- **The tails of HD 11964 on a cell, anisotropic**: from cell models of `P` and `G₂` on
`stripA ρ`, with the closed-form weight of `modesHD` at any `q₀, q₁ < 1` with
`e^{-2πσ_j} ≤ q_j`, `0 < σ_j < ρ_j`. Every quantity on the right is cell data. -/
theorem tails_HD_of_cell_aniso (cell : AffineCell) (hcell : cell.wf = true) (i : Fin 2)
    {ρ σ : Fin 2 → ℝ} {rP rG q₀ q₁ : ℝ} (hσ0 : ∀ j, 0 < σ j) (hσ : ∀ j, σ j < ρ j)
    (hq₀ : Real.exp (-(2 * π * σ 0)) ≤ q₀) (hq₀1 : q₀ < 1)
    (hq₁ : Real.exp (-(2 * π * σ 1)) ≤ q₁) (hq₁1 : q₁ < 1)
    {Pc Gc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {p g : TFPoly}
    (hPd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Pc θ u) (stripA ρ))
    (hPp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
      Pc (θ + Pi.single j 1) u = Pc θ u)
    (hPm : ∀ θ ∈ stripA ρ, ∀ u ∈ polyDiscC 6 1, ‖Pc θ u - p.eval θ u‖ ≤ rP)
    (hPl : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Pc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (chartPert nu mu (withAngles w (fun i => 2 * π * t i)) : ℂ))
    (hGd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Gc θ u) (stripA ρ))
    (hGp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
      Gc (θ + Pi.single j 1) u = Gc θ u)
    (hGm : ∀ θ ∈ stripA ρ, ∀ u ∈ polyDiscC 6 1, ‖Gc θ u - g.eval θ u‖ ≤ rG)
    (hGl : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Gc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (G2HD (withAngles w (fun i => 2 * π * t i)) : ℂ))
    {w : Phase (2 + 2)} (hw : w ∈ cell.toSet) (hwU : w ∈ openHD) :
    |dirDeriv (angleDir (Fin.castAdd 2 i)) (residual₁ (hProd 1 nu) (chartPert nu mu) chi1HD) w| ≤
      ∑ k ∈ p.support \ modesHD, |(k i : ℝ)| * l1 (p k) + rP * boxTailBoundA 80 20 i q₀ q₁ ∧
    |dirDeriv (angleDir (Fin.castAdd 2 i))
        (residual₂ (hProd 1 nu) (chartPert nu mu) chi1HD chi2HD) w| ≤
      ∑ k ∈ g.support \ modesHD, |(k i : ℝ)| * l1 (g k) + rG * boxTailBoundA 80 20 i q₀ q₁ := by
  have hρ : ∀ j, 0 < ρ j := fun j => (hσ0 j).trans (hσ j)
  have hW := tailWeightA_le_boxTailBoundA 80 20 i (hσ0 0) (hσ0 1) modesHD_box hq₀ hq₀1 hq₁ hq₁1
  have hrP : 0 ≤ rP := (norm_nonneg _).trans (hPm _ (ofReal_mem_stripA hρ 0) 0
    (fun j => by simp))
  have hrG : 0 ≤ rG := (norm_nonneg _).trans (hGm _ (ofReal_mem_stripA hρ 0) 0
    (fun j => by simp))
  have h := abs_tails_le_of_cell_aniso isOpen_openHD isAngleSaturated_openHD openHD_subset_dom
    contDiffOn_chartPert_HD isModeSet_HD cell hcell i hσ0 hσ hPd hPp hPm hPl hGd hGp hGm hGl hw hwU
  exact ⟨h.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hW hrP)),
    h.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hW hrG))⟩

end HD11964.Cover

end
