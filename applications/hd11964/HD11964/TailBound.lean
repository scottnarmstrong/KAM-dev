/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.ChiRot
public import HD11964.TailSum
public import KAM.Strip.Fourier
public import KAM.Strip.FourierBasic
public import KAM.Strip.FourierDerivative
public import KAM.Strip.FourierSeries

/-!
# HD 11964: the tails `T₁`, `T₂` from Fourier decay on a strip (HD11964-ROT, piece 2)

On an open angle-saturated `U`, `r₁ = P - Π_S P` and `r₂ = G₂ - Π_S G₂` (HD11964-CHI), so the
tails `T_j = D_i r_j` of the bracket bound are `D_i (Q - Π_S Q)` with `Q = P` or `G₂`.

* `torusCoeff_eq_iint`: `KAM.torusCoeff` is the iterated integral over `[0, 1]²` (Fubini).
* `norm_fourierCoeff2_sub_le_decay` (2a): a cell model of `P` on the strip of width `ρ`
  (holomorphic and `1`-periodic in `θ`, within `r_P` of `p`) has `|P̂_k - p_k| ≤ e^{-2πρ|k|₁} r_P`
  (`KAM.norm_torusCoeff_le`).
* `norm_genChi_sub_le_decay` (2b): the certified remainder of the generator with that decay
  (AUDIT-HD11964-LEMMAS-1, L6): the weight of `r_P B_k` becomes `e^{2π(ρ' - ρ)|k|₁}` on the strip
  of width `ρ'`.
* `abs_dirDeriv_sub_projS_le` (2c): at a point `w`, if `Qc` extends the slice
  `t ↦ Q(withAngles w (2πt))` holomorphically and periodically to the strip and is within `r` of
  `Σ_{k ∈ T} a_k e(k·θ)` there, then
  `|D_i (Q - Π_S Q)(w)| ≤ Σ_{k ∈ T \ S} |k_i| |a_k| + r Σ_{k ∉ S} |k_i| e^{-2πρ|k|₁}`
  (Fourier inversion of `∂_i` of the slice, `KAM.hasSum_torusCoeff_mul_character`).
* `abs_tails_le_of_cell` (2d): `T₁` and `T₂` on a cell from cell models of `P` and `G₂`.
* `tails_HD_of_cell`: the HD 11964 instance (`openHD`, `modesHD`, `χ₁ = chi1HD`, `G₂ = G2HD`,
  `χ₂ = chi2HD`), with the closed-form weight of `modesHD` (`K₀ = 80`, `K₁ = 20`) at a rational
  `q̄ ≥ e^{-2πρ}`: every quantity on the right is cell data.
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory KAM.Planetary KAM.Application.LambdaDrift
open KAM (complexStrip)
open scoped Real ContDiff

namespace HD11964.Cover

/-! ### The torus coefficient as an iterated integral -/

theorem setIntegral_Icc01 (f : ℝ → ℂ) :
    ∫ x in Icc (0 : ℝ) 1, f x = ∫ x in (0 : ℝ)..1, f x := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

/-- The average over the unit cube of `ℝ²` is the iterated integral over `[0, 1]²`. -/
theorem setIntegral_unitCube_eq_iint {f : (Fin 2 → ℝ) → ℂ} (hf : Continuous f) :
    ∫ x in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) 1), f x =
      ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1, f ![t₀, t₁] := by
  let e := MeasurableEquiv.finTwoArrow (α := ℝ)
  have he : MeasurePreserving e volume volume := volume_preserving_finTwoArrow ℝ
  have hset : Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) 1) = e ⁻¹' (Icc 0 1 ×ˢ Icc 0 1) := by
    ext F
    simp only [Set.mem_pi, mem_univ, true_implies, Fin.forall_fin_two, mem_preimage, mem_prod]
    simp [e, MeasurableEquiv.finTwoArrow]
  have h2 : ∀ F : Fin 2 → ℝ, f F = (fun p : ℝ × ℝ => f ![p.1, p.2]) (e F) := by
    intro F
    congr 1
    funext i
    fin_cases i <;> simp [e, MeasurableEquiv.finTwoArrow]
  rw [hset]
  have k := he.setIntegral_preimage_emb e.measurableEmbedding
    (fun p : ℝ × ℝ => f ![p.1, p.2]) (Icc 0 1 ×ˢ Icc 0 1)
  simp only [← h2] at k
  rw [k]
  have hc : Continuous fun p : ℝ × ℝ => f ![p.1, p.2] := hf.comp continuous_vec2
  have hint : IntegrableOn (fun p : ℝ × ℝ => f ![p.1, p.2]) (Icc 0 1 ×ˢ Icc 0 1)
      (volume.prod volume) :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint]
  simp only [setIntegral_Icc01]

theorem continuous_ofRealVec : Continuous fun x : Fin 2 → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

theorem charE_eq_character (k : Fin 2 → ℤ) (θ : Fin 2 → ℂ) : charE k θ = KAM.character k θ :=
  rfl

/-- **`KAM.torusCoeff` is the iterated integral** over `[0, 1]²`. -/
theorem torusCoeff_eq_iint {v : (Fin 2 → ℝ) → ℂ} (hv : Continuous v) (k : Fin 2 → ℤ) :
    KAM.torusCoeff v k =
      ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1, v ![t₀, t₁] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)] := by
  have hL : Continuous fun x : Fin 2 → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character _).continuous.comp continuous_ofRealVec
  have h := setIntegral_unitCube_eq_iint (hL.mul hv)
  unfold KAM.torusCoeff KAM.torusAverage
  refine h.trans ?_
  refine intervalIntegral.integral_congr fun t₀ _ => intervalIntegral.integral_congr fun t₁ _ => ?_
  show _ = _
  rw [vec2_ofReal]
  exact mul_comm _ _

/-! ### (2a) Coefficient decay of a cell model -/

theorem charE_add_single (k : Fin 2 → ℤ) (θ : Fin 2 → ℂ) (j : Fin 2) :
    charE k (θ + Pi.single j 1) = charE k θ :=
  KAM.character_add_single k θ j

theorem differentiable_charE (k : Fin 2 → ℤ) : Differentiable ℂ (charE k) :=
  KAM.differentiable_character k

theorem differentiable_tfEval (p : TFPoly) (u : Fin 6 → ℂ) :
    Differentiable ℂ fun θ => p.eval θ u := by
  unfold TFPoly.eval Finsupp.sum
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (differentiable_charE k)

theorem tfEval_add_single (p : TFPoly) (θ : Fin 2 → ℂ) (u : Fin 6 → ℂ) (j : Fin 2) :
    p.eval (θ + Pi.single j 1) u = p.eval θ u := by
  unfold TFPoly.eval
  simp only [charE_add_single]

/-- Coefficient decay for a function of `θ` holomorphic, `1`-periodic and bounded by `A` on the
strip (`KAM.norm_torusCoeff_le`, in the iterated form). -/
theorem norm_iint_coeff_le {ρ A : ℝ} (hρ : 0 < ρ) {f : (Fin 2 → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (complexStrip 2 ρ))
    (hp : ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ → f (θ + Pi.single j 1) = f θ)
    (hA : ∀ θ ∈ complexStrip 2 ρ, ‖f θ‖ ≤ A) (k : Fin 2 → ℤ) :
    ‖∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
        f ![(t₀ : ℂ), (t₁ : ℂ)] * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]‖ ≤
      Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|)) * A := by
  have hc : Continuous fun x : Fin 2 → ℝ => f (fun j => (x j : ℂ)) :=
    hf.continuousOn.comp_continuous continuous_ofRealVec fun x => KAM.ofReal_mem_complexStrip hρ x
  have h := KAM.norm_torusCoeff_le hρ hf hp hA k
  rw [torusCoeff_eq_iint hc k] at h
  refine (le_of_eq ?_).trans h
  congr 1
  refine intervalIntegral.integral_congr fun t₀ _ => intervalIntegral.integral_congr fun t₁ _ => ?_
  show f _ * _ = f _ * _
  rw [vec2_ofReal]

/-- **(2a) Coefficient decay of a cell model**: `|P̂_k(u) - p_k(u)| ≤ e^{-2πρ|k|₁} r_P`. -/
theorem norm_fourierCoeff2_sub_le_decay {Pc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {p : TFPoly}
    {ρ rP : ℝ} (hρ : 0 < ρ)
    (hPd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Pc θ u) (complexStrip 2 ρ))
    (hPp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ →
      Pc (θ + Pi.single j 1) u = Pc θ u)
    (hP : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖Pc θ u - p.eval θ u‖ ≤ rP)
    {u : Fin 6 → ℂ} (hu : u ∈ polyDiscC 6 1) (k : Fin 2 → ℤ) :
    ‖fourierCoeff2 Pc k u - MvPolynomial.eval u (p k)‖ ≤
      Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|)) * rP := by
  have hc : Continuous fun t : Fin 2 → ℝ => Pc (fun i => (t i : ℂ)) u :=
    (hPd u hu).continuousOn.comp_continuous continuous_ofRealVec
      fun x => KAM.ofReal_mem_complexStrip hρ x
  have hpc : Continuous fun t : Fin 2 → ℝ => p.eval (fun i => (t i : ℂ)) u :=
    (differentiable_tfEval p u).continuous.comp continuous_ofRealVec
  rw [← fourierCoeff2_eval p k u, fourierCoeff2_sub hc hpc k]
  exact norm_iint_coeff_le (f := fun θ => Pc θ u - p.eval θ u) hρ
    ((hPd u hu).sub (differentiable_tfEval p u).differentiableOn)
    (fun j θ hθ => by simp only [hPp u hu j θ hθ, tfEval_add_single]) (fun θ hθ => hP θ hθ u hu) k

/-! ### (2b) The certified remainder of the generator, with decay -/

/-- **(2b) The certified remainder of the generator with decay** (AUDIT-HD11964-LEMMAS-1, L6):
`norm_genChi_sub_le` with `|P̂_k - p_k| ≤ e^{-2πρ|k|₁} r_P` (the model holomorphic and periodic on
the strip of width `ρ`), evaluated on the strip of width `ρ'`. -/
theorem norm_genChi_sub_le_decay (S : Finset (Fin 2 → ℤ)) (om : (Fin 6 → ℂ) → Fin 2 → ℂ)
    (Pc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) {ρ ρ' rP : ℝ} (p c : TFPoly)
    (q : (Fin 2 → ℤ) → MvPolynomial (Fin 6) ℂ) (ε B : (Fin 2 → ℤ) → ℝ) (hρ : 0 < ρ)
    (hPd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Pc θ u) (complexStrip 2 ρ))
    (hPp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ →
      Pc (θ + Pi.single j 1) u = Pc θ u)
    (hP : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖Pc θ u - p.eval θ u‖ ≤ rP)
    (hq : ∀ k ∈ S, ∀ u ∈ polyDiscC 6 1,
      ‖(Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹ - MvPolynomial.eval u (q k)‖ ≤ ε k)
    (hB : ∀ k ∈ S, ∀ u ∈ polyDiscC 6 1, ‖(Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹‖ ≤ B k)
    (hc : ↑c.support ⊆ (S : Set (Fin 2 → ℤ))) :
    ∀ θ ∈ complexStrip 2 ρ', ∀ u ∈ polyDiscC 6 1, ‖genChi S om Pc θ u - c.eval θ u‖ ≤
      ∑ k ∈ S, Real.exp (2 * π * ρ' * ∑ i, |(k i : ℝ)|) *
        (Real.exp (-(2 * π * ρ * ∑ i, |(k i : ℝ)|)) * rP * B k + l1 (p k) * ε k +
          l1 (p k * q k - c k)) := by
  intro θ hθ u hu
  have hcoef := norm_fourierCoeff2_sub_le_decay hρ hPd hPp hP hu
  have hceval : c.eval θ u = ∑ k ∈ S, MvPolynomial.eval u (c k) * charE k θ := by
    unfold TFPoly.eval
    exact Finsupp.sum_of_support_subset c (fun k hk => hc hk) _ fun k _ => by simp
  rw [hceval, genChi, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  set inv := (Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹
  set ph := MvPolynomial.eval u (p k)
  have hsplit : fourierCoeff2 Pc k u * inv * charE k θ - MvPolynomial.eval u (c k) * charE k θ =
      ((fourierCoeff2 Pc k u - ph) * inv + ph * (inv - MvPolynomial.eval u (q k)) +
        MvPolynomial.eval u (p k * q k - c k)) * charE k θ := by
    rw [map_sub, map_mul]
    ring
  rw [hsplit, norm_mul, mul_comm]
  refine mul_le_mul (norm_charE_le hθ k) ?_ (norm_nonneg _) (Real.exp_pos _).le
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_))
    (norm_eval_le_l1 _ hu))
  · rw [norm_mul]
    exact mul_le_mul (hcoef k) (hB k hk u hu) (norm_nonneg _)
      ((norm_nonneg _).trans (hcoef k))
  · rw [norm_mul]
    exact mul_le_mul (norm_eval_le_l1 _ hu) (hq k hk u hu) (norm_nonneg _)
      ((norm_nonneg _).trans (norm_eval_le_l1 _ hu))

/-! ### (2c) The tail bound at a point -/

theorem withAngles_self (y : Phase (2 + 2)) : withAngles y (fast y.1) = y := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;>
  simp [withAngles, assemble, fast, slow]

/-- The line `t ↦ w + t·angleDir_i` is the slice at `w`, at `λ/2π + (t/2π) e_i`. -/
theorem withAngles_line (w : Phase (2 + 2)) (i : Fin 2) (t : ℝ) :
    withAngles w (fun j => 2 * π * ((fun l => fast w.1 l / (2 * π)) +
      (t / (2 * π)) • (Pi.single i 1 : Fin 2 → ℝ)) j) = w + t • angleDir (Fin.castAdd 2 i) := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  conv_rhs => rw [← withAngles_self (w + t • angleDir (Fin.castAdd 2 i)),
    withAngles_add_angleDir]
  congr 1
  funext j
  rw [fast_add_angleDir_fst]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> field_simp

/-- The coefficients of `Π_S` along the angle line. -/
theorem projS_line (S : Finset (Fin 2 → ℤ)) (Q : Phase (2 + 2) → ℝ) (w : Phase (2 + 2))
    (i : Fin 2) (t : ℝ) :
    projS S Q (w + t • angleDir (Fin.castAdd 2 i)) =
      (∑ k ∈ S, chartCoeff Q k w * charE k (fun j => ((fast w.1 j / (2 * π) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (k i : ℂ) * t)).re := by
  unfold projS
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chartCoeff_add_angleDir, charE_add_angleDir]
  ring

theorem norm_charE_real (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    ‖charE k (fun j => (x j : ℂ))‖ = 1 :=
  KAM.norm_character_real k x

/-- **(2c) The tail bound at a point.** -/
theorem abs_dirDeriv_sub_projS_le {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) {Q : Phase (2 + 2) → ℝ} (hQ : ContDiffOn ℝ ∞ Q U)
    (S T : Finset (Fin 2 → ℤ)) (i : Fin 2) {w : Phase (2 + 2)} (hw : w ∈ U) {ρ r : ℝ}
    (hρ : 0 < ρ) {Qc : (Fin 2 → ℂ) → ℂ} (hQc : DifferentiableOn ℂ Qc (complexStrip 2 ρ))
    (hper : ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ → Qc (θ + Pi.single j 1) = Qc θ)
    (hlink : ∀ t : Fin 2 → ℝ, Qc (fun j => (t j : ℂ)) = (Q (withAngles w fun j => 2 * π * t j) : ℂ))
    (a : (Fin 2 → ℤ) → ℂ) (hrem : ∀ θ ∈ complexStrip 2 ρ, ‖Qc θ - ∑ k ∈ T, a k * charE k θ‖ ≤ r) :
    |dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => Q y - projS S Q y) w| ≤
      ∑ k ∈ T \ S, |(k i : ℝ)| * ‖a k‖ + r * tailWeight S i ρ := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  -- the slice and its coefficients
  set g : (Fin 2 → ℝ) → ℂ := fun x => (Q (withAngles w fun j => 2 * π * x j) : ℂ) with hg
  have hgQ : ∀ x, g x = Qc (fun j => (x j : ℂ)) := fun x => (hlink x).symm
  have hσ : ContDiff ℝ ∞ fun x : Fin 2 → ℝ => withAngles w fun j => 2 * π * x j :=
    contDiff_withAngles.comp (contDiff_const.prodMk
      (contDiff_pi.2 fun j => contDiff_const.mul (contDiff_coord j)))
  have hgC : ContDiff ℝ 1 g :=
    (Complex.ofRealCLM.contDiff.comp (hQ.comp_contDiff hσ fun x => hsat w hw _)).of_le
      (by exact_mod_cast le_top)
  have hgp : ∀ (j : Fin 2) x, g (x + Pi.single j 1) = g x := by
    intro j x
    have e : (fun l => (((x + Pi.single j 1 : Fin 2 → ℝ) l : ℝ) : ℂ)) =
        (fun l => (x l : ℂ)) + Pi.single j 1 := by
      funext l
      by_cases h : l = j
      · subst h; simp
      · simp [h]
    rw [hgQ, hgQ, e, hper j _ (KAM.ofReal_mem_complexStrip hρ x)]
  set c : (Fin 2 → ℤ) → ℂ := KAM.torusCoeff g with hcdef
  have hchart : ∀ k, chartCoeff Q k w = c k := by
    intro k
    rw [hcdef, torusCoeff_eq_iint hgC.continuous k]
    unfold chartCoeff
    refine intervalIntegral.integral_congr fun t₀ _ =>
      intervalIntegral.integral_congr fun t₁ _ => ?_
    have e : (fun j => 2 * π * (![t₀, t₁] : Fin 2 → ℝ) j) = ![2 * π * t₀, 2 * π * t₁] := by
      funext j
      fin_cases j <;> rfl
    simp only [hg, e]
  -- decay
  have hdecay : ∀ k, ‖c k - (if k ∈ T then a k else 0)‖ ≤
      Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|)) * r := by
    intro k
    have hf : DifferentiableOn ℂ (fun θ => Qc θ - ∑ k ∈ T, a k * charE k θ) (complexStrip 2 ρ) :=
      hQc.sub (Differentiable.fun_sum fun k _ =>
        (differentiable_const _).mul (differentiable_charE k)).differentiableOn
    have hfp : ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ →
        Qc (θ + Pi.single j 1) - ∑ k ∈ T, a k * charE k (θ + Pi.single j 1) =
          Qc θ - ∑ k ∈ T, a k * charE k θ := by
      intro j θ hθ
      simp only [hper j θ hθ, charE_add_single]
    have h := KAM.norm_torusCoeff_le hρ hf hfp hrem k
    have hcQ : Continuous fun x : Fin 2 → ℝ => Qc (fun j => (x j : ℂ)) :=
      hQc.continuousOn.comp_continuous continuous_ofRealVec
        fun x => KAM.ofReal_mem_complexStrip hρ x
    have hch : ∀ k' : Fin 2 → ℤ, Continuous fun x : Fin 2 → ℝ => charE k' (fun j => (x j : ℂ)) :=
      fun k' => (differentiable_charE k').continuous.comp continuous_ofRealVec
    have hlin : KAM.torusCoeff (fun x : Fin 2 → ℝ => Qc (fun j => (x j : ℂ)) -
        ∑ k' ∈ T, a k' * charE k' (fun j => (x j : ℂ))) k = c k - if k ∈ T then a k else 0 := by
      rw [KAM.torusCoeff_sub (f := fun x : Fin 2 → ℝ => Qc (fun j => (x j : ℂ)))
        (g := fun x : Fin 2 → ℝ => ∑ k' ∈ T, a k' * charE k' (fun j => (x j : ℂ))) hcQ
        (continuous_finsetSum _ fun k' _ => continuous_const.mul (hch k')),
        KAM.torusCoeff_finset_sum_mul T hch a k]
      have horth : ∀ k' : Fin 2 → ℤ, KAM.torusCoeff (fun x : Fin 2 → ℝ =>
          charE k' (fun j => (x j : ℂ))) k = if k' = k then 1 else 0 := by
        intro k'
        unfold KAM.torusCoeff
        simp only [← charE_eq_character]
        have e : ∀ x : Fin 2 → ℝ, charE (-k) (fun j => (x j : ℂ)) * charE k' (fun j => (x j : ℂ)) =
            KAM.character (-k + k') (fun j => (x j : ℂ)) := fun x => KAM.character_mul _ _ _
        simp only [e, KAM.torusAverage_character]
        by_cases h : k' = k
        · subst h; simp
        · have h' : -k + k' ≠ 0 := fun h' => h (by rw [neg_add_eq_zero] at h'; exact h'.symm)
          simp [h, h']
      simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hcdef]
      congr 2
      funext x
      exact (hgQ x).symm
    rw [hlin] at h
    exact h
  have hcb : ∀ k, ‖c k‖ ≤ (if k ∈ T then ‖a k‖ else 0) +
      Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|)) * r := by
    intro k
    have h := (norm_sub_norm_le (c k) (if k ∈ T then a k else 0)).trans (hdecay k)
    have e : ‖(if k ∈ T then a k else 0)‖ = if k ∈ T then ‖a k‖ else 0 := by
      split_ifs <;> simp
    rw [e] at h
    linarith
  -- the derivative of the slice and its Fourier series
  set Dg : (Fin 2 → ℝ) → ℂ := fun x => fderiv ℝ g x (Pi.single i 1) with hDg
  have hDgc : Continuous Dg :=
    (hgC.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDgp : ∀ (j : Fin 2) x, Dg (x + Pi.single j 1) = Dg x := by
    intro j x
    have e : (fun y => g (y + Pi.single j 1)) = g := funext fun y => hgp j y
    simp only [hDg]
    rw [← fderiv_comp_add_right, e]
  have hDcoef : ∀ k, KAM.torusCoeff Dg k = 2 * π * Complex.I * (k i : ℂ) * c k :=
    fun k => KAM.torusCoeff_fderiv_coordinate_real hgC hgp i k
  set x₀ : Fin 2 → ℝ := fun l => fast w.1 l / (2 * π) with hx₀
  -- the bound on the derivative's coefficients
  set B : (Fin 2 → ℤ) → ℝ := fun k => |(k i : ℝ)| * ((if k ∈ T then ‖a k‖ else 0) +
      Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|)) * r) with hBdef
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hrem _ (KAM.ofReal_mem_complexStrip hρ 0))
  have hBs : Summable B := by
    have h1 : Summable fun k : Fin 2 → ℤ => |(k i : ℝ)| * (if k ∈ T then ‖a k‖ else 0) :=
      summable_of_ne_finset_zero (s := T) fun k hk => by simp [hk]
    have h2 := (summable_absMul_exp i hρ).mul_right r
    refine (h1.add h2).congr fun k => ?_
    simp only [hBdef]
    ring
  have hcB : ∀ k, |(k i : ℝ)| * ‖c k‖ ≤ B k := fun k =>
    mul_le_mul_of_nonneg_left (hcb k) (abs_nonneg _)
  have hDs : Summable fun k => ‖KAM.torusCoeff Dg k‖ := by
    refine ((hBs.mul_left (2 * π)).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_)
    rw [hDcoef]
    have e : ‖2 * π * Complex.I * (k i : ℂ) * c k‖ = 2 * π * (|(k i : ℝ)| * ‖c k‖) := by
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_intCast, abs_of_pos Real.pi_pos, Complex.norm_two]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (hcB k) (by positivity)
  have hinv := KAM.hasSum_torusCoeff_mul_character hDgc hDgp hDs x₀
  set b : (Fin 2 → ℤ) → ℂ := fun k =>
    c k * charE k (fun j => (x₀ j : ℂ)) * (Complex.I * (k i : ℂ)) with hbdef
  have hb : HasSum b (((2 * π)⁻¹ : ℝ) • Dg x₀) := by
    have h := hinv.const_smul ((2 * π)⁻¹ : ℝ)
    convert h using 1
    funext k
    rw [hDcoef, hbdef, ← charE_eq_character]
    simp only [Complex.real_smul]
    push_cast
    field_simp
  -- the derivative along the line
  set f : Phase (2 + 2) → ℝ := fun y => Q y - projS S Q y with hfdef
  have hdiff : DifferentiableAt ℝ f w := by
    have h1 := (hQ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hw)
    have h2 := ((contDiffOn_projS hU hsat S hQ).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hw)
    exact h1.sub h2
  set G : ℝ → ℂ := fun t => g (x₀ + (t / (2 * π)) • (Pi.single i 1 : Fin 2 → ℝ)) -
    ∑ k ∈ S, c k * charE k (fun j => (x₀ j : ℂ)) * Complex.exp (Complex.I * (k i : ℂ) * t)
    with hGdef
  have hline : (fun t : ℝ => f (w + t • angleDir (Fin.castAdd 2 i))) = fun t => (G t).re := by
    funext t
    simp only [hfdef, hGdef, hg, Complex.sub_re, Complex.ofReal_re]
    rw [withAngles_line, projS_line]
    simp only [hchart, hx₀]
  have hGd : HasDerivAt G (((2 * π)⁻¹ : ℝ) • Dg x₀ - ∑ k ∈ S, b k) 0 := by
    have hl : HasDerivAt (fun t : ℝ => x₀ + (t / (2 * π)) • (Pi.single i 1 : Fin 2 → ℝ))
        (((2 * π)⁻¹ : ℝ) • (Pi.single i 1 : Fin 2 → ℝ)) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).div_const (2 * π)).smul_const
        (Pi.single i 1 : Fin 2 → ℝ)
      simpa [div_eq_mul_inv] using h.const_add x₀
    have hgd : HasFDerivAt g (fderiv ℝ g x₀) (x₀ + ((0 : ℝ) / (2 * π)) • Pi.single i 1) := by
      simpa using (hgC.differentiable one_ne_zero x₀).hasFDerivAt
    have h1 := hgd.comp_hasDerivAt (0 : ℝ) hl
    have h2 : HasDerivAt (fun t : ℝ => ∑ k ∈ S, c k * charE k (fun j => (x₀ j : ℂ)) *
        Complex.exp (Complex.I * (k i : ℂ) * t)) (∑ k ∈ S, b k) 0 := by
      refine HasDerivAt.fun_sum fun k _ => ?_
      have hl' : HasDerivAt (fun t : ℝ => Complex.I * (k i : ℂ) * (t : ℂ))
          (Complex.I * (k i : ℂ)) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (Complex.I * (k i : ℂ))
      simpa [hbdef] using hl'.cexp.const_mul (c k * charE k (fun j => (x₀ j : ℂ)))
    have h3 := h1.sub h2
    rw [map_smul] at h3
    exact h3
  have hD : dirDeriv (angleDir (Fin.castAdd 2 i)) f w =
      (((2 * π)⁻¹ : ℝ) • Dg x₀ - ∑ k ∈ S, b k).re := by
    unfold dirDeriv
    rw [fderiv_eq_deriv_line _ hdiff, hline]
    exact ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hGd).deriv)
  -- the tail of the series
  have htail : HasSum (fun k => if k ∈ S then 0 else b k)
      (((2 * π)⁻¹ : ℝ) • Dg x₀ - ∑ k ∈ S, b k) := by
    have hS' : HasSum (fun k => if k ∈ S then b k else 0) (∑ k ∈ S, b k) := by
      have h : HasSum (fun k => if k ∈ S then b k else 0)
          (∑ k ∈ S, if k ∈ S then b k else 0) :=
        hasSum_sum_of_ne_finset_zero fun k hk => by simp [hk]
      convert h using 1
      exact (Finset.sum_congr rfl fun k hk => by simp [hk]).symm
    convert hb.sub hS' using 1
    funext k
    split_ifs <;> simp
  have hbn : ∀ k, ‖if k ∈ S then 0 else b k‖ ≤ if k ∈ S then 0 else B k := by
    intro k
    split_ifs
    · simp
    · rw [hbdef]
      simp only [norm_mul, norm_charE_real, Complex.norm_I, Complex.norm_intCast, mul_one, one_mul]
      rw [mul_comm]
      exact hcB k
  have hBS : Summable fun k => if k ∈ S then 0 else B k :=
    hBs.of_nonneg_of_le (fun k => by split_ifs <;> [exact le_rfl; positivity])
      fun k => by split_ifs <;> [positivity; exact le_rfl]
  have hnorm : ‖((2 * π)⁻¹ : ℝ) • Dg x₀ - ∑ k ∈ S, b k‖ ≤ ∑' k, if k ∈ S then 0 else B k := by
    rw [← htail.tsum_eq]
    exact (norm_tsum_le_tsum_norm (hBS.of_nonneg_of_le (fun _ => norm_nonneg _) hbn)).trans
      ((hBS.of_nonneg_of_le (fun _ => norm_nonneg _) hbn).tsum_le_tsum hbn hBS)
  -- the tail sum
  have hsplit : (∑' k, if k ∈ S then 0 else B k) =
      ∑ k ∈ T \ S, |(k i : ℝ)| * ‖a k‖ + r * tailWeight S i ρ := by
    have h1 : Summable fun k : Fin 2 → ℤ =>
        if k ∈ S then 0 else |(k i : ℝ)| * (if k ∈ T then ‖a k‖ else 0) :=
      summable_of_ne_finset_zero (s := T) fun k hk => by simp [hk]
    have h2 := (summable_tailTerm S i hρ).mul_left r
    have e : (fun k => if k ∈ S then 0 else B k) = fun k =>
        (if k ∈ S then 0 else |(k i : ℝ)| * (if k ∈ T then ‖a k‖ else 0)) +
          r * (if k ∈ S then 0 else
            |(k i : ℝ)| * Real.exp (-(2 * π * ρ * ∑ j, |(k j : ℝ)|))) := by
      funext k
      simp only [hBdef]
      split_ifs <;> ring
    rw [e, h1.tsum_add h2, tsum_mul_left, tailWeight]
    congr 1
    rw [tsum_eq_sum (s := T \ S) fun k hk => by
      rw [Finset.mem_sdiff] at hk
      by_cases hS : k ∈ S
      · simp [hS]
      · have hT : k ∉ T := fun hT => hk ⟨hT, hS⟩
        simp [hS, hT]]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_sdiff] at hk
    simp [hk.1, hk.2]
  rw [hD, ← hsplit]
  exact (Complex.abs_re_le_norm _).trans hnorm

/-! ### (2d) The tails on a cell -/

/-- The slice of a cell model at a point of the cell (the cell data's form of `(2c)`). -/
theorem abs_dirDeriv_sub_projS_le_of_cell {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) {Q : Phase (2 + 2) → ℝ} (hQ : ContDiffOn ℝ ∞ Q U)
    (S : Finset (Fin 2 → ℤ)) (i : Fin 2) (cell : AffineCell) (hcell : cell.wf = true) {ρ r : ℝ}
    (hρ : 0 < ρ) {Qc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {p : TFPoly}
    (hQd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Qc θ u) (complexStrip 2 ρ))
    (hQp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ →
      Qc (θ + Pi.single j 1) u = Qc θ u)
    (hQm : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖Qc θ u - p.eval θ u‖ ≤ r)
    (hlink : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Qc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (Q (withAngles w (fun i => 2 * π * t i)) : ℂ))
    {w : Phase (2 + 2)} (hw : w ∈ cell.toSet) (hwU : w ∈ U) :
    |dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => Q y - projS S Q y) w| ≤
      ∑ k ∈ p.support \ S, |(k i : ℝ)| * l1 (p k) + r * tailWeight S i ρ := by
  obtain ⟨u, hu, hx⟩ := hw
  have hw' : w ∈ cell.toSet := ⟨u, hu, hx⟩
  set uc : Fin 6 → ℂ := fun j => (cell.coord (cellCoord w) j : ℂ) with huc
  have hU' : uc ∈ polyDiscC 6 1 := by
    intro j
    rw [huc, hx, AffineCell.coord_map cell hcell u, Complex.norm_real, Real.norm_eq_abs]
    exact hu j
  have hrem : ∀ θ ∈ complexStrip 2 ρ, ‖Qc θ uc -
      ∑ k ∈ p.support, MvPolynomial.eval uc (p k) * charE k θ‖ ≤ r := fun θ hθ => by
    have h := hQm θ hθ uc hU'
    unfold TFPoly.eval Finsupp.sum at h
    exact h
  have h := abs_dirDeriv_sub_projS_le hU hsat hQ S p.support i hwU hρ (hQd uc hU')
    (fun j θ hθ => hQp uc hU' j θ hθ) (fun t => hlink w hw' t)
    (fun k => MvPolynomial.eval uc (p k)) hrem
  refine h.trans (add_le_add (Finset.sum_le_sum fun k _ => ?_) le_rfl)
  exact mul_le_mul_of_nonneg_left (norm_eval_le_l1 _ hU') (abs_nonneg _)

/-- **(2d) The tails `T₁ = D_i r₁` and `T₂ = D_i r₂` on a cell**, from cell models of `P` and
`G₂ = {P - ½ Π_S P, χ₁}` (holomorphic and `1`-periodic in `θ` on the strip, within `r_P`, `r_G`
of `p`, `g` on strip × polydisc, linked at real points of the cell). -/
theorem abs_tails_le_of_cell {ν : Fin 2 → ℝ} {U : Set (Phase (2 + 2))} (hU : IsOpen U)
    (hsat : IsAngleSaturated U) (hdom : U ⊆ poincareProdDom 2) {S : Finset (Fin 2 → ℤ)}
    {P : Phase (2 + 2) → ℝ} (hP : ContDiffOn ℝ ∞ P U) (hS : IsModeSet S (keplerFreq ν) U)
    (cell : AffineCell) (hcell : cell.wf = true) (i : Fin 2) {ρ rP rG : ℝ} (hρ : 0 < ρ)
    {Pc Gc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {p g : TFPoly}
    (hPd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Pc θ u) (complexStrip 2 ρ))
    (hPp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ →
      Pc (θ + Pi.single j 1) u = Pc θ u)
    (hPm : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖Pc θ u - p.eval θ u‖ ≤ rP)
    (hPl : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Pc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (P (withAngles w (fun i => 2 * π * t i)) : ℂ))
    (hGd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Gc θ u) (complexStrip 2 ρ))
    (hGp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ →
      Gc (θ + Pi.single j 1) u = Gc θ u)
    (hGm : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖Gc θ u - g.eval θ u‖ ≤ rG)
    (hGl : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Gc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (pb (fun y => P y - projS S P y / 2) (chiStar S (keplerFreq ν) P)
          (withAngles w (fun i => 2 * π * t i)) : ℂ))
    {w : Phase (2 + 2)} (hw : w ∈ cell.toSet) (hwU : w ∈ U) :
    |dirDeriv (angleDir (Fin.castAdd 2 i))
        (residual₁ (hProd 1 ν) P (chiStar S (keplerFreq ν) P)) w| ≤
      ∑ k ∈ p.support \ S, |(k i : ℝ)| * l1 (p k) + rP * tailWeight S i ρ ∧
    |dirDeriv (angleDir (Fin.castAdd 2 i)) (residual₂ (hProd 1 ν) P (chiStar S (keplerFreq ν) P)
        (chiStar S (keplerFreq ν) (pb (fun y => P y - projS S P y / 2)
          (chiStar S (keplerFreq ν) P)))) w| ≤
      ∑ k ∈ g.support \ S, |(k i : ℝ)| * l1 (g k) + rG * tailWeight S i ρ := by
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
    exact abs_dirDeriv_sub_projS_le_of_cell hU hsat hP S i cell hcell hρ hPd hPp hPm hPl hw hwU
  · rw [e₂]
    exact abs_dirDeriv_sub_projS_le_of_cell hU hsat hG₂ S i cell hcell hρ hGd hGp hGm hGl hw hwU

theorem modesHD_box (k : Fin 2 → ℤ) (hk : k ≠ 0) (h0 : |k 0| ≤ ((80 : ℕ) : ℤ))
    (h1 : |k 1| ≤ ((20 : ℕ) : ℤ)) : k ∈ modesHD :=
  mem_modesHD.mpr ⟨hk, by exact_mod_cast h0, by exact_mod_cast h1⟩

/-- **The tails of HD 11964 on a cell** (`T₁ = D_i r₁`, `T₂ = D_i r₂`, `i` the planet), from cell
models of `P` and `G₂` on the strip of width `ρ`, with the closed-form weight of `modesHD` at any
`q̄ < 1` with `e^{-2πρ} ≤ q̄`. -/
theorem tails_HD_of_cell (cell : AffineCell) (hcell : cell.wf = true) (i : Fin 2)
    {ρ rP rG q : ℝ} (hρ : 0 < ρ) (hq : Real.exp (-(2 * π * ρ)) ≤ q) (hq1 : q < 1)
    {Pc Gc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ} {p g : TFPoly}
    (hPd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Pc θ u) (complexStrip 2 ρ))
    (hPp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ →
      Pc (θ + Pi.single j 1) u = Pc θ u)
    (hPm : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖Pc θ u - p.eval θ u‖ ≤ rP)
    (hPl : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Pc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (chartPert nu mu (withAngles w (fun i => 2 * π * t i)) : ℂ))
    (hGd : ∀ u ∈ polyDiscC 6 1, DifferentiableOn ℂ (fun θ => Gc θ u) (complexStrip 2 ρ))
    (hGp : ∀ u ∈ polyDiscC 6 1, ∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ complexStrip 2 ρ →
      Gc (θ + Pi.single j 1) u = Gc θ u)
    (hGm : ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖Gc θ u - g.eval θ u‖ ≤ rG)
    (hGl : ∀ w ∈ cell.toSet, ∀ t : Fin 2 → ℝ,
      Gc (fun i => (t i : ℂ)) (fun j => (cell.coord (cellCoord w) j : ℂ)) =
        (G2HD (withAngles w (fun i => 2 * π * t i)) : ℂ))
    {w : Phase (2 + 2)} (hw : w ∈ cell.toSet) (hwU : w ∈ openHD) :
    |dirDeriv (angleDir (Fin.castAdd 2 i)) (residual₁ (hProd 1 nu) (chartPert nu mu) chi1HD) w| ≤
      ∑ k ∈ p.support \ modesHD, |(k i : ℝ)| * l1 (p k) + rP * boxTailBound 80 20 i q ∧
    |dirDeriv (angleDir (Fin.castAdd 2 i))
        (residual₂ (hProd 1 nu) (chartPert nu mu) chi1HD chi2HD) w| ≤
      ∑ k ∈ g.support \ modesHD, |(k i : ℝ)| * l1 (g k) + rG * boxTailBound 80 20 i q := by
  have hW := tailWeight_le_boxTailBound 80 20 i hρ modesHD_box hq hq1
  have hrP : 0 ≤ rP := (norm_nonneg _).trans (hPm _ (KAM.ofReal_mem_complexStrip hρ 0) 0
    (fun j => by simp))
  have hrG : 0 ≤ rG := (norm_nonneg _).trans (hGm _ (KAM.ofReal_mem_complexStrip hρ 0) 0
    (fun j => by simp))
  have h := abs_tails_le_of_cell isOpen_openHD isAngleSaturated_openHD openHD_subset_dom
    contDiffOn_chartPert_HD isModeSet_HD cell hcell i hρ hPd hPp hPm hPl hGd hGp hGm hGl hw hwU
  exact ⟨h.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hW hrP)),
    h.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hW hrG))⟩

end HD11964.Cover

end
