/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Defs.HasDefiniteFastPart
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Planetary.Exponential.Setting
public import KAM.Planetary.Exponential.Enlargement
public import KAM.Planetary.Exponential.LocalComplexification

/-!
# P14 package E4: the Kepler data `h_data`

Blueprint P, Part 14 (`bpP:p14:h-data`, steps `hd-i`, `hd-ii`, `hd-iv`, `hd-v`): the
complexified Kepler part `planetaryKeplerC m I = -∑ m_i³ / (2 I_i²)` on the complex collar of the
enlarged action box is holomorphic, `C²`, real on real points, has Hessian bounded by
`M = ∑ 3 m_i³ / (5 lower_i / 8)⁴`, and has a definite fast Hessian and nonvanishing frequency
with the explicit constants `g`, `v` (attained minima), for `h` and `-h`.

The calculus is done once over `𝕜 = ℝ, ℂ` for `keplerSumGen`, on the open set of nowhere-zero
coordinates.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators ContDiff

namespace KAM.Planetary

variable {n : ℕ}

/-- The Kepler sum `-∑ m_i³ / (2 z_i²)` over a scalar field `𝕜`. -/
def keplerSumGen (𝕜 : Type*) [RCLike 𝕜] (m : Fin n → ℝ) (z : Fin n → 𝕜) : 𝕜 :=
  -∑ i, (m i : 𝕜)^3 / (2 * z i ^ 2)

section Calculus

variable {𝕜 : Type*} [RCLike 𝕜]

theorem keplerSumGen_contDiffOn (m : Fin n → ℝ) (k : WithTop ℕ∞) :
    ContDiffOn 𝕜 k (keplerSumGen 𝕜 m) {z | ∀ i, z i ≠ 0} := by
  unfold keplerSumGen
  refine ContDiffOn.neg (ContDiffOn.sum fun i _ => ?_)
  refine contDiffOn_const.div (contDiffOn_const.mul ?_) fun z hz => ?_
  · exact ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).contDiff.pow 2).contDiffOn
  · exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (hz i))

private theorem hasDerivAt_inv_sq (c w : 𝕜) (hw : w ≠ 0) :
    HasDerivAt (fun w : 𝕜 => c / (2 * w ^ 2)) (-c / w ^ 3) w := by
  have h := (hasDerivAt_const w c).div ((hasDerivAt_pow 2 w).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 hw))
  convert h using 1
  field_simp
  ring

private theorem hasDerivAt_inv_cube (c w : 𝕜) (hw : w ≠ 0) :
    HasDerivAt (fun w : 𝕜 => c / w ^ 3) (-3 * c / w ^ 4) w := by
  have h := (hasDerivAt_const w c).div (hasDerivAt_pow 3 w) (pow_ne_zero 3 hw)
  convert h using 1
  field_simp
  ring

/-- The first derivative of `keplerSumGen` as a continuous linear map. -/
def keplerSumGenD (m : Fin n → ℝ) (z : Fin n → 𝕜) : (Fin n → 𝕜) →L[𝕜] 𝕜 :=
  ∑ i, ((m i : 𝕜)^3 / z i ^ 3) • (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)

theorem keplerSumGen_hasFDerivAt (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0) :
    HasFDerivAt (keplerSumGen 𝕜 m) (keplerSumGenD m z) z := by
  unfold keplerSumGen keplerSumGenD
  have h : HasFDerivAt (fun z : Fin n → 𝕜 => ∑ i, (m i : 𝕜)^3 / (2 * z i ^ 2))
      (∑ i, ((-(m i : 𝕜)^3) / z i ^ 3) • (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜))
      z := by
    have key : ∀ i, HasFDerivAt (fun z : Fin n → 𝕜 => (m i : 𝕜)^3 / (2 * z i ^ 2))
        (((-(m i : 𝕜)^3) / z i ^ 3) •
          (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)) z := fun i =>
      (hasDerivAt_inv_sq ((m i : 𝕜)^3) (z i) (hz i)).comp_hasFDerivAt
        (f := fun z : Fin n → 𝕜 => z i) z (hasFDerivAt_apply i z)
    exact HasFDerivAt.fun_sum fun i _ => key i
  refine h.neg.congr_fderiv ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_div]
  ext w
  simp

theorem keplerSumGen_fderiv_eq (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0) :
    fderiv 𝕜 (keplerSumGen 𝕜 m) z = keplerSumGenD m z :=
  (keplerSumGen_hasFDerivAt m hz).fderiv

theorem keplerSumGenD_hasFDerivAt (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0) :
    HasFDerivAt (keplerSumGenD m)
      (∑ i, ((-3 * (m i : 𝕜)^3 / z i ^ 4) •
        (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)).smulRight
        (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)) z := by
  unfold keplerSumGenD
  have key : ∀ i, HasFDerivAt (fun z : Fin n → 𝕜 => ((m i : 𝕜)^3 / z i ^ 3) •
        (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜))
        (((-3 * (m i : 𝕜)^3 / z i ^ 4) •
          (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)).smulRight
          (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)) z := fun i =>
    ((hasDerivAt_inv_cube ((m i : 𝕜)^3) (z i) (hz i)).comp_hasFDerivAt
      (f := fun z : Fin n → 𝕜 => z i) z (hasFDerivAt_apply i z)).smul_const
      (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)
  exact HasFDerivAt.fun_sum fun i _ => key i

/-- The second derivative of `keplerSumGen` is the diagonal form `-3 m_i³ / z_i⁴`. -/
theorem keplerSumGen_fderiv2_apply (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0)
    (w v : Fin n → 𝕜) :
    fderiv 𝕜 (fderiv 𝕜 (keplerSumGen 𝕜 m)) z w v =
      ∑ i, (-3 * (m i : 𝕜)^3 / z i ^ 4) * (w i * v i) := by
  have hS : {z : Fin n → 𝕜 | ∀ i, z i ≠ 0} ∈ nhds z := by
    have hopen : IsOpen (Set.pi Set.univ (fun _ : Fin n => ({0}ᶜ : Set 𝕜))) :=
      isOpen_set_pi (Set.toFinite _) fun _ _ => isOpen_compl_singleton
    have hset : {z : Fin n → 𝕜 | ∀ i, z i ≠ 0} = Set.pi Set.univ (fun _ : Fin n => ({0}ᶜ : Set 𝕜)) := by
      ext y; simp [Set.mem_pi]
    rw [hset]
    exact hopen.mem_nhds (by simpa [Set.mem_pi] using hz)
  have hev : fderiv 𝕜 (keplerSumGen 𝕜 m) =ᶠ[nhds z] keplerSumGenD m :=
    Filter.eventuallyEq_of_mem hS fun y hy => keplerSumGen_fderiv_eq m hy
  rw [hev.fderiv_eq, (keplerSumGenD_hasFDerivAt m hz).fderiv]
  simp [mul_assoc]

/-- The Hessian of `keplerSumGen` has curried operator norm at most `∑ 3 |m_i|³ / ‖z_i‖⁴`. -/
theorem keplerSumGen_hess_norm_le (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0) :
    ‖fderiv 𝕜 (fderiv 𝕜 (keplerSumGen 𝕜 m)) z‖ ≤ ∑ i, 3 * |m i| ^ 3 / ‖z i‖ ^ 4 := by
  have hnn : 0 ≤ ∑ i, 3 * |m i| ^ 3 / ‖z i‖ ^ 4 :=
    Finset.sum_nonneg fun i _ => by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hnn fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [keplerSumGen_fderiv2_apply m hz]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hzi : 0 < ‖z i‖ := norm_pos_iff.2 (hz i)
  have hw : ‖w i‖ ≤ ‖w‖ := norm_le_pi_norm w i
  have hv : ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
  rw [norm_mul, norm_mul, norm_div, norm_mul, norm_pow, norm_pow, RCLike.norm_ofReal, norm_neg,
    RCLike.norm_ofNat]
  calc 3 * |m i| ^ 3 / ‖z i‖ ^ 4 * (‖w i‖ * ‖v i‖)
      ≤ 3 * |m i| ^ 3 / ‖z i‖ ^ 4 * (‖w‖ * ‖v‖) := by gcongr
    _ = _ := by ring

end Calculus

/-- Coordinate margins on the complex collar of the doubled fast box. -/
theorem keplerData_margin (B : AMDBox n) (hB : B.Admissible) {kappa e A rho : ℝ}
    (hd : EnlargedData B kappa e A) (hrk : rho ≤ kappa) {z : Fin n → ℂ}
    (hz : z ∈ KAM.actionNbhd (fastBox B (2 * kappa)) rho) (i : Fin n) :
    0 < 5 * B.lower i / 8 ∧ 5 * B.lower i / 8 ≤ B.lower i - 3 * kappa ∧
      B.lower i - 3 * kappa ≤ (z i).re ∧ ‖z i‖ ≤ B.upper i + 3 * kappa := by
  obtain ⟨J, hJ, hlt⟩ := hz
  have hl := (hB.1 i).2.1
  have hs := hd.small i
  have hk := hd.kappa_pos
  have hJi := hJ i
  have hdiff : ‖z i - (J i : ℂ)‖ ≤ ‖z - fun j => (J j : ℂ)‖ :=
    norm_le_pi_norm (z - fun j => (J j : ℂ)) i
  have hre : |(z i).re - J i| ≤ ‖z i - (J i : ℂ)‖ := by
    have := Complex.abs_re_le_norm (z i - (J i : ℂ))
    simpa using this
  have hre' := abs_le.1 (hre.trans (hdiff.trans hlt.le |>.trans hrk))
  refine ⟨by linarith, by linarith, by linarith [hJi.1, hre'.1], ?_⟩
  have hJpos : 0 < J i := by linarith [hJi.1]
  calc ‖z i‖ = ‖(J i : ℂ) + (z i - (J i : ℂ))‖ := by rw [add_sub_cancel]
    _ ≤ ‖(J i : ℂ)‖ + ‖z i - (J i : ℂ)‖ := norm_add_le _ _
    _ ≤ B.upper i + 3 * kappa := by
      rw [Complex.norm_real, Real.norm_of_nonneg hJpos.le]
      linarith [hJi.2, hdiff.trans hlt.le |>.trans hrk]

/-- Negation exchanges the two signs of a definite fast part. -/
theorem hasDefiniteFastPart_neg {G : Set (Fin n → ℝ)} {rho g v : ℝ} {h : (Fin n → ℂ) → ℂ}
    (H : KAM.Nekhoroshev.HasDefiniteFastPart G rho g v h) :
    KAM.Nekhoroshev.HasDefiniteFastPart G rho g v (-h) := by
  have hr : KAM.Nekhoroshev.realPart (-h) = fun I => -KAM.Nekhoroshev.realPart h I := by
    funext I
    simp [KAM.Nekhoroshev.realPart]
  obtain ⟨hg, hm, hC, σ, hσ, hmain⟩ := H
  refine ⟨hg, hm, ?_, -σ, ?_, ?_⟩
  · rw [hr]
    exact hC.neg
  · rcases hσ with h1 | h1 <;> simp [h1]
  · intro I hI
    obtain ⟨hf, hq⟩ := hmain I hI
    have hfreq : KAM.frequencyMap (-h) I = -KAM.frequencyMap h I := by
      funext i
      show fderiv ℝ (KAM.Nekhoroshev.realPart (-h)) I (Pi.single i 1) =
        -(fderiv ℝ (KAM.Nekhoroshev.realPart h) I (Pi.single i 1))
      rw [hr, fderiv_fun_neg]
      rfl
    refine ⟨by rw [hfreq, norm_neg]; exact hf, fun w => ?_⟩
    have h2 : fderiv ℝ (fderiv ℝ (KAM.Nekhoroshev.realPart (-h))) I w w =
        -(fderiv ℝ (fderiv ℝ (KAM.Nekhoroshev.realPart h)) I w w) := by
      rw [hr]
      have : fderiv ℝ (fun I => -KAM.Nekhoroshev.realPart h I) =
          fun I => -fderiv ℝ (KAM.Nekhoroshev.realPart h) I := funext fun _ => fderiv_fun_neg
      rw [this, fderiv_fun_neg]
      simp
    rw [h2]
    have := hq w
    linarith

theorem planetaryKeplerC_ofReal (m I : Fin n → ℝ) :
    planetaryKeplerC m (fun i => (I i : ℂ)) = ((keplerSumGen ℝ m I : ℝ) : ℂ) := by
  simp [planetaryKeplerC, keplerSumGen]

theorem realPart_planetaryKeplerC (m : Fin n → ℝ) :
    KAM.Nekhoroshev.realPart (planetaryKeplerC m) = keplerSumGen ℝ m := by
  funext I
  simp [KAM.Nekhoroshev.realPart, planetaryKeplerC_ofReal]

theorem planetaryKeplerC_eq (m : Fin n → ℝ) : planetaryKeplerC m = keplerSumGen ℂ m := rfl

/-- The first-derivative value of the real Kepler sum on the unit coordinate vectors. -/
theorem keplerSumGen_real_freq (m : Fin n → ℝ) {I : Fin n → ℝ} (hI : ∀ i, I i ≠ 0) (i : Fin n) :
    fderiv ℝ (keplerSumGen ℝ m) I (Pi.single i 1) = m i ^ 3 / I i ^ 3 := by
  rw [keplerSumGen_fderiv_eq m hI]
  simp [keplerSumGenD, Pi.single_apply]

theorem keplerSumGen_real_hess (m : Fin n → ℝ) {I : Fin n → ℝ} (hI : ∀ i, I i ≠ 0)
    (w : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (keplerSumGen ℝ m)) I w w = -∑ i, 3 * m i ^ 3 / I i ^ 4 * w i ^ 2 := by
  rw [keplerSumGen_fderiv2_apply m hI, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

/-- `h_data` (`bpP:p14:h-data`). -/
theorem h_data (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible)
    {kappa e A rho : ℝ} (hd : EnlargedData B kappa e A)
    (hrho : 0 < rho) (hrk : rho ≤ kappa) :
    (∀ I ∈ fastBox B kappa, Metric.closedBall I rho ⊆ fastBox B (2*kappa)) ∧
    ∃ g v M : ℝ,
      (∀ i, g ≤ B.mass i^3 / (B.upper i + 3*kappa)^3) ∧
      (∃ i, g = B.mass i^3 / (B.upper i + 3*kappa)^3) ∧
      (∀ i, v ≤ 3 * B.mass i^3 / (B.upper i + 3*kappa)^4) ∧
      (∃ i, v = 3 * B.mass i^3 / (B.upper i + 3*kappa)^4) ∧
      M = ∑ i, 3 * B.mass i^3 / (5 * B.lower i / 8)^4 ∧
      0 < g ∧ 0 < v ∧ 0 < M ∧
      DifferentiableOn ℂ (planetaryKeplerC B.mass) (KAM.actionNbhd (fastBox B (2*kappa)) rho) ∧
      ContDiffOn ℂ 2 (planetaryKeplerC B.mass) (KAM.actionNbhd (fastBox B (2*kappa)) rho) ∧
      (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho →
        (planetaryKeplerC B.mass (fun i => (I i : ℂ))).im = 0) ∧
      (∀ z ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho,
        ‖fderiv ℂ (fderiv ℂ (planetaryKeplerC B.mass)) z‖ ≤ M) ∧
      KAM.Nekhoroshev.HasDefiniteFastPart (fastBox B (2*kappa)) rho g v (planetaryKeplerC B.mass) ∧
      KAM.Nekhoroshev.HasDefiniteFastPart (fastBox B (2*kappa)) rho g v (-planetaryKeplerC B.mass) ∧
      ∀ z ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho, ∀ i,
        0 < 5 * B.lower i / 8 ∧
        5 * B.lower i / 8 ≤ B.lower i - 3*kappa ∧
        B.lower i - 3*kappa ≤ (z i).re := by
  have hk := hd.kappa_pos
  have hBi := hB.1
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hupos : ∀ i, 0 < B.upper i := fun i => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hBi i
    linarith
  have hmpos : ∀ i, 0 < B.mass i := fun i => (hBi i).1
  have hmarg := fun {z : Fin n → ℂ} (hz : z ∈ KAM.actionNbhd (fastBox B (2 * kappa)) rho)
    (i : Fin n) => keplerData_margin B hB hd hrk hz i
  refine ⟨?_, ?_⟩
  · intro I hI J hJ i
    have h1 : |J i - I i| ≤ rho := by
      have := norm_le_pi_norm (J - I) i
      rw [Metric.mem_closedBall, dist_eq_norm] at hJ
      simpa using this.trans hJ
    have h2 := abs_le.1 h1
    have := hI i
    constructor <;> linarith [this.1, this.2]
  obtain ⟨ig, -, hig⟩ := Finset.exists_min_image Finset.univ
    (fun i => B.mass i ^ 3 / (B.upper i + 3 * kappa) ^ 3) Finset.univ_nonempty
  obtain ⟨iv, -, hiv⟩ := Finset.exists_min_image Finset.univ
    (fun i => 3 * B.mass i ^ 3 / (B.upper i + 3 * kappa) ^ 4) Finset.univ_nonempty
  have hden : ∀ i, 0 < B.upper i + 3 * kappa := fun i => by linarith [hupos i]
  have hgpos : 0 < B.mass ig ^ 3 / (B.upper ig + 3 * kappa) ^ 3 := by
    have := hmpos ig; have := hden ig; positivity
  have hvpos : 0 < 3 * B.mass iv ^ 3 / (B.upper iv + 3 * kappa) ^ 4 := by
    have := hmpos iv; have := hden iv; positivity
  have hlpos : ∀ i, 0 < 5 * B.lower i / 8 := fun i => by linarith [(hBi i).2.1]
  have hMpos : 0 < ∑ i, 3 * B.mass i ^ 3 / (5 * B.lower i / 8) ^ 4 :=
    Finset.sum_pos (fun i _ => by have := hmpos i; have := hlpos i; positivity)
      Finset.univ_nonempty
  obtain ⟨g, hg⟩ : ∃ g, g = B.mass ig ^ 3 / (B.upper ig + 3 * kappa) ^ 3 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = 3 * B.mass iv ^ 3 / (B.upper iv + 3 * kappa) ^ 4 := ⟨_, rfl⟩
  have hgle : ∀ i, g ≤ B.mass i ^ 3 / (B.upper i + 3 * kappa) ^ 3 := fun i =>
    hg ▸ hig i (Finset.mem_univ i)
  have hvle : ∀ i, v ≤ 3 * B.mass i ^ 3 / (B.upper i + 3 * kappa) ^ 4 := fun i =>
    hv ▸ hiv i (Finset.mem_univ i)
  have hz0 : ∀ z ∈ KAM.actionNbhd (fastBox B (2 * kappa)) rho, ∀ i, z i ≠ 0 := fun z hz i h0 => by
    have := (hmarg hz i).2.2.1
    have h1 := hlpos i
    have h2 := (hmarg hz i).2.1
    rw [h0] at this
    simp at this
    linarith
  have hCD : ∀ k : WithTop ℕ∞, ContDiffOn ℂ k (planetaryKeplerC B.mass)
      (KAM.actionNbhd (fastBox B (2 * kappa)) rho) := fun k =>
    (keplerSumGen_contDiffOn (𝕜 := ℂ) B.mass k).mono fun z hz => hz0 z hz
  have hdef : KAM.Nekhoroshev.HasDefiniteFastPart (fastBox B (2*kappa)) rho g v
      (planetaryKeplerC B.mass) := by
    have hU : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd (fastBox B (2 * kappa)) rho →
        ∀ i, 0 < I i ∧ I i ≤ B.upper i + 3 * kappa := fun I hI i => by
      have h1 := hmarg hI i
      have h2 := hlpos i
      have h3 : (((I i : ℝ) : ℂ)).re = I i := Complex.ofReal_re _
      have h4 : ‖((I i : ℝ) : ℂ)‖ = |I i| := Complex.norm_real _
      refine ⟨by linarith [h1.2.2.1], ?_⟩
      have := h1.2.2.2
      rw [h4, abs_of_pos (by linarith [h1.2.2.1])] at this
      exact this
    refine ⟨hg ▸ hgpos, hv ▸ hvpos, ?_, -1, Or.inr rfl, fun I hI => ?_⟩
    · rw [realPart_planetaryKeplerC]
      exact (keplerSumGen_contDiffOn (𝕜 := ℝ) B.mass 3).mono fun I hI i =>
        (hU I hI i).1.ne'
    · have hnz : ∀ i, I i ≠ 0 := fun i => (hU I hI i).1.ne'
      refine ⟨?_, fun w => ?_⟩
      · refine le_trans ?_ (norm_le_pi_norm (KAM.frequencyMap (planetaryKeplerC B.mass) I) ig)
        show _ ≤ ‖fderiv ℝ (KAM.Nekhoroshev.realPart (planetaryKeplerC B.mass)) I
          (Pi.single ig 1)‖
        rw [realPart_planetaryKeplerC, keplerSumGen_real_freq _ hnz]
        have hi := hU I hI ig
        have hmg := hmpos ig
        have hIp : 0 < I ig := hi.1
        rw [Real.norm_of_nonneg (by positivity)]
        calc g ≤ B.mass ig ^ 3 / (B.upper ig + 3 * kappa) ^ 3 := hgle ig
          _ ≤ _ := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact pow_le_pow_left₀ hi.1.le hi.2 3
      · show _ ≤ _ * fderiv ℝ (fderiv ℝ (KAM.Nekhoroshev.realPart (planetaryKeplerC B.mass))) I w w
        rw [realPart_planetaryKeplerC, keplerSumGen_real_hess _ hnz]
        rw [Finset.mul_sum]
        have : -1 * -∑ i, 3 * B.mass i ^ 3 / I i ^ 4 * w i ^ 2
            = ∑ i, 3 * B.mass i ^ 3 / I i ^ 4 * w i ^ 2 := by ring
        rw [this]
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := hU I hI i
        have hmg := hmpos i
        have hIp : 0 < I i := hi.1
        have : v ≤ 3 * B.mass i ^ 3 / I i ^ 4 :=
          (hvle i).trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ hi.1.le hi.2 4))
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  refine ⟨g, v, _, hgle, ⟨ig, hg⟩, hvle, ⟨iv, hv⟩, rfl, hg ▸ hgpos, hv ▸ hvpos, hMpos,
    (hCD 2).differentiableOn (by norm_num), hCD 2, ?_, ?_, hdef, hasDefiniteFastPart_neg hdef,
    fun z hz i => ⟨(hmarg hz i).1, (hmarg hz i).2.1, (hmarg hz i).2.2.1⟩⟩
  · intro I _
    rw [planetaryKeplerC_ofReal]
    exact Complex.ofReal_im _
  · intro z hz
    have hz' := hz0 z hz
    refine (keplerSumGen_hess_norm_le (𝕜 := ℂ) B.mass hz').trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hmarg hz i
    have hre : 5 * B.lower i / 8 ≤ ‖z i‖ := by
      have := Complex.re_le_norm (z i)
      linarith [h1.2.1, h1.2.2.1]
    rw [abs_of_pos (hmpos i)]
    have hmg := hmpos i
    have hl := hlpos i
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hl.le hre 4)

end KAM.Planetary

end
