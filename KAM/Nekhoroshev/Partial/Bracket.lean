/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Weighted.Algebra
public import KAM.Weighted.Cauchy
public import KAM.Weighted.SupWeighted
import Mathlib.Analysis.Complex.ExponentialBounds
import KAM.Strip.FourierDerivative
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The extended weighted bracket estimate (`bpN:p11:bracket`, Part 11, package N11-C)

`ext_part4` (the sup bound for the extended class), `bracket` (Lemma B.4ᵉ: the weighted norm of
`{u, v}_c` in terms of those of `u` and `v`, with the extra slow-pair term `2kc/((R₀-R+ρ)ρ)`),
`bracket_dominated` (under `(SL)_{ρ,σ}` the bracket in `[ ]` is at most half of the fast part) and
`bracket_g` (the decomposed version, as in Part 6).

The proof is Part 4's `wbound_bracket` with the four families of products
`∂_θu ∂_I v`, `-∂_I u ∂_θ v`, `c ∂_{q̃}u ∂_{p̃}v`, `-c ∂_{p̃}u ∂_{q̃}v` (the proofs `br-fast`,
`br-slow`, `br-dom`): the coefficients of a finite sum are the sums of coefficients, each product
is handled by `coeff_mul`, and `cauchy_theta`, `cauchy_action` bound the derivatives.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

/-- `bpN:p11:ext-part4`: the sup bound for the extended class. -/
theorem ext_part4 (b : PartialBlock n k) {R s U : ℝ} {u : EC n k → ℂ}
    (hs : 0 < s) (hu : InClass b.base R s u) (hb : WBound b.base R s u U) :
    ∀ z ∈ Dom n b.base R s, ‖u z‖ ≤ U := by
  have _ := hs
  exact sup_le_wbound hu hb

/-! ### The bracket as a finite sum of products -/

/-- A continuous linear functional is the sum of its values on the coordinate directions. -/
private theorem clm_eq_sum (L : EC n k →L[ℂ] ℂ) (x : EC n k) :
    L x = ∑ i, x.1 i * L (Pi.single i 1, 0) + ∑ j, x.2 j * L (0, Pi.single j 1) := by
  have h1 : ((x.1, 0) : EC n k) = ∑ i, x.1 i • ((Pi.single i 1, 0) : EC n k) := by
    ext a
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  have h2 : ((0, x.2) : EC n k) = ∑ j, x.2 j • ((0, Pi.single j 1) : EC n k) := by
    ext a
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  conv_lhs => rw [hx, map_add, h1, h2, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Index set of the four families of products. -/
private abbrev BrIdx (n k : ℕ) := Fin n ⊕ Fin n ⊕ Fin k ⊕ Fin k

private def brCoef (c : ℝ) : BrIdx n k → ℂ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => -1) (Sum.elim (fun _ => (c : ℂ))
    (fun _ => -(c : ℂ))))

private def brTerm (u v : EC n k → ℂ) : BrIdx n k → EC n k → ℂ :=
  Sum.elim (fun i z => dtheta i u z * dI (Fin.castAdd (k + k) i) v z)
    (Sum.elim (fun i z => dI (Fin.castAdd (k + k) i) u z * dtheta i v z)
      (Sum.elim
        (fun i z => dI (Fin.natAdd n (Fin.castAdd k i)) u z *
          dI (Fin.natAdd n (Fin.natAdd k i)) v z)
        (fun i z => dI (Fin.natAdd n (Fin.natAdd k i)) u z *
          dI (Fin.natAdd n (Fin.castAdd k i)) v z)))

private theorem extBracket_eq (c : ℝ) (u v : EC n k → ℂ) :
    extBracket c u v = fun z => ∑ j, brCoef c j * brTerm u v j z := by
  funext z
  unfold extBracket
  rw [clm_eq_sum]
  simp only [Fintype.sum_sum_type, brCoef, brTerm, Sum.elim_inl, Sum.elim_inr, one_mul,
    neg_mul]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [wfield, Fin.append_left, Fin.append_right, dtheta, dI, Finset.sum_neg_distrib,
    neg_mul, mul_comm (fderiv ℂ u z _), mul_assoc]

/-! ### Weighted-norm helpers (generic base dimension) -/

private theorem inClass_anti {m : ℕ} {D : Set (Fin m → ℂ)} {r₀ s₀ r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s ≤ s₀) :
    InClass D r s u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

private theorem wsum_nonneg' {m : ℕ} (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) (s : ℝ)
    (I : Fin m → ℂ) : 0 ≤ wsum f s I :=
  tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

private theorem continuous_slice {m : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hs : 0 < s) (hu : InClass D r s u) {I : Fin m → ℂ}
    (hI : I ∈ polyNbhd D r) : Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I) :=
  hu.differentiableOn.continuousOn.comp_continuous
    ((continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)).prodMk
      continuous_const) fun x => ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

private theorem inClass_mul' {m : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r s u) (hv : InClass D r s v) :
    InClass D r s (fun z => u z * v z) :=
  ⟨hu.differentiableOn.mul hv.differentiableOn, fun j z hz => by
    simp only [hu.periodic j z hz, hv.periodic j z hz]⟩

private theorem inClass_sum {m : ℕ} {ι : Type*} [Fintype ι] {D : Set (Fin m → ℂ)} {r s : ℝ}
    (a : ι → ℂ) (g : ι → (Fin n → ℂ) × (Fin m → ℂ) → ℂ) (hg : ∀ j, InClass D r s (g j)) :
    InClass D r s (fun z => ∑ j, a j * g j z) :=
  ⟨DifferentiableOn.fun_sum fun j _ => (differentiableOn_const _).mul (hg j).differentiableOn,
    fun l z hz => Finset.sum_congr rfl fun j _ => by rw [(hg j).periodic l z hz]⟩

/-- The weighted sum is subadditive for finite linear combinations (coefficients are linear). -/
private theorem wsum_sum_le {m : ℕ} {ι : Type*} [Fintype ι] {s : ℝ} {I : Fin m → ℂ}
    (a : ι → ℂ) (g : ι → (Fin n → ℂ) × (Fin m → ℂ) → ℂ)
    (hc : ∀ j, Continuous fun x : Fin n → ℝ => g j (fun l => (x l : ℂ), I))
    (hg : ∀ j, WSummable (g j) s I) :
    WSummable (fun z => ∑ j, a j * g j z) s I ∧
      wsum (fun z => ∑ j, a j * g j z) s I ≤ ∑ j, ‖a j‖ * wsum (g j) s I := by
  have hcoeff : ∀ k, coeff (fun z => ∑ j, a j * g j z) I k = ∑ j, a j * coeff (g j) I k :=
    fun k => KAM.torusCoeff_finset_sum_mul Finset.univ hc a k
  have hterm : ∀ k, ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k ≤
      ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) := fun k => by
    rw [hcoeff]
    calc ‖∑ j, a j * coeff (g j) I k‖ * modeWeight s k
        ≤ (∑ j, ‖a j * coeff (g j) I k‖) * modeWeight s k :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
      _ = ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, mul_assoc]
  have hsum : Summable fun k : Fin n → ℤ =>
      ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) :=
    summable_sum fun j _ => (hg j).mul_left _
  have hnn : ∀ k : Fin n → ℤ, 0 ≤ ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k :=
    fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsum, ?_⟩
  unfold wsum
  calc ∑' k, ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k
      ≤ ∑' k, ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le hnn hterm hsum) hsum
    _ = ∑ j, ‖a j‖ * ∑' k, ‖coeff (g j) I k‖ * modeWeight s k := by
        rw [Summable.tsum_finsetSum fun j _ => (hg j).mul_left _]
        exact Finset.sum_congr rfl fun j _ => tsum_mul_left

/-- A product of two summable class functions at a fixed `I`. -/
private theorem prod_wsum {m : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}
    {a b : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hs : 0 < s) (ha : InClass D r s a)
    (hb : InClass D r s b) {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) (hsa : WSummable a s I)
    (hsb : WSummable b s I) :
    WSummable (fun z => a z * b z) s I ∧
      wsum (fun z => a z * b z) s I ≤ wsum a s I * wsum b s I := by
  obtain ⟨-, -, -, h4, h5⟩ := coeff_mul hs ha hb hI hsa hsb
  exact ⟨h4, h5⟩

/-! ### The bracket estimate -/

private theorem blockC_nonneg (b : PartialBlock n k) : 0 ≤ b.c :=
  div_nonneg (by positivity) (sq_nonneg _)

theorem bracket (b : PartialBlock n k) {R0 s0 R s ρ σ U V : ℝ} {u v : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hR0 : R-ρ < R0) (hs0 : s-σ < s0)
    (hu : InClass b.base R0 s0 u) (hv : InClass b.base R s v)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hbu : WBound b.base R0 s0 u U) (hbv : WBound b.base R s v V) :
    InClass b.base (R-ρ) (s-σ) (extBracket b.c u v) ∧
    WBound b.base (R-ρ) (s-σ) (extBracket b.c u v)
      (((Real.exp 1)⁻¹*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ))+
        2*k*b.c/((R0-R+ρ)*ρ))*U*V) := by
  -- `hρR`, `hV` are part of the signature (not needed for the estimate).
  have _ := hρR
  have _ := hV
  have hc := blockC_nonneg b
  have hs : 0 < s := hσ.trans hσs
  have ht : 0 < s - σ := sub_pos.mpr hσs
  have hs₀ : 0 < s0 := ht.trans hs0
  have hd1 : 0 < R0 - R + ρ := by linarith
  have hd2 : 0 < s0 - s + σ := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hu' : InClass b.base (R - ρ) (s - σ) u := inClass_anti hu hR0.le hs0.le
  have hv' : InClass b.base (R - ρ) (s - σ) v := inClass_anti hv (by linarith) (by linarith)
  have e1 : R0 - (R - ρ) = R0 - R + ρ := by ring
  have e2 : s0 - (s - σ) = s0 - s + σ := by ring
  have e3 : s - (s - σ) = σ := by ring
  have e4 : R - (R - ρ) = ρ := by ring
  have hθu := cauchy_theta hu hbu ht hs0
  have hθv := cauchy_theta hv hbv ht (by linarith : s - σ < s)
  have hau := cauchy_action hs₀ hu hbu hR0
  have hav := cauchy_action hs hv hbv (by linarith : R - ρ < R)
  rw [e1] at hau
  rw [e4] at hav
  rw [e2] at hθu
  rw [e3] at hθv
  -- classes of the derivatives
  have hdθu : ∀ i, InClass b.base (R - ρ) (s - σ) (dtheta i u) := fun i =>
    inClass_fderiv_apply hu' (Pi.single i 1, 0)
  have hdθv : ∀ i, InClass b.base (R - ρ) (s - σ) (dtheta i v) := fun i =>
    inClass_fderiv_apply hv' (Pi.single i 1, 0)
  have hdIu' : ∀ i, InClass b.base (R - ρ) (s - σ) (dI i u) := fun i =>
    inClass_fderiv_apply hu' (0, Pi.single i 1)
  have hdIv' : ∀ i, InClass b.base (R - ρ) (s - σ) (dI i v) := fun i =>
    inClass_fderiv_apply hv' (0, Pi.single i 1)
  refine ⟨?_, ?_⟩
  · rw [extBracket_eq]
    refine inClass_sum _ _ fun j => ?_
    rcases j with i | i | i | i
    · exact inClass_mul' (hdθu i) (hdIv' _)
    · exact inClass_mul' (hdIu' _) (hdθv i)
    · exact inClass_mul' (hdIu' _) (hdIv' _)
    · exact inClass_mul' (hdIu' _) (hdIv' _)
  intro I hI
  have hIu : I ∈ polyNbhd b.base R0 := polyNbhd_mono hR0.le hI
  have hIv : I ∈ polyNbhd b.base R := polyNbhd_mono (by linarith) hI
  have hMu : wsum u s0 I ≤ U := (hbu I hIu).2
  have hMv : wsum v s I ≤ V := (hbv I hIv).2
  obtain ⟨hθu_s, hθu_sum⟩ := hθu.1 I hIu
  obtain ⟨hθv_s, hθv_sum⟩ := hθv.1 I hIv
  have hdIu : ∀ i, WBound b.base (R - ρ) (s - σ) (dI i u) (U / (R0 - R + ρ)) := fun i =>
    (hau i).mono le_rfl hs0.le le_rfl
  have hdIv : ∀ i, WBound b.base (R - ρ) (s - σ) (dI i v) (V / ρ) := fun i =>
    (hav i).mono le_rfl (by linarith) le_rfl
  have hP := fun i j => prod_wsum ht (hdθu i) (hdIv' j) hI (hθu_s i) (hdIv j I hI).1
  have hQ := fun i j => prod_wsum ht (hdIu' i) (hdθv j) hI (hdIu i I hI).1 (hθv_s j)
  have hS := fun i j => prod_wsum ht (hdIu' i) (hdIv' j) hI (hdIu i I hI).1 (hdIv j I hI).1
  obtain ⟨hws, hwle⟩ := wsum_sum_le (s := s - σ) (I := I) (brCoef b.c) (brTerm u v)
    (fun j => by
      rcases j with i | i | i | i
      · exact continuous_slice ht (inClass_mul' (hdθu i) (hdIv' _)) hI
      · exact continuous_slice ht (inClass_mul' (hdIu' _) (hdθv i)) hI
      · exact continuous_slice ht (inClass_mul' (hdIu' _) (hdIv' _)) hI
      · exact continuous_slice ht (inClass_mul' (hdIu' _) (hdIv' _)) hI)
    (fun j => by
      rcases j with i | i | i | i
      · exact (hP i _).1
      · exact (hQ _ i).1
      · exact (hS _ _).1
      · exact (hS _ _).1)
  rw [← extBracket_eq] at hws hwle
  refine ⟨hws, hwle.trans ?_⟩
  simp only [Fintype.sum_sum_type, brCoef, brTerm, Sum.elim_inl, Sum.elim_inr, norm_one,
    norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, one_mul, ← Finset.mul_sum]
  have hA : ∑ i, wsum (fun z => dtheta i u z * dI (Fin.castAdd (k + k) i) v z) (s - σ) I ≤
      U / (Real.exp 1 * (s0 - s + σ)) * (V / ρ) := by
    calc ∑ i, wsum (fun z => dtheta i u z * dI (Fin.castAdd (k + k) i) v z) (s - σ) I
        ≤ ∑ i, wsum (dtheta i u) (s - σ) I * (V / ρ) :=
          Finset.sum_le_sum fun i _ =>
            (hP i _).2.trans (mul_le_mul_of_nonneg_left (hdIv _ I hI).2 (wsum_nonneg' _ _ _))
      _ = (∑ i, wsum (dtheta i u) (s - σ) I) * (V / ρ) := by rw [Finset.sum_mul]
      _ ≤ U / (Real.exp 1 * (s0 - s + σ)) * (V / ρ) := by
          refine mul_le_mul_of_nonneg_right (hθu_sum.trans ?_) (by positivity)
          exact div_le_div_of_nonneg_right hMu (by positivity)
  have hB : ∑ i, wsum (fun z => dI (Fin.castAdd (k + k) i) u z * dtheta i v z) (s - σ) I ≤
      U / (R0 - R + ρ) * (V / (Real.exp 1 * σ)) := by
    calc ∑ i, wsum (fun z => dI (Fin.castAdd (k + k) i) u z * dtheta i v z) (s - σ) I
        ≤ ∑ i, U / (R0 - R + ρ) * wsum (dtheta i v) (s - σ) I :=
          Finset.sum_le_sum fun i _ =>
            (hQ _ i).2.trans (mul_le_mul_of_nonneg_right (hdIu _ I hI).2 (wsum_nonneg' _ _ _))
      _ = U / (R0 - R + ρ) * ∑ i, wsum (dtheta i v) (s - σ) I := by rw [Finset.mul_sum]
      _ ≤ U / (R0 - R + ρ) * (V / (Real.exp 1 * σ)) := by
          refine mul_le_mul_of_nonneg_left (hθv_sum.trans ?_) (by positivity)
          exact div_le_div_of_nonneg_right hMv (by positivity)
  have hslow : ∀ (f g : Fin k → Fin (n + (k + k))),
      ∑ i, wsum (fun z => dI (f i) u z * dI (g i) v z) (s - σ) I ≤
        k * (U / (R0 - R + ρ) * (V / ρ)) := by
    intro f g
    calc ∑ i, wsum (fun z => dI (f i) u z * dI (g i) v z) (s - σ) I
        ≤ ∑ _i : Fin k, U / (R0 - R + ρ) * (V / ρ) :=
          Finset.sum_le_sum fun i _ =>
            (hS _ _).2.trans (mul_le_mul (hdIu _ I hI).2 (hdIv _ I hI).2 (wsum_nonneg' _ _ _)
              (by positivity))
      _ = k * (U / (R0 - R + ρ) * (V / ρ)) := by simp
  have hC := hslow (fun i => Fin.natAdd n (Fin.castAdd k i))
    (fun i => Fin.natAdd n (Fin.natAdd k i))
  have hD := hslow (fun i => Fin.natAdd n (Fin.natAdd k i))
    (fun i => Fin.natAdd n (Fin.castAdd k i))
  have hcC := mul_le_mul_of_nonneg_left hC hc
  have hcD := mul_le_mul_of_nonneg_left hD hc
  refine (add_le_add hA (add_le_add hB (add_le_add hcC hcD))).trans (le_of_eq ?_)
  field_simp
  ring

theorem bracket_dominated {c ρ σ R0 R s0 s : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hσ : 0 < σ) (hR : R-ρ < R0) (hs : s-σ < s0) (hSL : slowLoss c ρ σ k) :
    (Real.exp 1)⁻¹*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ)) + 2*k*c/((R0-R+ρ)*ρ) ≤
      (1/2)*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ)) := by
  -- `hc` is part of the signature (not needed: a negative `c` only helps).
  have _ := hc
  have hd1 : 0 < R0 - R + ρ := by linarith
  have hd2 : 0 < s0 - s + σ := by linarith
  have hX : 0 < 1/((R0-R+ρ)*σ) := by positivity
  have hY : 0 < 1/((s0-s+σ)*ρ) := by positivity
  have hslow : 2*k*c/((R0-R+ρ)*ρ) ≤ (1/8)*(1/((R0-R+ρ)*σ)) := by
    rw [div_le_iff₀ (by positivity)]
    have h : (1/8)*(1/((R0-R+ρ)*σ))*((R0-R+ρ)*ρ) = ρ/(8*σ) := by field_simp
    rw [h, le_div_iff₀ (by positivity)]
    unfold slowLoss at hSL
    nlinarith
  have hinv : (Real.exp 1)⁻¹ ≤ 3/8 := by
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num
    linarith
  have hmul := mul_le_mul_of_nonneg_right hinv (add_pos hX hY).le
  linarith

/-- The coefficients of two functions agreeing on `𝒟_{r,s}` agree (`s > 0`). -/
private theorem wbound_congr {m : ℕ} {D : Set (Fin m → ℂ)} {r s M : ℝ}
    {f F : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hs : 0 < s) (h : ∀ z ∈ Dom n D r s, f z = F z)
    (hF : WBound D r s F M) : WBound D r s f M := by
  intro I hI
  have hcoeff : ∀ k, coeff f I k = coeff F I k := fun k => by
    unfold coeff
    congr 1
    funext x
    exact h _ ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩
  obtain ⟨h1, h2⟩ := hF I hI
  refine ⟨?_, ?_⟩
  · simpa only [WSummable, hcoeff] using h1
  · simpa only [wsum, hcoeff] using h2

private theorem wbound_sum {m : ℕ} {ι : Type*} [Fintype ι] {D : Set (Fin m → ℂ)} {r s : ℝ}
    (hs : 0 < s) (g : ι → (Fin n → ℂ) × (Fin m → ℂ) → ℂ) (M : ι → ℝ)
    (hg : ∀ j, InClass D r s (g j)) (hb : ∀ j, WBound D r s (g j) (M j)) :
    WBound D r s (fun z => ∑ j, g j z) (∑ j, M j) := by
  intro I hI
  obtain ⟨h1, h2⟩ := wsum_sum_le (s := s) (I := I) (fun _ => (1 : ℂ)) g
    (fun j => continuous_slice hs (hg j) hI) (fun j => (hb j I hI).1)
  simp only [one_mul, norm_one] at h1 h2
  exact ⟨h1, h2.trans (Finset.sum_le_sum fun j _ => (hb j I hI).2)⟩

/-- Decomposition is literal finite summation, as Part 6, with independent base dimension. -/
theorem bracket_g (b : PartialBlock n k) {N : ℕ} {R s ρ σ V : ℝ}
    (gj : Fin N → EC n k → ℂ) (Rj sj Uj : Fin N → ℝ) (φ : EC n k → ℂ)
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hSL : slowLoss b.c ρ σ k) (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j)
    (hU : ∀ j, 0 ≤ Uj j) (hV : 0 ≤ V)
    (hg : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j))
    (hφ : InClass b.base R s φ) (hφb : WBound b.base R s φ V) :
    WBound b.base (R-ρ) (s-σ) (extBracket b.c (fun z => ∑ j, gj j z) φ)
      ((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)*V/(ρ*σ)) := by
  have hc := blockC_nonneg b
  have ht : 0 < s - σ := sub_pos.mpr hσs
  have per : ∀ j, InClass b.base (R-ρ) (s-σ) (extBracket b.c (gj j) φ) ∧
      WBound b.base (R-ρ) (s-σ) (extBracket b.c (gj j) φ)
        ((1/2)*(1/((Rj j-R+ρ)*σ)+1/((sj j-s+σ)*ρ))*Uj j*V) := fun j => by
    have h1 : R - ρ < Rj j := by linarith [hRj j]
    have h2 : s - σ < sj j := by linarith [hsj j]
    obtain ⟨hc1, hb1⟩ := bracket b hρ hρR hσ hσs h1 h2 (hg j) hφ (hU j) hV (hgb j) hφb
    refine ⟨hc1, hb1.mono le_rfl le_rfl ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (bracket_dominated hc hρ hσ h1 h2 hSL) (hU j)) hV
  have hsum := wbound_sum ht (fun j => extBracket b.c (gj j) φ) _ (fun j => (per j).1)
    (fun j => (per j).2)
  refine wbound_congr ht (fun z hz => ?_) (hsum.mono le_rfl le_rfl (le_of_eq ?_))
  · have hd : ∀ j ∈ Finset.univ, DifferentiableAt ℂ (gj j) z := fun j _ =>
      ((hg j).differentiableOn.differentiableAt
        ((isOpen_Dom b.base (Rj j) (sj j)).mem_nhds
          (Dom_mono (by linarith [hRj j]) (by linarith [hsj j]) hz)))
    unfold extBracket
    rw [fderiv_fun_sum hd, sum_apply]
  · rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd1 : 0 < Rj j - R + ρ := by linarith [hRj j]
    have hd2 : 0 < sj j - s + σ := by linarith [hsj j]
    field_simp

end KAM.Nekhoroshev

end
