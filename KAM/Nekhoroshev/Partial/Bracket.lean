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

end KAM.Nekhoroshev

end
