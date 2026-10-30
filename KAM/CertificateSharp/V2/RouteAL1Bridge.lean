/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Step0.L1Model
public import KAM.Sharp2.L1.NormsOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From the certifier's sup models to certified ℓ¹ norms (package C6L1)

The certifier encloses its objects in the sup norm on `T_ρ` (`CertModel.Encloses`). The ℓ¹ entry
needs weighted ℓ¹ norms of the coefficients (`KAM.Sharp2.L1.L1Vec`, `L1Mat`) on a strip `T_{ρ'}`,
`ρ' < ρ`. C5CORE's `CertModel.Encloses.toL1` converts: the polynomial part is carried exactly, only
the remainder pays `cothPowUp n (ρ - ρ')`.

* `l1Up W' C m`: the certified ℓ¹ bound, at the weight `W'` of `T_{ρ'}`, of a function enclosed in
  sup by `m` on `T_ρ`: the sup bound of the model with radius `C · rad` (`l1Model`);
* `poly_weightedNorm_le`: `∑_k |P̂_k| e^{2πρ'|k|₁} ≤ P.weightedNormUp W'`;
* `weightedNorm_le_supBound`: an ℓ¹ enclosure at `W'.rho` is bounded by the model's `supBound W'`;
* `weightedNorm_le_l1Up`: **sup model ⇒ certified ℓ¹ norm** for a holomorphic `1`-periodic
  function;
* `torusCoeff_neg'`, `weightedNorm_neg`: signs do not change ℓ¹ norms.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.V2.L1

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The ℓ¹ model after the conversion: the same polynomial, the radius times `C`. -/
def l1Model (C : ℚ) (m : CertModel α) : CertModel α := ⟨m.deg, m.poly, upMul (ofRatUp C) m.rad⟩

/-- The certified ℓ¹ bound at the weight `W'` of a function enclosed in sup by `m`, with the
conversion factor `C`. -/
def l1Up (W' : CertWeight) (C : ℚ) (m : CertModel α) : α := (l1Model C m).supBound W'

theorem torusCoeff_neg' (f : (Fin n → ℝ) → ℂ) (k : Fin n → ℤ) :
    torusCoeff (fun x => -f x) k = -torusCoeff f k := by
  simp only [torusCoeff, torusAverage, mul_neg, MeasureTheory.integral_neg]

theorem summableWeighted_neg {s : ℝ} {a : (Fin n → ℤ) → ℂ} (h : Fourier.SummableWeighted s a) :
    Fourier.SummableWeighted s (fun k => -a k) := by
  simpa [Fourier.SummableWeighted, norm_neg] using h

theorem weightedNorm_neg (s : ℝ) (a : (Fin n → ℤ) → ℂ) :
    Fourier.weightedNorm s (fun k => -a k) = Fourier.weightedNorm s a := by
  simp [Fourier.weightedNorm, norm_neg]

variable [LawfulCertArith α]

/-- The weighted ℓ¹ norm of a polynomial at the weight `W` is at most `P.weightedNormUp W`. -/
theorem poly_weightedNorm_le {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (P : CertPoly α) :
    Fourier.weightedNorm (2 * Real.pi * W.rho) (P.coeff n) ≤ val (P.weightedNormUp W) := by
  have e : P.coeff n = fun k => (P.terms.map fun t =>
      if certKeyFun n t.1 = k then t.2.toC else 0).sum := funext (P.coeff_eq_sum n)
  have hL := (summableWeighted_list (β := CertKey × CC α) (2 * Real.pi * W.rho)
    (fun t => certKeyFun n t.1) (fun t => t.2.toC) P.terms).2
  rw [e]
  refine hL.trans ?_
  unfold CertPoly.weightedNormUp
  induction P.terms with
  | nil => simp [LawfulCertArith.val_ofInt]
  | cons t L ih =>
    have hw1 := CertWeight.one_le_w hW
    have hq : (0 : ℝ) ≤ ((W.w ^ (t.1.map Int.natAbs).sum : ℚ) : ℝ) := by
      have : (0 : ℝ) ≤ W.w := by linarith
      push_cast; positivity
    have hr := LawfulCertArith.ofRatUp_ge (α := α) (W.w ^ (t.1.map Int.natAbs).sum)
    have hn := CC.normUp_nonneg t.2
    have hm := LawfulCertArith.upMul_ge t.2.normUp
      (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum)) hn (hq.trans hr)
    have hs := LawfulCertArith.upAdd_ge
      (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum)))
      (L.foldr (fun t acc =>
        upAdd (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0))
    have hexp : Real.exp (2 * Real.pi * W.rho * Fourier.modeSize (certKeyFun n t.1)) ≤
        (W.w : ℝ) ^ (t.1.map Int.natAbs).sum := by
      have hmo : Fourier.modeSize (certKeyFun n t.1) =
          ((∑ i, (certKeyFun n t.1 i).natAbs : ℕ) : ℝ) := by
        simp [Fourier.modeSize, Nat.cast_sum, Nat.cast_natAbs]
      rw [hmo, mul_comm, Real.exp_nat_mul]
      exact (pow_le_pow_left₀ (Real.exp_nonneg _) (CertWeight.exp_le_w hW) _).trans
        (pow_le_pow_right₀ hw1 (sum_natAbs_certKeyFun_le n t.1))
    have hterm : ‖t.2.toC‖ * Real.exp (2 * Real.pi * W.rho * Fourier.modeSize (certKeyFun n t.1)) ≤
        val t.2.normUp * ((W.w : ℝ) ^ (t.1.map Int.natAbs).sum) :=
      mul_le_mul (CC.norm_le_normUp t.2) hexp (Real.exp_pos _).le hn
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    push_cast at hq hr hm hs
    have : val t.2.normUp * ((W.w : ℝ) ^ (t.1.map Int.natAbs).sum) ≤
        val t.2.normUp * val (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum) : α) :=
      mul_le_mul_of_nonneg_left hr hn
    linarith

/-- An ℓ¹ enclosure at the width of `W` is bounded by the model's sup bound at `W`. -/
theorem weightedNorm_le_supBound {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {m : CertModel α} {f : (Fin n → ℂ) → ℂ} (h : CertModel.EnclosesL1 n W.rho m f) :
    Fourier.SummableWeighted (2 * Real.pi * W.rho) (torusCoeff fun x => f fun j => (x j : ℂ)) ∧
      Fourier.weightedNorm (2 * Real.pi * W.rho) (torusCoeff fun x => f fun j => (x j : ℂ)) ≤
        val (m.supBound W) := by
  refine ⟨h.summableWeighted, ?_⟩
  have e : (torusCoeff fun x => f fun j => (x j : ℂ)) =
      fun k => (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.coeff n k + CertModel.residualCoeff n m f k :=
    funext (CertModel.torusCoeff_eq m f)
  have hP := CertPoly.summableWeighted_coeff (n := n) (2 * Real.pi * W.rho) m.poly
  obtain ⟨hc1, hc2⟩ := KAM.CertificateSharp.summableWeighted_const_mul
    ((2 * (Real.pi : ℂ)) ^ m.deg) hP
  obtain ⟨-, hadd⟩ := KAM.CertificateSharp.summableWeighted_add hc1 h.1
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ m.deg := by positivity
  have hnorm : ‖(2 * (Real.pi : ℂ)) ^ m.deg‖ = (2 * Real.pi) ^ m.deg := by
    rw [norm_zpow]
    have : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul]; simp [abs_of_pos Real.pi_pos]
    rw [this]
  have hrad : 0 ≤ val m.rad := h.rad_nonneg
  have hWP := poly_weightedNorm_le (n := n) hW m.poly
  have hS0 : 0 ≤ val (m.poly.weightedNormUp W) :=
    (KAM.CertificateSharp.weightedNorm_nonneg (n := n) _ _).trans hWP
  have hadd' := LawfulCertArith.upAdd_ge (m.poly.weightedNormUp W) m.rad
  have hF : (0 : ℝ) ≤ (degFactorUp m.deg : ℝ) := h2pi.le.trans (two_pi_zpow_le _)
  have hF' := LawfulCertArith.ofRatUp_ge (α := α) (degFactorUp m.deg)
  have hmul := LawfulCertArith.upMul_ge (ofRatUp (degFactorUp m.deg))
    (upAdd (m.poly.weightedNormUp W) m.rad) (hF.trans hF') (by linarith)
  rw [e]
  calc Fourier.weightedNorm (2 * Real.pi * W.rho)
        (fun k => (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.coeff n k + CertModel.residualCoeff n m f k)
      ≤ (2 * Real.pi) ^ m.deg * val (m.poly.weightedNormUp W) +
          (2 * Real.pi) ^ m.deg * val m.rad := by
        refine hadd.trans (add_le_add ?_ h.2)
        rw [hc2, hnorm]
        exact mul_le_mul_of_nonneg_left hWP h2pi.le
    _ = (2 * Real.pi) ^ m.deg * (val (m.poly.weightedNormUp W) + val m.rad) := by ring
    _ ≤ (degFactorUp m.deg : ℝ) * val (upAdd (m.poly.weightedNormUp W) m.rad) :=
        mul_le_mul (two_pi_zpow_le _) hadd' (by linarith) hF
    _ ≤ val (ofRatUp (degFactorUp m.deg) : α) * val (upAdd (m.poly.weightedNormUp W) m.rad) :=
        mul_le_mul_of_nonneg_right hF' (by linarith)
    _ ≤ val (m.supBound W) := hmul

/-- **Sup model ⇒ certified ℓ¹ norm.** If `m` encloses the holomorphic `1`-periodic `f` in sup on
`T_ρ` and `W'.rho < ρ`, the coefficients of `f` are summable at `W'.rho` with weighted norm at most
`l1Up W' C m`, for every rational `C ≥ cothPowUp n (ρ - W'.rho)`. -/
theorem weightedNorm_le_l1Up {W' : CertWeight} {s N : ℕ} (hW' : checkWeight W' s N = true)
    {ρ : ℚ} (hρ : W'.rho < ρ) {C : ℚ} (hC : cothPowUp n (ρ - W'.rho) ≤ C) {m : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (hfd : DifferentiableOn ℂ f (complexStrip n ρ))
    (hfp : IsPeriodicOn f ρ) (h : m.Encloses n ρ f) :
    Fourier.SummableWeighted (2 * Real.pi * W'.rho) (torusCoeff fun x => f fun j => (x j : ℂ)) ∧
      Fourier.weightedNorm (2 * Real.pi * W'.rho) (torusCoeff fun x => f fun j => (x j : ℂ)) ≤
        val (l1Up W' C m) := by
  have hρ' := CertWeight.rho_pos hW'
  have hδ : (0 : ℝ) < ((ρ - W'.rho : ℚ) : ℝ) := by
    have : (0 : ℚ) < ρ - W'.rho := by linarith
    exact_mod_cast this
  have hδρ : ((ρ - W'.rho : ℚ) : ℝ) < ρ := by push_cast; linarith
  have hρ0 : (0 : ℝ) < ρ := by
    have : (W'.rho : ℝ) < ρ := by exact_mod_cast hρ
    linarith
  have hrad := CertModel.Encloses.rad_nonneg hρ0 h
  have hcoth := coth_pow_le_cothPowUp n (show (0 : ℚ) < ρ - W'.rho by linarith)
  have hC' : (cothPowUp n (ρ - W'.rho) : ℝ) ≤ C := by exact_mod_cast hC
  have hC0 : (0 : ℝ) ≤ C := by
    refine le_trans ?_ (hcoth.trans hC')
    have hx : 0 < Real.pi * ((ρ - W'.rho : ℚ) : ℝ) := by positivity
    exact pow_nonneg (div_nonneg (Real.cosh_pos _).le (coth_le_one_add_inv hx).2.le) n
  have hCu := LawfulCertArith.ofRatUp_ge (α := α) C
  have hr : (C : ℝ) * val m.rad ≤ val (upMul (ofRatUp C) m.rad : α) :=
    (mul_le_mul_of_nonneg_right hCu hrad).trans
      (LawfulCertArith.upMul_ge (ofRatUp C) m.rad (hC0.trans hCu) hrad)
  have hL := CertModel.Encloses.toL1 hδ hδρ hfd hfp h (hcoth.trans hC') hr
  have e : ((ρ : ℝ) - ((ρ - W'.rho : ℚ) : ℝ)) = (W'.rho : ℝ) := by push_cast; ring
  rw [e] at hL
  exact weightedNorm_le_supBound hW' hL

end KAM.CertificateSharp.V2.L1

end
