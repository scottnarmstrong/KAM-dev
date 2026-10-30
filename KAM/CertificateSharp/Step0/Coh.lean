/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Step0.L1Model
public import KAM.CertificateSharp.Freq.SmallDivisorSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Certified cohomological solves on Fourier models

Given a model `m = ⟨deg, P, rad⟩` that encloses `g` with an ℓ¹ remainder of strip width `ρ`
(`CertModel.EnclosesL1`), and a frequency box enclosing `ω`, `CertModel.cohSolve` builds the model
of the solution `𝓡 g = KAM.cohSolution ω g` (coefficients `ĝ_k / (2πi k·ω)`, zero mode `0`). The
solved model has degree `deg − 1`, which absorbs the factor `2π`, and polynomial coefficients
`−i c_k / D_k`. Here `D_k = k·c` is the divisor at the box centre `c`, and `1/D_k` is an exact
rational, so each coefficient is a single backend product. Terms whose key is zero are dropped. Its
ℓ¹ radius, at the output width `W.rho = ρ − δ`, is

`Σ_k e_k w^{|k|₁}  +  2π Γ · rad`,

* **First summand.** The per-coefficient errors are
  `e_k = |c_k| (R_k/(L_k|D_k|) + width(1/D_k)) + rounding`, with:
  - `L_k = |D_k| − R_k` the box lower bound of `|k·ω|` (`KAM.CertificateSharp.boxLb`, package C2);
  - `R_k` the box radius.
* **Second summand.** `Γ ≥ Γ_∞(ω, δ)` (`KAM.smallDivisorSup`, SHARP-L9) bounds the solution of
  the remainder through the weighted ℓ¹ estimate `KAM.summableWeighted_solve_sup`.

**Norm of the radius.** Both input and output radii are weighted ℓ¹ norms of torus coefficients
(widths `ρ` and `W.rho`). `CertModel.EnclosesL1.cohSolve_encloses` turns the output into a sup
enclosure on `T_{W.rho}` with the same model, which feeds the certifier's sup-model arithmetic.

* **Scalar.** `CertModel.EnclosesL1.cohSolve`.
* **Vectors.** `cohSolve_pi` (the step-0 `ξᴺ = 𝓡 ηᴺ`), componentwise.
* **Matrices.** `cohSolve_mat`, entrywise (`Ω_K`-type solves). `norm_cohSolutionMat_le_rowSum`
  bounds the operator norm by row sums of the solved models' sup bounds.
* **Side condition.** `solveCheck`: every term is either divided (`L_k > 0`) or has a zero key.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp

open KAM KAM.Certificate CertArith

variable {n : ℕ}

section Defs

variable {α : Type} [CertArith α]

/-- `−i c`, exactly. -/
def CC.mulNegI (c : CC α) : CC α := ⟨c.im, neg c.re⟩

/-- A term is divided when the box gives a positive lower bound of `|k·ω|` at its key. -/
def solveKeep (n : ℕ) (box : FreqBox) (t : CertKey × CC α) : Bool :=
  decide (0 < boxLb box (certKeyFun n t.1))

/-- The exact rational `1/D_k`, `D_k = k·c` at the box centre. -/
def solveInv (n : ℕ) (box : FreqBox) (k : CertKey) : ℚ := (boxDot box (certKeyFun n k))⁻¹

/-- The rational bound `R_k/(L_k |D_k|)` of `|1/(k·ω) − 1/D_k|`. -/
def solveDivErr (n : ℕ) (box : FreqBox) (k : CertKey) : ℚ :=
  boxRad box (certKeyFun n k) / (boxLb box (certKeyFun n k) * |boxDot box (certKeyFun n k)|)

/-- The width `ofRatUp q − ofRatDown q` of the backend conversion of `q = 1/D_k`, upward. -/
def solveWidth (n : ℕ) (box : FreqBox) (k : CertKey) : α :=
  upAdd (ofRatUp (solveInv n box k)) (neg (ofRatDown (solveInv n box k)))

/-- The divided term: key, centre `ofRatUp(1/D_k) · (−i c_k)`, and its error bound. -/
def solveItem (n : ℕ) (box : FreqBox) (t : CertKey × CC α) : ErrTerm α :=
  (t.1, CC.scaleC (ofRatUp (solveInv n box t.1)) (CC.mulNegI t.2),
    upAdd (CC.scaleErrC (ofRatUp (solveInv n box t.1)) (CC.mulNegI t.2))
      (upMul t.2.normUp (upAdd (ofRatUp (solveDivErr n box t.1)) (solveWidth n box t.1))))

/-- The divided terms of a polynomial. -/
def solveItems (n : ℕ) (box : FreqBox) (P : CertPoly α) : List (ErrTerm α) :=
  (P.terms.filter (solveKeep n box)).map (solveItem n box)

/-- The side condition: every term is divided or has a zero key (the zero mode, dropped). -/
def solveCheck (n : ℕ) (box : FreqBox) (P : CertPoly α) : Bool :=
  P.terms.all fun t => solveKeep n box t || t.1.all fun z => z == 0

/-- The model of `𝓡 g` at the output weight `W` (strip width `W.rho`), for `Γ ≥ Γ_∞(ω, δ)`. -/
def CertModel.cohSolve (n : ℕ) (box : FreqBox) (Γ : ℚ) (W : CertWeight) (m : CertModel α) :
    CertModel α :=
  ⟨m.deg - 1, itemsPoly (solveItems n box m.poly),
    upAdd (errRadius W (solveItems n box m.poly)) (upMul (ofRatUp (2 * piUpQ * Γ)) m.rad)⟩

/-- The exact divided coefficient `c / (i k·ω)` of a term (`0` at the zero mode). -/
def exactSolveTerm (ω : Fin n → ℝ) (t : CertKey × CC α) : ℂ :=
  if certKeyFun n t.1 = 0 then 0 else
    t.2.toC / (Complex.I * (Diophantine.frequencyDot ω (certKeyFun n t.1) : ℂ))

/-- The computed centre of a term (`0` if it is dropped). -/
def centreSolveTerm (n : ℕ) (box : FreqBox) (t : CertKey × CC α) : ℂ :=
  if solveKeep n box t then (solveItem n box t).2.1.toC else 0

end Defs

section Lemmas

variable {α : Type} [CertArith α]

@[simp] theorem solveItem_fst (box : FreqBox) (t : CertKey × CC α) :
    (solveItem n box t).1 = t.1 := rfl

theorem getD_eq_zero_of_all : ∀ (k : List ℤ) (i : ℕ), (k.all fun z => z == 0) = true →
    k.getD i 0 = 0
  | [], _, _ => by simp
  | a :: l, 0, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1]
  | a :: l, i + 1, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_eq_zero_of_all l i h.2

theorem certKeyFun_eq_zero_of_all {k : CertKey} (h : (k.all fun z => z == 0) = true) :
    certKeyFun n k = 0 :=
  funext fun i => getD_eq_zero_of_all k i.val h

theorem ne_zero_of_boxLb_pos {box : FreqBox} {k : Fin n → ℤ} (h : 0 < boxLb box k) : k ≠ 0 := by
  rintro rfl
  simp [boxLb, boxDot, boxRad] at h

/-- The coefficients of the solved polynomial, term by term. -/
theorem coeff_itemsPoly_solveItems (box : FreqBox) (P : CertPoly α) (k : Fin n → ℤ) :
    (itemsPoly (solveItems n box P)).coeff n k =
      (P.terms.map fun t => if certKeyFun n t.1 = k then centreSolveTerm n box t else 0).sum := by
  rw [CertPoly.coeff_eq_sum]
  obtain ⟨L⟩ := P
  simp only [itemsPoly, solveItems, List.map_map]
  induction L with
  | nil => simp
  | cons t L ih =>
    by_cases h : solveKeep n box t = true
    · simp only [List.filter_cons, h, ↓reduceIte, List.map_cons, List.sum_cons, ih,
        Function.comp_apply, solveItem_fst, centreSolveTerm]
      rfl
    · simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte, ih, centreSolveTerm]
      simp only [List.map_cons, List.sum_cons, h, Bool.false_eq_true, ↓reduceIte, ite_self,
        zero_add]

theorem list_sum_ite_div {β : Type*} (L : List β) (p : β → Prop) [DecidablePred p] (a : β → ℂ)
    (d : ℂ) : (L.map fun t => if p t then a t / d else 0).sum =
      (L.map fun t => if p t then a t else 0).sum / d := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, ih, add_div]
    split_ifs <;> simp

theorem list_sum_ite_sub {β : Type*} (L : List β) (p : β → Prop) [DecidablePred p]
    (a b : β → ℂ) : (L.map fun t => if p t then a t else 0).sum -
      (L.map fun t => if p t then b t else 0).sum =
        (L.map fun t => if p t then a t - b t else 0).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    split_ifs <;> ring

theorem solve_add (ω : Fin n → ℝ) (a b : (Fin n → ℤ) → ℂ) (k : Fin n → ℤ) :
    Diophantine.solve ω (fun k => a k + b k) k =
      Diophantine.solve ω a k + Diophantine.solve ω b k := by
  unfold Diophantine.solve
  split_ifs <;> simp [add_div]

/-- The solve of the polynomial part, term by term: `𝓡((2π)^d P) = (2π)^{d−1} Σ c_k/(i k·ω) χ_k`. -/
theorem solve_const_mul_coeff (ω : Fin n → ℝ) (d : ℤ) (P : CertPoly α) (k : Fin n → ℤ) :
    Diophantine.solve ω (fun k => (2 * (Real.pi : ℂ)) ^ d * P.coeff n k) k =
      (2 * (Real.pi : ℂ)) ^ (d - 1) *
        (P.terms.map fun t => if certKeyFun n t.1 = k then exactSolveTerm ω t else 0).sum := by
  unfold Diophantine.solve
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte]
    have : (P.terms.map fun t =>
        if certKeyFun n t.1 = 0 then exactSolveTerm ω t else 0).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
      by_cases ht : certKeyFun n t.1 = 0 <;> simp [ht, exactSolveTerm]
    rw [this, mul_zero]
  · simp only [hk, ↓reduceIte]
    rw [CertPoly.coeff_eq_sum]
    have e : (P.terms.map fun t => if certKeyFun n t.1 = k then exactSolveTerm ω t else 0) =
        P.terms.map fun t => if certKeyFun n t.1 = k then
          t.2.toC / (Complex.I * (Diophantine.frequencyDot ω k : ℂ)) else 0 := by
      refine List.map_congr_left fun t _ => ?_
      by_cases ht : certKeyFun n t.1 = k
      · simp only [exactSolveTerm, ht, hk, ↓reduceIte]
      · simp only [ht, ↓reduceIte]
    rw [e, list_sum_ite_div, Diophantine.flowMultiplier]
    have h2 : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    rw [show (2 * (Real.pi : ℂ)) ^ d = (2 * (Real.pi : ℂ)) ^ (d - 1) * (2 * Real.pi) by
      rw [← zpow_add_one₀ h2, sub_add_cancel]]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (Diophantine.frequencyDot ω k : ℂ) =
      (2 * Real.pi) * (Complex.I * (Diophantine.frequencyDot ω k : ℂ)) by ring,
      show (2 * (Real.pi : ℂ)) ^ (d - 1) * (2 * Real.pi) *
        (P.terms.map fun t => if certKeyFun n t.1 = k then t.2.toC else 0).sum =
        (2 * Real.pi) * ((2 * (Real.pi : ℂ)) ^ (d - 1) *
          (P.terms.map fun t => if certKeyFun n t.1 = k then t.2.toC else 0).sum) by ring,
      mul_div_mul_left _ _ h2, mul_div_assoc]

variable [LawfulCertArith α]

theorem CC.toC_mulNegI (c : CC α) : (CC.mulNegI c).toC = -Complex.I * c.toC := by
  apply Complex.ext <;> simp [CC.mulNegI, CC.toC, LawfulCertArith.val_neg]

/-- **The error of one division.** For `ω` in the box and a divided term,
`|c/(i k·ω) − centre| ≤ e`. -/
theorem solveItem_err {box : FreqBox} {ω : Fin n → ℝ} (hbox : FreqEncloses n box ω)
    (t : CertKey × CC α) (hkeep : solveKeep n box t = true) :
    ‖t.2.toC / (Complex.I * (Diophantine.frequencyDot ω (certKeyFun n t.1) : ℂ)) -
        (solveItem n box t).2.1.toC‖ ≤ val (solveItem n box t).2.2 := by
  set k := certKeyFun n t.1 with hk
  have hLb : (0 : ℚ) < boxLb box k := by simpa [solveKeep] using hkeep
  set x := Diophantine.frequencyDot ω k with hx
  set D : ℚ := boxDot box k with hD
  set R : ℚ := boxRad box k with hR
  have hR0 : (0 : ℝ) ≤ R := by
    rw [hR]
    unfold boxRad
    push_cast
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans (hbox j))
  have hLbD : boxLb box k = |D| - R := rfl
  have hLb' : (0 : ℝ) < (boxLb box k : ℝ) := by exact_mod_cast hLb
  have hDpos : (0 : ℝ) < |(D : ℝ)| := by
    have : ((boxLb box k : ℚ) : ℝ) = |(D : ℝ)| - R := by rw [hLbD]; push_cast; rfl
    linarith
  have hD0 : (D : ℝ) ≠ 0 := abs_pos.mp hDpos
  have hxl : (boxLb box k : ℝ) ≤ |x| := boxLb_le hbox k
  have hxpos : 0 < |x| := hLb'.trans_le hxl
  have hx0 : x ≠ 0 := abs_pos.mp hxpos
  have hxD : |x - D| ≤ R := dot_sub_boxDot_le hbox k
  -- the real bound `|1/x − 1/D| ≤ R/(L |D|)`
  have hinv : |x⁻¹ - (D : ℝ)⁻¹| ≤ (solveDivErr n box t.1 : ℝ) := by
    have e : x⁻¹ - (D : ℝ)⁻¹ = (D - x) / (x * D) := by field_simp
    rw [e, abs_div, abs_mul, abs_sub_comm]
    unfold solveDivErr
    rw [← hk]
    push_cast
    exact div_le_div₀ hR0 hxD (by positivity) (mul_le_mul_of_nonneg_right hxl (abs_nonneg _))
  -- the backend scalar
  set q : ℚ := solveInv n box t.1 with hq
  have hqD : (q : ℝ) = (D : ℝ)⁻¹ := by rw [hq, solveInv, ← hk]; push_cast; rfl
  set s : α := ofRatUp q with hs
  have hsq : (q : ℝ) ≤ val s := LawfulCertArith.ofRatUp_ge q
  have hdq : val (ofRatDown q : α) ≤ q := LawfulCertArith.ofRatDown_le q
  have hw := LawfulCertArith.upAdd_ge s (neg (ofRatDown q : α))
  rw [LawfulCertArith.val_neg] at hw
  have hwid : |(q : ℝ) - val s| ≤ val (solveWidth n box t.1 : α) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    show _ ≤ val (upAdd s (neg (ofRatDown q)))
    linarith
  -- the complex decomposition
  set c : ℂ := t.2.toC with hc
  set r : ℂ := (CC.mulNegI t.2).toC with hr
  have hrc : r = -Complex.I * c := CC.toC_mulNegI t.2
  have hnr : ‖r‖ = ‖c‖ := by rw [hrc, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have e0 : c / (Complex.I * (x : ℂ)) = r * (x : ℂ)⁻¹ := by
    rw [hrc, div_eq_mul_inv, mul_inv, Complex.inv_I]
    ring
  have hsc := CC.norm_scale_sub_scaleC s (CC.mulNegI t.2)
  set ctr : ℂ := (CC.scaleC s (CC.mulNegI t.2)).toC with hctr
  have e1 : r * (x : ℂ)⁻¹ - ctr = r * (((x⁻¹ - (q : ℝ)) : ℝ) : ℂ) +
      r * ((((q : ℝ) - val s) : ℝ) : ℂ) + ((val s : ℂ) * r - ctr) := by
    push_cast
    ring
  have hn0 := CC.normUp_nonneg t.2
  have hc1 := CC.norm_le_normUp t.2
  have hdiv0 : (0 : ℝ) ≤ (solveDivErr n box t.1 : ℝ) := (abs_nonneg _).trans hinv
  have hup1 := LawfulCertArith.ofRatUp_ge (α := α) (solveDivErr n box t.1)
  have hsum := LawfulCertArith.upAdd_ge (ofRatUp (solveDivErr n box t.1) : α)
    (solveWidth n box t.1)
  have hw0 : 0 ≤ val (solveWidth n box t.1 : α) := (abs_nonneg _).trans hwid
  have hmul := LawfulCertArith.upMul_ge t.2.normUp
    (upAdd (ofRatUp (solveDivErr n box t.1)) (solveWidth n box t.1)) hn0 (by linarith)
  have htot := LawfulCertArith.upAdd_ge (CC.scaleErrC s (CC.mulNegI t.2))
    (upMul t.2.normUp (upAdd (ofRatUp (solveDivErr n box t.1)) (solveWidth n box t.1)))
  show ‖c / (Complex.I * (x : ℂ)) - ctr‖ ≤
    val (upAdd (CC.scaleErrC s (CC.mulNegI t.2))
      (upMul t.2.normUp (upAdd (ofRatUp (solveDivErr n box t.1)) (solveWidth n box t.1))))
  rw [e0, e1]
  have hn1 : ‖r * (((x⁻¹ - (q : ℝ)) : ℝ) : ℂ)‖ = ‖c‖ * |x⁻¹ - (q : ℝ)| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnr]
  have hn2 : ‖r * ((((q : ℝ) - val s) : ℝ) : ℂ)‖ = ‖c‖ * |(q : ℝ) - val s| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnr]
  have hA := norm_add_le (r * (((x⁻¹ - (q : ℝ)) : ℝ) : ℂ)) (r * ((((q : ℝ) - val s) : ℝ) : ℂ))
  have hB := norm_add_le (r * (((x⁻¹ - (q : ℝ)) : ℝ) : ℂ) + r * ((((q : ℝ) - val s) : ℝ) : ℂ))
    ((val s : ℂ) * r - ctr)
  have hsc' : ‖(val s : ℂ) * r - ctr‖ ≤ val (CC.scaleErrC s (CC.mulNegI t.2)) := hsc
  have h1 : ‖c‖ * |x⁻¹ - (q : ℝ)| ≤ ‖c‖ * (solveDivErr n box t.1 : ℝ) :=
    mul_le_mul_of_nonneg_left (by rw [hqD]; exact hinv) (norm_nonneg _)
  have h2 : ‖c‖ * |(q : ℝ) - val s| ≤ ‖c‖ * val (solveWidth n box t.1 : α) :=
    mul_le_mul_of_nonneg_left hwid (norm_nonneg _)
  have h3 : ‖c‖ * ((solveDivErr n box t.1 : ℝ) + val (solveWidth n box t.1 : α)) ≤
      val t.2.normUp * val (upAdd (ofRatUp (solveDivErr n box t.1)) (solveWidth n box t.1) : α) :=
    mul_le_mul hc1 (by linarith) (by positivity) hn0
  rw [hn1, hn2] at hA
  nlinarith


/-- The per-term error budget: `|exact − centre| ≤ e` for a divided term, `0` for a dropped one. -/
theorem norm_exact_sub_centre_le {box : FreqBox} {ω : Fin n → ℝ} (hbox : FreqEncloses n box ω)
    (t : CertKey × CC α) (hchk : (solveKeep n box t || t.1.all fun z => z == 0) = true) :
    ‖exactSolveTerm ω t - centreSolveTerm n box t‖ ≤
      if solveKeep n box t then val (solveItem n box t).2.2 else 0 := by
  by_cases h : solveKeep n box t = true
  · have hk : certKeyFun n t.1 ≠ 0 := ne_zero_of_boxLb_pos (by simpa [solveKeep] using h)
    simp only [exactSolveTerm, centreSolveTerm, hk, h, ↓reduceIte]
    exact solveItem_err hbox t h
  · have hz : certKeyFun n t.1 = 0 := by
      simp only [h, Bool.false_or] at hchk
      exact certKeyFun_eq_zero_of_all hchk
    simp [exactSolveTerm, centreSolveTerm, hz, h]

/-- The weighted ℓ¹ norm of the polynomial-part error is at most the error radius. -/
theorem sum_err_le_errRadius {box : FreqBox} {ω : Fin n → ℝ} (hbox : FreqEncloses n box ω)
    {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (P : CertPoly α)
    (hchk : solveCheck n box P = true) :
    (P.terms.map fun t => ‖exactSolveTerm ω t - centreSolveTerm n box t‖ *
      Real.exp (2 * Real.pi * W.rho * Fourier.modeSize (certKeyFun n t.1))).sum ≤
        val (errRadius W (solveItems n box P)) := by
  have hall : ∀ t ∈ P.terms, (solveKeep n box t || t.1.all fun z => z == 0) = true := by
    simpa [solveCheck, List.all_eq_true] using hchk
  have hexp : ∀ k : CertKey, Real.exp (2 * Real.pi * W.rho * Fourier.modeSize (certKeyFun n k)) ≤
      (W.w : ℝ) ^ keyDeg k := by
    intro k
    have hm : Fourier.modeSize (certKeyFun n k) =
        ((∑ i, (certKeyFun n k i).natAbs : ℕ) : ℝ) := by
      simp [Fourier.modeSize, Nat.cast_sum, Nat.cast_natAbs]
    rw [hm, mul_comm, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_nonneg _) (CertWeight.exp_le_w hW) _).trans
      (pow_le_pow_right₀ (CertWeight.one_le_w hW) (sum_natAbs_certKeyFun_le n k))
  have hterm : ∀ t : ErrTerm α, val t.2.2 *
      Real.exp (2 * Real.pi * W.rho * Fourier.modeSize (certKeyFun n t.1)) ≤
        val (weightTermUp W t.1 t.2.2) := by
    intro t
    have hw : (0 : ℝ) ≤ ((W.w ^ keyDeg t.1 : ℚ) : ℝ) := by
      have := CertWeight.one_le_w hW
      push_cast; positivity
    have h1 := LawfulCertArith.ofRatUp_ge (α := α) (W.w ^ keyDeg t.1)
    have h2 := LawfulCertArith.upMul_ge (abs t.2.2) (ofRatUp (W.w ^ keyDeg t.1))
      (by rw [LawfulCertArith.val_abs]; positivity) (hw.trans h1)
    rw [LawfulCertArith.val_abs] at h2
    push_cast at h1
    calc val t.2.2 * Real.exp (2 * Real.pi * W.rho * Fourier.modeSize (certKeyFun n t.1))
        ≤ |val t.2.2| * Real.exp (2 * Real.pi * W.rho * Fourier.modeSize (certKeyFun n t.1)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |val t.2.2| * val (ofRatUp (W.w ^ keyDeg t.1) : α) :=
          mul_le_mul_of_nonneg_left ((hexp t.1).trans h1) (abs_nonneg _)
      _ ≤ _ := h2
  refine le_trans ?_ (sumUp_ge _ _)
  clear hchk
  obtain ⟨L⟩ := P
  simp only [solveItems] at hall ⊢
  induction L with
  | nil => simp
  | cons t L ih =>
    have ht := norm_exact_sub_centre_le hbox t (hall t (by simp))
    have hL := ih fun u hu => hall u (by simp [hu])
    have he := (Real.exp_pos (2 * Real.pi * W.rho * Fourier.modeSize (certKeyFun n t.1))).le
    by_cases h : solveKeep n box t = true
    · simp only [h, ↓reduceIte] at ht
      simp only [List.map_cons, List.sum_cons, List.filter_cons, h, ↓reduceIte, solveItem_fst]
      have := hterm (solveItem n box t)
      simp only [solveItem_fst] at this
      have := mul_le_mul_of_nonneg_right ht he
      linarith
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at ht
      simp only [List.map_cons, List.sum_cons, List.filter_cons, h, Bool.false_eq_true,
        ↓reduceIte]
      have := mul_le_mul_of_nonneg_right ht he
      rw [zero_mul] at this
      linarith

/-- **The certified cohomological solve on a model.** Let `ω` lie in the box, be
`(γ, τ)`-Diophantine, and satisfy `Γ_∞(ω, ρ − W.rho) ≤ Γ`. If `m` encloses `g` with an ℓ¹
remainder of width `ρ > W.rho` and the side condition holds, then `m.cohSolve` encloses
`𝓡 g = cohSolution ω g` with an ℓ¹ remainder of width `W.rho`. -/
theorem CertModel.EnclosesL1.cohSolve {box : FreqBox} {ω : Fin n → ℝ}
    (hbox : FreqEncloses n box ω) {γ τ : ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) {ρ : ℝ}
    (hρ : (W.rho : ℝ) < ρ) {Γ : ℚ} (hΓ : smallDivisorSup ω (ρ - W.rho) ≤ Γ)
    {m : CertModel α} (hchk : solveCheck n box m.poly = true) {g : (Fin n → ℂ) → ℂ}
    (hg : CertModel.EnclosesL1 n ρ m g) :
    CertModel.EnclosesL1 n W.rho (CertModel.cohSolve n box Γ W m) (cohSolution ω g) := by
  have hc : Diophantine.Condition ω γ τ := hω.condition
  have hW0 := CertWeight.rho_pos hW
  have hδ : 0 < ρ - W.rho := sub_pos.mpr hρ
  have hδρ : ρ - W.rho < ρ := by linarith
  have hs := hg.summableWeighted
  obtain ⟨-, -, hcoef⟩ := torusCoeff_cohSolution_l1 hω hγ hτ hδ hδρ hs
  have hrad : 2 * Real.pi * ρ - 2 * Real.pi * (ρ - W.rho) = 2 * Real.pi * W.rho := by ring
  obtain ⟨hS1, hS2⟩ := summableWeighted_solve_sup hc hγ hτ hδ hg.1
  rw [hrad] at hS1 hS2
  set d : CertKey × CC α → ℂ := fun t => exactSolveTerm ω t - centreSolveTerm n box t with hd
  obtain ⟨hD1, hD2⟩ := summableWeighted_list (2 * Real.pi * W.rho) (fun t => certKeyFun n t.1) d
    m.poly.terms
  have hDb := sum_err_le_errRadius hbox hW m.poly hchk
  -- the residual of the solved model
  have hres : CertModel.residualCoeff n (CertModel.cohSolve n box Γ W m) (cohSolution ω g) =
      fun k =>
      (2 * (Real.pi : ℂ)) ^ (m.deg - 1) *
        (m.poly.terms.map fun t => if certKeyFun n t.1 = k then d t else 0).sum +
        Diophantine.solve ω (CertModel.residualCoeff n m g) k := by
    funext k
    have hg' : (torusCoeff fun x => g fun j => (x j : ℂ)) =
        fun k => (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.coeff n k + CertModel.residualCoeff n m g k :=
      funext (CertModel.torusCoeff_eq m g)
    show torusCoeff (fun x => cohSolution ω g fun j => (x j : ℂ)) k -
        (2 * (Real.pi : ℂ)) ^ (m.deg - 1) * (itemsPoly (solveItems n box m.poly)).coeff n k = _
    rw [hcoef, hg', solve_add, solve_const_mul_coeff, coeff_itemsPoly_solveItems]
    simp only [hd]
    rw [← list_sum_ite_sub]
    ring
  have hrad0 := hg.rad_nonneg
  have hΓ0 : (0 : ℝ) ≤ Γ := (smallDivisorSup_nonneg _ _).trans hΓ
  unfold CertModel.EnclosesL1
  rw [hres]
  obtain ⟨hA1, hA2⟩ := summableWeighted_const_mul ((2 * (Real.pi : ℂ)) ^ (m.deg - 1)) hD1
  obtain ⟨hT1, hT2⟩ := summableWeighted_add hA1 hS1
  refine ⟨hT1, hT2.trans ?_⟩
  rw [hA2, norm_two_pi_zpow]
  show _ ≤ (2 * Real.pi) ^ (m.deg - 1) * val (upAdd (errRadius W (solveItems n box m.poly))
    (upMul (ofRatUp (2 * piUpQ * Γ)) m.rad))
  have hp0 : (0 : ℝ) < (2 * Real.pi) ^ (m.deg - 1) := by positivity
  have h2pi : (2 * Real.pi) ^ m.deg = (2 * Real.pi) ^ (m.deg - 1) * (2 * Real.pi) := by
    rw [← zpow_add_one₀ (by positivity), sub_add_cancel]
  have hR0 := weightedNorm_nonneg (2 * Real.pi * ρ) (CertModel.residualCoeff n m g)
  have hsup0 := smallDivisorSup_nonneg ω (ρ - W.rho)
  have hpiq : (2 * Real.pi) * (Γ : ℝ) ≤ ((2 * piUpQ * Γ : ℚ) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_right (by linarith [pi_lt_piUpQ]) hΓ0
  have hq := LawfulCertArith.ofRatUp_ge (α := α) (2 * piUpQ * Γ)
  have hmul := LawfulCertArith.upMul_ge (ofRatUp (2 * piUpQ * Γ) : α) m.rad
    (by have : (0 : ℝ) ≤ 2 * Real.pi * Γ := by positivity
        linarith) hrad0
  have hadd := LawfulCertArith.upAdd_ge (errRadius W (solveItems n box m.poly))
    (upMul (ofRatUp (2 * piUpQ * Γ)) m.rad)
  have hE : Fourier.weightedNorm (2 * Real.pi * W.rho)
      (fun k => (m.poly.terms.map fun t => if certKeyFun n t.1 = k then d t else 0).sum) ≤
        val (errRadius W (solveItems n box m.poly)) := hD2.trans hDb
  have hX : smallDivisorSup ω (ρ - W.rho) * Fourier.weightedNorm (2 * Real.pi * ρ)
      (CertModel.residualCoeff n m g) ≤
        (2 * Real.pi) ^ (m.deg - 1) * ((2 * Real.pi) * Γ * val m.rad) := by
    calc smallDivisorSup ω (ρ - W.rho) * Fourier.weightedNorm (2 * Real.pi * ρ)
          (CertModel.residualCoeff n m g)
        ≤ Γ * ((2 * Real.pi) ^ m.deg * val m.rad) := mul_le_mul hΓ hg.2 hR0 hΓ0
      _ = (2 * Real.pi) ^ (m.deg - 1) * ((2 * Real.pi) * Γ * val m.rad) := by rw [h2pi]; ring
  have hY : (2 * Real.pi) * Γ * val m.rad ≤ val (upMul (ofRatUp (2 * piUpQ * Γ)) m.rad : α) :=
    (mul_le_mul_of_nonneg_right (hpiq.trans hq) hrad0).trans hmul
  calc (2 * Real.pi) ^ (m.deg - 1) * Fourier.weightedNorm (2 * Real.pi * W.rho)
        (fun k => (m.poly.terms.map fun t => if certKeyFun n t.1 = k then d t else 0).sum) +
        Fourier.weightedNorm (2 * Real.pi * W.rho)
          (Diophantine.solve ω (CertModel.residualCoeff n m g))
      ≤ (2 * Real.pi) ^ (m.deg - 1) * val (errRadius W (solveItems n box m.poly)) +
          (2 * Real.pi) ^ (m.deg - 1) * ((2 * Real.pi) * Γ * val m.rad) :=
        add_le_add (mul_le_mul_of_nonneg_left hE hp0.le) (hS2.trans hX)
    _ ≤ (2 * Real.pi) ^ (m.deg - 1) * val (upAdd (errRadius W (solveItems n box m.poly))
          (upMul (ofRatUp (2 * piUpQ * Γ)) m.rad)) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (by linarith) hp0.le

/-- The solved model also encloses `𝓡 g` in the sup norm on `T_{W.rho}` (same model). -/
theorem CertModel.EnclosesL1.cohSolve_encloses {box : FreqBox} {ω : Fin n → ℝ}
    (hbox : FreqEncloses n box ω) {γ τ : ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) {ρ : ℝ}
    (hρ : (W.rho : ℝ) < ρ) {Γ : ℚ} (hΓ : smallDivisorSup ω (ρ - W.rho) ≤ Γ)
    {m : CertModel α} (hchk : solveCheck n box m.poly = true) {g : (Fin n → ℂ) → ℂ}
    (hg : CertModel.EnclosesL1 n ρ m g) :
    (CertModel.cohSolve n box Γ W m).Encloses n W.rho (cohSolution ω g) := by
  have hδ : 0 < ρ - W.rho := sub_pos.mpr hρ
  have hδρ : ρ - W.rho < ρ := by linarith [CertWeight.rho_pos hW]
  obtain ⟨-, -, hcoef⟩ := torusCoeff_cohSolution_l1 hω hγ hτ hδ hδρ hg.summableWeighted
  refine (hg.cohSolve hbox hω hγ hτ hW hρ hΓ hchk).encloses fun θ _ => ?_
  rw [hcoef, cohSolution_eq_fourierSum]

/-- **Vectors** (the step-0 `ξᴺ = 𝓡 ηᴺ`): componentwise models. -/
theorem cohSolve_pi {p : ℕ} {box : FreqBox} {ω : Fin n → ℝ} (hbox : FreqEncloses n box ω)
    {γ τ : ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) {W : CertWeight}
    {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) {ρ : ℝ} (hρ : (W.rho : ℝ) < ρ) {Γ : ℚ}
    (hΓ : smallDivisorSup ω (ρ - W.rho) ≤ Γ) {ms : Fin p → CertModel α}
    (hchk : ∀ l, solveCheck n box (ms l).poly = true) {g : (Fin n → ℂ) → Fin p → ℂ}
    (hg : ∀ l, CertModel.EnclosesL1 n ρ (ms l) fun z => g z l) (l : Fin p) :
    CertModel.EnclosesL1 n W.rho (CertModel.cohSolve n box Γ W (ms l))
        (fun z => cohSolutionPi ω g z l) ∧
      (CertModel.cohSolve n box Γ W (ms l)).Encloses n W.rho (fun z => cohSolutionPi ω g z l) :=
  ⟨(hg l).cohSolve hbox hω hγ hτ hW hρ hΓ (hchk l),
    (hg l).cohSolve_encloses hbox hω hγ hτ hW hρ hΓ (hchk l)⟩

/-- **Matrices** (`Ω_K`-type solves): entrywise models. -/
theorem cohSolve_mat {p q : ℕ} {box : FreqBox} {ω : Fin n → ℝ} (hbox : FreqEncloses n box ω)
    {γ τ : ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) {W : CertWeight}
    {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) {ρ : ℝ} (hρ : (W.rho : ℝ) < ρ) {Γ : ℚ}
    (hΓ : smallDivisorSup ω (ρ - W.rho) ≤ Γ) {ms : Fin p → Fin q → CertModel α}
    (hchk : ∀ i j, solveCheck n box (ms i j).poly = true)
    {g : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ}
    (hg : ∀ i j, CertModel.EnclosesL1 n ρ (ms i j) fun z => g z i j) (i : Fin p) (j : Fin q) :
    CertModel.EnclosesL1 n W.rho (CertModel.cohSolve n box Γ W (ms i j))
        (fun z => cohSolutionMat ω g z i j) ∧
      (CertModel.cohSolve n box Γ W (ms i j)).Encloses n W.rho
        (fun z => cohSolutionMat ω g z i j) :=
  ⟨(hg i j).cohSolve hbox hω hγ hτ hW hρ hΓ (hchk i j),
    (hg i j).cohSolve_encloses hbox hω hγ hτ hW hρ hΓ (hchk i j)⟩

open scoped Matrix.Norms.Operator in
/-- The operator norm of the matrix solution on `T_{W.rho}` by row sums of the solved models'
certified sup bounds. -/
theorem norm_cohSolutionMat_le_rowSum {p q : ℕ} {box : FreqBox} {ω : Fin n → ℝ}
    (hbox : FreqEncloses n box ω) {γ τ : ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) {ρ : ℝ}
    (hρ : (W.rho : ℝ) < ρ) {Γ : ℚ} (hΓ : smallDivisorSup ω (ρ - W.rho) ≤ Γ)
    {ms : Fin p → Fin q → CertModel α} (hchk : ∀ i j, solveCheck n box (ms i j).poly = true)
    {g : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ}
    (hg : ∀ i j, CertModel.EnclosesL1 n ρ (ms i j) fun z => g z i j) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i, ∑ j, val ((CertModel.cohSolve n box Γ W (ms i j)).supBound W) ≤ B)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) : ‖cohSolutionMat ω g θ‖ ≤ B := by
  refine (KAM.norm_le_iff_forall_rowSum hB0).mpr fun i => (Finset.sum_le_sum fun j _ => ?_).trans
    (hB i)
  exact CertModel.norm_le_supBound hW
    (cohSolve_mat hbox hω hγ hτ hW hρ hΓ hchk hg i j).2 hθ

end Lemmas

end KAM.CertificateSharp

end
