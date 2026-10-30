/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Ops
public import KAM.Strip.CohomologicalL1Bound
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Fourier models with a weighted ℓ¹ remainder

A certifier model `m = ⟨deg, P, rad⟩` (`KAM.Certificate.CertModel`) encloses `f` in the sup norm
when `sup_{T_ρ} |f − (2π)^deg P| ≤ (2π)^deg rad` (`CertModel.Encloses`). The cohomological solve
is sharp in the weighted ℓ¹ norm of the coefficients (the Wiener algebra of the strip,
`KAM.cohomological_l1`), so the step-0 models carry their remainder in that norm:

`CertModel.EnclosesL1 n ρ m f`: the torus coefficients `R_k = f̂_k − (2π)^deg P̂_k` of the remainder
(`CertModel.residualCoeff`) satisfy `∑_k |R_k| e^{2πρ|k|₁} ≤ (2π)^deg rad`.

* `summableWeighted_list`: finitely supported coefficient families (term lists) are summable at
  every radius, with the triangle bound; `summableWeighted_add`, `summableWeighted_const_mul`.
* `CertModel.EnclosesL1.encloses`: an ℓ¹ enclosure is a sup enclosure on `T_ρ` of every `f` that
  is the Fourier series of its coefficients there (holomorphic periodic data, a cohomological
  solution), with the same model.
* `CertModel.Encloses.toL1`: a sup enclosure of a holomorphic `1`-periodic `f` on `T_ρ` is an ℓ¹
  enclosure at `ρ − δ₁` once the radius is multiplied by `coth(πδ₁)^n`, which is at most the
  rational `cothPowUp n δ₁ = (1 + 1/(3.14 δ₁))^n` (`coth_pow_le_cothPowUp`). This is how the
  certifier's sup models (the invariance error and the frame models) enter the solve: only their
  remainder pays the factor, their polynomial part is carried exactly.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp

open KAM KAM.Certificate CertArith

variable {n : ℕ}

/-! ### Weighted ℓ¹ norms of finitely supported families -/

theorem summableWeighted_ite_add {s : ℝ} (k₀ : Fin n → ℤ) (v : ℂ) {b : (Fin n → ℤ) → ℂ}
    (hb : Fourier.SummableWeighted s b) :
    Fourier.SummableWeighted s (fun k => (if k₀ = k then v else 0) + b k) ∧
      Fourier.weightedNorm s (fun k => (if k₀ = k then v else 0) + b k) ≤
        ‖v‖ * Real.exp (s * Fourier.modeSize k₀) + Fourier.weightedNorm s b := by
  have h1 : HasSum (fun k : Fin n → ℤ =>
      ‖(if k₀ = k then v else 0)‖ * Real.exp (s * Fourier.modeSize k))
      (‖v‖ * Real.exp (s * Fourier.modeSize k₀)) := by
    have := hasSum_ite_eq k₀ (‖v‖ * Real.exp (s * Fourier.modeSize k₀))
    convert this using 1
    funext k
    by_cases h : k₀ = k
    · subst h; simp
    · simp [h, Ne.symm h]
  have hle : ∀ k, ‖(if k₀ = k then v else 0) + b k‖ * Real.exp (s * Fourier.modeSize k) ≤
      ‖(if k₀ = k then v else 0)‖ * Real.exp (s * Fourier.modeSize k) +
        ‖b k‖ * Real.exp (s * Fourier.modeSize k) := fun k => by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le
  have hs : Fourier.SummableWeighted s (fun k => (if k₀ = k then v else 0) + b k) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle (h1.summable.add hb)
  refine ⟨hs, ?_⟩
  calc Fourier.weightedNorm s (fun k => (if k₀ = k then v else 0) + b k)
      ≤ ∑' k, (‖(if k₀ = k then v else 0)‖ * Real.exp (s * Fourier.modeSize k) +
          ‖b k‖ * Real.exp (s * Fourier.modeSize k)) :=
        Summable.tsum_le_tsum hle hs (h1.summable.add hb)
    _ = _ := by
        rw [Summable.tsum_add h1.summable hb, h1.tsum_eq]
        rfl

/-- The family `k ↦ ∑_{t ∈ L, key t = k} v t` of a finite term list is summable at every radius,
and its weighted norm is at most `∑_t |v t| e^{s|key t|₁}`. -/
theorem summableWeighted_list {β : Type*} (s : ℝ) (key : β → Fin n → ℤ) (v : β → ℂ)
    (L : List β) :
    Fourier.SummableWeighted s (fun k => (L.map fun t => if key t = k then v t else 0).sum) ∧
      Fourier.weightedNorm s (fun k => (L.map fun t => if key t = k then v t else 0).sum) ≤
        (L.map fun t => ‖v t‖ * Real.exp (s * Fourier.modeSize (key t))).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ⟨by simp [Fourier.SummableWeighted], by simp [Fourier.weightedNorm]⟩
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨h1, h2⟩ := summableWeighted_ite_add (s := s) (key t) (v t) ih.1
    exact ⟨h1, h2.trans (by linarith [ih.2])⟩

theorem summableWeighted_add {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted s a) (hb : Fourier.SummableWeighted s b) :
    Fourier.SummableWeighted s (fun k => a k + b k) ∧
      Fourier.weightedNorm s (fun k => a k + b k) ≤
        Fourier.weightedNorm s a + Fourier.weightedNorm s b := by
  have hle : ∀ k, ‖a k + b k‖ * Real.exp (s * Fourier.modeSize k) ≤
      ‖a k‖ * Real.exp (s * Fourier.modeSize k) + ‖b k‖ * Real.exp (s * Fourier.modeSize k) :=
    fun k => by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le
  have hs : Fourier.SummableWeighted s (fun k => a k + b k) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle (ha.add hb)
  exact ⟨hs, (Summable.tsum_le_tsum hle hs (ha.add hb)).trans_eq (Summable.tsum_add ha hb)⟩

theorem summableWeighted_const_mul {s : ℝ} (c : ℂ) {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted s a) :
    Fourier.SummableWeighted s (fun k => c * a k) ∧
      Fourier.weightedNorm s (fun k => c * a k) = ‖c‖ * Fourier.weightedNorm s a := by
  have e : (fun k => ‖c * a k‖ * Real.exp (s * Fourier.modeSize k)) =
      fun k => ‖c‖ * (‖a k‖ * Real.exp (s * Fourier.modeSize k)) := by
    funext k; rw [norm_mul]; ring
  refine ⟨?_, ?_⟩
  · show Summable fun k => ‖c * a k‖ * Real.exp (s * Fourier.modeSize k)
    rw [e]
    exact ha.mul_left _
  · show ∑' k, ‖c * a k‖ * Real.exp (s * Fourier.modeSize k) = _
    rw [e, tsum_mul_left]
    rfl

theorem weightedNorm_nonneg (s : ℝ) (a : (Fin n → ℤ) → ℂ) : 0 ≤ Fourier.weightedNorm s a :=
  tsum_nonneg fun _ => by positivity

/-- `coth x ≤ 1 + 1/x` for `x > 0` (from `e^{2x} ≥ 1 + 2x`), and `sinh x > 0`. -/
theorem coth_le_one_add_inv {x : ℝ} (hx : 0 < x) :
    Real.cosh x / Real.sinh x ≤ 1 + 1 / x ∧ 0 < Real.sinh x := by
  have hE := Real.exp_pos (-x)
  have h2 : 2 * x + 1 ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have hsx : Real.sinh x = Real.exp (-x) * (Real.exp (2 * x) - 1) / 2 := by
    rw [Real.sinh_eq, mul_sub, mul_one, ← Real.exp_add, show -x + 2 * x = x by ring]
  have hs : x * Real.exp (-x) ≤ Real.sinh x := by
    rw [hsx]
    nlinarith
  have hspos : 0 < Real.sinh x := lt_of_lt_of_le (by positivity) hs
  have hc : Real.cosh x = Real.sinh x + Real.exp (-x) := by linarith [Real.cosh_sub_sinh x]
  refine ⟨?_, hspos⟩
  rw [div_le_iff₀ hspos, hc]
  have : Real.exp (-x) ≤ 1 / x * Real.sinh x := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hx]
    linarith
  linarith

/-- A rational upper bound `(1 + 1/(3.14 δ))^n` of `coth(πδ)^n`. -/
def cothPowUp (n : ℕ) (δ : ℚ) : ℚ := (1 + 1 / (314 / 100 * δ)) ^ n

theorem coth_pow_le_cothPowUp (n : ℕ) {δ : ℚ} (hδ : 0 < δ) :
    (Real.cosh (Real.pi * δ) / Real.sinh (Real.pi * δ)) ^ n ≤ (cothPowUp n δ : ℝ) := by
  have hd : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hx : 0 < Real.pi * δ := by positivity
  obtain ⟨h1, hspos⟩ := coth_le_one_add_inv hx
  have hc0 : 0 ≤ Real.cosh (Real.pi * δ) / Real.sinh (Real.pi * δ) :=
    div_nonneg (Real.cosh_pos _).le hspos.le
  have hpi := Real.pi_gt_d2
  have h2 : 1 / (Real.pi * δ) ≤ 1 / (314 / 100 * δ) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  unfold cothPowUp
  push_cast
  exact pow_le_pow_left₀ hc0 (h1.trans (by linarith)) n

theorem CertPoly.summableWeighted_coeff {α : Type} [CertArith α] (s : ℝ) (P : CertPoly α) :
    Fourier.SummableWeighted s (P.coeff n) := by
  have e : P.coeff n = fun k => (P.terms.map fun t =>
      if certKeyFun n t.1 = k then t.2.toC else 0).sum := funext (P.coeff_eq_sum n)
  have h := (summableWeighted_list (β := CertKey × CC α) s (fun t => certKeyFun n t.1)
    (fun t => t.2.toC) P.terms).1
  rw [e]
  exact h

theorem CertPoly.eval_add_single {α : Type} [CertArith α] (P : CertPoly α) (z : Fin n → ℂ)
    (i : Fin n) : P.eval n (z + Pi.single i (1 : ℂ)) = P.eval n z := by
  unfold CertPoly.eval
  simp only [character_add_single]

/-- `c P(θ)` is the Fourier series of `c P̂`. -/
theorem CertPoly.const_mul_eval_eq_fourierSum {α : Type} [CertArith α] (c : ℂ) (P : CertPoly α)
    (θ : Fin n → ℂ) : c * P.eval n θ = fourierSum (fun k => c * P.coeff n k) θ := by
  rw [CertPoly.eval_eq_fourierSum]
  simp only [fourierSum]
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by ring

/-! ### The ℓ¹ enclosure -/

section Model

variable {α : Type} [CertArith α]

/-- The torus coefficients `f̂_k − (2π)^deg P̂_k` of the remainder of `f` over the model. -/
def CertModel.residualCoeff (n : ℕ) (m : CertModel α) (f : (Fin n → ℂ) → ℂ)
    (k : Fin n → ℤ) : ℂ :=
  torusCoeff (fun x => f fun j => (x j : ℂ)) k - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.coeff n k

/-- `m` encloses `f` with an ℓ¹ remainder of strip width `ρ`: the coefficients of
`f − (2π)^deg P` on the real torus have weighted ℓ¹ norm `∑_k |R_k| e^{2πρ|k|₁} ≤ (2π)^deg rad`. -/
def CertModel.EnclosesL1 (n : ℕ) (ρ : ℝ) (m : CertModel α) (f : (Fin n → ℂ) → ℂ) : Prop :=
  Fourier.SummableWeighted (2 * Real.pi * ρ) (CertModel.residualCoeff n m f) ∧
    Fourier.weightedNorm (2 * Real.pi * ρ) (CertModel.residualCoeff n m f) ≤
      (2 * Real.pi) ^ m.deg * val m.rad

theorem CertModel.torusCoeff_eq (m : CertModel α) (f : (Fin n → ℂ) → ℂ) (k : Fin n → ℤ) :
    torusCoeff (fun x => f fun j => (x j : ℂ)) k =
      (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.coeff n k + CertModel.residualCoeff n m f k := by
  unfold CertModel.residualCoeff
  ring

theorem CertModel.EnclosesL1.rad_nonneg {ρ : ℝ} {m : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (h : CertModel.EnclosesL1 n ρ m f) : 0 ≤ val m.rad :=
  nonneg_of_mul_nonneg_right ((weightedNorm_nonneg _ _).trans h.2) (by positivity)

/-- The coefficients of an ℓ¹-enclosed function are summable at its radius. -/
theorem CertModel.EnclosesL1.summableWeighted {ρ : ℝ} {m : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (h : CertModel.EnclosesL1 n ρ m f) :
    Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => f fun j => (x j : ℂ)) := by
  have e : (torusCoeff fun x => f fun j => (x j : ℂ)) =
      fun k => (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.coeff n k + CertModel.residualCoeff n m f k :=
    funext (CertModel.torusCoeff_eq m f)
  rw [e]
  exact (summableWeighted_add
    (summableWeighted_const_mul _ (CertPoly.summableWeighted_coeff (n := n) _ m.poly)).1 h.1).1

/-- **ℓ¹ to sup.** An ℓ¹ enclosure is a sup enclosure on `T_ρ` of a function that is the Fourier
series of its coefficients there. -/
theorem CertModel.EnclosesL1.encloses {ρ : ℝ} {m : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (h : CertModel.EnclosesL1 n ρ m f)
    (hf : ∀ θ ∈ complexStrip n ρ,
      f θ = fourierSum (torusCoeff fun x => f fun j => (x j : ℂ)) θ) :
    m.Encloses n ρ f := by
  intro θ hθ
  have hP := CertPoly.summableWeighted_coeff (n := n) (2 * Real.pi * ρ) m.poly
  have hsP := summable_coeff_mul_character hP hθ
  have hsR := summable_coeff_mul_character h.1 hθ
  have e1 : (fun k => torusCoeff (fun x => f fun j => (x j : ℂ)) k * character k θ) =
      fun k => (2 * (Real.pi : ℂ)) ^ m.deg * (m.poly.coeff n k * character k θ) +
        CertModel.residualCoeff n m f k * character k θ := by
    funext k
    rw [CertModel.torusCoeff_eq m f k]
    ring
  have e : f θ - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n θ =
      fourierSum (CertModel.residualCoeff n m f) θ := by
    rw [hf θ hθ, CertPoly.eval_eq_fourierSum]
    simp only [fourierSum]
    rw [e1, Summable.tsum_add (hsP.mul_left _) hsR, tsum_mul_left]
    ring
  rw [e]
  exact (norm_fourierSum_le h.1 hθ).trans h.2

/-- **Sup to ℓ¹.** A sup enclosure of a holomorphic `1`-periodic `f` on `T_ρ` is an ℓ¹ enclosure
at `ρ − δ₁` by the same polynomial, with any radius `r ≥ C rad`, `C ≥ coth(πδ₁)^n`. -/
theorem CertModel.Encloses.toL1 [LawfulCertArith α] {ρ δ₁ : ℝ} (hδ : 0 < δ₁) (hδρ : δ₁ < ρ)
    {m : CertModel α} {f : (Fin n → ℂ) → ℂ} (hfd : DifferentiableOn ℂ f (complexStrip n ρ))
    (hfp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → f (z + Pi.single i 1) = f z)
    (h : m.Encloses n ρ f) {C : ℝ}
    (hC : (Real.cosh (Real.pi * δ₁) / Real.sinh (Real.pi * δ₁)) ^ n ≤ C) {r : α}
    (hr : C * val m.rad ≤ val r) :
    CertModel.EnclosesL1 n (ρ - δ₁) (⟨m.deg, m.poly, r⟩ : CertModel α) f := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hrad := CertModel.Encloses.rad_nonneg hρ h
  set c : ℂ := (2 * (Real.pi : ℂ)) ^ m.deg with hc
  set u : (Fin n → ℂ) → ℂ := fun θ => f θ - c * m.poly.eval n θ with hu
  have hud : DifferentiableOn ℂ u (complexStrip n ρ) :=
    hfd.sub ((m.poly.differentiable_eval n).const_mul _).differentiableOn
  have hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z :=
    fun i z hz => by simp only [hu, hfp i z hz, CertPoly.eval_add_single]
  obtain ⟨h1, h2⟩ := summableWeighted_torusCoeff hδ hδρ hud hup h
  have hcf : Continuous fun x : Fin n → ℝ => f fun j => (x j : ℂ) :=
    hfd.continuousOn.comp_continuous continuous_realPoint fun x => ofReal_mem_complexStrip hρ x
  have hcp : Continuous fun x : Fin n → ℝ => c * m.poly.eval n fun j => (x j : ℂ) :=
    continuous_const.mul ((m.poly.differentiable_eval n).continuous.comp continuous_realPoint)
  have hcoef : (torusCoeff fun x => u fun j => (x j : ℂ)) =
      CertModel.residualCoeff n (⟨m.deg, m.poly, r⟩ : CertModel α) f := by
    funext k
    have hP : (torusCoeff fun x : Fin n → ℝ => c * m.poly.eval n fun j => (x j : ℂ)) k =
        c * m.poly.coeff n k := by
      have e : (fun x : Fin n → ℝ => c * m.poly.eval n fun j => (x j : ℂ)) =
          fun x => fourierSum (fun k => c * m.poly.coeff n k) fun j => (x j : ℂ) :=
        funext fun x => CertPoly.const_mul_eval_eq_fourierSum c m.poly _
      rw [e, torusCoeff_fourierSum (ρ := 0) le_rfl
        (summableWeighted_const_mul c (CertPoly.summableWeighted_coeff (n := n) _ m.poly)).1 k]
    simp only [hu]
    rw [torusCoeff_sub hcf hcp k, hP]
    rfl
  rw [hcoef] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  show _ ≤ (2 * Real.pi) ^ m.deg * val r
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ m.deg := by positivity
  have hC0 : 0 ≤ C := (pow_nonneg (div_nonneg (Real.cosh_pos _).le
    (coth_le_one_add_inv (by positivity : 0 < Real.pi * δ₁)).2.le) n).trans hC
  calc (Real.cosh (Real.pi * δ₁) / Real.sinh (Real.pi * δ₁)) ^ n *
        ((2 * Real.pi) ^ m.deg * val m.rad)
      ≤ C * ((2 * Real.pi) ^ m.deg * val m.rad) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
    _ = (2 * Real.pi) ^ m.deg * (C * val m.rad) := by ring
    _ ≤ (2 * Real.pi) ^ m.deg * val r := mul_le_mul_of_nonneg_left hr h2pi.le

end Model

end KAM.CertificateSharp

end
