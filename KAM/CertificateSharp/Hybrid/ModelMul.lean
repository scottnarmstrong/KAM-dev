/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Torsion.Models
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Products of models for the certified first step (package C8c)

The hybrid checker multiplies the composed models of `DX_H ∘ K` and of `DH ∘ K` by the step `ΔK`,
and the derivative models of `K` and `K + ΔK` by each other (`Ω_K`, `Ω_{K₁}`). The sup arithmetic of
the certifier already has the product `CertModel.mul`, but it takes its polynomial product from the
advice book and falls back to the crude enclosure `sup|a| · sup|b|` when the advice is missing.

* `directCfg`, `CertModel.mulD`, `CertModel.Encloses.mulD`: the product with the direct polynomial
  product at the hybrid's key (no advice needed), and its soundness (`CertModel.Encloses.mul`);
* `dotModel`, `dotModel_encloses`: `∑_j a_j b_j` as one model. The partial products are summed by
  `modelSum`, whose additions merge the terms of equal key (`mergeErrTerms`) **before** any norm is
  taken, so a cancellation between the summands (the Newton cancellation in `Ẽ`) is kept;
* `realWeight`, `CertModel.norm_le_supBound_real`: the sup bound at real points with the weight
  `w = 1` (every character has modulus `1` there).
-/

@[expose] public section

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate CertArith

variable {α : Type} [CertArith α]

/-- The product key of the hybrid's products. -/
def hybKey : ProductKey := [8]

/-- The model configuration with the direct product at the hybrid's key. -/
def directCfg (cfg : ModelConfig α) : ModelConfig α :=
  { cfg with advice := (hybKey, ProductAdvice.direct) :: cfg.advice }

/-- The model product with the direct polynomial product (no advice needed). -/
def CertModel.mulD (W : CertWeight) (cfg : ModelConfig α) (a b : CertModel α) : CertModel α :=
  CertModel.mul W (directCfg cfg) hybKey a b

omit [CertArith α] in
/-- The advice at the hybrid's key is the direct product. -/
theorem adviceLookup_directCfg (cfg : ModelConfig α) :
    adviceLookup (directCfg cfg).advice hybKey = some ProductAdvice.direct := by
  simp [adviceLookup, directCfg]

/-- `∑_{j < c} a_j b_j` as one model (direct products, merged sums). -/
def dotModel (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (c : ℕ)
    (a b : ℕ → CertModel α) : CertModel α :=
  modelSum W pe (List.ofFn fun j : Fin c => CertModel.mulD W cfg (a j.val) (b j.val))

/-- The weight of the real torus: `w = 1`. -/
def realWeight : CertWeight := ⟨0, 1⟩

variable [LawfulCertArith α] {n : ℕ}

/-- Soundness of the direct product. -/
theorem CertModel.Encloses.mulD {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) {a b : CertModel α} {f g : (Fin n → ℂ) → ℂ}
    (ha : a.Encloses n W.rho f) (hb : b.Encloses n W.rho g) :
    (CertModel.mulD W cfg a b).Encloses n W.rho (f * g) :=
  CertModel.Encloses.mul hW (directCfg cfg) hybKey ha hb

/-- Soundness of `dotModel`. -/
theorem dotModel_encloses {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) (c : ℕ)
    {a b : ℕ → CertModel α} {fa fb : Fin c → (Fin n → ℂ) → ℂ}
    (ha : ∀ j : Fin c, (a j.val).Encloses n W.rho (fa j))
    (hb : ∀ j : Fin c, (b j.val).Encloses n W.rho (fb j)) :
    (dotModel W cfg pe c a b).Encloses n W.rho (fun θ => ∑ j, fa j θ * fb j θ) := by
  let L : EnclosedList α n := List.ofFn fun j : Fin c =>
    (CertModel.mulD W cfg (a j.val) (b j.val), fun θ => fa j θ * fb j θ)
  have hL : ∀ p ∈ L, p.1.Encloses n W.rho p.2 := by
    intro p hp
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hp
    exact CertModel.Encloses.mulD hW cfg (ha j) (hb j)
  have h := modelSum_encloses hW hpe L hL
  have hfst :
      L.map Prod.fst = List.ofFn fun j : Fin c => CertModel.mulD W cfg (a j.val) (b j.val) :=
    by simp only [L, List.map_ofFn]; rfl
  rw [hfst] at h
  refine h.of_eq_fun fun θ => ?_
  simp only [L, List.map_ofFn, List.sum_ofFn, Function.comp_def]

omit [LawfulCertArith α] in
theorem norm_character_real (k : Fin n → ℤ) (x : Fin n → ℝ) :
    ‖character k (fun i => (x i : ℂ))‖ = 1 := by
  rw [norm_character]
  simp

/-- The weighted norm at `w = 1` bounds a polynomial at real points. -/
theorem CertPoly.norm_eval_real_le (P : CertPoly α) (x : Fin n → ℝ) :
    ‖P.eval n (fun i => (x i : ℂ))‖ ≤ val (P.weightedNormUp realWeight) := by
  have hterm : ∀ t : CertKey × CC α, ‖t.2.toC * character (certKeyFun n t.1) (fun i => (x i : ℂ))‖ ≤
      val (upMul t.2.normUp (ofRatUp (realWeight.w ^ (t.1.map Int.natAbs).sum)) : α) := by
    intro t
    have hn := CC.normUp_nonneg t.2
    have h1 : ((realWeight.w ^ (t.1.map Int.natAbs).sum : ℚ) : ℝ) = 1 := by
      simp [realWeight]
    have hr := LawfulCertArith.ofRatUp_ge (α := α) (realWeight.w ^ (t.1.map Int.natAbs).sum)
    rw [h1] at hr
    calc ‖t.2.toC * character (certKeyFun n t.1) (fun i => (x i : ℂ))‖
        = ‖t.2.toC‖ := by rw [norm_mul, norm_character_real, mul_one]
      _ ≤ val t.2.normUp := CC.norm_le_normUp t.2
      _ = val t.2.normUp * 1 := (mul_one _).symm
      _ ≤ val t.2.normUp * val (ofRatUp (realWeight.w ^ (t.1.map Int.natAbs).sum) : α) :=
          mul_le_mul_of_nonneg_left hr hn
      _ ≤ val (upMul t.2.normUp (ofRatUp (realWeight.w ^ (t.1.map Int.natAbs).sum)) : α) :=
          LawfulCertArith.upMul_ge _ _ hn (zero_le_one.trans hr)
  unfold CertPoly.weightedNormUp
  refine le_trans ?_ (sumUp_ge _ _)
  unfold CertPoly.eval
  induction P.terms with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (hterm t) ih)

/-- **The sup bound at real points**, with the weight `w = 1`. -/
theorem CertModel.norm_le_supBound_real {ρ : ℝ} (hρ : 0 < ρ) {m : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (hm : m.Encloses n ρ f) (x : Fin n → ℝ) :
    ‖f (fun i => (x i : ℂ))‖ ≤ val (m.supBound realWeight) := by
  have hx : (fun i => (x i : ℂ)) ∈ complexStrip n ρ := ofReal_mem_complexStrip hρ x
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ m.deg := by positivity
  have hrad : 0 ≤ val m.rad := CertModel.Encloses.rad_nonneg hρ hm
  have hP := CertPoly.norm_eval_real_le m.poly x
  have hS0 : 0 ≤ val (m.poly.weightedNormUp realWeight) := (norm_nonneg _).trans hP
  have hadd := LawfulCertArith.upAdd_ge (m.poly.weightedNormUp realWeight) m.rad
  have hF : (0 : ℝ) ≤ (degFactorUp m.deg : ℝ) := h2pi.le.trans (two_pi_zpow_le _)
  have hF' := LawfulCertArith.ofRatUp_ge (α := α) (degFactorUp m.deg)
  have hmul := LawfulCertArith.upMul_ge (ofRatUp (degFactorUp m.deg))
    (upAdd (m.poly.weightedNormUp realWeight) m.rad) (hF.trans hF') (by linarith)
  have hX : ‖(2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n (fun i => (x i : ℂ))‖ ≤
      (2 * Real.pi) ^ m.deg * val (m.poly.weightedNormUp realWeight) := by
    rw [norm_mul, norm_two_pi_zpow]
    exact mul_le_mul_of_nonneg_left hP h2pi.le
  have hsub := hm _ hx
  have hle : ‖f (fun i => (x i : ℂ))‖ ≤
      ‖f (fun i => (x i : ℂ)) - (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n (fun i => (x i : ℂ))‖ +
        ‖(2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n (fun i => (x i : ℂ))‖ := by
    simpa using norm_add_le (f (fun i => (x i : ℂ)) -
      (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n (fun i => (x i : ℂ)))
      ((2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n (fun i => (x i : ℂ)))
  calc ‖f (fun i => (x i : ℂ))‖
      ≤ (2 * Real.pi) ^ m.deg * (val (m.poly.weightedNormUp realWeight) + val m.rad) := by
        nlinarith
    _ ≤ (degFactorUp m.deg : ℝ) * val (upAdd (m.poly.weightedNormUp realWeight) m.rad) :=
        mul_le_mul (two_pi_zpow_le _) hadd (by linarith) hF
    _ ≤ val (ofRatUp (degFactorUp m.deg) : α) *
          val (upAdd (m.poly.weightedNormUp realWeight) m.rad) :=
        mul_le_mul_of_nonneg_right hF' (by linarith)
    _ ≤ val (m.supBound realWeight) := hmul

end KAM.CertificateSharp.Hybrid

end
