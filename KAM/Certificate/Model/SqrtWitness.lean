/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.ComposeModels
public import KAM.Certificate.Expr.Sqrt

/-!
# Square-root witnesses

The witness for `√g` of a degree-zero model `g` is a polynomial `W ≈ √g` with a positive rational
anchor `s` and margin `d`. The checker `sqrtWitnessRadius` verifies, with the outward-rounded
model arithmetic and uniform sup bounds on the strip (`CertModel.supBound`):

1. `0 ≤ d < s`;
2. `sup |W - s| ≤ d`, so `re W ≥ s - d > 0`: `W` is on the side of the principal root;
3. `sup |g - s²| < s²`, so `re g > 0` on the strip;
4. `ε ≥ sup |g - W²|`,

and returns the radius `ε · (1/(s - d))↑`. Soundness (`sqrtWitness_sound`) is the pointwise rule
`sqrtE_model_error`: `|√g - W| = |g - W²| / |√g + W| ≤ ε/(s - d)`, because `re √g ≥ 0` and
`re W ≥ s - d`. The products `W · W` use the product site `3` of the witness configuration
(`ModelConfig.forWitness 3 i`, key `[3]`); the scalar product by `-1` takes the scalar route.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-- The composition witness for `√g` (analogue of `ExpWitness`): the model polynomial `W`, the
rational anchor `s > 0` and margin `d < s`. -/
structure SqrtWitness (α : Type) where
  poly : CertPoly α
  anchor : ℚ
  margin : ℚ

section Defs

variable {α : Type} [CertArith α]

/-- The exact model of a witness polynomial. -/
def SqrtWitness.model (S : SqrtWitness α) : CertModel α := ⟨0, S.poly, ofInt 0⟩

/-- The model of `W - s`. -/
def sqrtAnchorDiff (n : ℕ) (W : CertWeight) (S : SqrtWitness α) : CertModel α :=
  CertModel.add W S.model (constModel n (-S.anchor) 0 0)

/-- The model of `g - s²`. -/
def sqrtRadicandDiff (n : ℕ) (W : CertWeight) (g : CertModel α) (S : SqrtWitness α) :
    CertModel α :=
  CertModel.add W g (constModel n (-(S.anchor * S.anchor)) 0 0)

/-- The model of the residual `g - W²`. -/
def sqrtResidual (n : ℕ) (W : CertWeight) (cfg : ModelConfig α) (g : CertModel α)
    (S : SqrtWitness α) : CertModel α :=
  CertModel.add W g (CertModel.mul W cfg [3] (constModel n (-1) 0 0)
    (CertModel.mul W cfg [3] S.model S.model))

/-- The checker: `0 ≤ d < s`, `sup |W - s| ≤ d`, `sup |g - s²| < s²`; returns the radius
`sup |g - W²| · (1/(s - d))↑` (`none` if a check fails). -/
def sqrtWitnessRadius (n : ℕ) (W : CertWeight) (cfg : ModelConfig α) (g : CertModel α)
    (S : SqrtWitness α) : Option α :=
  if decide (0 ≤ S.margin ∧ S.margin < S.anchor) &&
      ble ((sqrtAnchorDiff n W S).supBound W) (ofRatDown S.margin) &&
      blt ((sqrtRadicandDiff n W g S).supBound W) (ofRatDown (S.anchor * S.anchor)) then
    some (upMul ((sqrtResidual n W cfg g S).supBound W) (ofRatUp (1 / (S.anchor - S.margin))))
  else none

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α]

theorem slpConstVal_neg_rat (q : ℚ) : slpConstVal (-q) 0 0 = -((q : ℝ) : ℂ) := by
  simp [slpConstVal]

theorem SqrtWitness.model_encloses (n : ℕ) (ρ : ℝ) (S : SqrtWitness α) :
    S.model.Encloses n ρ (S.poly.eval n) := by
  intro θ _
  simp [SqrtWitness.model, LawfulCertArith.val_ofInt]

theorem sqrtWitness_sound {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {g : CertModel α} {gf : (Fin n → ℂ) → ℂ} (hg : g.Encloses n W.rho gf) (hdeg : g.deg = 0)
    {S : SqrtWitness α} {r : α} (hS : sqrtWitnessRadius n W cfg g S = some r) :
    (∀ θ ∈ complexStrip n W.rho, 0 < (gf θ).re) ∧
      (⟨0, S.poly, r⟩ : CertModel α).Encloses n W.rho (fun θ => sqrtE (gf θ)) := by
  unfold sqrtWitnessRadius at hS
  split_ifs at hS with hc
  simp only [Option.some.injEq] at hS
  subst hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hd0, hds⟩, hb1⟩, hb2⟩ := hc
  set sq := S.anchor
  set d := S.margin
  have hb1' := LawfulCertArith.ble_sound _ _ hb1
  have hb2' := LawfulCertArith.blt_sound _ _ hb2
  have hd1 := LawfulCertArith.ofRatDown_le (α := α) d
  have hd2 := LawfulCertArith.ofRatDown_le (α := α) (sq * sq)
  have hP := S.model_encloses n W.rho
  -- the three model enclosures
  have hA : (sqrtAnchorDiff n W S).Encloses n W.rho
      (S.poly.eval n + fun _ => slpConstVal (-sq) 0 0) :=
    CertModel.Encloses.add hW hP (constModel_encloses (α := α) n W.rho (-sq) 0 0) rfl
  have hB : (sqrtRadicandDiff n W g S).Encloses n W.rho
      (gf + fun _ => slpConstVal (-(sq * sq)) 0 0) :=
    CertModel.Encloses.add hW hg (constModel_encloses (α := α) n W.rho (-(sq * sq)) 0 0)
      (by rw [hdeg]; rfl)
  have hsq := CertModel.Encloses.mul hW cfg [3] hP hP
  have hC : (sqrtResidual n W cfg g S).Encloses n W.rho
      (gf + (fun _ => slpConstVal (-1) 0 0) * (S.poly.eval n * S.poly.eval n)) :=
    CertModel.Encloses.add hW hg
      (CertModel.Encloses.mul hW cfg [3] (constModel_encloses (α := α) n W.rho (-1) 0 0) hsq)
      (by rw [hdeg, CertModel.mul_deg, CertModel.mul_deg]; rfl)
  have hs0 : (0 : ℝ) < sq := by exact_mod_cast hd0.trans_lt hds
  have hd0' : (0 : ℝ) ≤ d := by exact_mod_cast hd0
  have hds' : (d : ℝ) < sq := by exact_mod_cast hds
  have hpos : ∀ θ ∈ complexStrip n W.rho, 0 < (gf θ).re := by
    intro θ hθ
    have h := CertModel.norm_le_supBound hW hB hθ
    have e : ((gf + fun _ => slpConstVal (-(sq * sq)) 0 0 : (Fin n → ℂ) → ℂ)) θ =
        gf θ - ((sq : ℝ) : ℂ) ^ 2 := by
      simp only [Pi.add_apply, slpConstVal_neg_rat]
      push_cast
      ring
    rw [e] at h
    have hd2' : ((sq * sq : ℚ) : ℝ) = (sq : ℝ) ^ 2 := by push_cast; ring
    have h' : ‖gf θ - ((sq : ℝ) : ℂ) ^ 2‖ < (sq : ℝ) ^ 2 := by linarith
    have h2 := (Complex.abs_re_le_norm _).trans_lt h'
    have e2 : (gf θ - ((sq : ℝ) : ℂ) ^ 2).re = (gf θ).re - (sq : ℝ) ^ 2 := by
      rw [Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [e2] at h2
    linarith [neg_abs_le ((gf θ).re - (sq : ℝ) ^ 2)]
  refine ⟨hpos, fun θ hθ => ?_⟩
  have hWs : ‖S.poly.eval n θ - ((sq : ℝ) : ℂ)‖ ≤ d := by
    have h := CertModel.norm_le_supBound hW hA hθ
    have e : ((S.poly.eval n + fun _ => slpConstVal (-sq) 0 0 : (Fin n → ℂ) → ℂ)) θ =
        S.poly.eval n θ - ((sq : ℝ) : ℂ) := by
      simp only [Pi.add_apply, slpConstVal_neg_rat]
      ring
    rw [e] at h
    linarith
  have hres : ‖gf θ - S.poly.eval n θ ^ 2‖ ≤
      val ((sqrtResidual n W cfg g S).supBound W) := by
    have h := CertModel.norm_le_supBound hW hC hθ
    have e : ((gf + (fun _ => slpConstVal (-1) 0 0) * (S.poly.eval n * S.poly.eval n) :
        (Fin n → ℂ) → ℂ)) θ =
        gf θ - S.poly.eval n θ ^ 2 := by
      simp only [Pi.add_apply, Pi.mul_apply, slpConstVal_neg_rat]
      push_cast
      ring
    rwa [e] at h
  have hm := sqrtE_model_error hs0 hd0' hds' (hpos θ hθ) hWs hres
  have hε0 : 0 ≤ val ((sqrtResidual n W cfg g S).supBound W) := (norm_nonneg _).trans hres
  have hq := LawfulCertArith.ofRatUp_ge (α := α) (1 / (sq - d))
  have hq0 : (0 : ℝ) ≤ val (ofRatUp (α := α) (1 / (sq - d))) := by
    refine le_trans ?_ hq
    have : (0 : ℚ) ≤ 1 / (sq - d) := by
      have : (0 : ℚ) < sq - d := by linarith
      positivity
    exact_mod_cast this
  have hu := LawfulCertArith.upMul_ge _ _ hε0 hq0
  simp only [zpow_zero, one_mul]
  refine hm.trans (le_trans ?_ hu)
  rw [div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ hε0
  have e : ((1 / (sq - d) : ℚ) : ℝ) = 1 / ((sq : ℝ) - d) := by push_cast; ring
  rw [← e]
  exact hq

end Sound

end KAM.Certificate

end
