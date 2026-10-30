/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Ops

/-!
# Certified real lower bounds of models

`checkRealLowerBound` certifies `m ≤ Re f` on the real torus for an enclosed `f` of degree `0`.
With `f* (θ) = conj (f (conj θ))` and `g* = conjReflect g`, the check forms the model of
`2 (Re f - m₀ - g g*) = (f + f*) - 2 g g* - 2 m₀` from the model algebra (`add`, `mul`), bounds its
strip sup by `supBound`, and requires that bound to be at most `2 (m₀ - m)`. On the real torus
`g g* = |g|² ≥ 0`, so `Re f ≥ m₀ - r/2 ≥ m`. The product `g g*` uses the advice registered at the
SOS site key `[7]` and falls back to the direct product when none is registered; a missing or
failing advice only makes the model cruder, never unsound.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

section Defs

variable {α : Type} [CertArith α]

/-- The conjugate reflection with its terms reversed: negating keys reverses the lexicographic
order, so for sorted input the output is sorted again (the merges of `Model/Ops` are complete on
sorted keys). -/
def CertPoly.conjSorted (P : CertPoly α) : CertPoly α := ⟨P.conjReflect.terms.reverse⟩

/-- The model of the conjugate reflection `θ ↦ conj (f (conj θ))`: the polynomial is reflected,
the degree and the radius are unchanged. -/
def CertModel.starModel (m : CertModel α) : CertModel α := ⟨m.deg, m.poly.conjSorted, m.rad⟩

/-- The constant model with centre `u` and radius `r` (degree `0`), stored under the zero key of
length `len` (so that it merges with the constant term of a polynomial whose keys have length
`len`). -/
def CertModel.ofConst (len : ℕ) (u r : α) : CertModel α :=
  ⟨0, ⟨[(List.replicate len 0, ⟨u, ofInt 0⟩)]⟩, r⟩

/-- The key length of the first term of a polynomial (`0` for the empty polynomial). -/
def CertPoly.keyLen (P : CertPoly α) : ℕ := (P.terms.headD ([], ⟨ofInt 0, ofInt 0⟩)).1.length

/-- The model of `(f + f*) - 2 g g* - 2 m₀` (degree `0` when `f` has degree `0`). -/
def CertModel.realLowerModel (W : CertWeight) (cfg : ModelConfig α) (f : CertModel α)
    (m₀ : ℚ) (g : CertPoly α) : CertModel α :=
  let cfg' : ModelConfig α := { cfg with advice := cfg.advice ++ [([7], ProductAdvice.direct)] }
  let gg := CertModel.mul W cfg' [7] ⟨0, g, ofInt 0⟩ ⟨0, g.conjSorted, ofInt 0⟩
  let G := CertModel.mul W cfg' [7] gg (CertModel.ofConst g.keyLen (ofInt (-2)) (ofInt 0))
  let c : α := ofRatUp (-2 * m₀)
  let len := if f.poly.terms.isEmpty then g.keyLen else f.poly.keyLen
  CertModel.add W (CertModel.add W (CertModel.add W f f.starModel) G)
    (CertModel.ofConst len c (upAdd c (neg (ofRatDown (-2 * m₀)))))

end Defs

/-- Sum-of-squares lower bound on the real torus. The check forms the model of
`Re-part f - m₀ - g g*` (`g* = conjReflect g`), bounds its sup by `r`, and requires
`m ≤ m₀ - r` (the residual is PAID; a small `r` without that slack is rejected). -/
def checkRealLowerBound {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig α)
    (f : CertModel α) (m₀ m : ℚ) (g : CertPoly α) : Bool :=
  decide (f.deg = 0) &&
    ble ((CertModel.realLowerModel W cfg f m₀ g).supBound W) (ofRatDown (2 * (m₀ - m)))

section Lemmas

variable {α : Type} [CertArith α] [LawfulCertArith α]

omit [LawfulCertArith α] in
theorem CertPoly.eval_conjSorted (n : ℕ) (P : CertPoly α) (θ : Fin n → ℂ) :
    P.conjSorted.eval n θ = P.conjReflect.eval n θ := by
  simp [CertPoly.eval, CertPoly.conjSorted, List.map_reverse, List.sum_reverse]

theorem CertModel.Encloses.starModel {n : ℕ} {ρ : ℝ} {m : CertModel α} {ff : (Fin n → ℂ) → ℂ}
    (h : m.Encloses n ρ ff) :
    (CertModel.starModel m).Encloses n ρ
      fun θ => (starRingEnd ℂ) (ff fun i => (starRingEnd ℂ) (θ i)) := by
  intro θ hθ
  have hθ' : (fun i => (starRingEnd ℂ) (θ i)) ∈ complexStrip n ρ := fun i => by
    simpa using hθ i
  have := h _ hθ'
  simp only [CertModel.starModel, CertPoly.eval_conjSorted, CertPoly.eval_conjReflect]
  have e : (starRingEnd ℂ) (ff fun i => (starRingEnd ℂ) (θ i)) -
      (2 * (Real.pi : ℂ)) ^ m.deg * (starRingEnd ℂ) (m.poly.eval n fun i => (starRingEnd ℂ) (θ i))
      = (starRingEnd ℂ) (ff (fun i => (starRingEnd ℂ) (θ i)) -
        (2 * (Real.pi : ℂ)) ^ m.deg * m.poly.eval n fun i => (starRingEnd ℂ) (θ i)) := by
    have hC : (starRingEnd ℂ) ((2 * (Real.pi : ℂ)) ^ m.deg) = (2 * (Real.pi : ℂ)) ^ m.deg := by
      rw [map_zpow₀, map_mul, map_ofNat, Complex.conj_ofReal]
    rw [map_sub, map_mul, hC]
  rw [e, Complex.norm_conj]
  exact this

theorem certKeyFun_replicate (n len : ℕ) : certKeyFun n (List.replicate len 0) = 0 := by
  funext i
  simp [certKeyFun, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

theorem CertModel.Encloses.ofConst {n : ℕ} {ρ : ℝ} {len : ℕ} {u r : α} {z : ℝ}
    (h : |z - val u| ≤ val r) : (CertModel.ofConst len u r).Encloses n ρ fun _ => (z : ℂ) := by
  intro θ _
  simp only [CertModel.ofConst, CertPoly.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, certKeyFun_replicate, character_zero, zpow_zero, one_mul, add_zero]
  have : (z : ℂ) - (CC.toC ⟨u, ofInt 0⟩ : ℂ) = ((z - val u : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [CC.toC, LawfulCertArith.val_ofInt]
  rw [mul_one, this, Complex.norm_real, Real.norm_eq_abs]
  exact h

theorem CertModel.Encloses.ofPoly {n : ℕ} {ρ : ℝ} (g : CertPoly α) {F : (Fin n → ℂ) → ℂ}
    (hF : ∀ θ, g.eval n θ = F θ) : (⟨0, g, ofInt 0⟩ : CertModel α).Encloses n ρ F := by
  intro θ _
  simp [LawfulCertArith.val_ofInt, hF]

end Lemmas

theorem checkRealLowerBound_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {f : CertModel α} {ff : (Fin n → ℂ) → ℂ} (hf : f.Encloses n W.rho ff) {m₀ m : ℚ}
    {g : CertPoly α} (h : checkRealLowerBound W cfg f m₀ m g = true) (x : Fin n → ℝ) :
    (m : ℝ) ≤ (ff fun i => (x i : ℂ)).re := by
  simp only [checkRealLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hdeg, hb⟩ := h
  set cfg' : ModelConfig α := { cfg with advice := cfg.advice ++ [([7], ProductAdvice.direct)] }
  have hg := CertModel.Encloses.ofPoly (n := n) (ρ := W.rho) g (F := g.eval n) fun _ => rfl
  have hgs := CertModel.Encloses.ofPoly (n := n) (ρ := W.rho) g.conjSorted
    (F := g.conjReflect.eval n) (CertPoly.eval_conjSorted n g)
  have hgg := CertModel.Encloses.mul hW cfg' [7] hg hgs
  have hc2 := CertModel.Encloses.ofConst (n := n) (ρ := W.rho) (len := g.keyLen)
    (u := (ofInt (-2) : α)) (r := ofInt 0) (z := -2) (by simp [LawfulCertArith.val_ofInt])
  have hG := CertModel.Encloses.mul hW cfg' [7] hgg hc2
  have hS := CertModel.Encloses.add hW hf hf.starModel rfl
  have hc : |((-2 * m₀ : ℚ) : ℝ) - val (ofRatUp (-2 * m₀) : α)| ≤
      val (upAdd (ofRatUp (-2 * m₀) : α) (neg (ofRatDown (-2 * m₀)))) := by
    have h1 := LawfulCertArith.ofRatUp_ge (α := α) (-2 * m₀)
    have h2 := LawfulCertArith.ofRatDown_le (α := α) (-2 * m₀)
    have h3 := LawfulCertArith.upAdd_ge (ofRatUp (-2 * m₀) : α) (neg (ofRatDown (-2 * m₀)))
    rw [LawfulCertArith.val_neg] at h3
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hK := CertModel.Encloses.ofConst (n := n) (ρ := W.rho)
    (len := if f.poly.terms.isEmpty then g.keyLen else f.poly.keyLen) hc
  have hSG := CertModel.Encloses.add hW hS hG (by
    simp [CertModel.add, CertModel.mul_deg, CertModel.ofConst, hdeg, CertModel.starModel])
  have hH := CertModel.Encloses.add hW hSG hK (by
    simp [CertModel.add, CertModel.ofConst, hdeg, CertModel.starModel])
  have hx : (fun i => (x i : ℂ)) ∈ complexStrip n W.rho := ofReal_mem_complexStrip
    (CertWeight.rho_pos hW) x
  have hn := CertModel.norm_le_supBound hW hH hx
  have hq := LawfulCertArith.ble_sound _ _ hb
  have hq2 := LawfulCertArith.ofRatDown_le (α := α) (2 * (m₀ - m))
  have hre := (Complex.abs_re_le_norm _).trans (hn.trans (hq.trans hq2))
  have hconj : (fun i => (starRingEnd ℂ) ((x i : ℂ))) = fun i => (x i : ℂ) := by
    funext i; exact Complex.conj_ofReal _
  simp only [Pi.add_apply, Pi.mul_apply, CertPoly.eval_conjReflect, hconj] at hre
  generalize (ff fun i => (x i : ℂ)) = a at hre ⊢
  generalize CertPoly.eval n g (fun i => (x i : ℂ)) = b at hre
  rw [Complex.mul_conj] at hre
  have h2 := Complex.normSq_nonneg b
  have h3 := (abs_le.mp hre).1
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.ofReal_ratCast, Complex.ofReal_neg, Complex.ofReal_ofNat] at h3
  push_cast at h3
  have : (-2 : ℝ) * ((m₀ : ℝ)) = -2 * m₀ := rfl
  simp at h3
  nlinarith [h3, h2]

end KAM.Certificate
