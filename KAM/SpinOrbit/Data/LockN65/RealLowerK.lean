/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Positivity

/-!
# Real lower bounds with a product key (lock-owned)

`checkRealLowerBoundK W cfg key f m₀ m g` is the landed `checkRealLowerBound`
(`KAM/Certificate/Positivity.lean`) with the product key of the square `g g*` as a parameter in
place of `[7]`: the square is looked up under `key` in `cfg.advice ++ [(key, .direct)]`. The landed
check uses one key for every SOS square of a certificate, so a packed advice can serve only one of
them; with a key per square each gets its own advice (SOS option (a), additive form: core and the
band are untouched). The soundness proof is the landed one with `key` for `[7]`: it uses only the
enclosure of `CertModel.mul`, which holds for every key and every advice.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate CertArith

section Defs

variable {α : Type} [CertArith α]

/-- The model of `(f + f*) - 2 g g* - 2 m₀`, the square under the key `key`. -/
def realLowerModelK (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey) (f : CertModel α)
    (m₀ : ℚ) (g : CertPoly α) : CertModel α :=
  let cfg' : ModelConfig α :=
    { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] }
  let gg := CertModel.mul W cfg' key ⟨0, g, ofInt 0⟩ ⟨0, g.conjSorted, ofInt 0⟩
  let G := CertModel.mul W cfg' key gg (CertModel.ofConst g.keyLen (ofInt (-2)) (ofInt 0))
  let c : α := ofRatUp (-2 * m₀)
  let len := if f.poly.terms.isEmpty then g.keyLen else f.poly.keyLen
  CertModel.add W (CertModel.add W (CertModel.add W f f.starModel) G)
    (CertModel.ofConst len c (upAdd c (neg (ofRatDown (-2 * m₀)))))

end Defs

/-- The sum-of-squares lower bound with the square under the key `key`. -/
def checkRealLowerBoundK {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig α)
    (key : ProductKey) (f : CertModel α) (m₀ m : ℚ) (g : CertPoly α) : Bool :=
  decide (f.deg = 0) &&
    ble ((realLowerModelK W cfg key f m₀ g).supBound W) (ofRatDown (2 * (m₀ - m)))

/-- An advice lookup is unchanged by appending entries after a book in which the key is found. -/
theorem adviceLookup_append_of_isSome (A X : AdviceBook) (key : ProductKey)
    (h : (adviceLookup A key).isSome = true) : adviceLookup (A ++ X) key = adviceLookup A key := by
  unfold adviceLookup at h ⊢
  cases hf : A.find? (fun e => e.1 == key) with
  | none => simp [hf] at h
  | some e => simp [List.find?_append, hf]

/-- The square of `realLowerModelK` is the product of the certificate's own configuration when its
key has advice there (the appended `.direct` entry is never reached). -/
theorem polyProduct_append_of_isSome {α : Type} [CertArith α] (W : CertWeight)
    (cfg : ModelConfig α) (key : ProductKey) (X : AdviceBook) (a b : CertPoly α)
    (h : (adviceLookup cfg.advice key).isSome = true) :
    CertModel.polyProduct W { cfg with advice := cfg.advice ++ X } key a b =
      CertModel.polyProduct W cfg key a b := by
  unfold CertModel.polyProduct
  simp only [adviceLookup_append_of_isSome cfg.advice X key h]

theorem checkRealLowerBoundK_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    (key : ProductKey)
    {f : CertModel α} {ff : (Fin n → ℂ) → ℂ} (hf : f.Encloses n W.rho ff) {m₀ m : ℚ}
    {g : CertPoly α} (h : checkRealLowerBoundK W cfg key f m₀ m g = true) (x : Fin n → ℝ) :
    (m : ℝ) ≤ (ff fun i => (x i : ℂ)).re := by
  simp only [checkRealLowerBoundK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hdeg, hb⟩ := h
  set cfg' : ModelConfig α :=
    { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] }
  have hg := CertModel.Encloses.ofPoly (n := n) (ρ := W.rho) g (F := g.eval n) fun _ => rfl
  have hgs := CertModel.Encloses.ofPoly (n := n) (ρ := W.rho) g.conjSorted
    (F := g.conjReflect.eval n) (CertPoly.eval_conjSorted n g)
  have hgg := CertModel.Encloses.mul hW cfg' key hg hgs
  have hc2 := CertModel.Encloses.ofConst (n := n) (ρ := W.rho) (len := g.keyLen)
    (u := (ofInt (-2) : α)) (r := ofInt 0) (z := -2) (by simp [LawfulCertArith.val_ofInt])
  have hG := CertModel.Encloses.mul hW cfg' key hgg hc2
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

end KAM.SpinOrbit.Data.LockN65
