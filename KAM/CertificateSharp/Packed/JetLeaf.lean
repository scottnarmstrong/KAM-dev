/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetNode

/-!
# Leaf nodes of the packed jet: landed models packed at degree `0`

A leaf node of the packed jet (a constant, an action, a character, a witness output) comes from a
landed `CertModel` enclosing its slot function. `jLeaf` brings it to degree `0` through the `π`
enclosure (the landed `CertModel.toDeg`), drops the terms outside the node's layout into the radius
at their weighted size (`jBoxTrunc`, as the landed `CertModel.trim` does by size), and packs the
mantissas (`toMants`, `packOf`) with the norm bound `pnorm`. Everything is computed in the kernel;
`jLeaf_sound` turns the landed enclosure into the node's packed model.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

section Defs

variable {α : Type} [CertArith α] (W : CertWeight) (pe : PiEnclosure α) (cfg : ModelConfig α)
  (jb : JBook)

/-- The terms with a slot on `L` kept, the others dropped into the radius. -/
def jBoxTrunc (L : PackLayout) (a : CertModel α) : CertModel α :=
  ⟨a.deg, ⟨a.poly.terms.filter fun t => (L.slot t.1).isSome⟩,
    upAdd a.rad (CertPoly.supNormUp W ⟨a.poly.terms.filter fun t => !(L.slot t.1).isSome⟩)⟩

/-- **The leaf node** of a landed model, on `LU0` (`u`) or on the box, at the scale `2^P`. -/
def jLeaf (u : Bool) (A : ℕ) (m : CertModel α) : Option (JNode α) :=
  match (jBoxTrunc W (jLay jb u) (CertModel.toDeg W pe 0 m)).poly.toMants cfg.toMant jb.P with
  | some (re, im) =>
    if (if u then decide (A ≤ jb.aC) else decide (A ≤ 2 ^ jb.lb)) &&
        packRepOk (jLay jb u) re A && packRepOk (jLay jb u) im A then
      some ⟨u, A, jb.P, ⟨packOf (jLay jb u) re, packOf (jLay jb u) im⟩,
        (jBoxTrunc W (jLay jb u) (CertModel.toDeg W pe 0 m)).rad,
        pnorm W jb.q (if u then jb.lc else jb.ln) (jLay jb u) jb.P
          ⟨packOf (jLay jb u) re, packOf (jLay jb u) im⟩⟩
    else none
  | none => none

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight}
  {pe : PiEnclosure α} {cfg : ModelConfig α} {jb : JBook}

/-- The box truncation keeps the enclosure (the dropped terms at their sup bound). -/
theorem jBoxTrunc_encloses {s N : ℕ} (hW : checkWeight W s N = true) (L : PackLayout)
    {a : CertModel α} {f : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f) :
    (jBoxTrunc W L a).Encloses n W.rho f := by
  intro θ hθ
  have hA := ha θ hθ
  have hsplit := CertPoly.eval_filter_add n a.poly (fun t => (L.slot t.1).isSome) θ
  have hD := (⟨a.poly.terms.filter fun t => !(L.slot t.1).isSome⟩ :
    CertPoly α).norm_eval_le_supNormUp hW hθ
  have u := LawfulCertArith.upAdd_ge a.rad
    (CertPoly.supNormUp W ⟨a.poly.terms.filter fun t => !(L.slot t.1).isSome⟩)
  have hc : (0 : ℝ) < (2 * Real.pi) ^ a.deg := by positivity
  simp only [jBoxTrunc]
  rw [hsplit] at hA
  set C := (2 * (Real.pi : ℂ)) ^ a.deg
  set Kp := (⟨a.poly.terms.filter fun t => (L.slot t.1).isSome⟩ : CertPoly α).eval n θ
  set Dr := (⟨a.poly.terms.filter fun t => !(L.slot t.1).isSome⟩ : CertPoly α).eval n θ
  have : f θ - C * Kp = (f θ - C * (Kp + Dr)) + C * Dr := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_two_pi_zpow]
  have := mul_le_mul_of_nonneg_left hD hc.le
  nlinarith

/-- **A leaf node encloses the function of its landed model.** -/
theorem jLeaf_sound {s N : ℕ} (hW : checkWeight W s N = true) (hpe : checkPiEnclosure pe = true)
    (B : JBookFacts n W jb) {u : Bool} {A : ℕ} {m : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (hm : m.Encloses n W.rho f) {nd : JNode α} (h : jLeaf W pe cfg jb u A m = some nd) :
    JEnc n W jb nd f := by
  have h1 := jBoxTrunc_encloses hW (jLay jb u) (hm.toDeg hW hpe 0)
  have hd : (jBoxTrunc W (jLay jb u) (CertModel.toDeg W pe 0 m)).deg = 0 := by
    simp [jBoxTrunc, toDeg_deg]
  unfold jLeaf at h
  generalize hT : (jBoxTrunc W (jLay jb u) (CertModel.toDeg W pe 0 m)).poly.toMants cfg.toMant
    jb.P = T at h
  rcases T with _ | ⟨re, im⟩
  · cases h
  · simp only at h
    by_cases hc : ((if u then decide (A ≤ jb.aC) else decide (A ≤ 2 ^ jb.lb)) &&
        packRepOk (jLay jb u) re A && packRepOk (jLay jb u) im A) = true
    · simp only [hc, ↓reduceIte] at h
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hA, hpr⟩, hpi⟩ := hc
      have hw : layoutWf (jLay jb u) = true := by cases u <;> simp [jLay, B.wb, B.w0]
      have hok : normOk W jb.q (if u then jb.lc else jb.ln) A (jLay jb u) = true := by
        cases u
        · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hA ⊢
          exact normOk_mono B.nN hA
        · simp only [↓reduceIte, decide_eq_true_eq] at hA ⊢
          exact normOk_mono B.nC hA
      exact PEnc.ofPCRep hW hok (PCRep.ofMants hT hw hpr hpi) fun θ hθ =>
        encloses_deg0 h1 hd hθ
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      cases h

end Sound

end KAM.CertificateSharp.Packed
