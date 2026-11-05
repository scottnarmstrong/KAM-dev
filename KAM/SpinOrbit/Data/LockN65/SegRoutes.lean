/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.ProductSplit
public import KAM.CertificateSharp.Kernel.SegOne

/-!
# Memo routes for the exp, inv and sqrt arms of the composition (LOCK-DATA, B1)

SO-CSPLIT's product split (`ProductSplit`, `SegOne`) memoizes the `mul` and `char` arms of
`composeStep`. The lock program also has `exp`, `inv` and `sqrt` slots, whose witness checks each
carry one or two packed products. This module gives the matching equation lemmas, so a one-op
segment at such a slot is proved from its memoized products (each its own kernel run) and a few
cheap scalar facts:

* `composeStep_exp_eq`, `composeStep_inv_eq`, `composeStep_sqrt_eq`: the arms of the landed step
  with their witness radius memoized;
* the exp radius reuses `expWitnessRadius_eq_of_pin`, `expWitnessRadiusOf_eq_of_residuals` and
  `expResidualProduct_eq_of_polyProduct` unchanged;
* `invWitnessRadius_eq_of_delta`: the inverse radius from its `δ` and reciprocal bound;
* `sqrtWitnessRadius_eq_of_residual`: the square-root radius from its three checks and residual;
* `CertModel.mul_eq_of_polyProduct`: the landed `mul` with its polynomial product memoized.

Computation-only: no landed definition changes.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate CertArith

variable {α : Type} [CertArith α]

/-- The landed `mul` with its polynomial product memoized (radius verbatim). -/
theorem CertModel.mul_eq_of_polyProduct (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a b : CertModel α) {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W cfg key a.poly b.poly = some out) :
    CertModel.mul W cfg key a b =
      ⟨a.deg + b.deg, truncPoly cfg.cutoff out.1,
        upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff))))
          (upAdd (upAdd (crossUp (a.poly.supNormUp W) b.rad) (crossUp (b.poly.supNormUp W) a.rad))
            (upMul a.rad b.rad))⟩ := by
  simp only [CertModel.mul, h]

/-- The exp arm, with its witness radius memoized. -/
theorem composeStep_exp_eq (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) (a : ℕ) {E : ExpWitness α}
    {r : α} (hE : wit.expWit[st.nExp]? = some E)
    (hr : expWitnessRadius n W (cfg.forWitness 1 st.nExp)
      (CertModel.toDeg W pe 0 (st.slot W a).1) E = some r) :
    composeStep n K wit W cfg pe st (.exp a) =
      some { st.pushSlot W ⟨0, E.poly, r⟩ with nExp := st.nExp + 1 } := by
  simp only [composeStep, hE, hr]

/-- The inv arm, with its witness radius memoized. -/
theorem composeStep_inv_eq (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) (a : ℕ) {Q : CertPoly α}
    {r : α} (hQ : wit.invWit[st.nInv]? = some Q)
    (hr : invWitnessRadius n W (cfg.forWitness 2 st.nInv) (st.slot W a).1 Q = some r) :
    composeStep n K wit W cfg pe st (.inv a) =
      some { st.pushSlot W ⟨-(st.slot W a).1.deg, Q, r⟩ with nInv := st.nInv + 1 } := by
  simp only [composeStep, hQ, hr]

/-- The sqrt arm, with its witness radius memoized. -/
theorem composeStep_sqrt_eq (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) (a : ℕ) {i : ℕ}
    {S : SqrtWitness α} {r : α} (hS : wit.sqrtWit.find? (fun e => e.1 == st.len) = some (i, S))
    (hr : sqrtWitnessRadius n W (cfg.forWitness 3 st.len)
      (CertModel.toDeg W pe 0 (st.slot W a).1) S = some r) :
    composeStep n K wit W cfg pe st (.sqrt a) = some (st.pushSlot W ⟨0, S.poly, r⟩) := by
  simp only [composeStep, hS, hr]

/-- The inverse witness radius from its `δ` (the `oneSubSupUp` of the memoizable product) and the
reciprocal bound `t ≥ 1/(1 - δ)`. -/
theorem invWitnessRadius_eq_of_delta (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (b : CertModel α) (Q : CertPoly α) {δ t : α}
    (hδ : oneSubSupUp W (CertModel.mul W cfg [2] ⟨0, Q, ofInt 0⟩ ⟨0, b.poly, b.rad⟩) = δ)
    (hlt : blt δ (ofInt 1) = true) (ht : recipOneSubUp δ = some t) :
    invWitnessRadius n W cfg b Q = some (upMul (upMul (Q.supNormUp W) δ) t) := by
  unfold invWitnessRadius
  simp only [hδ, hlt, ht, ↓reduceIte]

/-- The square-root witness radius from its three checks and the bound `e` of the residual
`sup |g - W²|` (whose inner product `W · W` is memoizable). -/
theorem sqrtWitnessRadius_eq_of_residual (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (g : CertModel α) (S : SqrtWitness α) {e : α}
    (hok : (decide (0 ≤ S.margin ∧ S.margin < S.anchor) &&
      ble ((sqrtAnchorDiff n W S).supBound W) (ofRatDown S.margin) &&
      blt ((sqrtRadicandDiff n W g S).supBound W) (ofRatDown (S.anchor * S.anchor))) = true)
    (he : (sqrtResidual n W cfg g S).supBound W = e) :
    sqrtWitnessRadius n W cfg g S = some (upMul e (ofRatUp (1 / (S.anchor - S.margin)))) := by
  unfold sqrtWitnessRadius
  simp only [hok, he, ↓reduceIte]

end KAM.SpinOrbit.Data.LockN65
