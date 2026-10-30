/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Compose

/-!
# The product split: packed products proved apart from their consumers

Equation lemmas (design SO-CSPLIT §3.5, M3) that let a packed product be memoized as a literal and
proved by its own kernel run, apart from the op or stage entry that consumes it. They are
computation-only: no landed definition changes. The chain is
`checkPackedSp_of_groups` (shards in groups) → `packedRealProduct_eq_of_sparse` (or the empty
lemmas) → `CertPoly.mulPacked_eq_of_parts` → `polyProduct_eq_of_mulPacked` →
`CertModel.mulN_eq_of_polyProduct`; the character witness is memoized through
`charResolve_eq_of_radius`, `expWitnessRadius_eq_of_pin`, `expWitnessRadiusOf_eq_of_residuals`
and `expResidualProduct_eq_of_polyProduct`.
-/

@[expose] public section

namespace KAM.Certificate

open KAM CertArith

variable {α : Type} [CertArith α]

/-- The landed `mulN` with its polynomial product memoized (radius verbatim). -/
theorem CertModel.mulN_eq_of_polyProduct (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a : CertModel α) (na : α) (b : CertModel α) (nb : α) {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W cfg key a.poly b.poly = some out) :
    CertModel.mulN W cfg key a na b nb =
      ⟨a.deg + b.deg, truncPoly cfg.cutoff out.1,
        upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff))))
          (upAdd (upAdd (crossUp na b.rad) (crossUp nb a.rad)) (upMul a.rad b.rad))⟩ := by
  simp only [CertModel.mulN, h]

/-- F2: the packed branch of `polyProduct` returns the error terms of the packed polynomial. -/
theorem polyProduct_eq_of_mulPacked (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a b : CertPoly α) (P : ℕ) (rr ii ri ir : PackedAdvice) (out : CertPoly α × α)
    (ha : a.isConst = false) (hb : b.isConst = false)
    (hk : adviceLookup cfg.advice key = some (.packed P rr ii ri ir))
    (hp : CertPoly.mulPacked cfg.toMant W P rr ii ri ir a b = some out) :
    CertModel.polyProduct W cfg key a b = some (out.1.toErrTerms, out.2) := by
  simp only [CertModel.polyProduct, ha, hb, hk, hp, Bool.false_eq_true, ↓reduceIte]

/-- F2: `mulPacked` from its four real parts and their decodes (the II part negated into the real
component; RI, IR into the imaginary component, exactly as the landed body). -/
theorem CertPoly.mulPacked_eq_of_parts (dec : ℕ → α → Option ℤ) (W : CertWeight) (P : ℕ)
    (rr ii ri ir : PackedAdvice) (a b : CertPoly α)
    {ma mb : List (CertKey × ℤ) × List (CertKey × ℤ)}
    {pRR pII pRI pIR : List (CertKey × ℤ) × ℚ} {tRR tII tRI tIR : List (CertKey × CC α)}
    (hma : a.toMants dec P = some ma) (hmb : b.toMants dec P = some mb)
    (hRR : packedRealProduct rr W (2 * P) ma.1 mb.1 = some pRR)
    (hII : packedRealProduct ii W (2 * P) ma.2 mb.2 = some pII)
    (hRI : packedRealProduct ri W (2 * P) ma.1 mb.2 = some pRI)
    (hIR : packedRealProduct ir W (2 * P) ma.2 mb.1 = some pIR)
    (htRR : dyadicTerms (2 * P) rr.scale (fun v => ⟨v, ofInt 0⟩) pRR.1 = some tRR)
    (htII : dyadicTerms (2 * P) ii.scale (fun v => ⟨v, ofInt 0⟩)
      (pII.1.map fun t => (t.1, -t.2)) = some tII)
    (htRI : dyadicTerms (2 * P) ri.scale (fun v => ⟨ofInt 0, v⟩) pRI.1 = some tRI)
    (htIR : dyadicTerms (2 * P) ir.scale (fun v => ⟨ofInt 0, v⟩) pIR.1 = some tIR) :
    CertPoly.mulPacked dec W P rr ii ri ir a b =
      some (⟨tRR ++ tII ++ tRI ++ tIR⟩, ofRatUp (pRR.2 + pII.2 + pRI.2 + pIR.2)) := by
  simp only [CertPoly.mulPacked, hma, hmb, hRR, hII, hRI, hIR, htRR, htII, htRI, htIR,
    Option.bind_some]

/-- F3: an empty factor (left). -/
theorem packedRealProduct_eq_nil_left (adv : PackedAdvice) (W : CertWeight) (P2 : ℕ)
    {x : List (CertKey × ℤ)} (y : List (CertKey × ℤ)) (hx : x.isEmpty = true) :
    packedRealProduct adv W P2 x y = some ([], 0) := by
  simp [packedRealProduct, hx]

/-- F3: an empty factor (right). -/
theorem packedRealProduct_eq_nil_right (adv : PackedAdvice) (W : CertWeight) (P2 : ℕ)
    (x : List (CertKey × ℤ)) {y : List (CertKey × ℤ)} (hy : y.isEmpty = true) :
    packedRealProduct adv W P2 x y = some ([], 0) := by
  simp [packedRealProduct, hy]

/-- F3: the nonempty sparse branch. -/
theorem packedRealProduct_eq_of_sparse (adv : PackedAdvice) (W : CertWeight) (P2 : ℕ)
    (x y : List (CertKey × ℤ)) (hx : x.isEmpty = false) (hy : y.isEmpty = false)
    (ha : adv.la.allSlots x = true) (hb : adv.lb.allSlots y = true)
    (hs : checkPackedSp adv (adv.la.slotTerms x) (adv.lb.slotTerms y) = true) :
    packedRealProduct adv W P2 x y = some (adv.targetTerms, adv.remainderBound W P2) := by
  simp [packedRealProduct, hx, hy, ha, hb, hs]

/-- The non-shard prefix of `checkPackedSp` (shape, dense lengths, ordering, slot bounds, the
advice window count), verbatim. -/
def checkPackedSpPrefix (adv : PackedAdvice) (ea eb : List (ℕ × ℤ)) : Bool :=
  adv.shapeOK && decide (0 < adv.la.denseLen) && decide (0 < adv.lb.denseLen) &&
    packStrictAsc ea && packStrictAsc eb &&
    (ea.all fun e => decide (e.1 < adv.la.denseLen)) &&
    (eb.all fun e => decide (e.1 < adv.lb.denseLen)) &&
    adv.rounded.length == adv.spCount adv.la.denseLen + adv.spCount adv.lb.denseLen - 1

/-- The shard numbers of a product. -/
def PackedAdvice.shardRange (adv : PackedAdvice) : List ℕ :=
  List.range (adv.spCount adv.la.denseLen + adv.spCount adv.lb.denseLen - 1)

/-- One shard, at the exact blocks and bounds of `checkPackedSp`. -/
def checkShardAt (adv : PackedAdvice) (ea eb : List (ℕ × ℤ)) (s : ℕ) : Bool :=
  checkShardSp adv (spBlocks adv.blockLen (adv.spCount adv.la.denseLen) 0 ea)
    (spBlocks adv.blockLen (adv.spCount adv.lb.denseLen) 0 eb) (spMax ea) (spMax eb) s

/-- F3: the sparse check from its prefix and shard groups covering every shard number. -/
theorem checkPackedSp_of_groups (adv : PackedAdvice) (ea eb : List (ℕ × ℤ))
    (groups : List (List ℕ)) (hpre : checkPackedSpPrefix adv ea eb = true)
    (hcover : ∀ s ∈ adv.shardRange, ∃ g ∈ groups, s ∈ g)
    (hgroups : ∀ g ∈ groups, g.all (checkShardAt adv ea eb) = true) :
    checkPackedSp adv ea eb = true := by
  simp only [checkPackedSpPrefix, Bool.and_eq_true] at hpre
  simp only [checkPackedSp, Bool.and_eq_true, hpre, true_and, List.all_eq_true]
  intro s hs
  obtain ⟨g, hg, hsg⟩ := hcover s hs
  have := hgroups g hg
  rw [List.all_eq_true] at this
  exact this s hsg

/-- The character witness with its radius memoized (cache miss, own key). -/
theorem charResolve_eq_of_radius (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (cache : List (CertKey × CertPoly α × α)) (k' : CertKey) {c : ℕ} {E : ExpWitness α} {r : α}
    (hc : findKeyIdx k' cache = none) (hw : findKeyIdx k' wit.charWit = some (c, E))
    (hr : expWitnessRadius n W (cfg.forWitness 1 (wit.expWit.length + c))
      (charPhaseModel n K W pe k') E = some r) :
    charResolve n K wit W cfg pe cache k' = some ((E.poly, r), (k', E.poly, r) :: cache) := by
  simp only [charResolve, hc, hw, hr]

/-- The exp witness from its pin. -/
theorem expWitnessRadius_eq_of_pin (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (g : CertModel α) (E : ExpWitness α) {out : CC α × α}
    (h : certCExpReduced (expPinBall g).1 (expPinBall g).2 E.pinHalvings E.pinOrder = some out) :
    expWitnessRadius n W cfg g E = expWitnessRadiusOf n W cfg g E.poly out := by
  simp only [expWitnessRadius, h]

/-- The exp witness radius from its real bounds and memoized residuals. -/
theorem expWitnessRadiusOf_eq_of_residuals (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (g : CertModel α) (E : CertPoly α) (out : CC α × α) {mB mη : α} {rs : ℕ → α}
    (hB : expm1Up cfg.halvings cfg.taylorN (g.poly.supNormUp W) = some mB)
    (hη : expm1Up cfg.halvings cfg.taylorN g.rad = some mη)
    (hres : ∀ j : Fin n, expResidualUp W cfg g.poly E (E.supNormUp W) j.val = rs j.val) :
    expWitnessRadiusOf n W cfg g E out =
      some (upAdd (upMul (upMul (upAdd (ofInt 1) mB) (upAdd (ofInt 1) mB))
          (upAdd (expPinErr E out) (upMul (ofRatUp (1 / 2 + W.rho))
            (sumUp (fun j : Fin n => rs j.val) (List.finRange n)))))
        (upMul (upAdd (ofInt 1) mB) mη)) := by
  have : (fun j : Fin n => expResidualUp W cfg g.poly E (E.supNormUp W) j.val) =
      fun j : Fin n => rs j.val := funext hres
  simp only [expWitnessRadiusOf, hB, hη, this]

/-- One residual from its memoized packed product. -/
theorem expResidualProduct_eq_of_polyProduct (W : CertWeight) (cfg : ModelConfig α)
    (g₀ E : CertPoly α) (j : ℕ) {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W cfg [1, j] (itemsPoly (g₀.terms.filterMap (derivItem j)))
      E.negP = some out) :
    expResidualProduct W cfg g₀ E j = out := by
  simp only [expResidualProduct, h]

end KAM.Certificate
