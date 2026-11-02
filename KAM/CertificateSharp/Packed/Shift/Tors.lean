/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Shift.Cons
public import KAM.CertificateSharp.Packed.JetConsFrames

/-!
# Window-sized powers as shifts: the Gram core, the rounded torsion and the frames

The packed Gram core (`Gram.lean`), the stages and final checks of the rounded torsion on the jet
(`TorsR.lean`, `Stage.lean`, `JetConsTors.lean`) and the frame tests (`Frames.lean`) with the shift
leaves of `Shift/Base.lean`, each equal to the landed one (`…S_eq`). A certificate whose `DK` memo
covers a large box (MAG: 223 × 131 keys, products on windows of 116k slots) runs these checks on
windows above `2^24` bits.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-! ### The Gram core -/

section Gram

variable {α : Type} [CertArith α] (n : ℕ) (Binv : List (List (CertPoly α))) (W : CertWeight)
  (cfg : ModelConfig α) (bk : PGramBook) (mm : PGramMemo)

/-- `pgD` with a shift. -/
def pgDS (i j : ℕ) : PC :=
  pcUnitSubS bk.L3.width (pgP0 n bk) (if i = j then 2 ^ (3 * bk.P) else 0)
    (pgE n Binv cfg bk mm i j)

/-- `pgKn` with shifts. -/
def pgKnS (r a : ℕ) : α :=
  ofRatUp ((pcNormS W bk.q bk.lK bk.L1 (pgK bk mm r a) : ℚ) / 2 ^ (bk.P + 2 * bk.q))

/-- `pgGr` with shifts. -/
def pgGrS (k j : ℕ) : α :=
  sumUp (fun r : ℕ => upAdd (upAdd (upMul (pgKnS W bk mm r k) (pgKr (α := α) mm r j))
      (upMul (pgKnS W bk mm r j) (pgKr (α := α) mm r k)))
      (upMul (pgKr (α := α) mm r k) (pgKr (α := α) mm r j))) (List.range (2 * n))

/-- `pgBn` with shifts. -/
def pgBnS (i k : ℕ) : α :=
  ofRatUp ((pcNormS W bk.q bk.lB bk.LB (pgB Binv cfg bk i k) : ℚ) / 2 ^ (bk.P + 2 * bk.q))

/-- `pgDn` with shifts. -/
def pgDnS (i j : ℕ) : α :=
  upAdd (ofRatUp ((pcNormS W bk.q bk.lD bk.L3 (pgDS n Binv cfg bk mm i j) : ℚ) /
      2 ^ (3 * bk.P + 2 * bk.q)))
    (sumUp (fun k : ℕ => upMul (pgBnS Binv W cfg bk i k) (pgGrS (α := α) n W bk mm k j))
      (List.range n))

/-- `pgDRows` with shifts. -/
def pgDRowsS : List α :=
  List.ofFn fun i : Fin n => sumUp (fun j : Fin n => pgDnS n Binv W cfg bk mm i.val j.val)
    (List.finRange n)

/-- `pgBRows` with shifts. -/
def pgBRowsS : List α :=
  List.ofFn fun i : Fin n => sumUp (fun k : Fin n => pgBnS Binv W cfg bk i.val k.val)
    (List.finRange n)

/-- `gramPackedCore` with shifts. -/
def gramPackedCoreS (σBμ : ℚ) : Option (α × α) :=
  if gramInvShapeOk n Binv && pgGuard n Binv W cfg bk mm then
    if gramBoundsOk (pgDRowsS n Binv W cfg bk mm) (pgBRowsS n Binv W cfg bk)
        (maxCandidate (pgDRowsS n Binv W cfg bk mm)) (maxCandidate (pgBRowsS n Binv W cfg bk))
        σBμ then
      some (maxCandidate (pgDRowsS n Binv W cfg bk mm), maxCandidate (pgBRowsS n Binv W cfg bk))
    else none
  else none

end Gram

/-! ### The boundary matrices and the stages -/

section Tors

variable {α : Type} [CertArith α] (n : ℕ) (Binv : List (List (CertPoly α))) (W : CertWeight)
  (cfg : ModelConfig α) (box : FreqBox) (s : ℚ) (tb : PTorsBook) (mm : PGramMemo) (tm : PTorsMemo)

/-- `ptB` with shifts. -/
def ptBS (eps : α) : PMat α :=
  ⟨fun i k => pcOfPoly cfg.toMant tb.P tb.LB (gramInvPoly Binv i k), fun _ _ => eps,
    fun i k => pnormS W tb.q tb.lB tb.LB tb.P
      (pcOfPoly cfg.toMant tb.P tb.LB (gramInvPoly Binv i k))⟩

/-- `ptD2` with shifts. -/
def ptD2S (l : ℕ) : PMat α :=
  ⟨fun r j => memoPC tb.L1 (tm.d2.getD (d2Idx n r j l) ([], [], 0)),
    fun r j => ofRatUp (tm.d2.getD (d2Idx n r j l) ([], [], 0)).2.2,
    fun r j => pnormS W tb.q tb.lD tb.L1 tb.P
      (memoPC tb.L1 (tm.d2.getD (d2Idx n r j l) ([], [], 0)))⟩

end Tors

/-- `nodeRes` with a shift. -/
def nodeResS (n : ℕ) (Ld Lu : PackLayout) (s : ℕ) (x : PC) (t : NodeEntry) : PC :=
  pcAdd x (pcNeg (pcMul (nodePC Ld t) (pcUnitS Lu.width (zslot n Lu) (2 ^ s))))

theorem nodeResS_eq (n : ℕ) (Ld Lu : PackLayout) (s : ℕ) (x : PC) (t : NodeEntry) :
    nodeResS n Ld Lu s x t = nodeRes n Ld Lu s x t := by
  simp only [nodeResS, nodeRes, pcUnitSubS_eq, pcUnitS_eq]

/-- `stageOk` with shifts. -/
def stageOkS {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (q lr ln : ℕ)
    (Ls Ld Lu : PackLayout) (A' e s : ℕ) (x : PC) (r : α) (t : NodeEntry) : Bool :=
  nodePackOk Ld A' t &&
    ble (upAdd r (pnormS W q lr Ls e (nodeResS n Ld Lu s x t))) (ofRatUp t.2.2.1) &&
    ble (pnormS W q ln Ld (e - s) (nodePC Ld t) : α) (ofRatUp t.2.2.2)

/-- `stageAll` with shifts. -/
def stageAllS {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (q lr ln : ℕ)
    (Ls Ld Lu : PackLayout) (A' e s R C : ℕ) (M : PMat α) (tab : List (List NodeEntry)) : Bool :=
  (List.range R).all fun i => (List.range C).all fun j =>
    stageOkS n W q lr ln Ls Ld Lu A' e s (M.x i j) (M.r i j) (nodeAt tab i j)

section TorsR

variable {α : Type} [CertArith α] (n : ℕ) (Binv : List (List (CertPoly α))) (W : CertWeight)
  (cfg : ModelConfig α) (box : FreqBox) (s : ℚ) (rb : PRBook) (mm : PGramMemo) (tm : PTorsMemo)
  (rm : PRMemo) (eps : α)

/-- `trDL0` with shifts. -/
def trDL0S : PMat α :=
  ⟨fun r j => pcSumN
      (fun l => pcMul ((ptD2S (α := α) n W rb.toT tm l).x r j) (ptF n box s rb.toT l)) n,
    fun r j => sumUp (fun l => pmulRad ((ptD2S (α := α) n W rb.toT tm l).nb r j)
      ((ptD2S (α := α) n W rb.toT tm l).r r j) (ofRatUp (|(ptFc box s rb.toT l : ℚ)| / 2 ^ rb.P))
      (ofRatUp (ptFr box s rb.toT l))) (List.range n),
    fun r j => sumUp (fun l => upMul ((ptD2S (α := α) n W rb.toT tm l).nb r j)
      (ofRatUp (|(ptFc box s rb.toT l : ℚ)| / 2 ^ rb.P))) (List.range n)⟩

/-- `trMN` with shifts. -/
def trMNS : PMat α := PMat.mul n (ptKS W rb.toT mm) (ptBS Binv W cfg rb.toT eps)

/-- `trMDG` with shifts. -/
def trMDGS : PMat α :=
  PMat.add (PMat.mul (n + n) (nodeMat (α := α) rb.Lb rm.DL).tr (ptKS W rb.toT mm))
    (PMat.mul (n + n) (ptKS W rb.toT mm).tr (nodeMat rb.Lb rm.DL))

/-- `trMC` with shifts. -/
def trMCS : PMat α := PMat.mul n (ptBS Binv W cfg rb.toT eps) (nodeMat rb.Lb rm.DG)

/-- `trMDGi` with shifts. -/
def trMDGiS : PMat α := PMat.mul n (nodeMat rb.Lb rm.C) (ptBS Binv W cfg rb.toT eps)

/-- `trMDN` with shifts. -/
def trMDNS : PMat α :=
  PMat.add (PMat.mul n (nodeMat rb.Lb rm.DL) (ptBS Binv W cfg rb.toT eps))
    (PMat.mul n (ptKS W rb.toT mm) (trDGi rb rm))

/-- `trStage` with shifts. -/
def trStageS (R C : ℕ) (M : PMat α) (tab : List (List NodeEntry)) : Bool :=
  stageAllS n W rb.q rb.lW rb.lR rb.Lw rb.Lb rb.Lu rb.bR (2 * rb.P) rb.P R C M tab

/-- `trStN` with shifts. -/
def trStNS : Bool := trStageS n W rb (n + n) n (trMNS n Binv W cfg rb mm eps) rm.N

/-- `trStDL` with shifts. -/
def trStDLS : Bool :=
  stageAllS n W rb.q rb.lL rb.lR rb.LL rb.Lb rb.LU0 rb.bR (2 * rb.P) rb.P (n + n) n
    (trDL0S (α := α) n W box s rb tm) rm.DL

/-- `trStDG` with shifts. -/
def trStDGS : Bool := trStageS n W rb n n (trMDGS (α := α) n W rb mm rm) rm.DG

/-- `trStC` with shifts. -/
def trStCS : Bool := trStageS n W rb n n (trMCS n Binv W cfg rb rm eps) rm.C

/-- `trStDGi` with shifts. -/
def trStDGiS : Bool := trStageS n W rb n n (trMDGiS n Binv W cfg rb rm eps) rm.DGi

/-- `trStDN` with shifts. -/
def trStDNS : Bool := trStageS n W rb (n + n) n (trMDNS n Binv W cfg rb mm rm eps) rm.DN

/-- `trTCheck` with shifts. -/
def trTCheckS : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    decide (ptDigitS n rb.Lw (2 * rb.P) ((trT (α := α) n rb rm).x i j) =
        (rm.CT.getD i []).getD j (0, 0)) &&
      ble ((trT (α := α) n rb rm).r i j) (ofRatDown ((rm.RT.getD i []).getD j 0))

/-- `trFrameLOk` with shifts. -/
def trFrameLOkS (b : ℚ) : Bool :=
  (List.range n).all fun j =>
    ble (sumUp (fun r => pmBound (ptKS (α := α) W rb.toT mm) r j) (List.range (n + n)))
      (ofRatDown b)

/-- `trFrameTOk` with shifts. -/
def trFrameTOkS (bT : ℚ) : Bool :=
  decide (rb.aT n ≤ rb.aW) &&
    (List.range n).all fun i =>
      ble (sumUp (fun j => upAdd (pnormS W rb.q rb.lW rb.Lw (2 * rb.P)
        ((trT (α := α) n rb rm).x i j)) ((trT (α := α) n rb rm).r i j)) (List.range n))
        (ofRatDown bT)

end TorsR

/-- `trStXNJ` with shifts. -/
def trStXNJS {α : Type} [CertArith α] (n : ℕ) (J : HamJet) (js : JSlots α) (W : CertWeight)
    (rb : PRBook) (rm : PRMemo) : Bool :=
  trStageS n W rb (n + n) n (trMXNJ n J js rb rm) rm.XN

/-- `trYCheckJ` with shifts. -/
def trYCheckJS {α : Type} [CertArith α] (n : ℕ) (J : HamJet) (js : JSlots α) (rb : PRBook)
    (rm : PRMemo) : Bool :=
  (List.range n).all fun j =>
    decide (ptDigitS n rb.Lw (2 * rb.P) ((trYJ n J js rb rm).x 0 j) = rm.CY.getD j (0, 0)) &&
      ble ((trYJ n J js rb rm).r 0 j) (ofRatDown (rm.RY.getD j 0))

/-! ### Equality with the landed definitions -/

section Eq

variable {α : Type} [CertArith α] (n : ℕ) (Binv : List (List (CertPoly α))) (W : CertWeight)
  (cfg : ModelConfig α) (box : FreqBox) (s : ℚ) (bk : PGramBook) (tb : PTorsBook)
  (rb : PRBook) (mm : PGramMemo) (tm : PTorsMemo) (rm : PRMemo) (eps : α)

theorem pgDS_eq (i j : ℕ) : pgDS n Binv cfg bk mm i j = pgD n Binv cfg bk mm i j := by
  simp only [pgDS, pgD, pcUnitSubS_eq]

theorem pgKnS_eq (r a : ℕ) : pgKnS (α := α) W bk mm r a = pgKn W bk mm r a := by
  simp only [pgKnS, pgKn, pcNormS_eq]

theorem pgGrS_eq (k j : ℕ) : pgGrS (α := α) n W bk mm k j = pgGr n W bk mm k j := by
  simp only [pgGrS, pgGr, pgKnS_eq]

theorem pgBnS_eq (i k : ℕ) : pgBnS Binv W cfg bk i k = pgBn Binv W cfg bk i k := by
  simp only [pgBnS, pgBn, pcNormS_eq]

theorem pgDnS_eq (i j : ℕ) : pgDnS n Binv W cfg bk mm i j = pgDn n Binv W cfg bk mm i j := by
  simp only [pgDnS, pgDn, pcNormS_eq, pgDS_eq, pgBnS_eq, pgGrS_eq]

theorem pgDRowsS_eq : pgDRowsS n Binv W cfg bk mm = pgDRows n Binv W cfg bk mm := by
  simp only [pgDRowsS, pgDRows, pgDnS_eq]

theorem pgBRowsS_eq : pgBRowsS n Binv W cfg bk = pgBRows n Binv W cfg bk := by
  simp only [pgBRowsS, pgBRows, pgBnS_eq]

theorem gramPackedCoreS_eq (σBμ : ℚ) :
    gramPackedCoreS n Binv W cfg bk mm σBμ = gramPackedCore n Binv W cfg bk mm σBμ := by
  simp only [gramPackedCoreS, gramPackedCore, pgDRowsS_eq, pgBRowsS_eq]

theorem ptBS_eq : ptBS Binv W cfg tb eps = ptB Binv W cfg tb eps := by
  simp only [ptBS, ptB, pnormS_eq]

theorem ptD2S_eq (l : ℕ) : ptD2S (α := α) n W tb tm l = ptD2 n W tb tm l := by
  simp only [ptD2S, ptD2, pnormS_eq]

theorem stageOkS_eq (q lr ln : ℕ) (Ls Ld Lu : PackLayout) (A' e s' : ℕ) (x : PC) (r : α)
    (t : NodeEntry) :
    stageOkS n W q lr ln Ls Ld Lu A' e s' x r t = stageOk n W q lr ln Ls Ld Lu A' e s' x r t := by
  simp only [stageOkS, stageOk, pnormS_eq, nodeResS_eq]

theorem stageAllS_eq (q lr ln : ℕ) (Ls Ld Lu : PackLayout) (A' e s' R C : ℕ) (M : PMat α)
    (tab : List (List NodeEntry)) :
    stageAllS n W q lr ln Ls Ld Lu A' e s' R C M tab =
      stageAll n W q lr ln Ls Ld Lu A' e s' R C M tab := by
  simp only [stageAllS, stageAll, stageOkS_eq]

theorem trDL0S_eq : trDL0S (α := α) n W box s rb tm = trDL0 n W box s rb tm := by
  simp only [trDL0S, trDL0, ptD2S_eq]

theorem trStNS_eq : trStNS n Binv W cfg rb mm rm eps = trStN n Binv W cfg rb mm rm eps := by
  simp only [trStNS, trStN, trStageS, trStage, stageAllS_eq, trMNS, trMN, ptKS_eq, ptBS_eq]

theorem trStDLS_eq : trStDLS (α := α) n W box s rb tm rm = trStDL (α := α) n W box s rb tm rm := by
  simp only [trStDLS, trStDL, stageAllS_eq, trDL0S_eq]

theorem trStDGS_eq : trStDGS (α := α) n W rb mm rm = trStDG (α := α) n W rb mm rm := by
  simp only [trStDGS, trStDG, trStageS, trStage, stageAllS_eq, trMDGS, trMDG, ptKS_eq]

theorem trStCS_eq : trStCS n Binv W cfg rb rm eps = trStC n Binv W cfg rb rm eps := by
  simp only [trStCS, trStC, trStageS, trStage, stageAllS_eq, trMCS, trMC, ptBS_eq]

theorem trStDGiS_eq : trStDGiS n Binv W cfg rb rm eps = trStDGi n Binv W cfg rb rm eps := by
  simp only [trStDGiS, trStDGi, trStageS, trStage, stageAllS_eq, trMDGiS, trMDGi, ptBS_eq]

theorem trStDNS_eq : trStDNS n Binv W cfg rb mm rm eps = trStDN n Binv W cfg rb mm rm eps := by
  simp only [trStDNS, trStDN, trStageS, trStage, stageAllS_eq, trMDNS, trMDN, ptKS_eq, ptBS_eq]

theorem trTCheckS_eq : trTCheckS (α := α) n rb rm = trTCheck (α := α) n rb rm := by
  simp only [trTCheckS, trTCheck, ptDigitS_eq]

theorem trFrameLOkS_eq (b : ℚ) :
    trFrameLOkS (α := α) n W rb mm b = trFrameLOk (α := α) n W rb mm b := by
  simp only [trFrameLOkS, trFrameLOk, ptKS_eq]

theorem trFrameTOkS_eq (bT : ℚ) :
    trFrameTOkS (α := α) n W rb rm bT = trFrameTOk (α := α) n W rb rm bT := by
  simp only [trFrameTOkS, trFrameTOk, pnormS_eq]

theorem trStXNJS_eq (J : HamJet) (js : JSlots α) :
    trStXNJS n J js W rb rm = trStXNJ n J js W rb rm := by
  simp only [trStXNJS, trStXNJ, trStageS, trStage, stageAllS_eq]

theorem trYCheckJS_eq (J : HamJet) (js : JSlots α) :
    trYCheckJS n J js rb rm = trYCheckJ n J js rb rm := by
  simp only [trYCheckJS, trYCheckJ, ptDigitS_eq]

end Eq

/-! ### The Gram core from its parts -/

section Parts

variable {α : Type} [CertArith α] {n : ℕ} {Binv : List (List (CertPoly α))} {W : CertWeight}
  {cfg : ModelConfig α} {bk : PGramBook} {mm : PGramMemo}

/-- **The Gram core from its parts** (each in its own declaration: the guard, every defect entry
`pgDnS i j` and every witness norm `pgBnS i k` as a value): the core is the bound test on the
rows of those values. -/
theorem gramPackedCoreS_of_parts {D Bv : ℕ → ℕ → α} (σBμ : ℚ)
    (hg : (gramInvShapeOk n Binv && pgGuard n Binv W cfg bk mm) = true)
    (hD : ∀ i < n, ∀ j < n, pgDnS n Binv W cfg bk mm i j = D i j)
    (hB : ∀ i < n, ∀ k < n, pgBnS Binv W cfg bk i k = Bv i k) :
    gramPackedCoreS n Binv W cfg bk mm σBμ =
      if gramBoundsOk
          (List.ofFn fun i : Fin n => sumUp (fun j : Fin n => D i.val j.val) (List.finRange n))
          (List.ofFn fun i : Fin n => sumUp (fun k : Fin n => Bv i.val k.val) (List.finRange n))
          (maxCandidate
            (List.ofFn fun i : Fin n => sumUp (fun j : Fin n => D i.val j.val) (List.finRange n)))
          (maxCandidate
            (List.ofFn fun i : Fin n => sumUp (fun k : Fin n => Bv i.val k.val) (List.finRange n)))
          σBμ then
        some (maxCandidate
            (List.ofFn fun i : Fin n => sumUp (fun j : Fin n => D i.val j.val) (List.finRange n)),
          maxCandidate
            (List.ofFn fun i : Fin n => sumUp (fun k : Fin n => Bv i.val k.val) (List.finRange n)))
      else none := by
  have e1 : pgDRowsS n Binv W cfg bk mm =
      List.ofFn fun i : Fin n => sumUp (fun j : Fin n => D i.val j.val) (List.finRange n) :=
    congrArg List.ofFn (funext fun i => congrArg (fun f : Fin n → α => sumUp f (List.finRange n))
      (funext fun j => hD i.val i.isLt j.val j.isLt))
  have e2 : pgBRowsS n Binv W cfg bk =
      List.ofFn fun i : Fin n => sumUp (fun k : Fin n => Bv i.val k.val) (List.finRange n) :=
    congrArg List.ofFn (funext fun i => congrArg (fun f : Fin n → α => sumUp f (List.finRange n))
      (funext fun k => hB i.val i.isLt k.val k.isLt))
  simp only [gramPackedCoreS, hg, e1, e2, ↓reduceIte]

/-- **A stage from its entries** (each entry's `stageOkS` in its own declaration). -/
theorem stageAllS_of {q lr ln : ℕ} {Ls Ld Lu : PackLayout} {A' e s R C : ℕ} {M : PMat α}
    {tab : List (List NodeEntry)}
    (h : ∀ i < R, ∀ j < C,
      stageOkS n W q lr ln Ls Ld Lu A' e s (M.x i j) (M.r i j) (nodeAt tab i j) = true) :
    stageAllS n W q lr ln Ls Ld Lu A' e s R C M tab = true := by
  simp only [stageAllS, List.all_eq_true, List.mem_range]
  exact h

/-- `sumUp` reads its terms only on the list. -/
theorem sumUp_congr_mem {β : Type} {g g' : β → α} {L : List β} (h : ∀ x ∈ L, g x = g' x) :
    sumUp g L = sumUp g' L := by
  unfold sumUp
  rw [List.map_congr_left h]

/-- **The averages of `T` from their entries** (each entry in its own declaration). -/
theorem trTCheckS_of {rb : PRBook} {rm : PRMemo}
    (h : ∀ i < n, ∀ j < n, (decide (ptDigitS n rb.Lw (2 * rb.P) ((trT (α := α) n rb rm).x i j) =
        (rm.CT.getD i []).getD j (0, 0)) &&
      ble ((trT (α := α) n rb rm).r i j) (ofRatDown ((rm.RT.getD i []).getD j 0))) = true) :
    trTCheckS (α := α) n rb rm = true := by
  simp only [trTCheckS, List.all_eq_true, List.mem_range]
  exact h

/-- **The averages of `Y` (on the jet) from their entries.** -/
theorem trYCheckJS_of {J : HamJet} {js : JSlots α} {rb : PRBook} {rm : PRMemo}
    (h : ∀ j < n, (decide (ptDigitS n rb.Lw (2 * rb.P) ((trYJ n J js rb rm).x 0 j) =
        rm.CY.getD j (0, 0)) &&
      ble ((trYJ n J js rb rm).r 0 j) (ofRatDown (rm.RY.getD j 0))) = true) :
    trYCheckJS n J js rb rm = true := by
  simp only [trYCheckJS, List.all_eq_true, List.mem_range]
  exact h

/-- **The packed `sup |T|` test from the norms of its entries** (each norm a value, in its own
declaration) and the row sums of those values. -/
theorem trFrameTOkS_of {rb : PRBook} {rm : PRMemo} {bT : ℚ} {V : ℕ → ℕ → α}
    (hA : rb.aT n ≤ rb.aW)
    (hv : ∀ i < n, ∀ j < n,
      pnormS W rb.q rb.lW rb.Lw (2 * rb.P) ((trT (α := α) n rb rm).x i j) = V i j)
    (hrow : ∀ i < n, ble (sumUp (fun j => upAdd (V i j) ((trT (α := α) n rb rm).r i j))
      (List.range n)) (ofRatDown bT) = true) :
    trFrameTOkS (α := α) n W rb rm bT = true := by
  simp only [trFrameTOkS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨hA, fun i hi => ?_⟩
  rw [sumUp_congr_mem (g' := fun j => upAdd (V i j) ((trT (α := α) n rb rm).r i j))
    (fun j hj => by rw [hv i hi j (List.mem_range.mp hj)])]
  exact hrow i hi

end Parts

end KAM.CertificateSharp.Packed
