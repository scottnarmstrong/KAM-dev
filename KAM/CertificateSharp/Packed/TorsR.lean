/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Stage
public import KAM.CertificateSharp.Packed.TabFinal

/-!
# The rounded and truncated packed torsion stage: definitions

The exact packed chain of `Tors.lean` grows its windows with every product: at LG00 size its
numbers exceed the kernel's numeral cap and its memory exceeds 4 GB in one process (V2-PACKED-B3).
`checkTorsionR` certifies the same proposition with **bounded** packed models, as the landed models
do:

* **one box** `Lb` for every boundary entry and every node (the landed `cfgLow` truncation lies
  inside it), **one window** `Lw = win Lb Lb` for every product, one unit layout `Lu`
  (`win Lb Lu = Lw`);
* **every node** (`N`, `D L`, `DG`, `C`, `D(G⁻¹)`, `DN`, `X_N`) is a memo on `Lb` at scale `2^P`
  (`PRMemo`; rounded mantissas, truncated modes, computed by untrusted tooling), checked entry by
  entry against the exact product of its (memoized) inputs on `Lw` at scale `2^(2P)` by the residual
  (`stageAll`, `Stage.lean`): rounding and truncation errors are in the radius, never assumed;
* **the averages**: the zero-key slots of `T = Nᵀ Ω₀ X_N` and `Y = DH N` (on `Lw`) are checked
  against small tables of exact centres and radii (`trTCheck`, `trYCheck`), and the landed test runs
  on the tables (`tabFinal`).

Every conjunct of the core (`torsRCore`) is a separate small computation: the gate decides each in
its own process.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- The untrusted metadata of a rounded packed torsion check. -/
structure PRBook where
  /-- mantissa scale (that of every memo) -/
  P : ℕ
  /-- the box, the unit layout of the window, the 1 × 1 layout of the zero key -/
  Lb : PackLayout
  Lu : PackLayout
  LU0 : PackLayout
  /-- load bounds: `DK`, `B`, `D²K`, the jet slots, the frequency mantissas, the nodes -/
  bK : ℕ
  bB : ℕ
  bD : ℕ
  bA : ℕ
  bF : ℕ
  bR : ℕ
  /-- load bounds of every product on the window, and of `D L` on the box -/
  aW : ℕ
  aL : ℕ
  /-- norm precision and offsets: the inputs, the nodes, the window residuals, `D L` -/
  q : ℕ
  lK : ℕ
  lB : ℕ
  lD : ℕ
  lA : ℕ
  lR : ℕ
  lW : ℕ
  lL : ℕ

namespace PRBook

variable (rb : PRBook) (n : ℕ)

/-- The window of every product. -/
def Lw : PackLayout := win rb.Lb rb.Lb

/-- The source layout of `D L` (the box times the zero key). -/
def LL : PackLayout := win rb.Lb rb.LU0

/-- The book of `Tors.lean` for the boundary (every input on the box). -/
def toT : PTorsBook :=
  ⟨rb.P, rb.Lb, rb.Lb, rb.Lb, rb.LU0, rb.Lu, rb.Lu, rb.bK, rb.bB, rb.bD, rb.bA, rb.bF, rb.q,
    rb.lK, rb.lB, rb.lD, rb.lA, rb.lL, 0, 0, 0, 0, 0⟩

/-- The loads of the products. -/
def aN : ℕ := n * mulLoad rb.Lb rb.Lb rb.bK rb.bB
def aDL : ℕ := n * mulLoad rb.Lb rb.LU0 rb.bD rb.bF
def aDG : ℕ := (n + n) * mulLoad rb.Lb rb.Lb rb.bR rb.bK + (n + n) * mulLoad rb.Lb rb.Lb rb.bK rb.bR
def aC : ℕ := n * mulLoad rb.Lb rb.Lb rb.bB rb.bR
def aDGi : ℕ := n * mulLoad rb.Lb rb.Lb rb.bR rb.bB
def aDN : ℕ := n * mulLoad rb.Lb rb.Lb rb.bR rb.bB + n * mulLoad rb.Lb rb.Lb rb.bK rb.bR
def aXN : ℕ := (n + n) * mulLoad rb.Lb rb.Lb rb.bA rb.bR + mulLoad rb.Lb rb.Lu rb.bR (2 ^ rb.P)
def aT : ℕ := (n + n) * mulLoad rb.Lb rb.Lb rb.bR rb.bR
def aY : ℕ := (n + n) * mulLoad rb.Lb rb.Lb rb.bA rb.bR

end PRBook

/-- The memoized nodes and the tables of the averages. -/
structure PRMemo where
  /-- `L G⁻¹` (before `Ω₀`), `2n × n` -/
  N : List (List NodeEntry)
  /-- `D L`, `2n × n` -/
  DL : List (List NodeEntry)
  /-- `DG`, `C = G⁻¹ DG`, `C G⁻¹` (before the sign), `n × n` -/
  DG : List (List NodeEntry)
  C : List (List NodeEntry)
  DGi : List (List NodeEntry)
  /-- `D L G⁻¹ + L D(G⁻¹)` (before `Ω₀`) and `X_N`, `2n × n` -/
  DN : List (List NodeEntry)
  XN : List (List NodeEntry)
  /-- exact centres and radius bounds of the averages of `T` (`n × n`) and `Y` (`n`) -/
  CT : List (List (ℚ × ℚ))
  RT : List (List ℚ)
  CY : List (ℚ × ℚ)
  RY : List ℚ

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (Binv : List (List (CertPoly α))) (W : CertWeight)
  (cfg : ModelConfig α) (box : FreqBox) (s : ℚ) (rb : PRBook) (mm : PGramMemo) (tm : PTorsMemo)
  (rm : PRMemo) (eps : α)

/-! ### The exact products and the nodes -/

/-- `D L = Σ_l (s ω)_l ∂_l L` on `win Lb LU0`, scale `2^(2P)` (exact, from the boundary). -/
def trDL0 : PMat α :=
  ⟨fun r j => pcSumN
      (fun l => pcMul ((ptD2 (α := α) n W rb.toT tm l).x r j) (ptF n box s rb.toT l)) n,
    fun r j => sumUp (fun l => pmulRad ((ptD2 (α := α) n W rb.toT tm l).nb r j)
      ((ptD2 (α := α) n W rb.toT tm l).r r j) (ofRatUp (|(ptFc box s rb.toT l : ℚ)| / 2 ^ rb.P))
      (ofRatUp (ptFr box s rb.toT l))) (List.range n),
    fun r j => sumUp (fun l => upMul ((ptD2 (α := α) n W rb.toT tm l).nb r j)
      (ofRatUp (|(ptFc box s rb.toT l : ℚ)| / 2 ^ rb.P))) (List.range n)⟩

/-- The memoized nodes as packed model matrices (on `Lb`, scale `2^P`). -/
def trN : PMat α := PMat.omega n (nodeMat rb.Lb rm.N)
def trDGi : PMat α := PMat.neg (nodeMat rb.Lb rm.DGi)
def trDN : PMat α := PMat.omega n (nodeMat rb.Lb rm.DN)

/-- The exact products on `Lw`, scale `2^(2P)`, against which the nodes are checked. -/
def trMN : PMat α := PMat.mul n (ptK W rb.toT mm) (ptB Binv W cfg rb.toT eps)
def trMDG : PMat α :=
  PMat.add (PMat.mul (n + n) (nodeMat (α := α) rb.Lb rm.DL).tr (ptK W rb.toT mm))
    (PMat.mul (n + n) (ptK W rb.toT mm).tr (nodeMat rb.Lb rm.DL))
def trMC : PMat α := PMat.mul n (ptB Binv W cfg rb.toT eps) (nodeMat rb.Lb rm.DG)
def trMDGi : PMat α := PMat.mul n (nodeMat rb.Lb rm.C) (ptB Binv W cfg rb.toT eps)
def trMDN : PMat α :=
  PMat.add (PMat.mul n (nodeMat rb.Lb rm.DL) (ptB Binv W cfg rb.toT eps))
    (PMat.mul n (ptK W rb.toT mm) (trDGi rb rm))
def trMXN : PMat α :=
  PMat.add (PMat.mul (n + n) (ptA n W rb.toT tm) (trN n rb rm))
    (PMat.shift (pcUnit rb.Lu.width (zslot n rb.Lu) (2 ^ rb.P)) (PMat.neg (trDN n rb rm)))

/-- `T = Nᵀ (Ω₀ X_N)` and `Y = DH N` on `Lw`, scale `2^(2P)`. -/
def trT : PMat α := PMat.mul (n + n) (trN (α := α) n rb rm).tr (PMat.omega n (nodeMat rb.Lb rm.XN))
def trY : PMat α := PMat.mul (n + n) (ptD1 W rb.toT tm) (trN n rb rm)

/-! ### The checks -/

/-- A node checked on the window (scale `2^(2P)` to `2^P`). -/
def trStage (R C : ℕ) (M : PMat α) (tab : List (List NodeEntry)) : Bool :=
  stageAll n W rb.q rb.lW rb.lR rb.Lw rb.Lb rb.Lu rb.bR (2 * rb.P) rb.P R C M tab

def trStN : Bool := trStage n W rb (n + n) n (trMN n Binv W cfg rb mm eps) rm.N
def trStDL : Bool :=
  stageAll n W rb.q rb.lL rb.lR rb.LL rb.Lb rb.LU0 rb.bR (2 * rb.P) rb.P (n + n) n
    (trDL0 (α := α) n W box s rb tm) rm.DL
def trStDG : Bool := trStage n W rb n n (trMDG (α := α) n W rb mm rm) rm.DG
def trStC : Bool := trStage n W rb n n (trMC n Binv W cfg rb rm eps) rm.C
def trStDGi : Bool := trStage n W rb n n (trMDGi n Binv W cfg rb rm eps) rm.DGi
def trStDN : Bool := trStage n W rb (n + n) n (trMDN n Binv W cfg rb mm rm eps) rm.DN
def trStXN : Bool := trStage n W rb (n + n) n (trMXN (α := α) n W rb tm rm) rm.XN

/-- The averages of `T` against the tables. -/
def trTCheck : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    decide (ptDigit n rb.Lw (2 * rb.P) ((trT (α := α) n rb rm).x i j) =
        (rm.CT.getD i []).getD j (0, 0)) &&
      ble ((trT (α := α) n rb rm).r i j) (ofRatDown ((rm.RT.getD i []).getD j 0))

/-- The averages of `Y` against the tables. -/
def trYCheck : Bool :=
  (List.range n).all fun j =>
    decide (ptDigit n rb.Lw (2 * rb.P) ((trY (α := α) n W rb tm rm).x 0 j) = rm.CY.getD j (0, 0)) &&
      ble ((trY (α := α) n W rb tm rm).r 0 j) (ofRatDown (rm.RY.getD j 0))

/-- The centre table of the bordered average. -/
def trCentre (i j : ℕ) : ℚ × ℚ :=
  if i < n then (if j < n then (rm.CT.getD i []).getD j (0, 0) else (s * (box.getD i (0, 0)).1, 0))
  else (if j < n then rm.CY.getD j (0, 0) else (0, 0))

/-- The radius table of the bordered average. -/
def trRad (i j : ℕ) : ℚ :=
  if i < n then (if j < n then (rm.RT.getD i []).getD j 0 else |s| * (box.getD i (0, 0)).2)
  else (if j < n then rm.RY.getD j 0 else 0)

/-- Layouts: well-formed, compatible, the unit lands on the window, zero keys present. -/
def trLayOk : Bool :=
  layoutWf rb.Lb && layoutWf rb.Lu && layoutWf rb.LU0 && PackLayout.compat n rb.Lb rb.Lb &&
    PackLayout.compat n rb.Lb rb.Lu && PackLayout.compat n rb.Lb rb.LU0 &&
    layoutEq (win rb.Lb rb.Lu) rb.Lw && (rb.Lu.slot (List.replicate n 0)).isSome &&
    (rb.LU0.slot (List.replicate n 0)).isSome && (rb.Lw.slot (List.replicate n 0)).isSome

/-- Loads: the norm guards, every product below the window bound, the averaged slots, the
frequency mantissas. -/
def trNormOk : Bool :=
  normOk W rb.q rb.lK rb.bK rb.Lb && normOk W rb.q rb.lB rb.bB rb.Lb &&
    normOk W rb.q rb.lD rb.bD rb.Lb && normOk W rb.q rb.lA rb.bA rb.Lb &&
    normOk W rb.q rb.lR rb.bR rb.Lb &&
    normOk W rb.q rb.lW (rb.aW + mulLoad rb.Lb rb.Lu rb.bR (2 ^ rb.P)) rb.Lw &&
    normOk W rb.q rb.lL (rb.aL + mulLoad rb.Lb rb.LU0 rb.bR (2 ^ rb.P)) rb.LL &&
    decide (rb.aN n ≤ rb.aW) && decide (rb.aDL n ≤ rb.aL) && decide (rb.aDG n ≤ rb.aW) &&
    decide (rb.aC n ≤ rb.aW) && decide (rb.aDGi n ≤ rb.aW) && decide (rb.aDN n ≤ rb.aW) &&
    decide (rb.aXN n ≤ rb.aW) && decide (2 * rb.aT n < 2 ^ rb.Lw.width) &&
    decide (2 * rb.aY n < 2 ^ rb.Lw.width) &&
    (List.range n).all fun l => decide ((ptFc box s rb.toT l).natAbs ≤ rb.bF)

/-- **The core of the rounded packed torsion check** (everything but the boundary entries). -/
def torsRCore (S : List (List (CC α))) (σTμ : ℚ) : Bool :=
  trLayOk n rb && trNormOk n W box s rb && ptPackOk n Binv cfg rb.toT mm tm &&
    trStN n Binv W cfg rb mm rm eps && trStDL (α := α) n W box s rb tm rm &&
    trStDG (α := α) n W rb mm rm && trStC n Binv W cfg rb rm eps &&
    trStDGi n Binv W cfg rb rm eps && trStDN n Binv W cfg rb mm rm eps &&
    trStXN (α := α) n W rb tm rm && trTCheck (α := α) n rb rm && trYCheck (α := α) n W rb tm rm &&
    tabFinal n cfg rb.P (trCentre n box s rm) (trRad n box s rm) S σTμ

end Defs

/-- **The rounded packed torsion check** at the certificate's data: the packed Gram check (for
`δβ`), the landed jet composition at `cfgLow`, the boundary entries, then the core. -/
def checkTorsionR {n : ℕ} {α : Type} [CertArith α] (bk : PGramBook) (mm : PGramMemo)
    (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo) (c : TorusCertificate n α) : Bool :=
  match gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ, Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
        (torsionSlots n c.ham.jet) with
    | some eps, some ms =>
      rb.P == bk.P && ptEntries n c.emb c.weight c.cfgLow c.piEnc rb.toT tm ms &&
        torsRCore n c.gramInv c.weight c.cfgLow c.freqBox c.params.s rb mm tm rm eps c.torsInv
          (c.params.σT - c.params.μ)
    | _, _ => false
  | none => false

end KAM.CertificateSharp.Packed
