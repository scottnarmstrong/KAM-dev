/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Avg
public import KAM.Certificate.Defs

/-!
# The packed torsion stage: definitions

The landed torsion check (`checkTorsion`, `KAM/Certificate/Defs.lean`) builds the entrywise models
of the bordered torsion (`torsionModels`: ten stages of model-matrix products, each product a
sharded, advice-checked, truncated and rounded model product) and averages them
(`torsionAvgCheck`). `checkTorsionPacked` certifies **the same proposition**
(`checkTorsionPacked_sound`, `TorsSound.lean`) with packed exact arithmetic:

* **boundary** (`ptEntries`): every `D²K` entry is the landed `d2kModel`, every entry of `DX_H ∘ K`
  and of `DH ∘ K` is the landed `dxhModels`/`d1Models` entry at degree `0` (`CertModel.toDeg`), each
  memoized (`PTorsMemo`) and checked by `memoOk`, one entry per declaration if needed; `DK` is the
  Gram check's memo (`PGramMemo`, already checked by `pgEntries`); the witness `B` is packed
  directly; the frequency is a rounded dyadic constant with its rounding in the radius;
* **exact chain** (`PMat`): `N = Ω₀ (L B)`, `D L = Σ_l (s ω)_l ∂_l L`, `DG = D Lᵀ L + Lᵀ D L`,
  `C = B DG`, `DG⁻¹ = -(C B)`, `DN = Ω₀ (D L B + L DG⁻¹)`, `X_N = A N - DN`,
  `T = Nᵀ (Ω₀ X_N)`, `Y = DH N`, with no rounding; scales add (`2^(8P)` for `T`), windows add, and
  sums of different windows or scales go through a power of two at the zero key (`PMat.shift`);
* **radii** (backend, upward): `pmulRad` through every product, with packed weighted norms
  (`PMat.renorm`) where a norm feeds a radius;
* **the averaged test** (`ptFinal`): the zero modes are slot digits (`slotAt`), the centres exact
  rationals, `‖I - S C‖` exact (rows of `ℓ¹` bounds of complex rationals), then the landed
  `avgBoundsOk` with the landed `avgInvRows`.

Every guard (`ptGuard`) is decidable from metadata (`PTorsBook`) and the memo's packing.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- The untrusted metadata of a packed torsion check. -/
structure PTorsBook where
  /-- mantissa scale of the boundary (that of the Gram memo) -/
  P : ℕ
  /-- layouts: `DK` and `D²K`, the witness `B`, the jet slots, the units of the frequency and of
  the two shifts -/
  L1 : PackLayout
  LB : PackLayout
  LA : PackLayout
  LU0 : PackLayout
  LU1 : PackLayout
  LU2 : PackLayout
  /-- load bounds: `DK`, `B`, `D²K`, the jet slots, the frequency mantissas -/
  bK : ℕ
  bB : ℕ
  bD : ℕ
  bA : ℕ
  bF : ℕ
  /-- norm precision and the norm offset exponents of the nodes whose norms feed radii -/
  q : ℕ
  lK : ℕ
  lB : ℕ
  lD : ℕ
  lA : ℕ
  lDL : ℕ
  lN : ℕ
  lDG : ℕ
  lC : ℕ
  lDGi : ℕ
  lXN : ℕ

namespace PTorsBook

variable (tb : PTorsBook) (n : ℕ)

/-- The windows of the chain. -/
def LDL : PackLayout := win tb.L1 tb.LU0
def LN : PackLayout := win tb.L1 tb.LB
def LDG : PackLayout := win tb.LDL tb.L1
def LC : PackLayout := win tb.LB tb.LDG
def LDGi : PackLayout := win tb.LC tb.LB
def LDLB : PackLayout := win tb.LDL tb.LB
def LDN : PackLayout := win tb.L1 tb.LDGi
def LAN : PackLayout := win tb.LA tb.LN
def LT : PackLayout := win tb.LN tb.LDN

/-- The loads of the chain. -/
def aDL : ℕ := n * mulLoad tb.L1 tb.LU0 tb.bD tb.bF
def aN : ℕ := n * mulLoad tb.L1 tb.LB tb.bK tb.bB
def aDG : ℕ :=
  (n + n) * mulLoad tb.LDL tb.L1 (tb.aDL n) tb.bK + (n + n) * mulLoad tb.L1 tb.LDL tb.bK (tb.aDL n)
def aC : ℕ := n * mulLoad tb.LB tb.LDG tb.bB (tb.aDG n)
def aDGi : ℕ := n * mulLoad tb.LC tb.LB (tb.aC n) tb.bB
def aDN : ℕ :=
  mulLoad tb.LDLB tb.LU1 (n * mulLoad tb.LDL tb.LB (tb.aDL n) tb.bB) (2 ^ (3 * tb.P)) +
    n * mulLoad tb.L1 tb.LDGi tb.bK (tb.aDGi n)
def aXN : ℕ := mulLoad tb.LAN tb.LU2 ((n + n) * mulLoad tb.LA tb.LN tb.bA (tb.aN n)) (2 ^ (3 * tb.P)) +
  tb.aDN n
def aT : ℕ := (n + n) * mulLoad tb.LN tb.LDN (tb.aN n) (tb.aXN n)
def aY : ℕ := (n + n) * mulLoad tb.LA tb.LN tb.bA (tb.aN n)

end PTorsBook

/-- The slot of the zero key of a layout (`0` if none). -/
def zslot (n : ℕ) (L : PackLayout) : ℕ := (L.slot (List.replicate n 0)).getD 0

/-- The memoized boundary of the torsion (untrusted, backend-free): the `D²K` entries (index
`(r n + j) n + l`), the entries of `DX_H ∘ K` (index `a (2n) + b`) and of `DH ∘ K` (index `a`). -/
structure PTorsMemo where
  d2 : List MemoEntry
  ax : List MemoEntry
  d1 : List MemoEntry

/-- Layout equality as a Boolean. -/
def layoutEq (L L' : PackLayout) : Bool :=
  L.lo == L'.lo && L.dims == L'.dims && L.stride == L'.stride && L.width == L'.width &&
    L.blockRows == L'.blockRows

/-- The nearest integer (ties up). -/
def ratRound (x : ℚ) : ℤ := ⌊x + 1 / 2⌋

/-- A ball of complex rationals: the `ℓ¹` size `|re| + |im|`. -/
def qAbs1 (z : ℚ × ℚ) : ℚ := |z.1| + |z.2|

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (Binv : List (List (CertPoly α)))
  (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (box : FreqBox) (s : ℚ)
  (tb : PTorsBook) (mm : PGramMemo) (tm : PTorsMemo)

/-- The memo index of the `D²K` entry `(r, j, l)`. -/
def d2Idx (r j l : ℕ) : ℕ := (r * n + j) * n + l

/-! ### The boundary entries -/

/-- One `D²K` entry against the memo. -/
def ptD2Ok (r j l : ℕ) : Bool :=
  memoOk cfg.toMant tb.P (d2kModel n K W pe r j l) (tm.d2.getD (d2Idx n r j l) ([], [], 0))

/-- One entry of `DX_H ∘ K` (at degree `0`) against the memo. -/
def ptAOk (ms : List (CertModel α)) (a b : ℕ) : Bool :=
  memoOk cfg.toMant tb.P (CertModel.toDeg W pe 0 (modelMatrixEntry (dxhModels n ms) a b))
    (tm.ax.getD (a * (n + n) + b) ([], [], 0))

/-- One entry of `DH ∘ K` (at degree `0`) against the memo. -/
def ptD1Ok (ms : List (CertModel α)) (a : ℕ) : Bool :=
  memoOk cfg.toMant tb.P (CertModel.toDeg W pe 0 (modelMatrixEntry (d1Models n ms) 0 a))
    (tm.d1.getD a ([], [], 0))

/-- Every boundary entry of the torsion. -/
def ptEntries (ms : List (CertModel α)) : Bool :=
  ((List.range (n + n)).all fun r => (List.range n).all fun j => (List.range n).all fun l =>
      ptD2Ok n K W cfg pe tb tm r j l) &&
    ((List.range (n + n)).all fun a => (List.range (n + n)).all fun b =>
      ptAOk n W cfg pe tb tm ms a b) &&
    (List.range (n + n)).all fun a => ptD1Ok n W cfg pe tb tm ms a

/-! ### The packed base matrices -/

/-- `L = DK` on `L1` (the Gram memo, scale `2^P`). -/
def ptK : PMat α :=
  ⟨fun r a => ⟨packOf tb.L1 (mm.reAt r a), packOf tb.L1 (mm.imAt r a)⟩,
    fun r a => ofRatUp (mm.radAt r a),
    fun r a => pnorm W tb.q tb.lK tb.L1 tb.P ⟨packOf tb.L1 (mm.reAt r a), packOf tb.L1 (mm.imAt r a)⟩⟩

/-- `G⁻¹` as the witness `B` on `LB` with the radius `eps`. -/
def ptB (eps : α) : PMat α :=
  ⟨fun i k => pcOfPoly cfg.toMant tb.P tb.LB (gramInvPoly Binv i k), fun _ _ => eps,
    fun i k => pnorm W tb.q tb.lB tb.LB tb.P (pcOfPoly cfg.toMant tb.P tb.LB (gramInvPoly Binv i k))⟩

/-- `∂_l L` on `L1` (the torsion memo). -/
def ptD2 (l : ℕ) : PMat α :=
  ⟨fun r j => memoPC tb.L1 (tm.d2.getD (d2Idx n r j l) ([], [], 0)),
    fun r j => ofRatUp (tm.d2.getD (d2Idx n r j l) ([], [], 0)).2.2,
    fun r j => pnorm W tb.q tb.lD tb.L1 tb.P (memoPC tb.L1 (tm.d2.getD (d2Idx n r j l) ([], [], 0)))⟩

/-- The mantissa of the frequency coordinate `(s ω)_l` (the box centre, rounded). -/
def ptFc (l : ℕ) : ℤ := ratRound (s * (box.getD l (0, 0)).1 * 2 ^ tb.P)

/-- The radius of the frequency coordinate: the box and the rounding. -/
def ptFr (l : ℕ) : ℚ :=
  |s| * (box.getD l (0, 0)).2 + |s * (box.getD l (0, 0)).1 - (ptFc box s tb l : ℚ) / 2 ^ tb.P|

/-- The packed frequency coordinate on `LU0`. -/
def ptF (l : ℕ) : PC := pcUnit tb.LU0.width (zslot n tb.LU0) (ptFc box s tb l)

/-- `D L = Σ_l (s ω)_l ∂_l L` on `LDL` (scale `2^(2P)`). -/
def ptDL : PMat α :=
  PMat.renorm W tb.q tb.lDL tb.LDL (2 * tb.P)
    ⟨fun r j => pcSumN (fun l => pcMul ((ptD2 (α := α) n W tb tm l).x r j) (ptF n box s tb l)) n,
      fun r j => sumUp (fun l => pmulRad ((ptD2 n W tb tm l).nb r j) ((ptD2 n W tb tm l).r r j)
        (ofRatUp (|(ptFc box s tb l : ℚ)| / 2 ^ tb.P)) (ofRatUp (ptFr box s tb l))) (List.range n),
      fun _ _ => ofInt 0⟩

/-- `DX_H ∘ K` on `LA` (the torsion memo). -/
def ptA : PMat α :=
  ⟨fun a b => memoPC tb.LA (tm.ax.getD (a * (n + n) + b) ([], [], 0)),
    fun a b => ofRatUp (tm.ax.getD (a * (n + n) + b) ([], [], 0)).2.2,
    fun a b => pnorm W tb.q tb.lA tb.LA tb.P (memoPC tb.LA (tm.ax.getD (a * (n + n) + b) ([], [], 0)))⟩

/-- `DH ∘ K` (one row) on `LA` (the torsion memo). -/
def ptD1 : PMat α :=
  ⟨fun _ a => memoPC tb.LA (tm.d1.getD a ([], [], 0)), fun _ a => ofRatUp (tm.d1.getD a ([], [], 0)).2.2,
    fun _ a => pnorm W tb.q tb.lA tb.LA tb.P (memoPC tb.LA (tm.d1.getD a ([], [], 0)))⟩

/-! ### The chain -/

variable (eps : α)

/-- `N = Ω₀ (L B)` on `LN` (scale `2^(2P)`). -/
def ptN : PMat α :=
  PMat.renorm W tb.q tb.lN tb.LN (2 * tb.P)
    (PMat.omega n (PMat.mul n (ptK W tb mm) (ptB Binv W cfg tb eps)))

/-- `DG = D Lᵀ L + Lᵀ D L` on `LDG` (scale `2^(3P)`). -/
def ptDG : PMat α :=
  PMat.renorm W tb.q tb.lDG tb.LDG (3 * tb.P)
    (PMat.add (PMat.mul (n + n) (ptDL n W box s tb tm).tr (ptK W tb mm))
      (PMat.mul (n + n) (ptK W tb mm).tr (ptDL n W box s tb tm)))

/-- `C = B DG` on `LC` (scale `2^(4P)`). -/
def ptC : PMat α :=
  PMat.renorm W tb.q tb.lC tb.LC (4 * tb.P)
    (PMat.mul n (ptB Binv W cfg tb eps) (ptDG n W box s tb mm tm))

/-- `DG⁻¹ = -(C B)` on `LDGi` (scale `2^(5P)`). -/
def ptDGi : PMat α :=
  PMat.neg (PMat.renorm W tb.q tb.lDGi tb.LDGi (5 * tb.P)
    (PMat.mul n (ptC n Binv W cfg box s tb mm tm eps) (ptB Binv W cfg tb eps)))

/-- The unit `2^(3P)` at the zero key of a shift layout. -/
def ptU (L : PackLayout) : PC := pcUnit L.width (zslot n L) (2 ^ (3 * tb.P))

/-- `DN = Ω₀ (D L B + L DG⁻¹)` on `LDN` (scale `2^(6P)`). -/
def ptDN : PMat α :=
  PMat.omega n (PMat.add
    (PMat.shift (ptU n tb tb.LU1) (PMat.mul n (ptDL n W box s tb tm) (ptB Binv W cfg tb eps)))
    (PMat.mul n (ptK W tb mm) (ptDGi n Binv W cfg box s tb mm tm eps)))

/-- `X_N = A N - DN` on `LDN` (scale `2^(6P)`). -/
def ptXN : PMat α :=
  PMat.renorm W tb.q tb.lXN tb.LDN (6 * tb.P)
    (PMat.add (PMat.shift (ptU n tb tb.LU2)
        (PMat.mul (n + n) (ptA n W tb tm) (ptN n Binv W cfg tb mm eps)))
      (PMat.neg (ptDN n Binv W cfg box s tb mm tm eps)))

/-- `T = Nᵀ (Ω₀ X_N)` on `LT` (scale `2^(8P)`). -/
def ptT : PMat α :=
  PMat.mul (n + n) (ptN n Binv W cfg tb mm eps).tr
    (PMat.omega n (ptXN n Binv W cfg box s tb mm tm eps))

/-- `Y = DH N` on `LAN` (scale `2^(3P)`). -/
def ptY : PMat α := PMat.mul (n + n) (ptD1 W tb tm) (ptN n Binv W cfg tb mm eps)

/-! ### The averaged test -/

/-- The zero mode of a packed entry at scale `2^e`, as complex rational. -/
def ptDigit (L : PackLayout) (e : ℕ) (x : PC) : ℚ × ℚ :=
  ((slotAt L.width (zslot n L) x.re : ℚ) / 2 ^ e, (slotAt L.width (zslot n L) x.im : ℚ) / 2 ^ e)

/-- The centre of the average of the bordered torsion entry `(i, j)`. -/
def ptCentre (i j : ℕ) : ℚ × ℚ :=
  if i < n then
    (if j < n then ptDigit n tb.LT (8 * tb.P) ((ptT n Binv W cfg box s tb mm tm eps).x i j)
      else (s * (box.getD i (0, 0)).1, 0))
  else
    (if j < n then ptDigit n tb.LAN (3 * tb.P) ((ptY n Binv W cfg tb mm tm eps).x 0 j)
      else (0, 0))

/-- The radius of the average of the bordered torsion entry `(i, j)`. -/
def ptRad (i j : ℕ) : α :=
  if i < n then
    (if j < n then (ptT n Binv W cfg box s tb mm tm eps).r i j
      else ofRatUp (|s| * (box.getD i (0, 0)).2))
  else
    (if j < n then (ptY n Binv W cfg tb mm tm eps).r 0 j else ofInt 0)

/-- The exact value of a witness entry (`(0, 0)` if it does not decode). -/
def ptSq (S : List (List (CC α))) (i l : ℕ) : ℚ × ℚ :=
  match certMantPair cfg.toMant tb.P (ccEntry S i l) with
  | some z => ((z.1 : ℚ) / 2 ^ tb.P, (z.2 : ℚ) / 2 ^ tb.P)
  | none => (0, 0)

/-- Every witness entry decodes. -/
def ptSOk (S : List (List (CC α))) : Bool :=
  (List.range (n + 1)).all fun i => (List.range (n + 1)).all fun l =>
    (certMantPair cfg.toMant tb.P (ccEntry S i l)).isSome

/-- The entry `(i, j)` of `I - S C` (exact). -/
def ptDef (S : List (List (CC α))) (i j : ℕ) : ℚ × ℚ :=
  ((if i = j then 1 else 0) - ∑ l ∈ Finset.range (n + 1),
      ((ptSq cfg tb S i l).1 * (ptCentre n Binv W cfg box s tb mm tm eps l j).1 -
        (ptSq cfg tb S i l).2 * (ptCentre n Binv W cfg box s tb mm tm eps l j).2),
    -∑ l ∈ Finset.range (n + 1),
      ((ptSq cfg tb S i l).1 * (ptCentre n Binv W cfg box s tb mm tm eps l j).2 +
        (ptSq cfg tb S i l).2 * (ptCentre n Binv W cfg box s tb mm tm eps l j).1))

/-- Upper bounds of the rows of `I - S C`. -/
def ptDRows (S : List (List (CC α))) : List α :=
  List.ofFn fun i : Fin (n + 1) =>
    ofRatUp (∑ j ∈ Finset.range (n + 1), qAbs1 (ptDef n Binv W cfg box s tb mm tm eps S i.val j))

/-- The rows of the radius matrix. -/
def ptRRows : List α :=
  List.ofFn fun i : Fin (n + 1) =>
    sumUp (fun j : Fin (n + 1) => ptRad n Binv W cfg box s tb mm tm eps i.val j.val)
      (List.finRange (n + 1))

/-- The final test: `S` has the bordered shape and decodes, and the landed `avgBoundsOk` holds on
the packed rows. -/
def ptFinal (S : List (List (CC α))) (σTμ : ℚ) : Bool :=
  listShapeOk (n + 1) S && ptSOk n cfg tb S &&
    avgBoundsOk (ptDRows n Binv W cfg box s tb mm tm eps S) (avgInvRows n S)
      (ptRRows n Binv W cfg box s tb mm tm eps) σTμ

/-! ### The guard -/

/-- Layouts: well-formed inputs, compatible products, the shifts land on `LDN`, `DG`'s two terms
on one window, zero keys present. -/
def ptLayOk : Bool :=
  layoutWf tb.L1 && layoutWf tb.LB && layoutWf tb.LA && layoutWf tb.LU0 && layoutWf tb.LU1 &&
    layoutWf tb.LU2 &&
    PackLayout.compat n tb.L1 tb.LU0 && PackLayout.compat n tb.L1 tb.LB &&
    PackLayout.compat n tb.LDL tb.L1 && PackLayout.compat n tb.L1 tb.LDL &&
    PackLayout.compat n tb.LB tb.LDG && PackLayout.compat n tb.LC tb.LB &&
    PackLayout.compat n tb.LDL tb.LB && PackLayout.compat n tb.LDLB tb.LU1 &&
    PackLayout.compat n tb.L1 tb.LDGi && PackLayout.compat n tb.LA tb.LN &&
    PackLayout.compat n tb.LAN tb.LU2 && PackLayout.compat n tb.LN tb.LDN &&
    layoutEq (win tb.L1 tb.LDL) tb.LDG && layoutEq (win tb.LDLB tb.LU1) tb.LDN &&
    layoutEq (win tb.LAN tb.LU2) tb.LDN &&
    (tb.LU0.slot (List.replicate n 0)).isSome && (tb.LU1.slot (List.replicate n 0)).isSome &&
    (tb.LU2.slot (List.replicate n 0)).isSome && (tb.LT.slot (List.replicate n 0)).isSome &&
    (tb.LAN.slot (List.replicate n 0)).isSome

/-- Loads: the norm guards of the nodes whose norms feed radii, the slot bounds of the two
averaged nodes, and the frequency mantissas. -/
def ptNormOk : Bool :=
  normOk W tb.q tb.lK tb.bK tb.L1 && normOk W tb.q tb.lB tb.bB tb.LB &&
    normOk W tb.q tb.lD tb.bD tb.L1 && normOk W tb.q tb.lA tb.bA tb.LA &&
    normOk W tb.q tb.lDL (tb.aDL n) tb.LDL && normOk W tb.q tb.lN (tb.aN n) tb.LN &&
    normOk W tb.q tb.lDG (tb.aDG n) tb.LDG && normOk W tb.q tb.lC (tb.aC n) tb.LC &&
    normOk W tb.q tb.lDGi (tb.aDGi n) tb.LDGi && normOk W tb.q tb.lXN (tb.aXN n) tb.LDN &&
    decide (2 * tb.aT n < 2 ^ tb.LT.width) && decide (2 * tb.aY n < 2 ^ tb.LAN.width) &&
    (List.range n).all fun l => decide ((ptFc box s tb l).natAbs ≤ tb.bF)

/-- The packing of every boundary entry. -/
def ptPackOk : Bool :=
  ((List.range (n + n)).all fun r => (List.range n).all fun a =>
      packRepOk tb.L1 (mm.reAt r a) tb.bK && packRepOk tb.L1 (mm.imAt r a) tb.bK) &&
    ((List.range n).all fun i => (List.range n).all fun k =>
      pcOfPolyOk cfg.toMant tb.P tb.LB tb.bB (gramInvPoly Binv i k)) &&
    ((List.range (n + n)).all fun r => (List.range n).all fun j => (List.range n).all fun l =>
      memoPackOk tb.L1 tb.bD (tm.d2.getD (d2Idx n r j l) ([], [], 0))) &&
    ((List.range (n + n)).all fun a => (List.range (n + n)).all fun b =>
      memoPackOk tb.LA tb.bA (tm.ax.getD (a * (n + n) + b) ([], [], 0))) &&
    (List.range (n + n)).all fun a => memoPackOk tb.LA tb.bA (tm.d1.getD a ([], [], 0))

/-- **The core of the packed torsion check** (everything but the boundary entries). -/
def torsPackedCore (S : List (List (CC α))) (σTμ : ℚ) : Bool :=
  ptLayOk n tb && ptNormOk n W box s tb && ptPackOk n Binv cfg tb mm tm &&
    ptFinal n Binv W cfg box s tb mm tm eps S σTμ

end Defs

/-- **The packed torsion check** at the certificate's data: the packed Gram check (for `δβ`), the
landed jet composition at `cfgLow`, the boundary entries, then the core. -/
def checkTorsionPacked {n : ℕ} {α : Type} [CertArith α] (bk : PGramBook) (mm : PGramMemo)
    (tb : PTorsBook) (tm : PTorsMemo) (c : TorusCertificate n α) : Bool :=
  match gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ, Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
        (torsionSlots n c.ham.jet) with
    | some eps, some ms =>
      tb.P == bk.P && ptEntries n c.emb c.weight c.cfgLow c.piEnc tb tm ms &&
        torsPackedCore n c.gramInv c.weight c.cfgLow c.freqBox c.params.s tb mm tm eps c.torsInv
          (c.params.σT - c.params.μ)
    | _, _ => false
  | none => false

end KAM.CertificateSharp.Packed
