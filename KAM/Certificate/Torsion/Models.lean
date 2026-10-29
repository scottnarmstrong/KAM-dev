/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Torsion.Frame
public import KAM.Certificate.Expr.Compose
public import KAM.Certificate.Expr.Diff
public import KAM.Certificate.Freq
public import KAM.Certificate.Model.Inv

/-!
# The models of the bordered torsion

`torsionModels` builds the entrywise models of the LITERAL frozen
`extendedTorsion e.eval (K.eval n) (s ω)` on `T_ρ`, valid for every `ω` in the frequency box
(SO design §1.9, finding F3), from matrices of models (`modelMatMul`, `modelMatAdd`,
`modelMatNeg`, `modelMatTranspose`, `modelMatOmega`):

* `L = DK` (`dkModels`, the Gram check's `DK` entries) and `D_{sω} L = Σ_l (sω)_l ∂_l L`
  (`dkwModels`, second derivatives `CertModel.ofDeriv2`, the frequency balls `freqModel`);
* `G⁻¹` as the Gram witness `B` with the certified radius `δβ/(1 - δ)` (`gramInvModels`,
  `gramInvRadius`, `1/(1 - δ)` through `recipOneSubUp`);
* `N = Ω₀ (L G⁻¹)`, `DG = D L ᵀ L + Lᵀ D L`, `D(G⁻¹) = -(G⁻¹ DG G⁻¹)`,
  `DN = Ω₀ (D L G⁻¹ + L D(G⁻¹))` (`fderiv_normalMat_apply`);
* `DX_H ∘ K` from the jet slots `∂_{a.swap} ∂_b H` composed with `K` (`Slp.compose`, sign
  `hamSign a`), `X_N = (DX_H ∘ K) N - DN`, the block `Nᵀ (Ω₀ X_N)`;
* the border column `(s ω)_a` (`freqModel`), the last row `(∂_a H ∘ K) N` and the corner `0`.

Product keys `[4, t, i, j, k]` (`t = 0, …, 10`). Contract: `torsionModels_sound`.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus CertArith

section Defs

variable {α : Type} [CertArith α]

/-- A list matrix from an entry function (`r` rows, `c` columns). -/
def buildMat (r c : ℕ) (f : ℕ → ℕ → CertModel α) : ModelMatrix α :=
  (List.range r).map fun i => (List.range c).map fun j => f i j

/-- Exact negation of a model. -/
def CertModel.negM (a : CertModel α) : CertModel α := ⟨a.deg, a.poly.negP, a.rad⟩

/-- The product `A B` of model matrices (`r × m` times `m × c`): every entry is a balanced sum
of products at the keys `key ++ [i, j, k]`, re-expressed at degree `0`. -/
def modelMatMul (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (key : ProductKey)
    (r m c : ℕ) (A B : ModelMatrix α) : ModelMatrix α :=
  buildMat r c fun i j => CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun k : Fin m =>
    CertModel.mul W cfg (key ++ [i, j, k.val]) (modelMatrixEntry A i k.val)
      (modelMatrixEntry B k.val j)))

/-- The entrywise sum of model matrices. -/
def modelMatAdd (W : CertWeight) (pe : PiEnclosure α) (r c : ℕ) (A B : ModelMatrix α) :
    ModelMatrix α :=
  buildMat r c fun i j => CertModel.addMixed W pe (modelMatrixEntry A i j) (modelMatrixEntry B i j)

/-- The entrywise negation of a model matrix. -/
def modelMatNeg (r c : ℕ) (A : ModelMatrix α) : ModelMatrix α :=
  buildMat r c fun i j => (modelMatrixEntry A i j).negM

/-- The transpose of an `r × c` model matrix. -/
def modelMatTranspose (r c : ℕ) (A : ModelMatrix α) : ModelMatrix α :=
  buildMat c r fun i j => modelMatrixEntry A j i

/-- `Ω₀` applied to the rows of a `2n × c` model matrix: row `i < n` is minus row `n + i`, row
`n + i` is row `i`. -/
def modelMatOmega (n c : ℕ) (A : ModelMatrix α) : ModelMatrix α :=
  buildMat (n + n) c fun i j =>
    if i < n then (modelMatrixEntry A (n + i) j).negM else modelMatrixEntry A (i - n) j

/-- The model of a constant `x` with `|x - c| ≤ r` (rational centre and radius). -/
def ballModel (n : ℕ) (c r : ℚ) : CertModel α :=
  ⟨0, (constModel n c 0 0 : CertModel α).poly,
    upAdd (constModel n c 0 0 : CertModel α).rad (ofRatUp r)⟩

/-- The model of the coordinate `l` of `s ω`, for every `ω` in the box. -/
def freqModel (n : ℕ) (box : FreqBox) (s : ℚ) (l : ℕ) : CertModel α :=
  ballModel n (s * (box.getD l (0, 0)).1) (|s| * (box.getD l (0, 0)).2)

/-- `L = DK` (`2n × n`): the angle rows, then the action rows. -/
def dkModels (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α) :
    ModelMatrix α :=
  buildMat (n + n) n fun i j =>
    if i < n then dkAngleModel n K W pe i j else dkActionModel n K W pe (i - n) j

/-- The second partial `∂_l L_{ij}` at degree `0`. -/
def d2kModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α)
    (i j l : ℕ) : CertModel α :=
  if i < n then
    CertModel.toDeg W pe 0 (CertModel.ofDeriv2 W j l (K.angleDeg.getD i 0)
      (realCompPoly n K.angle[i]?))
  else
    CertModel.toDeg W pe 0 (CertModel.ofDeriv2 W j l (K.actionDeg.getD (i - n) 0)
      (realCompPoly n K.action[i - n]?))

/-- `D_{sω} L = Σ_l (sω)_l ∂_l L` (`2n × n`) for every `ω` in the box (scalar products: the
frequency factor is a constant model). -/
def dkwModels (n : ℕ) (K : CertEmbedding α) (box : FreqBox) (s : ℚ) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) : ModelMatrix α :=
  buildMat (n + n) n fun i j => CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun l : Fin n =>
    CertModel.mul W cfg [4, 10, i, j, l.val] (freqModel n box s l.val)
      (d2kModel n K W pe i j l.val)))

/-- The radius `δβ/(1 - δ)` of `G⁻¹ - B`, rounded upward (`none` unless `0 ≤ δ < 1`, `0 ≤ β`). -/
def gramInvRadius (δβ : α × α) : Option α :=
  if ble (ofInt 0) δβ.1 && ble (ofInt 0) δβ.2 && blt δβ.1 (ofInt 1) then
    (recipOneSubUp δβ.1).map fun t => upMul (upMul δβ.1 δβ.2) t
  else none

/-- `G⁻¹` (`n × n`): the witness `B` with the certified radius `eps`. -/
def gramInvModels (n : ℕ) (B : List (List (CertPoly α))) (eps : α) : ModelMatrix α :=
  buildMat n n fun k j => ⟨0, gramInvPoly B k j, eps⟩

/-- The jet slots read by the torsion: `∂_a H` (`a < 2n`), then `∂_a ∂_b H` (row-major,
`a, b < 2n`). -/
def torsionSlots (n : ℕ) (J : HamJet) : List ℕ :=
  (List.range (n + n)).map (fun a => J.d1.getD a 0) ++
    List.ofFn fun q : Fin ((n + n) * (n + n)) =>
      (J.d2.getD (q.val / (n + n)) []).getD (q.val % (n + n)) 0

/-- The phase index of the swapped coordinate: `a ↦ a + n` (`a < n`), `a ↦ a - n` otherwise. -/
def swapNat (n a : ℕ) : ℕ := if a < n then a + n else a - n

/-- `DX_H ∘ K` (`2n × 2n`): entry `(a, b)` is `± ∂_{a'} ∂_b H ∘ K` with `a' = swapNat n a`,
sign `+` for `a < n` (`hamSign`). -/
def dxhModels (n : ℕ) (ms : List (CertModel α)) : ModelMatrix α :=
  buildMat (n + n) (n + n) fun a b =>
    if a < n then ms.getD (n + n + (n + n) * swapNat n a + b) zeroModel
    else (ms.getD (n + n + (n + n) * swapNat n a + b) zeroModel).negM

/-- The row `∂_a H ∘ K` (`1 × 2n`). -/
def d1Models (n : ℕ) (ms : List (CertModel α)) : ModelMatrix α :=
  buildMat 1 (n + n) fun _ a => ms.getD a zeroModel

/-- Entrywise models of `extendedTorsion H K (s ω)` on `T_ρ` for EVERY `ω` in the box: the block
`torsion` from `DX_H ∘ K` (jet `d2` composed with `K`), the normal frame `N = Ω₀ DK B` with the
Gram witness `B` and the certified radius `δβ/(1 - δ)`, `DN[sω] = Ω₀ (D²K[sω] G⁻¹ + DK D(G⁻¹)[sω])`
with `D(G⁻¹)[sω] = -G⁻¹ (DG[sω]) G⁻¹`; the border column `s ω` from the box (ball); the last row
`DH(K) N` (jet `d1` composed with `K`). -/
def torsionModels {α : Type} [CertArith α] (n : ℕ) (e : HamExpr n) (K : CertEmbedding α)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (δβ : α × α) (box : FreqBox) (s : ℚ)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) : Option (ModelMatrix α) :=
  match gramInvRadius δβ, Slp.compose n e.jet.prog K wit W cfg pe (torsionSlots n e.jet) with
  | some eps, some ms =>
    let L := dkModels n K W pe
    let Gi := gramInvModels n Binv eps
    let DL := dkwModels n K box s W cfg pe
    let N := modelMatOmega n n (modelMatMul W cfg pe [4, 0] (n + n) n n L Gi)
    let DG := modelMatAdd W pe n n
      (modelMatMul W cfg pe [4, 1] n (n + n) n (modelMatTranspose (n + n) n DL) L)
      (modelMatMul W cfg pe [4, 2] n (n + n) n (modelMatTranspose (n + n) n L) DL)
    let DGi := modelMatNeg n n
      (modelMatMul W cfg pe [4, 4] n n n (modelMatMul W cfg pe [4, 3] n n n Gi DG) Gi)
    let DN := modelMatOmega n n (modelMatAdd W pe (n + n) n
      (modelMatMul W cfg pe [4, 5] (n + n) n n DL Gi)
      (modelMatMul W cfg pe [4, 6] (n + n) n n L DGi))
    let XN := modelMatAdd W pe (n + n) n
      (modelMatMul W cfg pe [4, 7] (n + n) (n + n) n (dxhModels n ms) N) (modelMatNeg (n + n) n DN)
    let Tb := modelMatMul W cfg pe [4, 8] n (n + n) n (modelMatTranspose (n + n) n N)
      (modelMatOmega n n XN)
    let Y := modelMatMul W cfg pe [4, 9] 1 (n + n) n (d1Models n ms) N
    some (buildMat (n + 1) (n + 1) fun i j =>
      if i < n then (if j < n then modelMatrixEntry Tb i j else freqModel n box s i)
      else (if j < n then modelMatrixEntry Y 0 j else zeroModel))
  | _, _ => none

end Defs

end KAM.Certificate

end
