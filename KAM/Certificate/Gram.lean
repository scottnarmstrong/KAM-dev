/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.ComposeModels
public import KAM.Certificate.MatrixInv
public import KAM.Frozen.Defs.GramMatrix
public import KAM.Matrix.Norms

/-!
# The Gram check

The Gram matrix `G = DKᵀ DK` (bilinear, `dotℂ`) of a certified embedding, its entrywise models,
and the certificate of its inverse from an approximate inverse witness `B` (SO design §1.8):

* `dkAngleModel`, `dkActionModel`: the entries `∂_j K_{1,i} = δ_ij + ∂_j((2π)^{dU_i} U_i)` and
  `∂_j K_{2,i} = ∂_j((2π)^{dA_i} A_i)` of `DK` as degree-`0` models (exact derivatives, then
  `toDeg 0`), with their contracts `dkAngleModel_encloses`, `dkActionModel_encloses`;
* `modelSum`: a balanced sum of models (pairwise rounds), contract `modelSum_encloses`;
* `gramModels`: the upper triangle `a ≤ b` of `G`, each entry `Σ_r DK_{ra} DK_{rb}` over the
  `2n` rows (angles, then actions) with product keys `[3, 0, a, b, r]`; the lower triangle reads
  the same models (`G` is symmetric). Contract `gramModels_sound`;
* `gramCheck`: the models of `B G` (product keys `[3, 1, i, j, k]`, `B_ik` exact), the row sums
  `δ` of `sup_{T_ρ} |(I - B G)_ij|` (diagonal through `oneSubSupUp`) and `β` of `|B_ij|_w`, and the
  tests `δ < 1`, `β/(1 - δ) ≤ σB - μ` (in the form `β + σ δ ≤ σ`). Contract `gramCheck_sound`:
  through `matrix_inv_of_approx_inverse` at every point of the strip, `G` is invertible, its
  inverse has row sums `≤ σB - μ`, and `‖G⁻¹ - B‖ ≤ δβ/(1 - δ)` (row-sum norm).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Certificate

open KAM CertArith

/-- A matrix of models (row-major), e.g. the Gram matrix or its approximate inverse. -/
abbrev ModelMatrix (α : Type) : Type := List (List (CertModel α))

/-- Entrywise enclosure of a matrix-valued function on `T_ρ`; every entry must be present (no
backend default model, finding F2). -/
def ModelMatrix.Encloses {α : Type} [CertArith α] (n : ℕ) {ι : Type*} (idx : ι → ℕ) (ρ : ℝ)
    (M : ModelMatrix α) (F : (Fin n → ℂ) → Matrix ι ι ℂ) : Prop :=
  ∀ i j, ∃ m : CertModel α, (M[idx i]?.bind fun r => r[idx j]?) = some m ∧
    m.Encloses n ρ (fun θ => F θ i j)

/-- The matrix of a polynomial-matrix witness (missing entries `0`). -/
def polyMatrix {α : Type} [CertArith α] (n : ℕ) (B : List (List (CertPoly α))) (θ : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (((B[i.val]?).bind fun r => r[j.val]?).map fun P => P.eval n θ).getD 0

section Defs

variable {α : Type} [CertArith α]

/-- `a + b` at the degree of `a` (`b` re-expressed by `toDeg`; a no-op at equal degrees). -/
def CertModel.addMixed (W : CertWeight) (pe : PiEnclosure α) (a b : CertModel α) :
    CertModel α :=
  CertModel.add W a (CertModel.toDeg W pe a.deg b)

/-- One round of pairwise model sums: `[a, b, c, d, e] ↦ [a + b, c + d, e]`. -/
def modelSumPairs (W : CertWeight) (pe : PiEnclosure α) : List (CertModel α) → List (CertModel α)
  | a :: b :: rest => CertModel.addMixed W pe a b :: modelSumPairs W pe rest
  | l => l

/-- `r` rounds of `modelSumPairs`. -/
def modelSumRounds (W : CertWeight) (pe : PiEnclosure α) :
    ℕ → List (CertModel α) → List (CertModel α)
  | 0, l => l
  | r + 1, l => modelSumRounds W pe r (modelSumPairs W pe l)

/-- The sum of a list of models as a balanced tree (64 rounds of pairwise sums, then a left fold
of what remains); the zero model for the empty list. -/
def modelSum (W : CertWeight) (pe : PiEnclosure α) (L : List (CertModel α)) : CertModel α :=
  match modelSumRounds W pe 64 L with
  | [] => zeroModel
  | a :: rest => rest.foldl (CertModel.addMixed W pe) a

/-- The polynomial of an optional real component (`0` if missing), in canonical order. -/
def realCompPoly (n : ℕ) : Option (CertRealPoly α) → CertPoly α
  | some P => P.toSortedPoly n
  | none => ⟨[]⟩

/-- The derivative `∂_j ((2π)^d P)` of an optional real component, as a degree-`0` model. -/
def compDerivModel (n : ℕ) (W : CertWeight) (pe : PiEnclosure α) (d : ℤ)
    (P : Option (CertRealPoly α)) (j : ℕ) : CertModel α :=
  CertModel.toDeg W pe 0 (CertModel.ofDeriv W j d (realCompPoly n P))

/-- The entry `∂_j K_{1,i} = δ_ij + ∂_j((2π)^{dU_i} U_i)` of `DK` (angle row `i`), degree `0`. -/
def dkAngleModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α)
    (i j : ℕ) : CertModel α :=
  if i = j then
    CertModel.add W (constModel n 1 0 0) (compDerivModel n W pe (K.angleDeg.getD i 0) K.angle[i]? j)
  else compDerivModel n W pe (K.angleDeg.getD i 0) K.angle[i]? j

/-- The entry `∂_j K_{2,i} = ∂_j((2π)^{dA_i} A_i)` of `DK` (action row `i`), degree `0`. -/
def dkActionModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α)
    (i j : ℕ) : CertModel α :=
  compDerivModel n W pe (K.actionDeg.getD i 0) K.action[i]? j

/-- The Gram entry `G_ab = Σ_r DK_{ra} DK_{rb}` over the angle rows, then the action rows
(product key `[3, 0, a, b, r]`), summed as a balanced tree. -/
def gramEntryModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (cfg : ModelConfig α)
    (pe : PiEnclosure α) (a b : ℕ) : CertModel α :=
  modelSum W pe
    (List.ofFn (fun k : Fin n => CertModel.mul W cfg [3, 0, a, b, k.val]
        (dkAngleModel n K W pe k.val a) (dkAngleModel n K W pe k.val b)) ++
      List.ofFn (fun k : Fin n => CertModel.mul W cfg [3, 0, a, b, n + k.val]
        (dkActionModel n K W pe k.val a) (dkActionModel n K W pe k.val b)))

/-- The Gram models `DKᵀ DK` (bilinear, `dotℂ`), computed at reduced precision. -/
def gramModels {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) : ModelMatrix α :=
  (List.range n).map fun a => (List.range n).map fun b =>
    if a ≤ b then gramEntryModel n K W cfg pe a b else gramEntryModel n K W cfg pe b a

/-- The entry `(i, j)` of a list matrix of models (the zero model if missing). -/
def modelMatrixEntry (M : ModelMatrix α) (i j : ℕ) : CertModel α :=
  ((M[i]?).bind fun r => r[j]?).getD zeroModel

/-- The entry `(i, k)` of the witness `B` (the zero polynomial if missing, as `polyMatrix`). -/
def gramInvPoly (B : List (List (CertPoly α))) (i k : ℕ) : CertPoly α :=
  ((B[i]?).bind fun r => r[k]?).getD ⟨[]⟩

/-- The model of `(B G)_ij = Σ_k B_ik G_kj` (product key `[3, 1, i, j, k]`, `B_ik` exact),
at degree `0`. -/
def gramBGModel (n : ℕ) (B : List (List (CertPoly α))) (G : ModelMatrix α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (i j : ℕ) : CertModel α :=
  CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun k : Fin n =>
    CertModel.mul W cfg [3, 1, i, j, k.val] ⟨0, gramInvPoly B i k.val, ofInt 0⟩
      (modelMatrixEntry G k.val j)))

/-- An upper bound of `sup_{T_ρ} |δ_ij - u|` for a degree-`0` model `u`: `oneSubSupUp` on the
diagonal, `|P|_w + rad` off it. -/
def gramDefectUp (W : CertWeight) (i j : ℕ) (u : CertModel α) : α :=
  if i = j then oneSubSupUp W u else upAdd (u.poly.supNormUp W) u.rad

/-- A candidate maximum of a list (each entry is re-checked against it by `ble`). -/
def maxCandidate (L : List α) : α := L.foldr (fun a b => if ble a b then b else a) (ofInt 0)

/-- The row sums of `sup |I - B G|` (entrywise bounds). -/
def gramDefectRows (n : ℕ) (B : List (List (CertPoly α))) (G : ModelMatrix α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) : List α :=
  List.ofFn fun i : Fin n =>
    sumUp (fun j : Fin n => gramDefectUp W i.val j.val (gramBGModel n B G W cfg pe i.val j.val))
      (List.finRange n)

/-- The row sums of `|B_ij|_w`. -/
def gramInvRows (n : ℕ) (B : List (List (CertPoly α))) (W : CertWeight) : List α :=
  List.ofFn fun i : Fin n =>
    sumUp (fun j : Fin n => (gramInvPoly B i.val j.val).supNormUp W) (List.finRange n)

/-- The exact `n × n` shape of the witness (fail closed otherwise). -/
def gramInvShapeOk (n : ℕ) (B : List (List (CertPoly α))) : Bool :=
  B.length == n && B.all fun r => r.length == n

/-- The final tests on `(δ, β)`: every row sum is below them, `0 ≤ δ < 1`, `0 ≤ σ` and
`β + σ δ ≤ σ` (that is `β/(1 - δ) ≤ σ`), rounded outward. -/
def gramBoundsOk (dRows bRows : List α) (δ β : α) (σBμ : ℚ) : Bool :=
  dRows.all (fun r => ble r δ) && bRows.all (fun r => ble r β) && blt δ (ofInt 1) &&
    ble (ofInt 0) δ && decide (0 ≤ σBμ) &&
    ble (upAdd β (upMul (ofRatUp σBμ) δ)) (ofRatDown σBμ)

/-- Gram check: with the witness `B ≈ G⁻¹`, `sup_{T_ρ}` row sums of `I - B G` give `δ < 1`,
`β ≥ sup ‖B‖`, and `β/(1 - δ) ≤ σB - μ`. Returns the certified `(δ, β)`. -/
def gramCheck {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (Binv : List (List
    (CertPoly α))) (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (σBμ : ℚ) :
    Option (α × α) :=
  if gramInvShapeOk n Binv then
    let dRows := gramDefectRows n Binv (gramModels n K W cfg pe) W cfg pe
    let bRows := gramInvRows n Binv W
    if gramBoundsOk dRows bRows (maxCandidate dRows) (maxCandidate bRows) σBμ then
      some (maxCandidate dRows, maxCandidate bRows)
    else none
  else none

end Defs

end KAM.Certificate
