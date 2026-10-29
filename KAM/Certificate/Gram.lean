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

/-! ### Contracts -/

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α]

omit [LawfulCertArith α] in
theorem CertModel.Encloses.of_eq {n : ℕ} {ρ : ℝ} {m : CertModel α} {f g : (Fin n → ℂ) → ℂ}
    (h : m.Encloses n ρ f) (hfg : ∀ θ, f θ = g θ) : m.Encloses n ρ g := by
  rwa [← funext hfg]

theorem CertModel.Encloses.addMixed {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    {a b : CertModel α} {f g : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f)
    (hb : b.Encloses n W.rho g) : (CertModel.addMixed W pe a b).Encloses n W.rho (f + g) :=
  CertModel.Encloses.add hW ha (hb.toDeg hW hpe a.deg) (toDeg_deg W pe a.deg b).symm

section ModelSum

variable {n : ℕ} {W : CertWeight} {s N : ℕ} {pe : PiEnclosure α}

/-- Pairs of a model and the function it encloses. -/
abbrev EnclosedList (α : Type) (n : ℕ) : Type := List (CertModel α × ((Fin n → ℂ) → ℂ))

theorem modelSumPairs_spec (hW : checkWeight W s N = true) (hpe : checkPiEnclosure pe = true) :
    ∀ L : EnclosedList α n, (∀ p ∈ L, p.1.Encloses n W.rho p.2) →
    ∃ L' : EnclosedList α n, (∀ p ∈ L', p.1.Encloses n W.rho p.2) ∧
      modelSumPairs W pe (L.map Prod.fst) = L'.map Prod.fst ∧
      ∀ θ, (L'.map fun p => p.2 θ).sum = (L.map fun p => p.2 θ).sum
  | [], _ => ⟨[], by simp, rfl, fun _ => rfl⟩
  | [a], h => ⟨[a], h, rfl, fun _ => rfl⟩
  | a :: b :: rest, h => by
    obtain ⟨L', h1, h2, h3⟩ :=
      modelSumPairs_spec hW hpe rest fun p hp => h p (by simp [hp])
    refine ⟨(CertModel.addMixed W pe a.1 b.1, a.2 + b.2) :: L', ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (h a (by simp)).addMixed hW hpe (h b (by simp))
      · exact h1 p hp
    · simp only [List.map_cons, modelSumPairs, h2]
    · intro θ
      simp only [List.map_cons, List.sum_cons, h3, Pi.add_apply, add_assoc]

theorem modelSumRounds_spec (hW : checkWeight W s N = true)
    (hpe : checkPiEnclosure pe = true) :
    ∀ (r : ℕ) (L : EnclosedList α n), (∀ p ∈ L, p.1.Encloses n W.rho p.2) →
    ∃ L' : EnclosedList α n, (∀ p ∈ L', p.1.Encloses n W.rho p.2) ∧
      modelSumRounds W pe r (L.map Prod.fst) = L'.map Prod.fst ∧
      ∀ θ, (L'.map fun p => p.2 θ).sum = (L.map fun p => p.2 θ).sum
  | 0, L, h => ⟨L, h, rfl, fun _ => rfl⟩
  | r + 1, L, h => by
    obtain ⟨L1, h1, e1, s1⟩ := modelSumPairs_spec hW hpe L h
    obtain ⟨L2, h2, e2, s2⟩ := modelSumRounds_spec hW hpe r L1 h1
    exact ⟨L2, h2, by simp only [modelSumRounds, e1, e2], fun θ => (s2 θ).trans (s1 θ)⟩

theorem foldl_addMixed_spec (hW : checkWeight W s N = true)
    (hpe : checkPiEnclosure pe = true) :
    ∀ (L : EnclosedList α n) (a : CertModel α) (f : (Fin n → ℂ) → ℂ),
    a.Encloses n W.rho f → (∀ p ∈ L, p.1.Encloses n W.rho p.2) →
    ((L.map Prod.fst).foldl (CertModel.addMixed W pe) a).Encloses n W.rho
      (fun θ => f θ + (L.map fun p => p.2 θ).sum)
  | [], a, f, ha, _ => ha.of_eq fun θ => by simp
  | p :: L, a, f, ha, h => by
    have := foldl_addMixed_spec hW hpe L _ _ (ha.addMixed hW hpe (h p (by simp)))
      fun q hq => h q (by simp [hq])
    simp only [List.map_cons, List.foldl_cons]
    exact this.of_eq fun θ => by simp only [Pi.add_apply, List.sum_cons, add_assoc]

/-- **Balanced sum contract.** -/
theorem modelSum_encloses (hW : checkWeight W s N = true) (hpe : checkPiEnclosure pe = true)
    (L : EnclosedList α n) (h : ∀ p ∈ L, p.1.Encloses n W.rho p.2) :
    (modelSum W pe (L.map Prod.fst)).Encloses n W.rho (fun θ => (L.map fun p => p.2 θ).sum) := by
  obtain ⟨L', h1, e1, s1⟩ := modelSumRounds_spec hW hpe 64 L h
  unfold modelSum
  rw [e1]
  refine CertModel.Encloses.of_eq (f := fun θ => (L'.map fun p => p.2 θ).sum) ?_ s1
  cases L' with
  | nil => exact (zeroModel_encloses n W.rho).of_eq fun θ => by simp
  | cons p L' =>
    exact (foldl_addMixed_spec hW hpe L' p.1 p.2 (h1 p (by simp))
      fun q hq => h1 q (by simp [hq])).of_eq fun θ => by simp

end ModelSum

/-! #### `DK` -/

theorem realComp_eq_realCompPoly (n : ℕ) (d : ℤ) (P : Option (CertRealPoly α)) (θ : Fin n → ℂ) :
    realComp n d P θ = (2 * (Real.pi : ℂ)) ^ d * (realCompPoly n P).eval n θ := by
  cases P with
  | none => simp [realComp, realCompPoly, CertPoly.eval]
  | some P =>
    simp only [realComp, realCompPoly, Option.map_some, Option.getD_some,
      CertRealPoly.eval_toSortedPoly]

theorem fderiv_realComp_apply (n : ℕ) (d : ℤ) (P : Option (CertRealPoly α))
    (θ v : Fin n → ℂ) : fderiv ℂ (realComp n d P) θ v =
      (2 * (Real.pi : ℂ)) ^ d * fderiv ℂ ((realCompPoly n P).eval n) θ v := by
  have h : realComp n d P = fun θ => (2 * (Real.pi : ℂ)) ^ d * (realCompPoly n P).eval n θ :=
    funext (realComp_eq_realCompPoly n d P)
  rw [h, fderiv_const_mul ((realCompPoly n P).differentiable_eval n θ)]
  rfl

theorem compDerivModel_encloses {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (d : ℤ) (P : Option (CertRealPoly α)) (j : Fin n) :
    (compDerivModel n W pe d P j.val).Encloses n W.rho
      (fun θ => fderiv ℂ (realComp n d P) θ (Pi.single j 1)) :=
  ((CertModel.Encloses.ofDeriv hW j d (realCompPoly n P)).toDeg hW hpe 0).of_eq
    fun θ => (fderiv_realComp_apply n d P θ _).symm

omit [LawfulCertArith α] in
theorem compDerivModel_deg (n : ℕ) (W : CertWeight) (pe : PiEnclosure α) (d : ℤ)
    (P : Option (CertRealPoly α)) (j : ℕ) : (compDerivModel n W pe d P j).deg = 0 :=
  toDeg_deg W pe 0 _

omit [LawfulCertArith α] in
/-- The angle rows of `DK`: `(DK v)_{1,i} = v_i + D U_i v`. -/
theorem CertEmbedding.fderiv_eval_fst (n : ℕ) (K : CertEmbedding α) (θ v : Fin n → ℂ)
    (i : Fin n) : (fderiv ℂ (K.eval n) θ v).1 i = v i + fderiv ℂ (K.angleAt n i.val) θ v := by
  let L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ))
  have h1 : HasFDerivAt (fun θ => (K.eval n θ).1 i) (L.comp (fderiv ℂ (K.eval n) θ)) θ :=
    L.hasFDerivAt.comp θ (K.differentiable_eval n θ).hasFDerivAt
  have h2 : HasFDerivAt (fun θ => (K.eval n θ).1 i)
      (ContinuousLinearMap.proj i + fderiv ℂ (K.angleAt n i.val) θ) θ :=
    (hasFDerivAt_apply i θ).add ((differentiable_angleAt n K i.val) θ).hasFDerivAt
  have := congrArg (fun T => T v) (h1.unique h2)
  simpa [L] using this

omit [LawfulCertArith α] in
/-- The action rows of `DK`: `(DK v)_{2,i} = D A_i v`. -/
theorem CertEmbedding.fderiv_eval_snd (n : ℕ) (K : CertEmbedding α) (θ v : Fin n → ℂ)
    (i : Fin n) : (fderiv ℂ (K.eval n) θ v).2 i = fderiv ℂ (K.actionAt n i.val) θ v := by
  let L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))
  have h1 : HasFDerivAt (fun θ => (K.eval n θ).2 i) (L.comp (fderiv ℂ (K.eval n) θ)) θ :=
    L.hasFDerivAt.comp θ (K.differentiable_eval n θ).hasFDerivAt
  have h2 : HasFDerivAt (fun θ => (K.eval n θ).2 i) (fderiv ℂ (K.actionAt n i.val) θ) θ :=
    (differentiable_realComp n _ _ θ).hasFDerivAt
  have := congrArg (fun T => T v) (h1.unique h2)
  simpa [L] using this

/-- **`DK` angle entries.** -/
theorem dkAngleModel_encloses {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) (i j : Fin n) :
    (dkAngleModel n K W pe i.val j.val).Encloses n W.rho
      (fun θ => (fderiv ℂ (K.eval n) θ (Pi.single j 1)).1 i) := by
  have hD := compDerivModel_encloses hW hpe (K.angleDeg.getD i.val 0) K.angle[i.val]? j
  have hA : K.angleAt n i.val = realComp n (K.angleDeg.getD i.val 0) K.angle[i.val]? := rfl
  unfold dkAngleModel
  split_ifs with hij
  · have hij' : i = j := Fin.ext hij
    subst hij'
    refine (CertModel.Encloses.add hW (constModel_encloses n W.rho 1 0 0) hD
      (compDerivModel_deg n W pe _ _ _).symm).of_eq fun θ => ?_
    rw [CertEmbedding.fderiv_eval_fst, hA]
    simp [slpConstVal]
  · have hij' : i ≠ j := fun h => hij (congrArg Fin.val h)
    refine hD.of_eq fun θ => ?_
    rw [CertEmbedding.fderiv_eval_fst, hA]
    simp [hij']

/-- **`DK` action entries.** -/
theorem dkActionModel_encloses {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) (i j : Fin n) :
    (dkActionModel n K W pe i.val j.val).Encloses n W.rho
      (fun θ => (fderiv ℂ (K.eval n) θ (Pi.single j 1)).2 i) :=
  (compDerivModel_encloses hW hpe (K.actionDeg.getD i.val 0) K.action[i.val]? j).of_eq
    fun θ => by rw [CertEmbedding.fderiv_eval_snd]; rfl

/-! #### Gram models -/

omit [LawfulCertArith α] in
theorem gramMatrix_comm {n : ℕ} (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (θ : Fin n → ℂ) (i j : Fin n) : gramMatrix K θ i j = gramMatrix K θ j i := by
  simp only [gramMatrix, dotℂ]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem gramEntryModel_encloses {n : ℕ} (K : CertEmbedding α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (a b : Fin n) :
    (gramEntryModel n K W cfg pe a.val b.val).Encloses n W.rho
      (fun θ => gramMatrix (K.eval n) θ a b) := by
  set DK := fun θ v => fderiv ℂ (K.eval n) θ (Pi.single v (1 : ℂ)) with hDK
  let L : EnclosedList α n :=
    List.ofFn (fun k : Fin n => (CertModel.mul W cfg [3, 0, a.val, b.val, k.val]
        (dkAngleModel n K W pe k.val a.val) (dkAngleModel n K W pe k.val b.val),
      (fun θ => (DK θ a).1 k) * (fun θ => (DK θ b).1 k))) ++
    List.ofFn (fun k : Fin n => (CertModel.mul W cfg [3, 0, a.val, b.val, n + k.val]
        (dkActionModel n K W pe k.val a.val) (dkActionModel n K W pe k.val b.val),
      (fun θ => (DK θ a).2 k) * (fun θ => (DK θ b).2 k)))
  have hL : ∀ p ∈ L, p.1.Encloses n W.rho p.2 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp hp
      exact CertModel.Encloses.mul hW cfg _ (dkAngleModel_encloses hW hpe K k a)
        (dkAngleModel_encloses hW hpe K k b)
    · obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp hp
      exact CertModel.Encloses.mul hW cfg _ (dkActionModel_encloses hW hpe K k a)
        (dkActionModel_encloses hW hpe K k b)
  have := modelSum_encloses hW hpe L hL
  have hfst : L.map Prod.fst = List.ofFn (fun k : Fin n =>
      CertModel.mul W cfg [3, 0, a.val, b.val, k.val]
        (dkAngleModel n K W pe k.val a.val) (dkAngleModel n K W pe k.val b.val)) ++
      List.ofFn (fun k : Fin n => CertModel.mul W cfg [3, 0, a.val, b.val, n + k.val]
        (dkActionModel n K W pe k.val a.val) (dkActionModel n K W pe k.val b.val)) := by
    simp only [L, List.map_append, List.map_ofFn]
    rfl
  rw [hfst] at this
  refine this.of_eq fun θ => ?_
  simp only [L, List.map_append, List.map_ofFn, List.sum_append, List.sum_ofFn,
    Function.comp_def, Pi.mul_apply, gramMatrix, dotℂ, Finset.sum_add_distrib, hDK]

/-- **Gram models contract.** -/
theorem gramModels_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    (K : CertEmbedding α) {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) :
    (gramModels n K W cfg pe).Encloses n (fun i : Fin n => i.val) W.rho
      (gramMatrix (K.eval n)) := by
  intro i j
  by_cases hij : i.val ≤ j.val
  · refine ⟨gramEntryModel n K W cfg pe i.val j.val, ?_,
      gramEntryModel_encloses K hW cfg hpe i j⟩
    simp [gramModels, hij]
  · refine ⟨gramEntryModel n K W cfg pe j.val i.val, ?_,
      (gramEntryModel_encloses K hW cfg hpe j i).of_eq fun θ => gramMatrix_comm _ θ j i⟩
    simp [gramModels, hij]

end Sound

end KAM.Certificate
