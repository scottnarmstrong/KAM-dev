/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Frame.Majorants

/-!
# Stage memoization: Gram, torsion and frames proved one entry at a time

Equation lemmas (design SO-CSPLIT §3.4, M2) that let a heavy closed stage of the landed Gram,
torsion and frame checks be memoized as a literal, proved by its own kernel run, and `rw`ritten
into its consumer. They are computation-only: no landed definition changes. The table lemmas
(`modelMatMul_eq_of_entries`, `matMulEntry_eq_of_products`, `gramModels_eq_of_entries`,
`gramDefectRows_eq_of_entries`) are stated over variables, so the per-entry equalities move under
the binders of the landed `buildMat` bodies; `gramCheck_eq_of_rows`,
`torsionModels_eq_of_stages` and `frameNModels_eq_of_stage` assemble the stages in the landed
order; the certificate bridges reduce `checkGram`, `checkTorsion`, `checkFrameT` and `checkFrameN`
to their residuals.

The proofs rewrite into the landed bodies by `unfold`/`rw` or a `simp only` with the stage
equations; a `simp` over a landed body is avoided (it can evaluate through defeq).
-/

@[expose] public section

namespace KAM.Certificate

open KAM KAM.CertificateSharp CertArith

variable {α : Type} [CertArith α]

/-- The `(i, j)` body of `modelMatMul` (definitionally equal; new name). -/
def matMulEntry (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (key : ProductKey)
    (m : ℕ) (A B : ModelMatrix α) (i j : ℕ) : CertModel α :=
  CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun k : Fin m =>
    CertModel.mul W cfg (key ++ [i, j, k.val]) (modelMatrixEntry A i k.val)
      (modelMatrixEntry B k.val j)))

theorem modelMatMul_eq_buildMat (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (key : ProductKey) (r m c : ℕ) (A B : ModelMatrix α) :
    modelMatMul W cfg pe key r m c A B = buildMat r c (matMulEntry W cfg pe key m A B) := rfl

/-- A list matrix of shape `r × c` is rebuilt from its entries. -/
theorem buildMat_modelMatrixEntry {r c : ℕ} {M : ModelMatrix α} (hrows : M.length = r)
    (hcols : ∀ row ∈ M, row.length = c) :
    buildMat r c (fun i j => modelMatrixEntry M i j) = M := by
  unfold buildMat
  apply List.ext_getElem (by simp [hrows])
  intro i hi hi'
  have hlen : M[i].length = c := hcols _ (List.getElem_mem hi')
  simp only [List.getElem_map, List.getElem_range]
  apply List.ext_getElem (by simp [hlen])
  intro j hj hj'
  simp [modelMatrixEntry, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj']

theorem modelMatMul_eq_of_entries (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (key : ProductKey) (r m c : ℕ) (A B : ModelMatrix α) {M : ModelMatrix α}
    (hrows : M.length = r) (hcols : ∀ row ∈ M, row.length = c)
    (h : ∀ i < r, ∀ j < c, matMulEntry W cfg pe key m A B i j = modelMatrixEntry M i j) :
    modelMatMul W cfg pe key r m c A B = M := by
  rw [modelMatMul_eq_buildMat]
  conv_rhs => rw [← buildMat_modelMatrixEntry hrows hcols]
  unfold buildMat
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  exact h i (List.mem_range.1 hi) j (List.mem_range.1 hj)

theorem matMulEntry_eq_of_products (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (key : ProductKey) (m : ℕ) (A B : ModelMatrix α) (i j : ℕ) {Pk : ℕ → CertModel α}
    (h : ∀ k < m, CertModel.mul W cfg (key ++ [i, j, k]) (modelMatrixEntry A i k)
      (modelMatrixEntry B k j) = Pk k) :
    matMulEntry W cfg pe key m A B i j =
      CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun k : Fin m => Pk k.val)) := by
  have : (fun k : Fin m => CertModel.mul W cfg (key ++ [i, j, k.val])
      (modelMatrixEntry A i k.val) (modelMatrixEntry B k.val j)) = fun k : Fin m => Pk k.val :=
    funext fun k => h k.val k.isLt
  simp only [matMulEntry, this]

theorem gramModels_eq_of_entries (n : ℕ) (K : CertEmbedding α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) {E : ℕ → ℕ → CertModel α}
    (h : ∀ a < n, ∀ b < n, a ≤ b → gramEntryModel n K W cfg pe a b = E a b) :
    gramModels n K W cfg pe = (List.range n).map fun a => (List.range n).map fun b =>
      if a ≤ b then E a b else E b a := by
  unfold gramModels
  refine List.map_congr_left fun a ha => List.map_congr_left fun b hb => ?_
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  by_cases hab : a ≤ b
  · simp only [hab, ↓reduceIte, h a ha' b hb' hab]
  · simp only [hab, ↓reduceIte, h b hb' a ha' (Nat.le_of_not_le hab)]

theorem gramDefectRows_eq_of_entries (n : ℕ) (B : List (List (CertPoly α))) (G : ModelMatrix α)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) {T : ℕ → ℕ → CertModel α}
    (h : ∀ i < n, ∀ j < n, gramBGModel n B G W cfg pe i j = T i j) :
    gramDefectRows n B G W cfg pe =
      List.ofFn fun i : Fin n =>
        sumUp (fun j : Fin n => gramDefectUp W i.val j.val (T i.val j.val)) (List.finRange n) := by
  -- explicit `congrArg`: `congr 1` tries `sumUp` by defeq and exhausts the heartbeats
  -- (design signal)
  have hT : ∀ i : Fin n, (fun j : Fin n =>
      gramDefectUp W i.val j.val (gramBGModel n B G W cfg pe i.val j.val)) =
      fun j : Fin n => gramDefectUp W i.val j.val (T i.val j.val) :=
    fun i => funext fun j => by rw [h i.val i.isLt j.val j.isLt]
  unfold gramDefectRows
  exact congrArg List.ofFn (funext fun i => congrArg (fun f => sumUp f (List.finRange n)) (hT i))

/-- `gramCheck` with its Gram matrix and defect rows memoized. -/
theorem gramCheck_eq_of_rows (n : ℕ) (K : CertEmbedding α) (Binv : List (List (CertPoly α)))
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (σBμ : ℚ) {dRows : List α}
    (hshape : gramInvShapeOk n Binv = true)
    (hrows : gramDefectRows n Binv (gramModels n K W cfg pe) W cfg pe = dRows) :
    gramCheck n K Binv W cfg pe σBμ =
      if gramBoundsOk dRows (gramInvRows n Binv W) (maxCandidate dRows)
          (maxCandidate (gramInvRows n Binv W)) σBμ then
        some (maxCandidate dRows, maxCandidate (gramInvRows n Binv W))
      else none := by
  simp only [gramCheck, hshape, hrows, ↓reduceIte]

/-- `torsionModels` from its stages, each stated on the previous stages' results, in the landed
order and with the landed keys and shapes. -/
theorem torsionModels_eq_of_stages (n : ℕ) (e : HamExpr n) (K : CertEmbedding α)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (δβ : α × α) (box : FreqBox) (s : ℚ)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) {eps : α}
    {ms : List (CertModel α)} {L Gi DL N0 DG1 DG2 DGi0 DGi1 DN1 DN2 XN1 Tb Y : ModelMatrix α}
    (heps : gramInvRadius δβ = some eps)
    (hms : Slp.compose n e.jet.prog K wit W cfg pe (torsionSlots n e.jet) = some ms)
    (hL : dkModels n K W pe = L) (hGi : gramInvModels n Binv eps = Gi)
    (hDL : dkwModels n K box s W cfg pe = DL)
    (hN0 : modelMatMul W cfg pe [4, 0] (n + n) n n L Gi = N0)
    (hDG1 : modelMatMul W cfg pe [4, 1] n (n + n) n (modelMatTranspose (n + n) n DL) L = DG1)
    (hDG2 : modelMatMul W cfg pe [4, 2] n (n + n) n (modelMatTranspose (n + n) n L) DL = DG2)
    (hDGi0 : modelMatMul W cfg pe [4, 3] n n n Gi (modelMatAdd W pe n n DG1 DG2) = DGi0)
    (hDGi1 : modelMatMul W cfg pe [4, 4] n n n DGi0 Gi = DGi1)
    (hDN1 : modelMatMul W cfg pe [4, 5] (n + n) n n DL Gi = DN1)
    (hDN2 : modelMatMul W cfg pe [4, 6] (n + n) n n L (modelMatNeg n n DGi1) = DN2)
    (hXN1 : modelMatMul W cfg pe [4, 7] (n + n) (n + n) n (dxhModels n ms)
      (modelMatOmega n n N0) = XN1)
    (hTb : modelMatMul W cfg pe [4, 8] n (n + n) n
      (modelMatTranspose (n + n) n (modelMatOmega n n N0))
      (modelMatOmega n n (modelMatAdd W pe (n + n) n XN1
        (modelMatNeg (n + n) n (modelMatOmega n n (modelMatAdd W pe (n + n) n DN1 DN2))))) = Tb)
    (hY : modelMatMul W cfg pe [4, 9] 1 (n + n) n (d1Models n ms) (modelMatOmega n n N0) = Y) :
    torsionModels n e K wit Binv δβ box s W cfg pe =
      some (buildMat (n + 1) (n + 1) fun i j =>
        if i < n then (if j < n then modelMatrixEntry Tb i j else freqModel n box s i)
        else (if j < n then modelMatrixEntry Y 0 j else zeroModel)) := by
  -- an explicit rewrite chain: a `simp` over the landed body exhausts the default heartbeats in
  -- `whnf` (design signal; recipes and generated proofs use `unfold`/`rw` only)
  unfold torsionModels
  rw [heps, hms]
  dsimp only
  rw [hL, hGi, hDL, hN0, hDG1, hDG2, hDGi0, hDGi1, hDN1, hDN2, hXN1, hTb, hY]

/-- `frameNModels` is the omega of the `[4,0]` stage (shared with torsion's `N`). -/
theorem frameNModels_eq_of_stage (n : ℕ) (K : CertEmbedding α) (Binv : List (List (CertPoly α)))
    (eps : α) (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    {L Gi N0 : ModelMatrix α} (hL : dkModels n K W pe = L) (hGi : gramInvModels n Binv eps = Gi)
    (hN0 : modelMatMul W cfg pe [4, 0] (n + n) n n L Gi = N0) :
    frameNModels n K Binv eps W cfg pe = modelMatOmega n n N0 := by
  simp only [frameNModels, hL, hGi, hN0]

/-! ### Certificate bridges -/

variable {n : ℕ}

theorem checkGram_of_gramCheck {c : TorusCertificate n α} {δβ : α × α}
    (h : gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ) =
      some δβ) :
    checkGram c = true := by
  simp only [checkGram, h, Option.isSome_some]

theorem checkTorsion_eq_of {c : TorusCertificate n α} {δβ : α × α} {T : ModelMatrix α}
    (hg : gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ) =
      some δβ)
    (ht : torsionModels n c.ham c.emb c.wit c.gramInv δβ c.freqBox c.params.s c.weight c.cfgLow
      c.piEnc = some T) :
    checkTorsion c = torsionAvgCheck n T c.torsInv (c.params.σT - c.params.μ) := by
  simp only [checkTorsion, hg, ht]

theorem checkFrameT_eq_of {c : TorusCertificate n α} {δβ : α × α} {T : ModelMatrix α} {b : ℚ}
    (hg : gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ) =
      some δβ)
    (ht : torsionModels n c.ham c.emb c.wit c.gramInv δβ c.freqBox c.params.s c.weight c.cfgLow
      c.piEnc = some T) :
    checkFrameT c b = (List.finRange n).all fun i =>
      rowCornerLeq c.weight (wloOf c.weight c.expOrder) n
        ((List.finRange n).map fun j => modelMatrixEntry T i.val j.val) (ofRatDown b) := by
  simp only [checkFrameT, frameGram, hg, ht]

theorem checkFrameN_eq_of {c : TorusCertificate n α} {δβ : α × α} {eps : α} {M : ModelMatrix α}
    {bN bNt : ℚ}
    (hg : gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ) =
      some δβ)
    (he : gramInvRadius δβ = some eps)
    (hM : frameNModels n c.emb c.gramInv eps c.weight c.cfgLow c.piEnc = M) :
    checkFrameN c bN bNt =
      (((List.finRange (n + n)).all fun r =>
        rowCornerLeq c.weight (wloOf c.weight c.expOrder) n
          ((List.finRange n).map fun j => modelMatrixEntry M r.val j.val) (ofRatDown bN)) &&
      ((List.finRange n).all fun j =>
        rowCornerLeq c.weight (wloOf c.weight c.expOrder) n
          ((List.finRange (n + n)).map fun r => modelMatrixEntry M r.val j.val)
            (ofRatDown bNt))) := by
  simp only [checkFrameN, frameGram, hg, he, hM]

end KAM.Certificate
