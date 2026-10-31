/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.Stage
public import KAM.CertificateSharp.Kernel.SegBridges
public import KAM.CertificateSharp.Kernel.SegOne
public import KAM.CertificateSharp.Kernel.ProductSplit

/-!
# Support lemmas for the generated segmented proofs (SO-CSEG-GEN)

Equations between computable terms, used by the modules that
`scripts/spin_orbit/csplit_emit.py` generates:

* `mul_eq_of_polyProduct_cseg`: the landed `CertModel.mul` with its polynomial product memoized
  (the analogue of `CertModel.mulN_eq_of_polyProduct` for the products of the Gram and torsion
  stages, which use `mul`);
* `eq_some_of_termsBeq_cseg`: an optional term list equal to a literal, from the tail-recursive
  `termsBeq` (the generated decode theorems; `CC` has no `DecidableEq`);
* `matMulEntry_two_cseg`, `matMulEntry_four_cseg`, `matMulEntry_one_cseg`,
  `gramEntryModel_two_cseg`, `gramBGModel_two_cseg`: the landed bodies at the lunar sizes with their
  products as closed terms (`rfl`), so that a memoized product rewrites in.

Nothing here is assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data

open KAM.Certificate CertArith

variable {α : Type} [CertArith α]

/-- The landed `CertModel.mul` with its polynomial product memoized (radius verbatim). -/
theorem mul_eq_of_polyProduct_cseg (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a b : CertModel α) {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W cfg key a.poly b.poly = some out) :
    CertModel.mul W cfg key a b =
      ⟨a.deg + b.deg, truncPoly cfg.cutoff out.1,
        upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff))))
          (upAdd (upAdd (crossUp (a.poly.supNormUp W) b.rad) (crossUp (b.poly.supNormUp W) a.rad))
            (upMul a.rad b.rad))⟩ := by
  simp only [CertModel.mul, h]

omit [CertArith α] in
/-- An optional term list equal to a literal, by `termsBeq`. -/
theorem eq_some_of_termsBeq_cseg [DecidableEq α] {o : Option (List (CertKey × CC α))}
    {t : List (CertKey × CC α)} (h : (o.map fun x => termsBeq x t) = some true) : o = some t := by
  cases o with
  | none => simp at h
  | some x =>
    simp only [Option.map_some, Option.some.injEq] at h
    rw [eq_of_termsBeq h]

theorem matMulEntry_one_cseg (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (key : ProductKey) (A B : ModelMatrix α) (i j : ℕ) :
    matMulEntry W cfg pe key 1 A B i j = CertModel.toDeg W pe 0 (modelSum W pe
      [CertModel.mul W cfg (key ++ [i, j, 0]) (modelMatrixEntry A i 0) (modelMatrixEntry B 0 j)]) :=
  rfl

theorem matMulEntry_two_cseg (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (key : ProductKey) (A B : ModelMatrix α) (i j : ℕ) :
    matMulEntry W cfg pe key 2 A B i j = CertModel.toDeg W pe 0 (modelSum W pe
      [CertModel.mul W cfg (key ++ [i, j, 0]) (modelMatrixEntry A i 0) (modelMatrixEntry B 0 j),
       CertModel.mul W cfg (key ++ [i, j, 1]) (modelMatrixEntry A i 1) (modelMatrixEntry B 1 j)]) :=
  rfl

theorem matMulEntry_four_cseg (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (key : ProductKey) (A B : ModelMatrix α) (i j : ℕ) :
    matMulEntry W cfg pe key 4 A B i j = CertModel.toDeg W pe 0 (modelSum W pe
      [CertModel.mul W cfg (key ++ [i, j, 0]) (modelMatrixEntry A i 0) (modelMatrixEntry B 0 j),
       CertModel.mul W cfg (key ++ [i, j, 1]) (modelMatrixEntry A i 1) (modelMatrixEntry B 1 j),
       CertModel.mul W cfg (key ++ [i, j, 2]) (modelMatrixEntry A i 2) (modelMatrixEntry B 2 j),
       CertModel.mul W cfg (key ++ [i, j, 3]) (modelMatrixEntry A i 3) (modelMatrixEntry B 3 j)]) :=
  rfl

theorem gramEntryModel_two_cseg (K : CertEmbedding α) (W : CertWeight) (cfg : ModelConfig α)
    (pe : PiEnclosure α) (a b : ℕ) :
    gramEntryModel 2 K W cfg pe a b = modelSum W pe
      [CertModel.mul W cfg [3, 0, a, b, 0] (dkAngleModel 2 K W pe 0 a) (dkAngleModel 2 K W pe 0 b),
        CertModel.mul W cfg [3, 0, a, b, 1] (dkAngleModel 2 K W pe 1 a) (dkAngleModel 2 K W pe 1 b),
        CertModel.mul W cfg [3, 0, a, b, 2] (dkActionModel 2 K W pe 0 a)
          (dkActionModel 2 K W pe 0 b),
        CertModel.mul W cfg [3, 0, a, b, 3] (dkActionModel 2 K W pe 1 a)
          (dkActionModel 2 K W pe 1 b)] :=
  rfl

theorem gramBGModel_two_cseg (B : List (List (CertPoly α))) (G : ModelMatrix α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (i j : ℕ) :
    gramBGModel 2 B G W cfg pe i j = CertModel.toDeg W pe 0 (modelSum W pe
      [CertModel.mul W cfg [3, 1, i, j, 0] ⟨0, gramInvPoly B i 0, ofInt 0⟩ (modelMatrixEntry G 0 j),
        CertModel.mul W cfg [3, 1, i, j, 1] ⟨0, gramInvPoly B i 1, ofInt 0⟩
          (modelMatrixEntry G 1 j)]) :=
  rfl

/-- The decode of an empty part (explicit `[]`, so no unification evaluates `dyadicTerms`). -/
theorem dyadicTerms_nil_cseg (P2 sc : ℕ) (place : α → CC α) :
    dyadicTerms P2 sc place ([] : List (CertKey × ℤ)) = some [] := by
  simp [dyadicTerms]

/-- An option that is `some`, as `some` of its `getD`. -/
theorem eq_some_getD_cseg {γ : Type} {o : Option γ} (d : γ) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => simp at h
  | some x => rfl

section Beq

variable {β : Type} [DecidableEq β]

/-- Tail-recursive equality of model rows. -/
def rowBeqCseg : List (CertModel β) → List (CertModel β) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.segBeq b && rowBeqCseg as bs
  | _, _ => false

/-- Tail-recursive equality of model matrices. -/
def matBeqCseg : ModelMatrix β → ModelMatrix β → Bool
  | [], [] => true
  | r :: rs, r' :: rs' => rowBeqCseg r r' && matBeqCseg rs rs'
  | _, _ => false

theorem eq_of_rowBeqCseg : ∀ {l l' : List (CertModel β)}, rowBeqCseg l l' = true → l = l'
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [rowBeqCseg, Bool.and_eq_true] at h
    rw [CertModel.eq_of_segBeq h.1, eq_of_rowBeqCseg h.2]
  | [], _ :: _, h => by simp [rowBeqCseg] at h
  | _ :: _, [], h => by simp [rowBeqCseg] at h

theorem eq_of_matBeqCseg : ∀ {M M' : ModelMatrix β}, matBeqCseg M M' = true → M = M'
  | [], [], _ => rfl
  | r :: rs, r' :: rs', h => by
    simp only [matBeqCseg, Bool.and_eq_true] at h
    rw [eq_of_rowBeqCseg h.1, eq_of_matBeqCseg h.2]
  | [], _ :: _, h => by simp [matBeqCseg] at h
  | _ :: _, [], h => by simp [matBeqCseg] at h

/-- An optional `(centre, radius)` ball equal to a literal. -/
theorem eq_some_pair_cseg {o : Option (CC β × β)} {c : CC β} {r : β}
    (h : (o.map fun x => ccBeq x.1 c && decide (x.2 = r)) = some true) : o = some (c, r) := by
  cases o with
  | none => simp at h
  | some x =>
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [← eq_of_ccBeq h.1, ← h.2]

end Beq

end KAM.SpinOrbit.Data
