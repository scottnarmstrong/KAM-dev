/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Compose

/-!
# A product whose packed advice fails

`CertModel.polyProduct` is `none` when the packed advice of a key fails its landed check, and
`CertModel.mulN` then returns the sound ball `⟨deg, [], (|a| + ra) (|b| + rb)⟩`. The lock
certificate was generated and checked with this branch at 219 products (ledger memos with no
output); their segment proofs state it here, the `none` being decided by the kernel.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate CertArith

variable {α : Type} [CertArith α]

/-- `mulN` on the `none` branch of `polyProduct`. -/
theorem mulN_eq_of_polyProduct_none (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a : CertModel α) (na : α) (b : CertModel α) (nb : α)
    (h : (CertModel.polyProduct W cfg key a.poly b.poly).isNone = true) :
    CertModel.mulN W cfg key a na b nb =
      ⟨a.deg + b.deg, ⟨[]⟩, upMul (upAdd na a.rad) (upAdd nb b.rad)⟩ := by
  have h' : CertModel.polyProduct W cfg key a.poly b.poly = none := Option.isNone_iff_eq_none.mp h
  simp only [CertModel.mulN, h']

/-- Two models are equal when their degrees, term lists and radii are (each checked on its own: the
comparison of a whole product model with its ledger model was OOM-killed at 10 GB on M7). -/
theorem certModel_eq_of_parts {a b : CertModel α} (h1 : a.deg = b.deg)
    (h2 : a.poly.terms = b.poly.terms) (h3 : a.rad = b.rad) : a = b := by
  obtain ⟨da, ⟨ta⟩, ra⟩ := a
  obtain ⟨db, ⟨tb⟩, rb⟩ := b
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

end KAM.SpinOrbit.Data.LockN65
