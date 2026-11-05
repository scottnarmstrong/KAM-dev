/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.SegSupport

/-!
# Memo equations stated on the exact terms of their memos (lock-owned)

Two forms of the generated proofs left the elaborator to unify a memoized statement against a
term that only agrees with it after evaluating checkpoint data, and it reached its maximum
recursion depth (lam run, DELTA-LAM-2):

* `mul_eq_of_polyProduct_cseg W cfg key ⟨d, P.poly, P.rad⟩ … h` asks `h` for
  `polyProduct … (⟨d, P.poly, P.rad⟩).poly …` while the memo states `P.poly`; with the same head
  `CertModel.poly` on both sides the unifier compares `⟨d, P.poly, P.rad⟩` with `P` by structure
  eta and evaluates the checkpoint slot `P` (`Seg.Rad.InvF1984`, slot 1983).
  `mul_mk_eq_of_polyProduct_cseg` takes the fields instead, so `h` is the memo's statement verbatim.
* `composeStep_char_eq … (ComposeState.seed …) k h` asks `h` for `charSlot … st.cache k` while the
  character memo states the cache literally (`Seg.Full.S9`, `Seg.Low.S11`).
  `composeStep_char_eq_of_cache_cseg` takes the cache equation `st.cache = c₀` separately (a
  top-level `rfl` in the generated module) and `h` at `c₀`.

Both are restatements of `mul_eq_of_polyProduct_cseg` and `composeStep_char_eq`; nothing is
assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate CertArith

variable {α : Type} [CertArith α]

/-- `mul_eq_of_polyProduct_cseg` with both factors given by their fields. -/
theorem mul_mk_eq_of_polyProduct_cseg (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (da : ℤ) (pa : CertPoly α) (ra : α) (db : ℤ) (pb : CertPoly α) (rb : α)
    {out : List (ErrTerm α) × α} (h : CertModel.polyProduct W cfg key pa pb = some out) :
    CertModel.mul W cfg key ⟨da, pa, ra⟩ ⟨db, pb, rb⟩ =
      ⟨da + db, truncPoly cfg.cutoff out.1,
        upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff))))
          (upAdd (upAdd (crossUp (pa.supNormUp W) rb) (crossUp (pb.supNormUp W) ra))
            (upMul ra rb))⟩ :=
  mul_eq_of_polyProduct_cseg W cfg key ⟨da, pa, ra⟩ ⟨db, pb, rb⟩ h

/-- `composeStep_char_eq` with the state's cache given by an equation. -/
theorem composeStep_char_eq_of_cache_cseg (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α)
    (k : CertKey) {c₀ : List (CertKey × CertPoly α × α)} {m : CertModel α}
    {c : List (CertKey × CertPoly α × α)} (hc : st.cache = c₀)
    (h : charSlot n K wit W cfg pe c₀ k = some (m, c)) :
    composeStep n K wit W cfg pe st (.char k) = some { st.pushSlot W m with cache := c } := by
  subst hc
  exact composeStep_char_eq n K wit W cfg pe st k h

end KAM.SpinOrbit.Data.LockN65
