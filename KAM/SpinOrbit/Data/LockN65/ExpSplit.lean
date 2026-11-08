/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Exp

/-!
# The exp residual bound in two parts (LOCK-DATA)

`expResidualUp` evaluates, in one kernel run, a weighted sum over the merged derivative and
product terms and the error radius of the derivative items of `g₀`. For the lock's largest exp
witnesses that run sits at the per-theorem memory budget; `expResidualUp_eq_of_parts` takes the
two parts as separate facts (each its own kernel theorem). Nothing is assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate CertArith

variable {α : Type} [CertArith α]

theorem expResidualUp_eq_of_parts (W : CertWeight) (cfg : ModelConfig α) (g₀ E : CertPoly α)
    (eN : α) (j : ℕ) {s r : α}
    (hs : sumUp (fun t => weightTermUp W t.1 (upAdd t.2.1.normUp t.2.2))
      (mergeErrTerms (E.terms.filterMap (derivItem j)) (expResidualProduct W cfg g₀ E j).1) = s)
    (hr : errRadius W (g₀.terms.filterMap (derivItem j)) = r) :
    expResidualUp W cfg g₀ E eN j =
      upMul (ofRatUp (2 * piUpQ)) (upAdd (upAdd s (expResidualProduct W cfg g₀ E j).2)
        (crossUp eN r)) := by
  unfold expResidualUp
  simp only [hs, hr]

end KAM.SpinOrbit.Data.LockN65
