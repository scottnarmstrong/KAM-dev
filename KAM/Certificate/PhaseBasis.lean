/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Torus.Basic

/-!
# The phase basis of `ℂⁿ × ℂⁿ`

The phase index `Fin n ⊕ Fin n` (angles `inl`, actions `inr`) and its basis vectors, as signed in
the SO design (Appendix A, §D). This tiny module exists so that the clock lemma does not depend
on the Hamiltonian-expression package; that package imports it instead of redefining
`phaseBasis`.
-/

@[expose] public section

noncomputable section

namespace KAM.Certificate

open KAM.Torus

/-- The phase index `Fin n ⊕ Fin n` (angles `inl`, actions `inr`) and its basis vector. -/
def phaseBasis {n : ℕ} (a : Fin n ⊕ Fin n) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (sumVec n).symm (Pi.single a 1)

theorem phaseBasis_inr {n : ℕ} (j : Fin n) :
    phaseBasis (.inr j) = (0, Pi.single j 1) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp [phaseBasis, sumVec]
  · by_cases h : i = j <;> simp [phaseBasis, sumVec, h]

end KAM.Certificate

end
