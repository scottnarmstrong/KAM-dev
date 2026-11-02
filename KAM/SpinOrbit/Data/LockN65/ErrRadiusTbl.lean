/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Terms

/-!
# The error radius through a table of weight powers (lock-owned)

`errRadius W L` weighs every error term by `ofRatUp (W.w ^ keyDeg k)`, a rational power recomputed
per term: over the ~26k terms of the lock's largest products one kernel run exceeds 10 GB.
`errRadius_eq_tbl`: given the table `tbl = [ofRatUp (W.w ^ d) | d < D]` (checked once by the
kernel) and every key degree of `L` below `D`, the radius is the same balanced sum with the
weights looked up in the table. Nothing is assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate CertArith

variable {α : Type} [CertArith α]

/-- The weighted size of an error term with its weight looked up in a table of powers. -/
def weightTermTbl (tbl : List α) (t : ErrTerm α) : α :=
  upMul (abs t.2.2) (tbl.getD (keyDeg t.1) (ofInt 0))

/-- `errRadius` with the weights from a table: `errRadius W L` when `tbl` is the table of the
powers of `W.w` and the key degrees of `L` are in its range (`errRadius_eq_tbl`). -/
def errRadiusTbl (tbl : List α) (L : List (ErrTerm α)) : α :=
  sumUp (weightTermTbl tbl) L

theorem errRadius_eq_tbl (W : CertWeight) (D : ℕ) {tbl : List α} (L : List (ErrTerm α))
    (hT : (List.range D).map (fun d => (ofRatUp (W.w ^ d) : α)) = tbl)
    (hL : (L.all fun t => decide (keyDeg t.1 < D)) = true) :
    errRadius W L = errRadiusTbl tbl L := by
  subst hT
  unfold errRadius errRadiusTbl sumUp
  congr 2
  apply List.map_congr_left
  intro t ht
  have hd : keyDeg t.1 < D := by
    have := List.all_eq_true.mp hL t ht
    simpa using this
  simp [weightTermUp, weightTermTbl, List.getD_eq_getElem?_getD, hd]

end KAM.SpinOrbit.Data.LockN65
