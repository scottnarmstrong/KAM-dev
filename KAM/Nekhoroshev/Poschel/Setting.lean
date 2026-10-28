/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.Setting
public import KAM.Nekhoroshev.Stability.Energy
public import KAM.Nekhoroshev.Interfaces.Constants
public import KAM.Weighted.Norm
public import KAM.Canonical.Setting

/-!
# Setting of Theorem 1 (`bpN:p9:setting`)

The structure `Theorem1Setting` bundling the standing hypotheses (S1)–(S4) of Pöschel's Theorem 1
together with the positive standing parameters, and its graph name `setting`. The constants
`thmA`, `thmEps0`, `thmK`, `theoremCover` are in `Poschel/Elementary.lean`. No hypothesis concerns
the final orbit.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.Canonical KAM.Stability

variable {n : ℕ}

/-- A Theorem-1 setting: `n ≥ 2`, positive parameters, and (S1)–(S4). -/
structure Theorem1Setting (P : Set (Fin n → ℝ)) (r0 s m M ell : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop where
  hn : 2 ≤ n
  hr0 : 0 < r0
  hs : 0 < s
  hm : 0 < m
  hmM : m ≤ M
  hell : 0 < ell
  holo : DifferentiableOn ℂ h (polyNbhd (cpx P) r0)
  real : RealOn (Dom n (cpx P) r0 s) (fun w => h w.2)
  hess : ∀ I ∈ polyNbhd (cpx P) r0, ∀ v : Fin n → ℂ,
    euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v
  qc : IsQuasiConvex (realNbhd P r0) h ell m
  radius : r0 ≤ ell / (2 * M)
  f_class : InClass (cpx P) r0 s f
  f_real : RealOn (Dom n (cpx P) r0 s) f
  f_finite : HasFiniteWNorm (cpx P) r0 s f

/-- Graph name `bpN:p9:setting`, with the descriptive structure retained for projections. -/
abbrev setting := @Theorem1Setting

end KAM.Nekhoroshev
