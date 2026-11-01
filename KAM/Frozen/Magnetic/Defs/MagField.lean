/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import KAM.Frozen.Magnetic.Defs.MagH0
public import KAM.Frozen.Magnetic.Defs.MagV

/-!
# Frozen definition `KAM.Magnetic.magField`

Owner-approved on 2026-11-01 (decision D68, docs/explorations/mag/FREEZE-PROPOSAL.md at
mag-pilot@a48eb432). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change
needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic

/-- The magnetic field-line vector field on `(q, p, φ)`: `q̇ = h'(p)`, `ṗ = -∂_q V`, `φ̇ = 1`
(field lines of `H = J + h(p) + V(q, φ)`; time is the toroidal angle in turns, `q` the
poloidal angle in turns, `p` the flux variable; all real lifts). -/
def magField (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (deriv magH0 x.2.1, -deriv (fun s => magV s x.2.2) x.1, 1)

end KAM.Magnetic

end
