/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Data.PNat.Basic

/-!
# Frozen definition `KAM.Wave.WaveSpace`

Blueprint-W Definition `bpW:w0:ellap` and Convention `bpW:w0:weights` (`a = p = 1`).

`E_{1,1} = ℓ^{1,1} × ℓ^{1,1}` is represented in *weighted coordinates*: a point is a pair
`(y, y')` of square-summable real sequences indexed by `j ≥ 1`, and the Fourier–sine coefficient
sequences are `q_j = y_j / ellWeight 1 1 j`, `p_j = y'_j / ellWeight 1 1 j` (`KAM.Wave.coeff`).
The map `q ↦ (ellWeight 1 1 j * q_j)_j` is an isometric isomorphism `ℓ^{1,1} ≃ ℓ²`, and the
product norm of Mathlib is the max norm, so `‖(y, y')‖ = max(‖q‖_{1,1}, ‖p‖_{1,1}) = ‖(q, p)‖_E`.

Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit
ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The phase space `E_{1,1}` in weighted coordinates (two copies of `ℓ²(ℕ+)`, max norm). -/
abbrev WaveSpace : Type :=
  lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2

end KAM.Wave

end
