/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import KAM.Frozen.Wave.Defs.Coeff
public import KAM.Frozen.Wave.Defs.Lam
public import KAM.Frozen.Wave.Defs.SineMode

/-!
# Frozen definition `KAM.Wave.reconU`

Blueprint-W Definition `bpW:w0:reconstruction`; P96-W p. 277. For every `y` the series converges
absolutely and uniformly in `x ∈ ℝ` (Lemma `bpW:w0n:recon-bounded`, since `a = 1 > 0`), so the
`tsum` never takes its non-summable default value.

Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit
ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The displacement reconstruction `U_m(q)(x) = Σ_{j ≥ 1} q_j / √λ_j · φ_j(x)`, where
`q = coeff y` (P96-W p. 277). -/
def reconU (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) : ℝ :=
  ∑' j : ℕ+, coeff y j / Real.sqrt (lam m hm j) * sineMode j x

end KAM.Wave

end
