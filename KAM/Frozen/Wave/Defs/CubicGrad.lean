/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import KAM.Frozen.Wave.Defs.ReconU

/-!
# Frozen definition `KAM.Wave.cubicGrad`

Blueprint-W Definition `bpW:w0:Gq`; P96-W (8)–(9) p. 280 with `g(u) = u⁴/4`.

Owner-approved on 2026-10-30 (decision D41; docs/tracks/W/W-STATEMENTS.md revision 1, commit
ffcbdb93). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The cubic gradient `𝒢(q)_l = λ_l^{-1/2} ∫₀^π U_m(q)(x)³ φ_l(x) dx`, `l ≥ 1`, i.e.
`∂G/∂q_l` for `G(q) = ¼ ∫₀^π U_m(q)⁴` (blueprint-W `bpW:w0:Gq`, Lemma `bpW:w0n:gradient`). -/
def cubicGrad (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) : ℝ :=
  (∫ x in (0 : ℝ)..Real.pi, reconU m hm y x ^ 3 * sineMode l x) / Real.sqrt (lam m hm l)

end KAM.Wave

end
