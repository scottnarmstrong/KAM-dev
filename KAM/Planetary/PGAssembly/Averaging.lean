/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingDisp

/-!
# P Part 5: the averaging record (`bpP:p5:avg`)

`avg` applies the P2 theorem `averaged_remainder` to the normalized data of `pg_osc_hyp`,
`pg_osc_bound` and conjugates by the normalization; `pgAvg` is the chosen record.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

theorem avg (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    ∃ A : PGAveraging (a+b), AveragingSpec d r mu A := by
  obtain ⟨Ψ, g, fs, R, c1, c2, c3, c4, c5, c6, -, -, -, -, -, -, c7, -, cls, hb, -, hd⟩ :=
    averaged_remainder (pg_osc_positive d r mu h).1 (pg_osc_positive d r mu h).2
      (pg_osc_hyp d r mu h) (pg_osc_bound d r mu h)
  have hb' : oscBound (checkedCore d r mu) ((params d r mu).rhoBar/2) (pgOscEpsilon d/2)
      (pgOscEpsilon d/2) (pgOscWidth d/6) R (avgB d r mu) := hb
  have hcls : oscClass (checkedCore d r mu) ((params d r mu).rhoBar/2) (pgOscEpsilon d/2)
      (pgOscEpsilon d/2) (pgOscWidth d/6) R := cls
  have hr := avg_real_mem h c6
  refine ⟨⟨avgPsi Ψ, avgRem R⟩, avg_diff h c1, avg_inj h c2, avg_maps h c3,
    avg_hamil h c7, avg_rem_diff h hcls, avg_rem_pointwise h hcls hb',
    fun I hI x hx => avg_rem_fourier h hb' hI hx, avg_periodic h c5,
    fun z hz => realAverageMap_spec (hr z hz), avg_chart h c1 c4 c6,
    avg_disp h c6 (fun z hz => ?_)⟩
  obtain ⟨e1, -, e3, e4⟩ := hd z hz
  exact ⟨e1, e3, e4⟩

/-- The chosen averaging record. -/
def pgAvg (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) : PGAveraging (a+b) :=
  (avg d r mu h).choose

end KAM.Planetary

end
