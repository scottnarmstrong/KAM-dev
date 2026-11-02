/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.Consts
public import KAM.Wave.Iteration.Constants

/-!
# W8: the W5–W6 constants as an instance of `W8UpstreamConsts` (blueprint `bpW:w8:const`)

Blueprint labels `bpW:w8:const`, `bpW:w6:constants` (milestones W6, W8).

`W8-PREP` (deviation D1) took W6's `γ, γ₁` and W5's `c_F, c^♮_F` as the record
`W8UpstreamConsts`. They now have Lean definitions: `γ = w6Gamma m hm`, `γ₁ = w6Gamma1 m hm`
(`bpW:w6:constants`), `c_F = w6CF = stepCF 24`, `c^♮_F = w6CFn = stepCFn 24` (`bpW:w5:ledger`).
`w8Upstream m hm` is the record they form; the W8 constants are to be evaluated at it. Also: W8's
`σ_P`, `σ₀`, `M` agree with W6's.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The W5–W6 constants of `bpW:w8:const`: `γ`, `γ₁` (`bpW:w6:constants`), `c_F`, `c^♮_F`
(`bpW:w5:ledger`, at `τ = 24`). -/
def w8Upstream (m : ℝ) (hm : 0 < m) : W8UpstreamConsts where
  gam := w6Gamma m hm
  gam1 := w6Gamma1 m hm
  cF := w6CF
  cFnat := w6CFn
  gam_pos := w6Gamma_pos m hm
  gam1_pos := w6Gamma1_pos m hm
  cF_pos := w6CF_pos
  cFnat_pos := w6CFn_pos

theorem w8SigmaP_eq_w6 : w8SigmaP = w6SigmaP := by rw [w6SigmaP_val]; unfold w8SigmaP; norm_num

theorem w8Sigma0_eq_w6 : w8Sigma0 = w6Sigma0 := by rw [w6Sigma0_val]; unfold w8Sigma0; norm_num

theorem w8M_eq_w6 (m : ℝ) (hm : 0 < m) : w8M m hm = w6M m hm := rfl

end KAM.Wave
