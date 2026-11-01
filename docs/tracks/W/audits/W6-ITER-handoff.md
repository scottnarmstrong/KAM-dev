# W6-ITER handoff (in progress)

Package W6-ITER, worktree `/root/code/KAM-inp-wpr`, branch `inp-wpr`. Off the frontier: source-faithful
infrastructure used by several nodes; the dependency graph is still being built.

## STEP 0 (rebuild on the W5-STEP base)

* `KAM/Wave/Iteration/*` and `KAM/Wave/Assembly/*` rebuild unchanged on this base, except
  `Assembly/ShellGeom.lean`: W7's `shellInner` is now `{I ∈ R_k | a < infDist I R_kᶜ}` (W7-FIX), so
  `w8Pi_subset_shellInner` and `shellInner_subset_w8Pi_of_lt` were re-proved (statements unchanged; the first is
  now definitional, the second is `hab.trans`).

## Labels and declarations

| label | status | declarations |
|---|---|---|
| `iter-lemma` | **done, except the reality of `P_{ν+1}`** (W5 reality clause pending, branch inp-w5r) | `Iteration/Bridge`: `w6Om7`, `w6L7`, `W6Mel` (the conditions `(bpW:w6:melnikov)`, W7 index, Dirichlet weight), `w6_homMelnikov_of_mel` (`bpW:w4:wave` (ii): they imply W5's `HomMelnikov 24`); `Iteration/Stage`: `W6StageCore`, `W6Stage` (hypotheses at stage `ν`), `W6Stage.stepHyp` (W5's `StepHypSrc` at stage `ν`, step `il-small`), objects `W6Stage.{omN, OmN, PhiN, PN, XN, PiN}`; `Iteration/IterLemma`: `W6Stage.w6IterLemma` (bundle), `phiN_mapsTo`, `next_core` (stage `ν+1` given `W6Mel0`, the `k = 0` conditions), `phiN_bounds`, `omN_inc`, `OmN_inc`, `OmN_inc_abs`, `w6_mel_perturb` (step `il-div`, with the Dirichlet weight), `w6_newerror_eq`; conditional helper `next_stage_of_stepReal` (hypothesis `W6StepReal` = W5's reality clause for `P_+`) |
