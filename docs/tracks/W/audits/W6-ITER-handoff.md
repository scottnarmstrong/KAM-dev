# W6-ITER handoff (in progress)

Package W6-ITER, worktree `/root/code/KAM-inp-wpr`, branch `inp-wpr`. Off the frontier: source-faithful
infrastructure used by several nodes; the dependency graph is still being built.

## STEP 0 (rebuild on the W5-STEP base)

* `KAM/Wave/Iteration/*` and `KAM/Wave/Assembly/*` rebuild unchanged on this base, except
  `Assembly/ShellGeom.lean`: W7's `shellInner` is now `{I ∈ R_k | a < infDist I R_kᶜ}` (W7-FIX), so
  `w8Pi_subset_shellInner` and `shellInner_subset_w8Pi_of_lt` were re-proved (statements unchanged; the first is
  now definitional, the second is `hab.trans`).
