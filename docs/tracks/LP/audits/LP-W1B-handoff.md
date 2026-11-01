# LP-W1B: combined audit handoff for LP-DICT + LP-GEOMOD (track LP, wave 1)

Branch `inp-lp-w1b` (worktree `/root/code/KAM-inp-lp-geomod`) = `inp-lp` (which contains the landed, audited
LP-THR + LP-MOM, main f1fe1d30) + `inp-lp-geomod` (dae4b49b) + `inp-lp-dict` (9d44a06b). The package diff is
`git diff inp-lp...HEAD -- KAM`: 6 new Lean modules plus the regenerated `KAM/Root/Planetary.lean`, about
1,380 lines. THR and MOM are already audited (LP-BAR1-1, PASS WITH NOTES) and are NOT in scope. Nothing in
track LP is frozen.

Prover handoffs (declarations, checks, axioms, each with its own AUDIT FOCUS):
- `docs/tracks/LP/audits/LP-GEOMOD-handoff.md`: MAIN Lemmas 5–6. Brief:
  `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-GEOMOD.md`.
- `docs/tracks/LP/audits/LP-DICT-handoff.md`: MAIN Lemma 7 dictionary (Part A) and the one-centre Lemma 13
  adapter test (Part B). Brief: `…/packages/LP-DICT.md`.

Source: `docs/tracks/LP/source/MAIN.md` (L5 162–175, L6 177–189, L7 193–242, L13 429–464) with
`docs/tracks/LP/source/AMENDMENTS.md`. **N2** (one shared compact `U`), **N6** (the L13 widths and `F`) and
**N11** (the order of `d_⋆`) bear directly on these packages.

## Orchestrator checks (kam-lp, on the W1B merge)

- `lp_build.sh` (4G cap) of Threshold.Pair, Threshold, Geometry, Modulus, Continuation, PlanarDictionary,
  NonresonantAdapterRescale, NonresonantAdapter: all "Build completed successfully".
- `lp_lint.sh`: exit 0. `main_shortname_check.py` on the 6 new modules: OK.
- Review: the Part B result "no convention mismatch" (period one, physical time, bracket `2π/ℓ²`) and the
  GEOMOD declaration list against the briefs. No finding.

## REPORT FORMAT

One section per package (LP-GEOMOD first, then LP-DICT), each with its own verdict, then a combined verdict.

## AUDIT FOCUS (beyond the two prover handoffs)

LP-GEOMOD:
- `DeficitBarrier` / `strongBarrier_physical`: constants chosen before `I`, `e`, `z`, and depending only on
  `(ν, U, m)`. Check the empty-`K_m` case.
- `strongThresholdModulus`: a literal `sSup`; check every use sits where the set is nonempty and bounded.
- M3 `strongAMD_le_of_tube` and the corollary `maximal_global_of_tube`: the prover dropped two unused premises
  (claimed harmless strengthening); confirm. The continuation statement uses `KAM.ODE.IsMaximalSolution` of the
  moving field on `collisionFreeDomain n`; check it is the actual moving dynamics (`moving_ode`).

LP-DICT:
- Part B `lpRescale_field` / `lpRescale_hasDerivAt`: the six components against `realWfield`, `fastAction`,
  `slowPair`. This is the convention check the proof audit asked for (PROOF-AUDIT-1 §6, point 2).
- `nonresonant_drift_of_chartData` is a CONDITIONAL helper (analytic data of L8 as premises). Check it has no
  drift, confinement or AMD premise, that its docstring says so, and that its premises are exactly the
  engine's inputs plus the physical solution and chart lift.
- `lpChart_eccVector_xy`: the sign convention `(ξ, η) = (x, −y)` against MAIN line 199.
