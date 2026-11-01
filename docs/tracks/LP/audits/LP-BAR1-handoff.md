# LP-BAR1: combined audit handoff for LP-THR + LP-MOM (track LP, wave 1, the barrier base)

Branch `inp-lp-bar1` (worktree `/root/code/KAM-inp-lp-thr`) = `inp-lp` + `inp-lp-thr` (e9814e95) + `inp-lp-mom`
(753470f7), merged at 8f6f6e4d. The package diff is `git diff inp-lp...HEAD -- KAM` (8 new Lean modules plus the
regenerated `KAM/Root/Planetary.lean`; about 1,350 lines). Nothing in track LP is frozen.

The two prover handoffs carry the declaration lists, checks and axioms:
- `docs/tracks/LP/audits/LP-THR-handoff.md` (MAIN Lemma 4; brief `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-THR.md`)
- `docs/tracks/LP/audits/LP-MOM-handoff.md` (MAIN Lemmas 2–3 planar; brief `…/packages/LP-MOM.md`)

Source: `docs/tracks/LP/source/MAIN.md` (lines 9–93 for (1)–(3), 110–160 for Lemmas 2–4) with
`docs/tracks/LP/source/AMENDMENTS.md` (N8 and N9 bear on these packages); conventions `docs/tracks/LP/SPEC.md`.

## Orchestrator checks (kam-lp, 2026-11-01 00:40 UTC, on 8f6f6e4d)

- `lp_build.sh` (4G cap): `KAM.Planetary.StrongAMD.{Orbital,Momentum,Reflection,Threshold}`: all "Build completed
  successfully".
- `lp_lint.sh`: exit 0 (`check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (177 …)`).
- `main_shortname_check.py` on all 8 modules: OK.
- Review of `Threshold/Defs.lean`, `Momentum.lean` (`strongAMD`) and `Reflection.lean` definitions against SPEC §2
  and the briefs: no finding.

## REPORT FORMAT (quota is scarce)

The codex-1 quota is nearly exhausted. Write the report incrementally: first the LP-THR section (verdict and
findings), saved to the report file, then the LP-MOM section, then the combined verdict. A run that stops early
must still leave a usable LP-THR verdict.

## AUDIT FOCUS

LP-THR:
- `pairFeasible` orientation `a_j(1−v) ≤ a_i(1+u)` and the contact parameterization (15) (`contactScale`,
  `contactPoint`, `α = a_i/a_j`), against MAIN lines 147–150.
- `pairThreshold` is a total `sInf` (overnight default OD-2). Check the attained-minimum characterization
  (`pairThreshold_isLeast`, `exists_pairThreshold_attained`) and that no downstream statement depends on
  off-chamber values. The carrier API (`OrderedActions`, `orderedPairThreshold`, `orderedStrongThreshold`) is
  definitionally the total helper.
- The finite minima use `⨅` over `AdjIdx n` / `Fin n`. In ℝ an empty `⨅` is 0, so check that every theorem that
  needs nonemptiness carries `2 ≤ n` / `1 ≤ n`.
- `strongThreshold_eq_min_first`: (14), `B = min(B_cross, I_1)`.
- `continuousOn_pairThreshold`: the route via `IsCompact.continuous_sInf` on the chamber subtype.

LP-MOM:
- `orbital_identities`: no prograde premise; the radial case `e = 1`, `L = 0`.
- `strongAMD` uses `|totalMomentum|` (OD-1). `strongAMD_eq_physicalAMD` is the bridge for `L ≥ 0`, and
  `isMovingSolutionOn_reflectPhase_iff` with the invariance lemmas is the N8 reflection bridge for `L < 0`.
- `cross_sign_and_margin`: MAIN's "if `C ≤ B_⋆ − m` then `H_i ≥ m`", stated per planet with `0 < L_i * L`.
- `hamiltonianVectorField_reflectPhase`: the chain-rule argument and the symplectic sign convention of
  `KAM.Iso.hamiltonianVectorField`.
- Deviation reported by the prover: `strongAMD_sub_eq_sum` drops MAIN's negative-energy premise. It is a stronger
  statement; confirm that it is still true and faithful.
