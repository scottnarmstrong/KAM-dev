# A6 prover handoff (branch inp-p14-a6, 0ac29a11; contains A3 and A5 (both passed; A3 on inp); offloaded P14 package run by the main orchestrator; PROVIDER package for the frozen DRAFT_SORRY anchor KAM.Planetary.amdConfinement)


## Files
- NEW `KAM/Planetary/AMD/ConfinementExit.lean` (~95 lines): abstract first-exit lemmas `amd_exit_forward`, `amd_exit_backward` (built on `KAM.ODE.gen_exit`).
- NEW `KAM/Planetary/AMD/Confinement.lean` (~190 lines): `isMovingSolutionOn_mono_of_subset`, `amd_inner_mem_collar`, `amd_collar_at`, `amd_collar_of_solution`, and the library theorem `KAM.Planetary.amd` (signature copied verbatim).
- CHANGED `KAM/Provider/Planetary/AmdConfinement.lean`: imports `KAM.Planetary.AMD.Confinement` only; `KAM.Provider.Planetary.amdConfinement` (telescope verbatim) with body `by exact KAM.Planetary.amd hn B hB mu T delta hmu hT hdelta hmargin hAMD z0 hz0 hstop`.
- Frozen anchor, manifest, KAM.lean untouched. Commits: e17f752e plus a line-wrap follow-up on branch inp-p14-a6.

## Approach
Apply `gen_confinement` with W = collisionFreeDomain, Phi = amdCompact B (uniform data from `gen_uniform_compact`, `amd_compact`).
The a priori confinement `hconf` comes from `amd_collar_of_solution`:
`amd_collar_at` uses `hstop` on [a,b] with a<=0<=b inside [-T,T] where the solution is in the outer region, plus `ang_mom`, to get the collar
(actions within delta of the inner datum; AMD = sum actions - momentum bounded by initialAMD + n*delta).
`amd_exit_forward/backward` (first exit via gen_exit; the exit time is a limit of earlier collar points, so `amd_closure` puts it in the collar, contradicting exit; backward by time reversal) show the solution never leaves the collar.
Collar is inside the outer region, hence in amdCompact by `geometry`. `gen_confinement` yields maximal z, z(0)=z0, solution on [-T,T] (strictly inside the maximal interval, so continuation beyond +-T comes for free from `gen_continuation`; `amd_compact` supplies the compact set).
MovingUniqueOn via `gen_uniqueness_inter` (U convex => OrdConnected); Newton via `isNewtonSolutionOn_of_isMovingSolutionOn`; momentum via `ang_mom`; ecc/radial/PairBounds via `geometry`; drift via `hstop` on [-T,T].
Uses `amd_closure` (not `closure`). `hn : 2 <= n` is unused (kept for the telescope; `have _hn := hn`).

## Checks
- Gate builds `KAM.Planetary.AMD.ConfinementExit`, `KAM.Planetary.AMD.Confinement`, `KAM.Provider.Planetary.AmdConfinement`: all succeed, no sorry, no errors (only pre-existing warnings in upstream files).
- `#print axioms KAM.Provider.Planetary.amdConfinement` and `KAM.Planetary.amd`: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: one over-100-column line (ConfinementExit.lean:48) was reported and fixed; the remaining message is "KAM.lean is out of date" (expected; regeneration is the integrator's job: new modules ConfinementExit, Confinement). The script takes >2 min here (timed out my 110s wrapper after printing the above); check_lean_modules PASS, FROZEN-ANCHOR GUARD OK.
- Statement of the provider compared with the frozen anchor's: identical telescope.

## Uncertainties / errata / deviations
- None found; no statement looked false. No heartbeat issues (all default). No deviations.
- Extra public names (grepped unique): amd_exit_forward, amd_exit_backward, amd_inner_mem_collar, amd_collar_at, amd_collar_of_solution, isMovingSolutionOn_mono_of_subset. `amd` itself is assigned to this package; no declaration belongs elsewhere.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row A6, the provider table row amdConfinement (line ~438) and 'Provider assembly to exact frozen types' (~418-432), the amd_closure rename note; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean; manifest/frozen-anchors.json entry planetary.d25.amdConfinement and its frozen file): this is a SEAL-KEY audit. (1) KAM.Planetary.amd = signature file EXACTLY; (2) KAM.Provider.Planetary.amdConfinement has EXACTLY the frozen anchor's type (compile an exact-type probe: the frozen statement's type is defeq/syntactically equal to the provider's; every binder, quantifier order, conjunction), and its body is the one-line application of amd; the provider file imports only KAM.Planetary.AMD.Confinement; (3) the proof consumes the intended predecessors per the plan (maximal solution, first exit only using hstop on [0,s]/[-s,0] inside the outer region, ang_mom for AMD(t)-AMD(0), amd_closure for no exit, gen_continuation, Reconstruction to the Newton predicate) and no hard step is a hypothesis; the unused hn is a signature premise; (4) quarantine: no module other than the anchor will import the provider; no DRAFT_SORRY import; (5) hygiene (no EuclideanSpace; no public short name used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/AMD/Confinement{,Exit}.lean and KAM/Provider/Planetary/AmdConfinement.lean (A5 AngularMomentum was audited separately).
