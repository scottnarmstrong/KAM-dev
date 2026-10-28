# A4 prover handoff (P14; branch inp-p14-a4, 84b11769; off inp; offloaded package run by the main orchestrator; prover on claude-8)


- Files: new `KAM/Planetary/AMD/MovingODE.lean` (~50 lines). Only declaration assigned: `KAM.Planetary.moving_ode` (signature verbatim).
- Approach: openness from `isOpen_collisionFreeDomain`; C^1 field from `analyticOnNhd_movingHamiltonian` -> `AnalyticOnNhd.contDiffOn` (open => UniqueDiffOn) -> `KAM.ODE.ham_smooth_c1`; predicate bridge by unfolding `IsMovingSolutionOn`/`IsHamiltonianSolutionOn` (differentiability from analyticity).
- Checks: gate build `KAM.Planetary.AMD.MovingODE` succeeded (only pre-existing Kepler/Energy linter warnings). `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; it reports "KAM.lean is out of date" (expected; KAM.lean not edited per rules).
- `#print axioms KAM.Planetary.moving_ode`: propext, Classical.choice, Quot.sound.
- No sorry, no heartbeat overrides, no EuclideanSpace. Name `moving_ode` not previously used in KAM outside Frozen/design.
- Uncertainties/errata/deviations: none. No design signals.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row A4, Appendix A and node rows; audits DESIGN-P14-design-audit-{1,2}.md; signatures .drafts/design/P14Signatures.lean): (1) moving_ode = signature file exactly, and the A4 slice is COMPLETE; (2) proof sound (openness of the collision-free domain, C^1 field from analyticity, KAM.ODE.ham_smooth_c1; Newtonian/Models and ODE/Hamiltonian consumed as designed); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/AMD/MovingODE.lean.
