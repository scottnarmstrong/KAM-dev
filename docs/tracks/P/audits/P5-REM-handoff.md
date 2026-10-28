# P5-REM prover handoff (branch inp-p5rem, 6ea225e; contains inp-p5jet (in audit) and inp-p5ex (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/PGAssembly/Remainder.lean` (≈357 lines). Nothing else touched (KAM.lean not edited).

**Declarations (signatures verbatim from P45Signatures.lean):**
- `KAM.Planetary.schwarz_order_five` (`stepP:p5:ur-schwarz` helper): removable-singularity quotient g/z^5
  (via `analyticOrderAt`/`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`), maximum principle
  (`Complex.norm_le_of_forall_mem_frontier_norm_le`) on circles R'<R (`schwarz_quotient_bound`), then R'↑R.
- `KAM.Planetary.uniform_remainder` (`bpP:p5:uniform-remainder`, `stepP:p5:ur-bound`): r1 = pgOscRadius/4,
  CQ = M1/(pgOscRadius/2)^5. M1 from helpers: `complexAverage_norm_le` (|avg| ≤ MP, integral over the torus box),
  `jet_norm_le` (Cauchy via `KAM.norm_iteratedFDeriv_le_of_closedBall`, jets of orders 2,4 and value at 0),
  `cPoly_norm_le`, `remainder_bound`. Then Schwarz on the complex line t ↦ Q(t•x) using
  `remainder_jet_tube` (P5-JET) and `KAM.iteratedDeriv_line_eq_iteratedFDeriv`. x = 0 handled via jet order 0.
  Uniform in mu ∈ [0,mu0] and I in the δ/4 tube (the argument works on the δ/2 tube).

**Checks:**
- `inp_lake_build.sh … KAM.Planetary.PGAssembly.Remainder`: "Build completed successfully (9113 jobs)"; only warnings are pre-existing unused-variable warnings in Jets.lean:98.
- `lint_sources.sh`: passes all file checks (line length, modules, frozen-anchor guard, ABI hashes); only message is the expected "KAM.lean is out of date" (generated root, not edited per rules).
- `#print axioms` for `schwarz_order_five` and `uniform_remainder`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties:** none; no signature changed, no extra hypotheses. `hM : 0 ≤ M` in `schwarz_order_five` is unused mathematically (consumed by a dummy `have _ := hM` to avoid a linter warning).
**Errata / deviations:** none. No heartbeat issues; no imports of providers or DRAFT_SORRY anchors.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-REM, proof plan and 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) statements = design signatures exactly (schwarz_order_five, uniform_remainder); constants and radii as designed; (2) proofs sound (one-variable maximum principle, P5-JET jets consumed as designed); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/PGAssembly/Remainder.lean (compare with branch inp-p5jet).
