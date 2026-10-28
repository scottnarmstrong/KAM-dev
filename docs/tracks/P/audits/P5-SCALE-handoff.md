# P5-SCALE prover handoff (branch inp-p5scale, e696db6; contains inp-p5fd (audited); offloaded package run by the main orchestrator; prover on claude-12)


Files: new `KAM/Planetary/PGAssembly/Scales.lean` (134 lines). Nothing else changed.

Declarations (signatures verbatim): `log_power_dominated`, `kam_c1`, `PGScales`, `pgTau`, `pgK0`, `pgChat`,
`PGScaleSpec`, `kam_cond`, `pgScales`. Extra helpers (new names): `log_power_dominated_large`
(unbounded K, from `isLittleO_log_rpow_rpow_atTop`), `pgTau_pos`, `pgChat_pos`, `pgWidth_pos`,
`one_le_kam_c1`, `pgScales_spec`.

Approach: `log_power_dominated_large` takes `c = 1/(2A)` in the little-o and intersects with
`K ≥ M`, `K > 1`. `kam_cond`: `k0 = C^2 K` with `K ≥ e` from the lemma
(`A = 9*chat*(720/w)^p`, `p = 2tau+2`), so `max 1 (log (k0^2/C^4)) = 2 log K`; `k1 = 4*chat*C^2+1`;
`G` = the max expression itself. No sorry/axiom, no heartbeat options.

Checks: gate build `KAM.Planetary.PGAssembly.Scales` succeeded (only warning: unused `hp` in
`log_power_dominated_large`'s signature-copy... actually in `log_power_dominated`, kept verbatim).
`scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; it reports
"KAM.lean is out of date; run scripts/gen_root_imports.py" (new module not in the generated root;
not edited per rules, orchestrator to regenerate).
`#print axioms` of log_power_dominated, kam_cond, kam_c1, pgScales: propext, Classical.choice, Quot.sound.

Uncertainties/errata/deviations: none. Statements were true as given (needs only `delta_pos`).

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-SCALE, proof plan and 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) statements and definitions = signature file exactly (log_power_dominated, kam_c1, PGScales, pgTau, pgK0, pgChat, PGScaleSpec, kam_cond, pgScales); (2) proofs sound (isLittleO_log_rpow_rpow_atTop; P5-FD consumed as designed); constants as designed; no added premises; (3) hygiene. Audit ONLY KAM/Planetary/PGAssembly/Scales.lean.
