# P5-PAR prover handoff (branch inp-p5par, d30c588; contains inp-p5scale (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/PGAssembly/Parameters.lean` (~75 lines).
**Declarations:** `PGParameters`, `params`, `checkedCore`, `pgActionDomain`, `pgD0`, `admissible` — copied verbatim
from P45Signatures.lean (only whitespace line-wraps of two lines for the 100-column lint). All are definitions; no proofs.
**Approach:** imports Scales (P5-SCALE), PGMeasure.Setting (P4 `freq`), Hamiltonian.Diophantine (P1 `twoScaleDiophantine`).
No frozen theorem or provider imported.
**Checks:** `inp_lake_build.sh ... KAM.Planetary.PGAssembly.Parameters` -> "Build completed successfully", no warnings in
my file. `scripts/lint_sources.sh`: only message "KAM.lean is out of date" (expected; KAM.lean is generated, not edited),
check_lean_modules PASS, frozen guard OK, ABI OK, no line-length complaints after the wrap.
**Axioms:** params, checkedCore, pgActionDomain, pgD0, admissible: propext, Classical.choice, Quot.sound only
(from `pgScales` choice).
**Uncertainties / errata / deviations:** none. No heartbeat problems.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-PAR, proof plan and 'Revision 4'; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): this package is DEFINITIONS ONLY, so check each body as a definition audit: (1) PGParameters, params, checkedCore, pgActionDomain, pgD0, admissible = signature file exactly (line wraps whitespace-only); (2) each body means the source object on its whole carrier (no fallback/default branches, no arbitrary witness choice, no over-broad carrier); P5-SCALE, P4 freq and P1 twoScaleDiophantine used as designed; (3) hygiene. Audit ONLY KAM/Planetary/PGAssembly/Parameters.lean.
