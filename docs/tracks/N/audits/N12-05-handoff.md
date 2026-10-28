# N12-05 prover handoff (branch inp-n1205, 3ba47d7; base inp-n1204; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/Corrector.lean` (118 lines), committed on inp-n1205. No other file touched.
**Nodes:** `bpN:p12:corrector` -> `KAM.Nekhoroshev.corrector`. Definitions copied verbatim from N12Signatures.lean: `avgPsi`, `avgPsiD`, `avgU`, `avgW`, `avgWenv`, `avgW1env`, `avgBterm`, `avgBenv`, `avgRenv`, `avgPhiEnv`, `avgResidual`.
**Approach:** `corrector` by elementary algebra: `ContDiff.div` with positive denominator; `HasDerivAt` via quotient rule; bounds via `y^2+κ^2 ≥ 2|y|κ`, `|κ²−y²| ≤ y²+κ²`. No regularity of `avgW` assumed; no imports beyond `Averaging.Coefficients`.
**Checks:** gate build of `KAM.Nekhoroshev.Averaging.Corrector`: success. `scripts/lint_sources.sh`: only complaint is "KAM.lean is out of date" (generated; I did not edit it; orchestrator must run gen_root_imports.py); modules/frozen/ABI checks PASS. No sorry, no heartbeat overrides.
`#print axioms KAM.Nekhoroshev.corrector`: [propext, Classical.choice, Quot.sound].
**Uncertainties / errata / deviations:** none. Signature variable block uses `{n}` only (h, f are explicit binders in the defs). Signature statements all unchanged.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-05 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements/definitions = design (rational divisor calculus, avgU, avgW, envelope definitions; NO regularity assumed), faithful on their whole carrier; (2) proofs sound; no added premises; (3) hygiene. Audit ONLY the Corrector module(s) (compare with branch inp-n1204).
