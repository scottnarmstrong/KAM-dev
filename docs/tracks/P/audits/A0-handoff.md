# A0 prover handoff (P14; branch inp-p14-a0, f93fcab7; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/AMD/Setting.lean` (≈45 lines). Branch inp-p14-a0.
**Declarations (bpP:p14:conv#data), copied verbatim from P14Signatures.lean:** `KAM.Planetary.amdOuter`,
`amdInner`, `amdCollar`, `amdCompact`. Grep confirmed none existed in KAM beforehand. Only frozen Defs imported
(AMDBox, BodyVector, KeplerAction, LowAMDRegion, PhysicalAMD, PlaneLength); no provider/DRAFT_SORRY imports.
**Approach:** definitions only; no proofs, no heartbeat/recursion overrides; no EuclideanSpace.
**Checks:** gate build `KAM.Planetary.AMD.Setting`: "Build completed successfully (9090 jobs)", no warnings.
`scripts/lint_sources.sh`: no long-line complaint after the fix; modules check PASS (766 files), frozen-anchor guard OK,
ABI hashes OK. Only the expected "KAM.lean is out of date" notice (generated; not edited per rules).
**#print axioms:** not applicable (definitions only, no theorems).
**Uncertainties / errata / deviations / design signals:** none. (Note: `collisionFreeDomain` etc. not needed here.)

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row A0, Appendix A and node rows; audits DESIGN-P14-design-audit-{1,2}.md; signatures .drafts/design/P14Signatures.lean): DEFINITIONS package: (1) amdOuter, amdInner, amdCollar, amdCompact = signature file exactly; (2) each body means the source object on its whole carrier (no fallback/default branches, no arbitrary witness, no over-broad carrier; any Prop structure contains only source data/premises); frozen definitions used as the design names them; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/AMD/Setting.lean.
