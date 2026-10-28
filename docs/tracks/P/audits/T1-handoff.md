# T1 prover handoff (P11C; branch inp-p11c-t1, 9f933900; off inp; offloaded package run by the main orchestrator; prover on claude-8)


**Files:** new `KAM/Planetary/PlanarTorsion/Setting.lean` (~65 lines). Branch inp-p11c-t1.

**Declarations (verbatim from P11CSignatures.lean, namespace KAM.Planetary):** `PlanarData`, `PlanarData.Valid`,
`PlanarData.kappa`, `p11c_axes`, `PlanarData.actions`, `PlanarData.axes`, `p11c_hatFix`, `p11c_hatMov`,
`p11c_secular`, `p11c_slowLength`, `p11c_pairDot`, `p11c_quartic`, and `p11c_homogeneousPart`.
All are definitions/structure; no theorems, so no `#print axioms`.

**Deviation / note for the orchestrator:** `p11c_homogeneousPart` is assigned to T6 in the design table, but design
audit N2 proposes moving it to Setting (T12 needs it earlier), so I placed it here. T6 must import it and NOT
redefine it (duplicate name). Also per N2: T15 can import Setting for `p11c_slowLength`.
The only change versus the signature file is the header/docstring and imports (`Poincare.Product`,
`Frozen...SecularAverage`; `Mathlib`); no existing KAM declaration used these names (grepped).

**Checks:** gate build `inp_lake_build.sh /root/code/KAM-inp-p11c-t1 KAM.Planetary.PlanarTorsion.Setting`: succeeded
(9109 jobs, no warnings in Setting). Default heartbeats, no overrides, no EuclideanSpace. `scripts/lint_sources.sh`:
PASS (check_lean_modules, frozen guard, ABI hashes OK; the only message is "KAM.lean is out of date", which is generated and not mine to edit).

**Uncertainties / errata / design signals:** none.

AUDIT FOCUS (design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T1 and Appendix; audit DESIGN-P11C-design-audit-1.md; signatures .drafts/design/P11CSignatures.lean): DEFINITIONS package: (1) PlanarData, PlanarData.Valid, kappa, p11c_axes, actions, axes, p11c_hatFix, p11c_hatMov, p11c_secular, p11c_slowLength, p11c_pairDot, p11c_quartic, p11c_homogeneousPart = signature file exactly, and the T1 slice is COMPLETE; (2) each body means the source object on its whole carrier (no fallback/default branches; PlanarData/Valid carry only source data and premises; the U2/frozen adapters match the frozen objects); (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/PlanarTorsion/Setting.lean.
