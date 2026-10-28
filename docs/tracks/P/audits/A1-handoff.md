# A1 prover handoff (P14; branch inp-p14-a1, 2a9f95f0; off inp; offloaded package run by the main orchestrator; prover on claude-10)


**Files:** new `KAM/Planetary/AMD/Elements.lean` (275 lines). Commit 2a9f95f0 on `inp-p14-a1` (handoff file itself is under .drafts, not force-added).

**Declarations (signatures verbatim from P14Signatures.lean, checked by script text-diff):** `KAM.Planetary.elements`, `KAM.Planetary.eccentricity_deficit`, `KAM.Planetary.ecc_bound`. Two private helpers: `planeSq_ecc_aux`, `elements_scalar`. No public name clash (grepped KAM).

**Approach:** `planeSq_ecc_aux` is the Lagrange-identity computation |e|² = 1 + 2E·C²/m³ (componentwise, field_simp + linear_combination with r² = q0²+q1²). `elements` establishes the dot-product identity q·e = C²/m² − r the same way, then generalizes every compound term to a real variable and applies the pure-real `elements_scalar` (axis/action/energy/|e|<1/radial bounds from |q·e| ≤ r|e|/etc.). `eccentricity_deficit` is monotonicity of sqrt on clause (l). `ecc_bound`: physicalAMD = Σ(Λ_i − C_i) with nonnegative summands (clause (m)), so each deficit < A ≤ lo_i(1−√(1−e²)) ≤ Λ_i(1−√(1−e²)); contradiction with eccentricity_deficit if |e_i| ≥ e; the second conjunct is the same inequality rearranged.

**Checks:**
- `lake env lean` on the file: no errors/warnings.
- `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh <worktree> KAM.Planetary.AMD.Elements`: "Built KAM.Planetary.AMD.Elements (36s). Build completed successfully".
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; it prints "KAM.lean is out of date; run scripts/gen_root_imports.py" because the new module is not yet in the generated root (I did not edit KAM.lean per rules; orchestrator regenerates).
- grep: no maxHeartbeats, EuclideanSpace, sorry in the file.
- `#print axioms` of elements, eccentricity_deficit, ecc_bound: [propext, Classical.choice, Quot.sound] each.

**Uncertainties:** none. `eccentricity_deficit` does not use `he1` (kept for the verbatim signature; referenced via `have _ := he1` to avoid an unused-variable warning).

**Errata / deviations:** none. No signature changed; no extra hypotheses. No design signals (default heartbeats throughout; an early scalar-heavy version timed out because of large compound terms, resolved by generalizing to real variables, not by budgets).

## Completeness check (orchestrator note)
The A1 / `AMD/Elements` slice of P14Signatures.lean is exactly `elements`, `eccentricity_deficit`, `ecc_bound` (all proved, verbatim). The design node table lists for this module only `bpP:p14:elements` (+ steps el-a..el-f, all exported as clauses of `elements`) and `bpP:p14:ecc-bound` (+ eb-sum, eb-ecc, internal to `ecc_bound`). Nothing is missing. Adjacent signatures `amdOuter/amdInner/amdCollar/amdCompact`, `geometry`, `amd_compact`, `closure` belong to A0/A2/A3 per the DAG (A2, A3 depend on A0, A1), so they are intentionally not here.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row A1, Appendix A and node rows; audits DESIGN-P14-design-audit-{1,2}.md; signatures .drafts/design/P14Signatures.lean, the AMD/Elements slice): (1) elements, eccentricity_deficit, ecc_bound = signature file exactly, and the slice is COMPLETE (no declaration the signature file/design assigns to AMD/Elements is missing); (2) proofs sound (Kepler/Plane and frozen elements consumed as designed); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/AMD/Elements.lean.
