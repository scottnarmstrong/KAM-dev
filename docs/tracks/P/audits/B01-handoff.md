# B01 prover handoff (P11B; branch inp-p11b-b01, 25caaf5f; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/WeakKAM/Data.lean` (115 lines). Commit 25caaf5f on inp-p11b-b01. KAM.lean untouched.

**Approach:** signature lines 38-112 of P11BSignatures.lean copied verbatim (SelectionR/C/PhaseC/Point, selectionReal/Re/Length/Thick/Domain/Scalar/DG/DGVector, SelectionData, SelectionPerturbation, sel_data), with the signature file's header, imports (lines 8-24), `@[expose] public noncomputable section`, opens, namespace KAM.Planetary and the same `variable` line, plus a module docstring and `end KAM.Planetary`. No proofs needed (definitions/structures only). Grep confirmed none of the 15 names exists elsewhere in KAM, so nothing was imported instead of redefined.

**Checks:**
- Gate build `KAM.Planetary.WeakKAM.Data`: "Build completed successfully (9079 jobs)", no warnings.
- `scripts/lint_sources.sh` exit 0: check_lean_modules PASS (765 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK. It prints "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: new module not in generated root; I must not edit KAM.lean, orchestrator regenerates).
- `#print axioms` of SelectionData, SelectionPerturbation, sel_data: [propext, Classical.choice, Quot.sound].

**Uncertainties:** the signature's `variable {n μ : ℕ} {t C₁ : ℝ}` stays (unused ones are harmless; kept verbatim). Imports mirror the full signature header (some unneeded for B01; downstream packages may narrow).

**Suspected errata / deviations:** none. No heartbeat options, no sorry, file well under 1500 lines. Design signals: none. Note audit-1 (selectionFixedKey requires d.h = d₀.h) concerns later packages, not B01.

AUDIT FOCUS (design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B01 and Appendix; audits DESIGN-P11B-design-audit-{1,2}.md; signatures .drafts/design/P11BSignatures.lean lines 38-112): this package is mostly DEFINITIONS: (1) SelectionR/C/PhaseC/Point, selectionReal/Re/Length/Thick/Domain/Scalar/DG/DGVector, SelectionData, SelectionPerturbation, sel_data = signature file exactly; (2) each definition body means the source object on its whole carrier (no fallback/default branches, no arbitrary witness choice, no over-broad carrier; SelectionData/SelectionPerturbation contain only source premises, not proof steps); sel_data proved; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/WeakKAM/Data.lean.
