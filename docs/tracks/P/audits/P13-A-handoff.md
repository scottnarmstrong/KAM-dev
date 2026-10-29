# P13-A prover handoff (branch inp-fx13a, 3c6c09d8; contains P12-C (in audit); offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/FixedAssembly/Data.lean` (~357 lines). No other file touched (KAM.lean not regenerated:
lint reports it out of date, the orchestrator must run `scripts/gen_root_imports.py`).

**Declarations (signatures verbatim from P1213Signatures.lean):** `FixedAssembly.perturbation` (def),
`fixed_hamiltonian_form` (= `fixedHamiltonian_poincareProd`), `perturbation_difference` (unfold; ring),
`chart_of_preserves_fast`, `pg_hypotheses` (fixed). Graph nodes fixed-hamiltonian-form, fh-chart, fh-id, fh-bnf,
data, chart, ch-same, ch-ham, pg-hypotheses and pg-* steps map to these.

**Approach:** same joint construction as `PlanarAssembly.pg_hypotheses` (P12-C): one `patch` / `PlanarBirkhoffResult`
elimination gives the shared map `T`, cube, jets `P0 = p11c_secular fhat I 0`, `2σ`, `p11c_beta`; the fixed
branch `p11c_hatFix` is taken from the same `hf` clause (`fFix ∘ poincareProd ∘ T` = `FixedAssembly.perturbation`
definitionally). Reuses `PlanarAssembly.{total_chart, kepler_h, forward_tube, collar, fast_diffeo, chart_of_birkhoff,
product_chart, action_center}`, `p12c_box`, `p12c_slow_small`; the three private helpers (tube_isOpen, shift_mem_tube,
slowLength_lt) of P12-C's Data.lean are private there and are copied privately here.
Delivery gate: T, cube, `Ω=2σ`, `β=beta-hat`, `P0fix=C0` are the same objects as in P12-C (same `patch` call shape).

**Checks:** `inp_lake_build.sh ... KAM.Planetary.FixedAssembly.Data`: Build completed successfully (only
unused-simp-arg linter warnings in the upstream P12-C file). `#print axioms` of all four theorems:
[propext, Classical.choice, Quot.sound]. `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK,
ABI HASHES OK; only complaint "KAM.lean is out of date". No sorry/maxHeartbeats/EuclideanSpace; lines ≤100.

**Uncertainties / errata / deviations:** none new. Upstream SOURCE_GAP rows (eigenframe, real flow, Lie/Taylor) are
discharged (or not) by the owner of `patch`; not re-examined here. Joint-existential of fixed and moving are
separate eliminations (own `patch` call), as the signature comment states.

AUDIT FOCUS: design docs/tracks/P/design/P1213-LEAN-DESIGN.md row P13-A (P12-C, Product, same actual Part 8/11b objects as C; fixed perturbation gets fresh joint witnesses) and its node table (fixed-hamiltonian-form, fh-*, data, chart, ch-*, pg-hypotheses, pg-*), and IN FULL the section 'Characterization and delivery gates (P12-C / P13-A)' and the SOURCE_GAP rows; P1213 design audits; signatures /root/code/KAM-inp/.drafts/design/P1213Signatures.lean. Gate checks: same owner objects as P12-C (T, cube, Omega = 2 sigma, beta = beta-hat), certificate P0fix = C0 proved on the same cube; fixed pg_hypotheses is one joint construction with fresh joint witnesses for the fixed perturbation as the design says. Audit ONLY KAM/Planetary/FixedAssembly/Data.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
