# PP1-6 prover handoff (branch inp-pp16, 850e2c3; contains inp-pp14, inp-pp11 (delivered); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- NEW `KAM/Planetary/Hamiltonian/Transport.lean` (373 lines). No other file touched (KAM.lean not regenerated).
  Imports: Chart (PP1-4), Diophantine (PP1-2, audit note N1), frozen Defs, Kepler.Basic, ODE.Basic. No provider / DRAFT_SORRY import.

## Nodes -> declarations (signatures copied verbatim from PPart1Signatures.lean section D)
- `bpP:p1:lattice-torus` -> `IsLatticeTorus`
- `bpP:p1:torus-transport` -> `torus_transport_cyl`, `torus_transport_phys`, `fderiv_chart_comp_torus`
- `bpP:p1:period-convert` (c) -> `periodOne`, `IsTwoPiLatticeTorus`, `analyticOnNhd_periodOne_iff`, `fderiv_periodOne`,
  `periodOne_lattice_iff`, `periodOne_injMod_iff`, `periodOne_hasDerivAt_iff`, `isLatticeTorus_periodOne_iff`
- `bpP:p1:cyl-pipeline` -> `cyl_pipeline`; `bpP:p1:phys-pipeline` -> `phys_pipeline`

## Approach
- Private `transport_core` (analyticity, differentiability of H at Ψ∘K, injectivity, Lagrangian, flow via `chart_orbit`) shared by cyl/phys;
  lattice/injectivity-mod clauses per case (cyl uses `hQ2` with `Fin.append k 0`, `Fin.append_left`; then L2, L3).
- period-convert (c): rescaling lemmas (`(2π)•(2π)⁻¹•ϑ = ϑ`); `fderiv_periodOne` by case split on differentiability of κ
  (unconditional); `isLatticeTorus_periodOne_iff` clause by clause.
- `cyl_pipeline`: `IsChart.comp` of `angleScale (2π)` (mono from univ) with Φ (`mul_one`), `angleScale_add_angleShift`, injectivity of `angleScale`.
- `phys_pipeline`: `chartPullback 1 H Φ = H ∘ Φ`, `isLatticeTorus_periodOne_iff`, `isDiophantine_smul_iff`, `Set.range_comp`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-pp16 KAM.Planetary.Hamiltonian.Transport`: "Build completed successfully (9059 jobs)"; only warning in my file: unused `hc` in `fderiv_chart_comp_torus` (signature kept verbatim).
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only complaint is
  "KAM.lean is out of date" (expected: generated file, not edited per brief; orchestrator regenerates).
- No `sorry`, `set_option`, axiom; no heartbeat issues (module elaborates in ~30 s at default heartbeats).
- `#print axioms` of torus_transport_cyl, torus_transport_phys, fderiv_chart_comp_torus, isLatticeTorus_periodOne_iff,
  cyl_pipeline, phys_pipeline: all `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations
- None: no statement was false or under-hypothesised; no signature changed. No source errata found.
- Minor: `hc` unused in `fderiv_chart_comp_torus` (kept as in signature).

AUDIT FOCUS (design docs/tracks/P/design/PART1-LEAN-DESIGN.md row P1-6 (Transport) and proof plan; its audit DESIGN-P1-design-audit-1.md; KEPLER design Part 1 dependency (item 8: S_c = angleScale, fullShift, lattice), P7-6 row; blueprint-P p1 lattice-torus, torus-transport, period-convert (c), cyl-/phys-pipeline): (1) statements = design signatures and blueprint; consumable by P7-6 as designed; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the PP1-6 module(s) (KAM/Planetary/Hamiltonian/Transport*).
