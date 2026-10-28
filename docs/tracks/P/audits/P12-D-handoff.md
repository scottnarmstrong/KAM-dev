# P12-D prover handoff (branch inp-p12d, b8f076d; off inp; offloaded package run by the main orchestrator; prover on claude-10)


**Files (new):** `KAM/Planetary/PlanarAssembly/Transport.lean` (97 lines), `KAM/Planetary/PlanarAssembly/Measure.lean` (~175 lines).
No other file touched; `KAM.lean` NOT regenerated (lint reports "KAM.lean is out of date; run scripts/gen_root_imports.py" — orchestrator to run it on landing).

**Declarations (signatures verbatim from P1213Signatures.lean, namespace `KAM.Planetary.PlanarAssembly`):**
- `transport` (bpP:p12:transport; tr-an/per/inj/lag/tr-flow/tr-dio): Transport.lean.
- `cylinder_set_shift` (stepP:p12:me-inv), `measure` (me-cell, me-meas), `measure_in_tube` (me-tube): Measure.lean.

**Approach.**
- transport: `IsChart 1 Ψ O` from analytic + symplectic; `chartPullback 1 G Ψ =ᶠ H` near each point of `O` (O open); G-differentiability via `chart_field_differentiableAt_iff`; periodicity from hQ1 and the cylinder-torus lattice law; injectivity mod ℤ from hQ2 + frozen torus injectivity; injective derivative via `bijective_fderiv`; Lagrangian via `hΨs`; Diophantine data reused (`a+b-1 < a+b < τ`); flow via `chart_orbit` (fderiv of eventually equal functions agree).
- cylinder_set_shift: completes `k` by zero on slow indices (`Fin.append k 0`), uses the frozen torus lattice law `K(θ+ℓ)=Kθ+fastShift(ℓ∘castAdd)` and `range K ⊆ S`; reverse inclusion via `-k`.
- measure: floor-shift into `[0,2π)` fast cell (using the shift invariance and hQ1); InjOn on the cell from hQ2 and `2π k i ∈ (-2π,2π)`; Borelness via `S ∩ cylinderCell V r = S ∩ {fast bounds}` using `S ⊆ cylinder V r` (no measurability of V); `measurableSet_chart_image` and `chart_measure_image` at c=1 (volume factor `ofReal (1^d)=1`).
- measure_in_tube: `MapsTo.mono_left` with `S ⊆ cylinder V r`; finiteness via `volume_lt_top_of_subset_circularTube`.

**Checks.**
- Gate build `KAM.Planetary.PlanarAssembly.Measure KAM.Planetary.PlanarAssembly.Transport`: "Build completed successfully (9113 jobs)", no warnings in my files.
- `scripts/lint_sources.sh`: check_lean_modules PASS (698 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only note: KAM.lean out of date (generated; not edited, rule 10). Line lengths ≤100 checked.
- `#print axioms` for transport, cylinder_set_shift, measure, measure_in_tube: all `[propext, Classical.choice, Quot.sound]`.
- No sorry/axiom/maxHeartbeats/EuclideanSpace; no provider or DRAFT_SORRY imports (frozen Defs only).

**Uncertainties / deviations:** none; all signatures proved as stated, no extra hypotheses. Delivery gates: consumed Part 1 results (`IsChart`, `chart_field_differentiableAt_iff`, `chart_orbit`, `measurableSet_chart_image`, `chart_measure_image`) and P6-5 `volume_lt_top_of_subset_circularTube` are in-tree on inp with the same axiom set; I did not re-audit them beyond their statements.
**Suspected errata:** none.
**Design signals:** none (all proofs elaborate at default heartbeats; each build ≈ 12–17 s).

AUDIT FOCUS (design docs/tracks/P/design/P1213-LEAN-DESIGN.md row P12-D and node table; audits DESIGN-P1213-design-audit-{1,2}.md; signatures .drafts/design/P1213Signatures.lean): (1) statements = signature file exactly (transport, cylinder_set_shift, measure, measure_in_tube); (2) proofs sound (frozen cylinder/physical predicates, Part 1 Chart, Transport, Liouville, P6-5 finite tube volume consumed as designed; generic local lemmas independent of P12-C); the transport hypotheses hQ1/hQ2 (lattice periodicity/injectivity) are signature premises: confirm they are source premises, not smuggled conclusions; no added premises; (3) hygiene (no EuclideanSpace; the FROZEN KAM.Planetary.fastShift is used deliberately; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/PlanarAssembly/Transport.lean and Measure.lean.
