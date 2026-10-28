# S7-R prover handoff (branch inp-s7r, 8076b5a; contains inp-s8b (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/SecularForm/ProductInterface.lean` (341 lines). No other file touched (KAM.lean not regenerated; lint reports it out of date, as expected).

**Declarations (signatures verbatim from P810Signatures.lean):** `SecularForm.keplerActionHam` (def), `product_chart`, `pc_prod`, `pc_share`, `pc_dec`, `SecularSpectrum.lattice`.
`polarMap`/`polarDom` already exist verbatim in `KAM/Planetary/Poincare/Lattice.lean` (identical bodies to the draft); not redefined. `angleScale`/`fullShift` come from Hamiltonian/Chart.

**Approach:**
- `pc_prod`, `lattice`: assembled from delivered Poincare/Product and Poincare/Lattice ingredients (`analyticOnNhd_poincareProd`, `poincareProd_symplectic`, `poincareProd_image`, `poincareProd_eq_iff`, `poincareProd_localDiffeo`, `analyticOnNhd_polarMap`, `polarMap_symplectic`, `polarMap_mapsTo`, `polarDom_shift`, `poincareProd_polar_lattice`, `poincareProd_polar_periodOne_symplectic`).
- Field transport: new `field_transport` (A X_{ℓ∘A} = X_ℓ for a symplectic surjection between phase spaces of syntactically different dimension) and `poincareProd_field` (via `poincareProd_fderiv_equiv` surjectivity + `poincareProd_symplectic`). `pc_share` uses it with `differentiableAt_{moving,fixed}Hamiltonian` at NoCollision plus the delivered `*_poincareProd` splits. `pc_dec` uses it with keplerPart, whose differentiability at the image needs only nonzero positions (from `regionProd`/`poincare_elements`): new public `analyticAt_keplerPart'` (Models.lean's version is private, copied locally with private helpers; no pair guard), and `hProd = keplerPart ∘ poincareProd` eventually near w.
- `product_chart`: `keplerActionHam` rewritten as `-∑ κ²m³/(2 I²)`; analytic on positive actions; first/second derivatives by line derivatives (`hasDerivAt_nu` from Product.lean); vector field of `hProd` from the explicit `fderiv_hProd` formula.

**Checks:**
- `lake build KAM.Planetary.SecularForm.ProductInterface` via compile gate: `Build completed successfully (9114 jobs)`, no warnings from my file.
- `scripts/lint_sources.sh`: line length OK, check_lean_modules PASS (552 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message is "KAM.lean is out of date" (generated; not edited per rules).
- `#print axioms` of product_chart, pc_prod, pc_share, pc_dec, lattice: `[propext, Classical.choice, Quot.sound]` each.
- No sorry/axiom/maxHeartbeats; no provider or frozen-theorem imports.

**Uncertainties:** none; no statement needed changes. Hypothesis `hW : NoCollision ...` in pc_share used only for differentiability.
**Errata / deviations:** none suspected. Design signals: none (all at default heartbeats).

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S7-R and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements/definitions = design signatures (product_chart, pc_prod, pc_dec, pc_share; polarMap/polarDom exact draft definitions and lattice); the delivered Poincare ingredients and P1 fullShift consumed, not re-declared; (2) proofs sound; no added premises; (3) hygiene. Audit ONLY SecularForm/ProductInterface*.lean (compare with branch inp-s8b).
