# Independent package audit S7-R, audit 1

Overall verdict: **PASS WITH NOTES** for the five owned infrastructure contracts. No defect requiring a Lean change was found. This package proves no frozen anchor; “seal-ready” is inapplicable, and this verdict does not close the whole Part 7 product-chart/lattice nodes or any physical headline.

Audited HEAD: `8076b5a6be4ca142c0dbb1938ccf5baf26e78683`. The requested `git diff inp...HEAD`, with `inp` at `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`, contains exactly one added file, `KAM/Planetary/SecularForm/ProductInterface.lean` (342 lines). The handoff's focused comparison against `inp-s8b` (`326288529ed59457294068ad2b05b5b9295b3099`) gives the identical new file when restricted to `SecularForm/ProductInterface*.lean`. The unrestricted comparison with that older branch contains unrelated inherited work and is outside this audit. The handoff's 341-line count is a harmless counting discrepancy.

Read the package brief, AGENTS, PLAN, DECISIONS, S7-R handoff, P810 design (including its revised Appendix A), both design audits, the actual `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, Part 7 product/lattice statements and proofs, track P's statement/conventions, and the consumed product, lattice, Hamiltonian algebra and Newtonian interfaces. Checked the relevant frozen Phase, Assemble, HamiltonianVectorField, SymplecticForm, NoCollision and physical Hamiltonian definitions. The draft is not present under this package worktree's `.drafts/design`; the main-worktree copy is a literal substring of the current Appendix A. Only this report is added to repository source paths; temporary probes are confined to this worktree's `.lake/abi-scratch/` and removed after use.

## Declaration-by-declaration findings

Names are relative to `KAM.Planetary`. Locations refer to `KAM/Planetary/SecularForm/ProductInterface.lean`.

| Node / role | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| Symplectic linear transport helper | `SecularForm.field_transport` (40) | PASS | Ordinary linear symplectic preservation and surjectivity imply field transport by nondegeneracy. Its premises describe the linear map, not the transport conclusion. Handles syntactically different dimensions. |
| Product-chart transport helper | `SecularForm.poincareProd_field` (51) | PASS | Positive masses/κ, chart-domain membership and differentiability of the target Hamiltonian suffice. Surjectivity is proved by the delivered `poincareProd_fderiv_equiv`, not assumed for the nonlinear chart. Chain rule uses actual differentiability of both maps. |
| Kepler analyticity helper | `SecularForm.analyticAt_keplerPart'` (94) | PASS | Requires only nonzero positions, stated as positive plane lengths. No pair separation and no assumed analytic conclusion; polynomial momentum terms remain analytic even for the total zero-mass convention. Stronger domain than the collision-free combined model. |
| `bpP:p7:product-chart` action definition | `SecularForm.keplerActionHam` (109) | PASS | Literal design body using existing `hProd` and frozen `assemble`; no alternative action Hamiltonian. |
| `bpP:p7:product-chart` (b), owned action/field cut | `SecularForm.product_chart` (196) | PASS | Exact draft signature. Analyticity on all positive actions, first derivative ν, correct negative second derivative and nonvanishing, plus explicit decoupled field with slow and momentum blocks zero. Constants retain κ²m³, with κ = Gm₀. |
| `stepP:p7:pc-prod`, owned quotient cut | `SecularForm.pc_prod` (259) | PASS | Exact draft signature. Joint analyticity, factor-one symplecticity, exact image, both directions of injectivity modulo the fast lattice, and analytic inverse on local chart targets. Existing Product results are consumed directly. |
| `stepP:p7:pc-share`, owned split/transport cut | `SecularForm.pc_share` (276) | PASS | Exact draft signature, same Boolean for physical Hamiltonian and perturbation; arbitrary real coupling, with chart and NoCollision guards exactly as designed. Each Boolean branch uses the matching physical split and genuine differentiability. |
| `stepP:p7:pc-dec`, owned guard-free Kepler cut | `SecularForm.pc_dec` (294) | PASS | Exact draft signature, no pair-collision guard. Region membership proves each position is nonzero. Equality of hProd and the pullback holds throughout an open neighborhood before transporting fderiv. No reliance on total fderiv at a singular point. |
| `bpP:p7:lattice`, owned polar quotient cut | `SecularSpectrum.lattice` (320) | PASS | Exact draft signature on existing polar definitions. Domain invariant under every full radian position shift; physical periodicity and converse lattice identification; period-one composition has conformal factor 2π on the literal preimage domain. |

The five theorem signature headers are equal to the original draft after removing whitespace. A separate Lean probe copies each full draft declaration under a fresh name and supplies respectively `by exact product_chart D`, `by exact pc_prod D`, `by exact pc_share D b μ hw hW`, `by exact pc_dec D hw`, and `by exact lattice D`. Thus binder order, implicit w, Boolean matching, carriers and all conclusions are checked by elaboration as well as textual comparison. There are no provider exports or frozen seals to compare; substituting an unrelated frozen theorem for these infrastructure contracts would be inappropriate.

## Definitions and proof review

Every new definition is classified here, including private helpers:

| Definition | Classification and whole-carrier assessment |
|---|---|
| `SecularForm.keplerActionHam` (109) | Intended action Hamiltonian, literally `hProd (D.G*D.m0) D.m (assemble I 0 0 0)`. At zero actions it inherits total real division; no theorem relies on those off-domain values. |
| private `posL` (71) | Continuous linear extraction of each physical position block using the existing body-index permutation. Exact on the entire phase space. |
| private `momL` (77) | Corresponding momentum extraction, exact on the entire phase space. |
| private `kepEnergy` (112) | Literal `-∑ κ² mᵢ³/(2 Iᵢ²)` on all actions. Total division agrees with `hProd` globally; derivatives/analyticity are guarded by nonzero actions. |
| private `fastL` (127) | Continuous linear extraction of the fast momentum/action block, exactly `fast w.2` everywhere. |

No new abbrev or structure. Existing `Data` contains only positive physical parameters and positive dimension, not proof conclusions. Existing `polarDom` and `polarMap` are reused from Poincare/Lattice; their bodies match the draft exactly after whitespace normalization and the probe checks their literal formulas by `rfl`. In particular `assemble I φ p q = (append φ q, append I p)`, so the cosine is the slow momentum and the sine the slow position. This is the blueprint's positive symplectic sign. P1's `angleScale` and `fullShift` are imported, not redeclared.

Reviewed the private derivative chain: `hProd_eq` and `fast_assemble` give the literal action formula; analyticity is proved before identifying fderiv with a line derivative; the reciprocal-square derivative gives positive κ²m³/I³, and the existing `hasDerivAt_nu` gives the stated negative second derivative. The field computation uses coordinate basis vectors and the frozen `(∂momentum, -∂position)` convention. The nonvanishing conclusion uses physical positivity and positive actions.

`field_transport` uses Ω(u,Xℓ)=ℓ(u) with the frozen sign. `poincareProd_field` derives the needed equivalence/surjectivity from the product derivative and uses the chain rule. For `pc_dec`, the new analytic helper deliberately avoids NoCollision's pair component; the open chart domain supplies eventual equality, hence equality of derivatives. For `pc_share`, NoCollision supplies differentiability of the correct moving/fixed Hamiltonian. The lattice assembly uses the delivered quotient theorem and period-one symplectic theorem, with no additional frequency or time scaling.

## Independent validation

All completed Lean checks below are serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. The targeted build goes through the prescribed compile gate. No heartbeat, recursion or synthesis budget was changed. An initial lint launch without the explicit environment/nice wrapper was interrupted; its child ABI invocation was also stopped, and the complete lint was rerun with the required wrapper. The reported lint result is the latter run.

### Targeted build

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s7r KAM.Planetary.SecularForm.ProductInterface
```

Exit **0**. Gate/build output:

```text
[inp-gate] slot 2 acquired 10:54:35 for KAM.Planetary.SecularForm.ProductInterface
Build completed successfully (9114 jobs).
```

The build replayed existing unused-variable warnings at `Kepler/Energy.lean:106`, `Poincare/Chart.lean:212,247`, `Kepler/Mass.lean:147,157,500`, `Hamiltonian/Algebra.lean:146` and `Hamiltonian/Chart.lean:193`. No warning names the audited file. The gate executes `nice -n 5 lake build` internally.

### Literal signature/definition probe and axioms

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S7RAudit.lean
```

Exit **0**. Five fresh copies of the draft theorem types elaborate with the delivered exports. Three `rfl` examples verify the literal bodies of keplerActionHam, polarDom and polarMap. Complete axiom output:

```text
'KAM.Planetary.SecularForm.field_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poincareProd_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_keplerPart'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.product_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pc_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pc_share' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pc_dec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Source lint

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the expressly permitted stale generated-root result. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (552 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

### Kernel replay

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.ProductInterface
```

Exit **0**. Complete output:

```text
replaying KAM.Planetary.SecularForm.ProductInterface
```

This is one invocation for the sole audited implementation module; there is no provider or additional newly changed lemma module. Kernel replay and the axiom inventory both pass.


Additional read-only checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0.
- `wc -l KAM/Planetary/SecularForm/ProductInterface.lean`: `342`.
- Source scan for sorry/admit/axiom/unsafe/opaque/EuclideanSpace, `set_option` and resource overrides: no matches in the audited file. Module header, copyright, public imports, module docstring and exposed public noncomputable section are present.
- Recursive scan of local KAM imports: 68 modules including the audited module; no provider imports and no frozen theorem imports at any depth. All frozen imports in this closure are definition modules. Consequently no DRAFT_SORRY theorem or provider dependency is being hidden behind the new interface.

## Notes, uncertainties, errata and deviations

1. **Scope:** the synced P7 export boundary at `docs/tracks/P/design/P810-LEAN-DESIGN.md:303–319` explicitly owns these five consumed contracts, rather than claiming whole-node completion. The blueprint's larger product theorem also discusses openness, lattice invariance, perturbation analyticity, orbit transfer and full Hamilton equations. Existing ingredients cover several of those facts, but this audit certifies the named design cuts only. In particular the source split holds as a total identity more broadly than the combined guarded `pc_share` export; its NoCollision premise is exactly the approved design premise, needed for its accompanying field assertion, not a new implementation restriction.
2. **Normalization:** `SecularSpectrum.lattice` proves the specified radian quotient facts and period-one symplectic factor. It does not independently package every period-one torus-transport predicate or the Hamiltonian normalization by 2π. Consumers must use P1's dictionary and the corresponding transport package. This is the design boundary, not a proof gap in the delivered signature.
3. **Hygiene:** generated KAM.lean remains stale as expressly permitted by the audit brief. No regeneration was performed. Replayed unused-variable warnings belong to existing dependencies, not this file.

No suspected pinned-source or blueprint defect was found within the assigned cuts. No mathematical deviation or extra source premise was introduced by the implementation. No unresolved proof uncertainty remains within the stated audit scope. No frozen anchor is sealed by S7-R.
