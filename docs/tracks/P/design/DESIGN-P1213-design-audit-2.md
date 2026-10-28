# Delta design audit: P1213, revision 2

Overall verdict: **PASS** (design level). **F1 is resolved. N1–N3 are addressed by the revised interfaces and explicit assignment instructions.** No new blocking finding. This accepts the audited design delta; it does not prove a theorem, discharge an upstream source gap, authorize a gated package before its inputs arrive, or permit sealing a frozen anchor.

Date: 2026-10-28. Independent refute-first delta review under `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`, continuing the manuscript-audit protocol used in audit 1. Scope: every audit-1 finding and every revision-2 hunk, including the changed helper, its consumers, added source-characterization/delivery gates, Mathlib-order and measurability instructions, signature comments, and revised receipts. Unchanged material is carried forward only after mechanical identity checks against the audited snapshot. No implementation repair or state-changing git operation was performed.

## Frozen inputs and delta boundary

- Current commit: `308f3b7727cca9e3d9726c338f336478958dc600` (`docs(P): revise Parts 12–13 design after audit`). Baseline: `8178e2dc6ba6d3653323edbf2cd072d336e0486c`.
- `git diff 8178e2d..HEAD` changes only `docs/tracks/P/design/P1213-LEAN-DESIGN.md`. Every hunk was read. Only `FixedAssembly.n_general` changes Lean semantics; all other Lean changes are comments. No frozen declaration, manifest, new definition, structure, instance, module path, package estimate or package order changes.
- Original signatures were read and copied byte for byte to a temporary `.lake/abi-scratch/` file for the required fresh elaboration. The original was never edited. All audit-owned probe files are removed at closeout.

| Input | SHA256 |
|---|---|
| Revision-2 design | `da905471b106707950e1de2c433228a74a967117f81e07cd767a1c7ffea05768` |
| `/root/code/KAM-inp/.drafts/design/P1213Signatures.lean` | `1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447` |
| Prior report `DESIGN-P1213-design-audit-1.md` | `10e5c6bdc78a88b7b83541abdd7fea2701f8d082c6f98779695dc3f9b6347636` |
| `blueprint-P/parts/p12-planar-assembly.tex` | `83eee5fc9d881bf115be39e811ffc58cc206d45355d7956599115c9c7e0965db` |
| `blueprint-P/parts/p13-fixed-assembly.tex` | `8b208fe0799dec36bf3ff95b51a08bda6d2ca705491e045fe7d3c150838bb9e5` |
| `docs/graph/P/packets/P-p12.nodes.md` | `1f77f2b9d213338c39e947a8a64abc77ef224a577b951f9c95b77c4055a7a7ee` |
| `docs/graph/P/packets/P-p13.nodes.md` | `36b9cf0d3c6141d3ebd2aa9cf59035e94b5eb71ee8a3ab879fb5b17b20feefb4` |
| `manifest/frozen-anchors.json` | `5d8d31f1cc70c3cc67375ab28562e4fd4280215c7455dd329004c4dcd7a2f6fa` |

Both blueprints, both local graph packets and the manifest retain their audit-1 hashes. The current signature appendix equals the standalone file exactly: 389 lines, 24 sorry-only theorem bodies, 13 definitions including the five explicitly temporary Tube copies. Removing comments/normalizing whitespace and isolating the first `n_general` command shows that the remaining 23 theorem commands and all 13 definitions are unchanged. All 89 local graph IDs and both locators per row remain exact.

## Earlier findings: re-check and disposition

| Finding | Earlier severity | Revision-2 evidence and independent re-check | Disposition |
|---|---|---|---|
| F1 | Medium, blocking | Design lines 703–713 and signatures lines 330–340 now bind `d := tubeD (axisGap a)` and `D := tubeBigD (axisGap a) (axisMax a)`, existentially selecting only eps0. The full helper telescope equals audit 1's proposed replacement. Re-read p13 lines 135–144, p6 lines 210–215, the p13 packet `SOURCE_QUANTIFIERS` and `CONSTANT_SCOPE`, and the actual Tube/FixedKolmogorovSet definitions. The literal constants depend on a alone. | **RESOLVED** at signature fidelity level. |
| N1 | Medium, nonblocking delivery gate | New design lines 64–68 demand exact owner names/full characterization types for the actual cube, C0, δS, σ, beta-hat and common T before P12-C/P13-A assignment. Both joint-output comments explicitly deny that their projections identify canonical objects or independent witnesses. No new theorem premise or assumed witness equality was added. | **ADDRESSED** as a mandatory delivery gate; the upstream certificates remain unproved/unreconciled until delivered. |
| N2 | Medium, nonblocking delivery gate | Design line 68 now requires each brief to carry applicable SOURCE_GAP rows and delivery plus proof/axiom audits. All 34 retained IDs/groups were checked against the global-review gap inventory, accounting for the table's stated prefix abbreviations. P-G sealing, P6-5/P7-6/Part 1 delivery, eigenframe, nonlinear real-flow and Lie applicability, and the general wrapper K1–K6 chain remain explicit. | **ADDRESSED** as assignment rules; no mathematical gap is declared paid. |
| N3 | Low | Design line 174 now explicitly selects ContDiff order ω before `.analyticAt`. Line 182 and the generic `measure` comment use S⊆cylinder to remove V from the measurability obligation. Both operations were checked in a fresh Lean probe, including the exact set identity for arbitrary a,b,V,r. | **ADDRESSED**; no added signature hypothesis. |

### F1 fidelity and consumer refutation pass

The source says “with ζ*, d, D of Definition ... tube-constants there is ε₀>0”; p6 explicitly fixes `d=γa/2`, `D=2*a_max+γa`, independent of η,G,m₀,m and coupling. The graph packet states `CONSTANT_SCOPE: d,D depend on a alone`. The revised helper now exports exactly those constants, their positivity/order, a threshold independent of the later ε, and the original frozen physical set predicate with positive finite measure. It adds no assumption and does not change the phase carrier or norm.

I checked the two possible regressions rather than accepting the response table alone:

1. **Can the wrapper produce the stronger output?** Yes, at design-interface level: `bpP:p11:wrapper` (p11 lines 237–244) supplies the threshold-first Borel positive-finite set in the canonical tube and whole physical tori. The exact designed `fixedKolmogorovSet_of_tube` consumes those data at γ=`axisGap a`, A=`axisMax a` and concludes the literal required d,D. The original positive ordered axes supply canonical AxisData and 0<d<D. No new positivity condition on ε beyond the existing root premises is introduced.
2. **Can the final frozen consumer still use the helper?** Yes. `fixed` and both registered providers retain their exact original telescopes. The new assembly text at design lines 184 and 297 explicitly packages the helper's canonical constants. A fresh no-sorry probe assumed the exact revised output type and elaborated its conversion to the exact old/frozen existential output:

```lean
obtain ⟨eps0, h0, hd, hdD, hS⟩ := h
exact ⟨eps0, tubeD (axisGap a),
  tubeBigD (axisGap a) (axisMax a), h0, hd, hdD, hS⟩
```

Thus the stronger helper does not force a frozen statement change, dependent-type cast, extra input or changed quantifier order. The consumer probe establishes the logical packaging, not existence of the helper's mathematical output. F1 is closed as a design defect; the theorem body remains unpaid.

## Per-signature delta ledger

Prefixes: `PA = KAM.Planetary.PlanarAssembly`, `FA = KAM.Planetary.FixedAssembly`, `PR = KAM.Provider.Planetary`. Labels abbreviate `bpP:`. For unchanged commands the reason below retains the audited source correspondence; the delta check confirms no signature drift. All PASS entries concern design/interface fidelity only.

| Lean name | Blueprint label / role | Verdict | Reason |
|---|---|---|---|
| `PA.compact_cell_isCompact` | `stepP:p12:ft-cpt` | PASS | Compactness of the literal finite-coordinate cell; arbitrary δ is safe (negative δ gives the empty set). |
| `PA.forward_tube` | `p12:forward-tube` | PASS | Same max norm, δ upper bounds, product-domain conclusion, pointwise circular comparison and tube inclusion; physical positivity and δ-before-w quantifiers retained. Axis separation/η are unused standing data, safely dropped. |
| `PA.collar` | `p12:collar` | PASS | Full two-sided frontier collar; `4(L₀+L₁)t`, sup distance, and both strict half-width conditions retained. |
| `PA.product_chart` | `p7:product-chart` (b), locally owned completion | PASS | Literal hProd restriction; positive-action analyticity, fast frequency, diagonal and cross Hessian entries and decoupling match. κ>0 subsumes the product Gm₀. |
| `PA.fast_diffeo` | `p12:fast-diffeo` | PASS | Exact frozen smooth-inverse predicate; positive κ/masses/endpoints suffice. Frequency identification is exported by `product_chart`; explicit cube-root inverse is the assigned construction. |
| `PA.radius_choices` | `p12:data` D8–D9; `p12:quantifiers`; `p13:data#choices` | PASS | Explicit min formulas, strict r<rG<1, `2r²≤δ/2`, positive threshold≤1 and strict coupling bound; no coupling-dependent choice. |
| `PA.birkhoff_mono_radius` | `stepP:p12:pg-h4`, `stepP:p13:pg-h4` | PASS | Restricts both integrability discs and little-o domain in the actual frozen predicate; r>0 and r≤r₀ suffice. |
| `PA.chart_of_birkhoff` | `stepP:p12:ch-chart` | PASS | Conditional composition tool, distinctly named; existing real analytic and symplectic maps with image guard. Analyticity supplies both differentiability premises of `IsSymplecticOn.comp`. |
| `PA.chart_hamiltonian_of_preserves_fast` | `stepP:p12:ch-ham` | PASS | Exact moving Hamiltonian and degenerateHamiltonian identity on guarded chart domain; genuine fast-action preservation input; arbitrary real μ is legitimate. |
| `PA.pg_hypotheses` | `p12:data`, `p12:chart`, `p12:pg-hypotheses` | PASS | Joint assembly output contains every P-G input and required chart/tube clause before μ; no result bundle is assumed. Finer canonical source identities remain behind explicit upstream characterization gates. |
| `PA.transport` | `p12:transport`, reused at `p13:transport` | PASS | Direct fast-lattice theorem with actual local hypotheses; actual cylinder and physical torus predicates, same frequency/time, full range image. a,b generalization is valid. |
| `PA.cylinder_set_shift` | `stepP:p12:me-inv` | PASS | Whole-torus union plus frozen fast winding supplies invariance, without a slow-position lattice. |
| `PA.measure` | `p12:measure`, `stepP:p13:tr-meas` | PASS | Fast-cell image equality, cell injectivity, Borel image and exact volume equality; S⊆O supplied at both consumers. The added cell-rewrite instructions cover arbitrary V. |
| `PA.measure_in_tube` | `p12:measure`, `p13:transport` measure clause | PASS | Explicitly conditional local tool combines cell positivity and equality with tube inclusion and finite tube volume. No unnecessary mass/radius sign premise. |
| `PA.planar` | `p12:planar`, frozen `p0:planar` | PASS | Byte-exact frozen telescope after theorem renaming, including all-time physical predicate, positive finite volume and threshold-first order. |
| `FA.fixed_hamiltonian_form` | `p13:fixed-hamiltonian-form` (a) identity | PASS | Exact existing product identity; accompanying analyticity reused from Product, parts (b)/(c) assigned across difference, upstream identification/BNF and joint construction. n=0 extension is an empty finite-sum identity. |
| `FA.perturbation_difference` | `p13:fixed-hamiltonian-form` (b), `stepP:p13:fh-id` direct difference | PASS | Literal fMov−fFix algebra, including `(2*m₀)` denominator; arbitrary T and zero/nonpositive parameters are safe for this total algebraic identity. Averaged/jet claims remain upstream. |
| `FA.chart_of_preserves_fast` | `p13:chart`, `stepP:p13:ch-ham` | PASS | Correct fixed perturbation, same fast-preservation guard and arbitrary real ε. |
| `FA.pg_hypotheses` | `p13:data`, `p13:chart`, `p13:pg-hypotheses` | PASS | Fresh full P-G input tuple for fFix; shared geometry need not imply equal P-G thresholds. Exact common-map/jet certificates are now explicit delivery gates. |
| `FA.n2` | `p13:n2` | PASS | Exact two-planet frozen conclusion with fixed Hamiltonian, original physical premises and strict coupling order. |
| `FA.n_general` | `p13:n-general` | PASS | Revised: literal canonical d,D, only eps0 existential; source and packet constant scope restored; consumer packaging independently elaborated. |
| `FA.fixed` | `p13:fixed`, frozen `p0:fixed` | PASS | Exact frozen telescope. Both branches can supply it; Canonical witness packaging from the stronger helper checks. |
| `PR.planarTwoPlanetKAM` | frozen `p0:planar`, `p12:planar` | PASS | Exact registered provider signature, no extra premise or parallel dynamics predicate. |
| `PR.fixedSunPlanetaryKAM` | frozen `p0:fixed`, `p13:fixed` | PASS | Exact registered provider signature, implicit dimension and ordered-axis binders preserved. |

Definition inventory: all formula bodies are unchanged, including their carriers and guards.

| Definition | Source / role | Verdict |
|---|---|---|
| `KAM.Planetary.axisMax` | Existing Tube maximum; scratch dependency copy only | PASS |
| `KAM.Planetary.axisGap` | Existing Tube axes/gaps minimum; scratch dependency copy only | PASS |
| `KAM.Planetary.tubeRadius` | Existing `min η (γ/6)`; scratch dependency copy only | PASS |
| `KAM.Planetary.tubeD` | Existing `γ/2`; now used literally by n_general | PASS |
| `KAM.Planetary.tubeBigD` | Existing `2*A+γ`; now used literally by n_general | PASS |
| `PA.kepler_h` | Literal hProd restriction | PASS |
| `PA.action_center` | `mᵢ*sqrt(G*m₀*aᵢ)` | PASS |
| `PA.total_chart` | Existing total product chart composed with T | PASS |
| `PA.perturbation` | Actual fMov, constant coupling family | PASS |
| `PA.compact_cell` | Closed fast cell, action box and Γ bounds | PASS |
| `PA.secular_radius` | `min rG (sqrt(δ/2))/2` | PASS |
| `PA.coupling_threshold` | `min 1 (r^6/log(1/r)^c)` | PASS |
| `FA.perturbation` | Actual fFix, constant coupling family | PASS |

No FAIL signature remains, so no further replacement block is required. No new numbered finding was accepted after refutation; F1/N1/N2/N3 above preserve their original identifiers.

## Consumer, frozen-object, definition and package verdicts

**Consumers: PASS.** The revised helper is produced by the same wrapper/P6 route and consumed by explicit existential packaging. Five root/provider transcriptions were re-compared mechanically: PA.planar, FA.n2 (the documented μ→ε/fixed-predicate specialization), FA.fixed and both providers. All match their frozen telescope. The separate n_general helper now deliberately has the stronger canonical-constant conclusion. The n=2 branch and dependent substitution are unchanged. The revision adds no new I/N/P consumer, rescaling, frequency requirement or standing premise.

**Frozen objects: PASS for the delta.** The actual `FixedKolmogorovSet`, `cylinderCell`, tube constants and frozen P-FIXED telescope were re-read, together with the wrapper and P6-5 interface used at their consumers. Manifest identity is unchanged, and no frozen source path is changed. The revised statements continue using the actual frozen predicates and retain all-time physical dynamics/pair-bound clauses. The 23 unchanged theorem commands preserve the audit-1 frozen-object and transport checks; no parallel definition replaces a frozen predicate. Provider quarantine and sealed-only P-G consumption remain mandatory.

**Definitions: PASS.** All 13 bodies are identical to the prior audited formulas; no new choice, fallback, structure field, function/matrix instance or off-source inference is introduced. The five Tube copies remain scratch-only and must be replaced by their owner import in implementation. New characterization prose creates a delivery obligation, not a theorem-shaped assumption bundle or permission to guess an upstream object.

**Packages: PASS for the design delta.** The module DAG, ownership, waves and estimates are unchanged: P12-A/D at 1, B at 2, C at 3, E/P13-A at 4, P13-B at 5, P13-C at 6; each planned file is below 1500 lines. The new proof packaging is a small terminal operation in P13-C, not an upstream dependency or cycle. Actual source-characterization and proof/axiom delivery gates must be satisfied before package assignment/import. This PASS does not declare those packages currently executable irrespective of their gates.

## Independent checks

The required signatures were elaborated once, independently of the designer's receipt:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-design-p1213 .lake/abi-scratch/P1213AuditR2Signatures.lean
exit 0
24 warnings: declaration uses sorry
0 errors; 0 other warnings
```

The gate invokes `LEAN_NUM_THREADS=1 nice -n 5 timeout 1800 lake env lean <absolute scratch path>` against the shared inp build. One audit-owned Lean/lake job ran at a time; no heartbeat, recursion or synthesis override, clean, cache download, Mathlib rebuild or project rebuild was used.

All six fresh diagnostic `#print axioms` results (PA.planar, FA.n2, FA.n_general, FA.fixed and both registered providers) were exactly:

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```

A separate `.lake/abi-scratch/P1213AuditR2Consumers.lean` used the same gate after the signatures run and exited 0. Its **proof terms contain no sorry**. It checked the exact canonical-output→frozen-output conversion shown above, the exact cell identity

```lean
S ∩ cylinderCell V r =
  S ∩ {z | ∀ i, fast z.1 i ∈ Set.Ico (0 : ℝ) (2 * Real.pi)}
```

under only `S ⊆ cylinder V r`, and the valid analytic-order real-power proof

```lean
example (x p : ℝ) (hx : x ≠ 0) : AnalyticAt ℝ (fun y : ℝ => y ^ p) x :=
  (contDiffAt_id.rpow_const_of_ne (p := p) hx).analyticAt
```

The probe also freshly checked the types of `ContDiffAt.rpow_const_of_ne`, `ContDiffAt.analyticAt`, `IsCompact.uniformContinuousOn_of_continuous`, `MeasurableSet.image_of_continuousOn_injOn`, `Real.volume_Ioo`, `Real.volume_Icc`, and `MeasureTheory.Measure.pi_pi`. All exist with the required types. The probe emitted seven unused-physical-premise binder warnings because pure existential packaging does not need those original hypotheses; these are probe-only warnings, not warnings from the delivered signatures. No suppression or resource override was added. The cell identity removes the only appearance of arbitrary V in the Borelness step; continuity of the finite fast coordinate maps supplies the remaining Borel bounds. It does not assume V measurable.

Static checks independently confirmed appendix/external-copy equality, only one semantic signature change, the exact audit-1 replacement, five unchanged frozen-type transcriptions, all 89 nodes/locators, and all 34 transitive gap records. The designer's check scripts/logs were not used as substitutes for these reruns. Fresh source lint ran after both probes, using the existing local shim to route its ABI elaboration through the shared gate:

```text
PATH="$PWD/.drafts/scratch/gated-bin:$PATH" LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
exit 0
check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

`git diff --check` returned 0. The report is untracked, so its tables, balanced fences, control characters and trailing whitespace were checked separately. Both audit-owned `.lake/abi-scratch/P1213AuditR2*.lean` files were deleted after completion. Final hashes confirm that the design, original signatures and prior audit report were untouched. The only persistent new artifact is this report; the pre-existing untracked audit-1 report remains in place.

No new pinned-paper erratum or suspected frozen-definition defect was found. The complete upstream mathematical proofs, signature reconciliation and actual implementation axiom closure are outside this delta audit; their original gates remain open.


## Closeout

- **F1: resolved. N1–N3: addressed at design level.** No remaining blocking design finding and no new accepted finding.
- All 24 theorem signatures and 13 definitions are classified; the one changed telescope and its consumer have fresh independent elaboration evidence.
- Design acceptance applies to revision `308f3b7727cca9e3d9726c338f336478958dc600` and signature hash `1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447`. The exact upstream characterization, delivery, proof/axiom and sealing gates remain mandatory.
