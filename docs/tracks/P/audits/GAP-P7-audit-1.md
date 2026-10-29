# GAP-P7 independent audit 1

Overall verdict: **FAIL (unsigned node completeness)**. Nine nodes pass, one fails: `stepI:p7:ci-alg`. The proofs of the statements actually exported compile and have only the permitted axioms. The failure is an incomplete source conclusion, not an unsound Lean proof.

Audited HEAD: `9782b5820ab32d44493ce2de317273e1aab67a8e`; comparison branch `inp`: `c1839fee225146e0c60e389ca73433801f3a9c52`. The full `git diff inp...HEAD` adds exactly `KAM/Kepler/ScalingNodes.lean` (250 lines) and `KAM/Planetary/Poincare/ChartNodes.lean` (497 lines), with no other tracked changes. The pre-existing untracked handoff was read and preserved. Report destination follows the user's explicit worktree-path instruction, superseding the generic brief's main-worktree destination.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the GAP-P7 handoff including AUDIT FOCUS, and the GAP-P7 section of `/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md` (319–333). Compared every named node's SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS and SOURCE_CONCLUSION with its cited blueprint text and the entire two-module implementation. Read the relevant track-P statement and frozen D25 definitions, together with the landed chart, orbit, scaling and secular-form interfaces.

All ten graph exports are UNSIGNED. There are **no provider exports, SIGNED signature-file obligations or frozen theorem anchors to seal** in this package. Provider/frozen type equality and fresh-name seal-body probes are therefore inapplicable; no seal-readiness is asserted for any campaign anchor. No signed statement was substituted with an unsigned helper.

## Per-node and public-declaration results

`CN` = `KAM/Planetary/Poincare/ChartNodes.lean`; `SN` = `KAM/Kepler/ScalingNodes.lean`. Graph locators below are in `docs/graph/P/DEPGRAPH.md`, including the track-I nodes mirrored there. P blueprint locators are in `blueprint-P/parts/p7-kepler-poincare.tex`; I locators in `blueprint-I/parts/p7-delaunay.tex`.

| Node / source locators | Lean declaration | Verdict | Comparison |
|---|---|---|---|
| `stepP:p7:pc-eq`; graph 13994–14003; P:208, 198–201 | `KAM.Planetary.SecularForm.pc_eq`, CN:174 | PASS | All four components, with correct signs, action derivative and slow-coordinate order. Bool selects moving/fixed model; arbitrary μ serves as ε in the fixed branch. Domain membership plus NoCollision is exactly the source chart preimage of W. |
| `bpP:p7:product-chart`; graph 13855–13864; P:188–203 | `KAM.Planetary.SecularForm.product_chart_full`, CN:233 | PASS WITH NOTES | Parts (a)–(d) are bundled: chart, lattice invariance, exact fibers, image, analytic local inverses and induced quotient bijection; action-only h and its derivatives; coupling-independent perturbations, analytic domain, field/orbit transport; both Hamilton equations. Quotient presentation discussed below. |
| `stepP:p7:la-ham`; graph 14247–14256; P:238, 232 | `KAM.Planetary.SecularForm.la_ham`, CN:205 | PASS | Both models, all z in O₀, action-only h(fast z.2); second conjunct proves independence whenever fast actions agree, even outside O₀. No assumed decoupling premise. |
| `stepP:p7:d25-e`; graph 14435–14444; P:263, 256 | `KAM.Planetary.d25_e`, CN:345 | PASS | O₂ and Γᵢ>0 are precisely the source guards. Establishes existence of g and all identities for every representative g, with ℓ=λ−g and u=eccAnom ℓ e. Independent of m, so omitting physical mass data strengthens the result. |
| `bpP:p7:d25`; graph 14276–14285; P:247–258 | `KAM.Planetary.d25`, CN:385 | PASS | Positive masses first, then all w in O₂ and all i; clauses (a)–(e), unique analytic F, arbitrary-F ellipse dictionary, frozen physical functions, and converse with exact lattice uniqueness. The proof explicitly establishes e<1 at CN:431, so the strictly positive lower Jacobian bound is established. |
| `stepP:p7:po-el#circular`; graph 14527–14536; P:158 | `KAM.Planetary.po_el_circular`, CN:480 | PASS | m,κ>0, arbitrary λ, Λ>0; q≠0, exact energy, cross=Λ>0, axis and physical action. Circular chart membership is proved internally. |
| `stepP:p7:rg-scale`; graph 12974–12983; P:64 | `KAM.Kepler.rg_scale`, SN:185 | PASS | Positive mass/strength and original physical-region membership only. Explicit inverse point, scaling back, correct energy denominator mκ², cross C/m and Λ/m square-root identity. |
| `stepI:p7:ci-alg`; graph 39338–39347; I:308, 304, 181–189 | `KAM.Kepler.ci_alg`, SN:218 | **FAIL** | The radius/speed/energy/cross formulas, three means and five explicit circular specializations are correct, but the source's endpoint parts (a),(b) also include radius bounds and q·p=L e sin u. Neither is in this export or proved in its body. See finding F1. |
| `stepI:p7:sc-alg`; graph 39369–39378; I:320 | `KAM.Kepler.sc_alg`, SN:105 | PASS | Exact energy and derivative identities; invariance of symplecticForm is the stated matrix identity in bilinear form. Holds on the entire total carrier, stronger than collision-free source domain. |
| `stepI:p7:sc-flow`; graph 39395–39404; I:321, 312–315 | `KAM.Kepler.sc_flow`, SN:127 | PASS WITH NOTES | Both field identities, pointwise time change for any solution, axis/energy and two mean-anomaly integrals on the explicit bound-orbit parametrization. Collision-free guard is sourced, not an additional estimate. See representation note below. |
| Auxiliary quotient clause | `KAM.Planetary.exists_quotient_bijection`, CN:71 | PASS | A well-defined bijection with explicit agreement with Ψ on quotient representatives. Source of product-chart(a); no arbitrary map substituted. |
| Definitional component equations | `KAM.Planetary.SecularForm.ChartHamiltonEq`, CN:110 | PASS | Exact four component equalities; definition only, never a premise of a public source export. |
| Definitional lattice relation | `KAM.Planetary.fastLatticeSetoid`, CN:63 | PASS | Intended full lattice orbit relation on Oₙ, with proved equivalence laws. |
| Definitional polar clause | `KAM.Planetary.D25Polar`, CN:329 | PASS | Literal existence and representative-independent polar identities; used as conclusion under the intended guards. |

### F1 — incomplete unsigned export for ci-alg

The graph's SOURCE_CONCLUSION at 39347 says “the radius, momentum, scalar energy and angular-momentum formulas and the three means extend to e=0”. Its source I:304 expressly says “the endpoint formulas (a), (b) of Proposition [orbit-identities]”. Those parts include, at I:184–185:

- L²(1−e) ≤ r ≤ L²(1+e);
- q·p = L e sin u, in addition to the angular-momentum identity.

SN:219–231 exports neither. SN:232–246 only assembles radius, squared speed, energy, cross and means, then the circular specializations; it never establishes the omitted radial-momentum identity or radius bounds. In particular radial momentum is not a projection of the exported radius/speed/cross identities (those do not supply its sign). This is a literal-conclusion failure under the handoff's UNSIGNED rule, even though the shorter summary row in GAP-PLAN-P emphasizes only the five circular values.

The repair needs no new mathematical assumption: landed `KAM.Kepler.orbitMapR_radius_bounds` (Orbit.lean:126) and `KAM.Kepler.orbitMapR_dot` (Orbit.lean:146) already prove the missing clauses for 0≤e<1. Add those clauses to the node-named export and assemble them. The audit does not edit Lean or silently reduce the source contract. All ten node names exist; this one remains incomplete.

### Representation and quantifier notes

For product-chart(a), the GAP-P7 design explicitly requests “a bijection ... that is a local analytic diffeomorphism”. CN:245–252 gives analytic inverse charts of the same Ψ plus a compatible quotient bijection, and CN:235 supplies analyticity. This implements the permitted quotient presentation. There is no independently declared analytic-manifold structure or analytic diffeomorphism object on `Quotient (fastLatticeSetoid n)`; the PASS accepts exactly the design's local-chart presentation. It must not be described as a separately constructed quotient-manifold API. The setoid is on Oₙ, not on unrestricted ambient space. Invariance in both directions follows from the same universal lattice clause with −k.

For product-chart(c), `perturbation D b` unfolds to fMov/fFix composed with the chart and has no coupling argument (Basic.lean:52–54); the same term is used for every μ. `Data` (Basic.lean:38–45) bundles only positive physical constants, positive component masses and n>0. It carries no conclusion-shaped spectral, analytic, noncollision or dynamical assertion. Universal Bool/μ quantification states both independent model assertions; no common-value restriction on the two couplings arises. The source's W condition is exactly the pair/nonorigin collision condition used here.

For sc-flow, `0 < planeLength z.1` is equivalent to Q≠0. A pointwise HasDerivAt statement for arbitrary Zc and t is sufficient, and stronger locally than assuming a solution on an entire interval; applying it at each time gives the interval assertion with the k² rescaling. The averages quantify g,L,e over the source's explicit Kepler ellipses, with L>0 and 0≤e<1, and retain the original mean-anomaly integration law. They do not assert classification of arbitrary Hamiltonian solutions or arbitrary invariant measures. No such classification is needed by this source proof step, which explicitly invokes the parametrized means proposition. The algebraic sc-alg extension to Q=0 uses Lean's total division; the physically used statements remain collision-free.

## Definition classification

There are three public definitions and one private definition; no new abbrev or structure.

| Definition | Classification / whole-carrier behavior |
|---|---|
| `fastLatticeSetoid` (CN:63) | Genuine orbit equivalence on the subtype Oₙ, all n; not an arbitrary equivalence selected to force a bijection. Zero, negation and addition of fastShift prove its laws. |
| `ChartHamiltonEq` (CN:110) | Transparent proposition specifying all components for arbitrary D,H,f,μ,w. It may be false for arbitrary inputs, as intended; theorems prove it for the physical models. No truth-by-fallback branch. |
| `D25Polar` (CN:329) | Transparent polar existence plus all-g identities for arbitrary w,i. Its positive-e clauses are intentionally guarded at theorem use by Γᵢ>0 and w∈O₂; no circular value or division fallback discharges a theorem. |
| Private `sclCLM` (SN:38) | Actual continuous linear map (Q,P)↦(k⁻¹Q,kP) for every real k. At k=0 it is the resulting zero map, not claimed symplectic; every symplectic application has k>0. |

Private proof helpers establish linearity, analytic differentiability off collision, field scaling and block identities from source data. No hard step is assumed as a typeclass or bundled field. Public declarations stay in KAM.Kepler, KAM.Planetary or KAM.Planetary.SecularForm. Repository-wide declaration searches found no reused public short name for any of the 14 new public declarations and no harmful root shadow.

## Independent validation

All Lean-bearing checks were serialized. The first lint invocation accidentally lacked the requested LEAN_NUM_THREADS/nice wrapper; it completed without another Lean process running. This audit-run deviation is recorded rather than concealed. The controlled rerun below is the validation receipt under the required wrapper. Targeted build, axiom probe and kernel replay use LEAN_NUM_THREADS=1 and nice -n 5; no resource overrides were used.

### Build

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp7 KAM.Kepler.ScalingNodes KAM.Planetary.Poincare.ChartNodes
```

Exit 0. Output starts `[inp-gate] slot 1 acquired 01:36:41 for KAM.Kepler.ScalingNodes KAM.Planetary.Poincare.ChartNodes` and ends `Build completed successfully (9125 jobs).` Replayed unused-variable warnings occurred only in landed Energy, Hamiltonian.Algebra/Chart, Poincare.Chart/D25 and Mass dependencies; neither audited module emitted a warning.

### Axioms

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/gap_p7_audit.lean
```

Exit 0. The temporary probe imports the two audited modules and runs `#print axioms` for every new public theorem. Exact output:

```text
'KAM.Kepler.sc_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.sc_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.rg_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Kepler.ci_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_quotient_bijection' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pc_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.la_ham' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.product_chart_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.d25_e' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.d25' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.po_el_circular' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Kepler.ScalingNodes KAM.Planetary.Poincare.ChartNodes
```

Exit 0. Exact verbose output:

```text
replaying KAM.Planetary.Poincare.ChartNodes
replaying KAM.Kepler.ScalingNodes
```

### Lint and static integrity

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1196 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The initial unwrapped invocation had the same output and exit code. No other lint finding occurred. The handoff and brief explicitly leave regeneration to the orchestrator; this is an accepted lint exception, not the reason for the overall FAIL.

Other checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.
- `git diff --check inp...HEAD`: exit 0, empty output.
- Entire diff: exactly the two new modules, 747 added lines. Both have copyright, module, public imports, module docstring and exposed public noncomputable section.
- Character counts: SN 250 lines, maximum width 100; CN 497 lines, maximum width 100.
- Direct forbidden-token/override search on both files: no matches (rg exit 1). No EuclideanSpace.
- Recursive local KAM import inspection: 79 modules in the combined closure, **zero providers and zero frozen theorem modules**. Thus no DRAFT_SORRY theorem import, and no SEALED theorem state exception is needed. Frozen definitions are legitimate imports.
- No generated root regeneration, frozen/manifest edits, git mutations or production-source repairs. The audit probe is removed before handoff.

## Defects, deviations and remaining scope

F1 is an implementation/source-fidelity deviation. No new suspected error in a frozen statement or pinned external source was found. Existing Part-7 normalization/sign and Fej04r proof-source caveats are documented at P:179–183, 282–285 and are not newly resolved by this package. The source of the failing requirement is the blueprint's explicit reference to full endpoint parts (a),(b), not an inferred strengthening of physical assumptions.

This audit establishes soundness of the exported Lean statements and identifies one missing literal node conclusion. It does not close a frozen anchor, change graph status, regenerate KAM.lean, or certify any track-I/N/P headline theorem. No new check beyond GAP-P7 was started.
