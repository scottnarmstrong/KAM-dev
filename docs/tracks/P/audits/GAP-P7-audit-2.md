# GAP-P7 independent audit 2

Overall verdict: **PASS WITH NOTES** for this unsigned graph-gap package. All ten node conclusions are established under source hypotheses. Audit 1's F1 is resolved at the audited HEAD. This is not a seal-readiness verdict for any frozen campaign theorem: the package has no provider or frozen theorem export.

Audited HEAD: `5e9079e0c91935fbcced44c4e76094cc21ff8e56`. Current comparison ref `inp`: `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`; merge base: `c2be145a358746329fa8147c2f951d8bfc7ecbfb`. Compared the full `git diff inp...HEAD`: two new Lean modules, the handoff and audit 1 (957 insertions). The Lean slice is 757 lines. The earlier audit's HEAD, base ref and 747-line count describe its older snapshot, not this run.

## Scope and method

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external `inp-audit-package.md` brief, GAP-P7 handoff and AUDIT FOCUS, audit 1, and GAP-PLAN-P.md:319–333. Read all ten NODE records in docs/graph/P/DEPGRAPH.md, including SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS and SOURCE_CONCLUSION; compared their cited blueprint statements/proofs with the entire two-module implementation. Consulted track statement conventions, the relevant frozen D25 definitions, and landed chart/scaling/orbit/means interfaces. Historical draft statement status does not override later owner decisions or the graph contracts.

Only `KAM/Kepler/ScalingNodes.lean` (SN) and `KAM/Planetary/Poincare/ChartNodes.lean` (CN) are audited as implementation. All ten node exports are UNSIGNED. No SIGNED signature-file equality obligation, provider=frozen comparison or fresh-name seal-body obligation applies. No source or graph statuses were changed. The explicit user destination in this worktree overrides the generic brief's main-worktree destination.

## Per-node results

Graph line numbers refer to docs/graph/P/DEPGRAPH.md. P lines refer to blueprint-P/parts/p7-kepler-poincare.tex; I lines to blueprint-I/parts/p7-delaunay.tex.

| Node; contract/source locators | Declaration | Verdict | Fidelity and premises |
|---|---|---|---|
| `stepP:p7:pc-eq`; graph 13994–14003; P:198–201,208 | `KAM.Planetary.SecularForm.pc_eq` (CN:174) | PASS | Four correct components of the physical pulled-back field. Positive physical data, chart membership and NoCollision express precisely the source preimage of W. Bool selects either model with arbitrary coupling; no derivative or decoupling identity is assumed. |
| `bpP:p7:product-chart`; graph 13855–13864; P:188–209 | `KAM.Planetary.SecularForm.product_chart_full` (CN:233) | PASS WITH NOTES | All (a)–(d): analytic symplectic chart, lattice invariance/exact fibers/image, compatible quotient bijection/local analytic inverses; action-only h, both derivatives and nonvanishing; both coupling-independent perturbations, analytic domain, field/orbit transport, component equations. See quotient representation note. |
| `stepP:p7:la-ham`; graph 14247–14256; P:226–238 | `KAM.Planetary.SecularForm.la_ham` (CN:205) | PASS | Each physical model and all z in O₀. Literal H∘Ψ∘Θ decomposition, I=fast z.2. Second conjunct proves independence whenever fast actions agree, on the entire carrier, stronger than the source restriction. |
| `stepP:p7:d25-e`; graph 14435–14444; P:256,263 | `KAM.Planetary.d25_e` (CN:345) | PASS | w∈O₂ and Γᵢ>0 only. Supplies a polar representative and identities for every representative g. Uses ℓ=λ−g and u=eccAnom ℓ e. Omitting mass data strengthens the source statement, since none of these objects depends on mass. |
| `bpP:p7:d25`; graph 14276–14285; P:247–264 | `KAM.Planetary.d25` (CN:385) | PASS | Positive m first; all w∈O₂ and i, then arbitrary F. All (a)–(e), unique analytic inverse anomaly, Jacobian bounds, arbitrary-F ellipse dictionary, frozen physical quantities, converse and exact lattice uniqueness. Proof at CN:431 establishes e<1, hence the source's strict 1−e>0 in addition to the exported J bounds. |
| `stepP:p7:po-el#circular`; graph 14527–14536; P:158 | `KAM.Planetary.po_el_circular` (CN:480) | PASS | Positive mass/strength, arbitrary λ, Λ>0; q≠0, correct energy, cross=Λ>0, axis and action. Chart membership is proved internally. No noncircular membership asserted. |
| `stepP:p7:rg-scale`; graph 12974–12983; P:49–64 | `KAM.Kepler.rg_scale` (SN:185) | PASS | Original physical-region premise and positive physical constants only. Explicit inverse scaling, energy divided by mκ², cross divided by m, and physical action/m equal to the correct square root. Also proves scaling back. |
| `stepI:p7:ci-alg`; graph 39338–39347; I:181–200,290–308 | `KAM.Kepler.ci_alg` (SN:218) | PASS | Full radius, speed, scalar energy, cross, radius bounds and radial momentum for every 0≤e<1; three means and explicit circular values. F1 repaired at SN:229–232,240–244,236–239,247–248. No extra hypothesis or noncircular conclusion. |
| `stepI:p7:sc-alg`; graph 39369–39378; I:312,320 | `KAM.Kepler.sc_alg` (SN:105) | PASS | Exact energy identity and derivative action diag(k⁻¹,k⁻¹,k,k); invariance of symplecticForm is the source matrix identity. Valid on all points, a stronger algebraic assertion than Q≠0. |
| `stepI:p7:sc-flow`; graph 39395–39404; I:312–321 | `KAM.Kepler.sc_flow` (SN:127) | PASS WITH NOTES | Both field identities, pointwise time change for any solution, a_k=a/k and exact scaled energy/two normalized mean-anomaly integrals. Collision-free guard is sourced. See flow/average representation note. |

All node-table entries are accounted for. No extra conclusion-shaped premise, widened constant dependence, changed norm or missing literal clause was found.

## Other public declarations and definitions

| Declaration | Verdict / classification |
|---|---|
| `KAM.Planetary.exists_quotient_bijection` (CN:71) | PASS. Eleven-theorem axiom check includes this auxiliary public theorem. Its bijection agrees explicitly with Ψ on each quotient representative, from landed exact fibers and image. |
| `KAM.Planetary.fastLatticeSetoid` (CN:63) | Intended orbit equivalence on the subtype Oₙ, for every n. Genuine fast lattice shifts; equivalence follows from zero, negation and addition. No arbitrary equivalence chosen to force bijectivity. |
| `KAM.Planetary.SecularForm.ChartHamiltonEq` (CN:110) | Transparent proposition encoding the four component identities for arbitrary D,H,f,μ,w. Used as a conclusion, never as a public source premise. Slow positions are ξ and slow momenta η; signs match frozen X_H. |
| `KAM.Planetary.D25Polar` (CN:329) | Transparent polar existence plus universal representative identities, for arbitrary w,i. The theorem guards O₂ and Γᵢ>0. No fallback value replaces a polar proof at Γ=0. |
| Private `sclCLM` (SN:38) | Actual CLM (Q,P)↦(k⁻¹Q,kP) for every real k. At k=0 it is zero under total inversion; every symplectic/scaling theorem assumes k>0. |

These are all four new definitions; there are no new abbrevs or structures. All 14 public short names occur in exactly one declaration in KAM according to repository-wide declaration searches. None is introduced at the root namespace; no harmful shadow found. Private lemmas prove the needed differentiability/linearity/field and coordinate identities; they do not add public assumptions.

## Notes on representations and F1 closure

The graph requests an analytic diffeomorphism on the lattice quotient. As explicitly permitted by the GAP-P7 design, `product_chart_full` supplies the actual quotient bijection together with local analytic inverse charts of the same Ψ, its analyticity, and the exact lattice fibers. This is the mathematical local-chart presentation of the quotient diffeomorphism. It does not introduce an independent analytic-manifold structure or a global analytic-diffeomorphism object on Lean's bare `Quotient`. The PASS covers this specified representation. Oₙ is open by the landed domain theorem; the universal forward lattice clause also gives reverse invariance by −k.

`Data n` contains n>0 and positive G,m0,m only (SecularForm/Basic.lean:38–45). `perturbation D b` literally composes the appropriate fMov/fFix with Ψ and has no coupling argument (Basic.lean:52–54). Thus fixing D,b before all μ has exactly the required independence; universally selecting either model imposes no relationship between μ and ε.

For `sc_flow`, a pointwise derivative assertion quantified over arbitrary Zc,t applies at every time of any source solution interval. The time argument is k²t and the collision-free premise is Q≠0, expressed by positive planeLength. The average clause uses the explicit bound ellipses with parameters g,L,e and the original normalized integral in mean anomaly. It proves the scaling statement in the source's parametrized-orbit presentation; it is not a classification theorem for arbitrary Hamiltonian solutions or invariant measures. The source's averages explicitly cite that ellipse/means presentation.

For `ci_alg`, ℓ,g appear before the universal e in Lean, whereas the graph lists e before ℓ,g. These are independent universal variables with only the source e guards: their permutation changes no dependency, introduces no existential choice, and supplies exactly the source order by specialization. D25 fixes positive masses before chart points; product-chart fixes physical data before the arbitrary couplings and points. No quantifier-dependence defect was found.

Audit 1 F1 quoted I:304, “the endpoint formulas (a), (b) of Proposition ... orbit-identities”, whose I:184–185 include radius bounds and q·p=L e sin u. Both are now in the node-named export, proved by landed `orbitMapR_radius_bounds` and `orbitMapR_dot`, also explicitly specialized at e=0. An independent Lean consumer probe projects both repaired clauses together under just L>0, 0≤e<1, arbitrary ℓ,g. It elaborates successfully. Audit 1's failure is closed for this HEAD, without reducing its source contract.

## Independent validation

All Lean-bearing commands were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion-depth or synthesis-budget override was used. Scratch probes lived only under this worktree's `.lake/abi-scratch/`.

Build command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp7 KAM.Kepler.ScalingNodes KAM.Planetary.Poincare.ChartNodes
```

Exit 0. Exact opening/final output:

```text
[inp-gate] slot 1 acquired 01:53:32 for KAM.Kepler.ScalingNodes KAM.Planetary.Poincare.ChartNodes
Build completed successfully (9125 jobs).
```

Only replayed unused-variable warnings in landed dependencies Energy, Mass, Hamiltonian.Algebra/Chart and Poincare.Chart/D25. Neither audited module emitted a warning.

Axioms and repaired-clause consumer command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/gap_p7_audit2.lean
```

Corrected probe exit 0; consumer example emits no output. Exact axiom output:

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

The first probe invocation exited 1 because the auditor's consumer example omitted `open KAM.Planetary`, leaving planeLength/planeDot unresolved. All eleven axiom commands had succeeded. Adding that namespace opening in scratch fixed the probe; no production edit was made. This was an audit-probe error, not a package defect.

Kernel replay command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Kepler.ScalingNodes KAM.Planetary.Poincare.ChartNodes
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.Poincare.ChartNodes
replaying KAM.Kepler.ScalingNodes
```

Static integrity checks:

- `git diff --check inp...HEAD`: exit 0, empty output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.
- SN: 260 lines; CN: 497 lines; maximum Unicode line length 100 in each. Both have copyright, module, public imports, module docstring, exposed public noncomputable section.
- Direct forbidden-token and option search in both modules: no matches for sorry/admit/axiom/unsafe/opaque/EuclideanSpace or set_option. Module names and carriers respect the project rules.
- Recursive local KAM import closure: 79 modules; zero provider modules and zero frozen theorem modules. Therefore no DRAFT_SORRY theorem import or SEALED-state exception is involved. The imported frozen definitions were inspected as definitions.
- New public declaration short-name searches: all 14 unique within KAM; no public root-namespace declaration.

Lint command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the stale generated root explicitly permitted by the brief/handoff. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1196 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated root was preserved. There was no substantive lint failure. The full axiom/consumer, kernel and lint checks above are fresh independent reruns, not copied worker receipts.

## Errata, deviations and remaining scope

No new suspected pinned-source or frozen-statement defect was found. Existing source caveats in P:179–183 state the corrected normalization/sign convention and the external proof-source gap: “Fej04r Thm. 62 gives no proof”, citing unpinned Poincaré/Chenciner. The blueprint supplies its own explicit-formula proof. This package composes landed results; its passing audit does not newly verify those external texts or erase that documented gap.

The only implementation deviation reported by audit 1 (F1) has been repaired under the original hypotheses. No new implementation deviation or default-heartbeat design signal was observed. The notes here limit descriptions of the quotient/flow APIs to the representations actually supplied; they do not introduce missing source premises.

Only this report was edited in the repository. The temporary probe was removed after checks. No generated file, frozen file, manifest, graph, production Lean file or git state was changed. The result certifies the requested GAP-P7 slice under its stated graph-gap design; it does not close any track-I/N/P headline theorem or frozen anchor.
