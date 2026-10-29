# GAP-P8b independent audit 3

Overall: **PASS WITH NOTES**. All four assigned graph nodes PASS for their current
named exports, including `stepP:p8:pa-avg -> perturbation_avg_node`. Audit 2's remaining
named-export failure is repaired. The complex derivative identity is present both in
that export and in the parent bundle. No proof-soundness or literal-conclusion gap
was found. Notes concern documentation accuracy and existing handoff whitespace.
Generated-root freshness is expressly excluded as a package finding.

Audited HEAD: `bc356ad4f4046c04a35a0c7bd15b8efeb3e39048`.
Observed `inp`: `5d2c928069e3d3bcea1f688373decd8fda061515`.
Three-dot merge base: `c2be145a358746329fa8147c2f951d8bfc7ecbfb`.
The complete comparison `git diff inp...HEAD` adds AnalyticNodes.lean (593 lines),
audit 1 (211), audit 2 (193), and the handoff (56). All four files were read;
implementation audit scope is solely `KAM/Planetary/SecularForm/AnalyticNodes.lean`.
Relative to audit 2's HEAD `890e319b28e92944a8701b35e7d4e33d4a23cbee`, the only Lean
change is the 16-line combined export at lines 575–590.

Authority: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied package audit
brief, docs/tracks/P/statement.md, handoff including AUDIT FOCUS and round 3,
both previous audits, GAP-PLAN-P.md:335–344, P810-LEAN-DESIGN.md's relevant node
table/signature, the four NODE records, and their cited blueprint text. The explicit
user path overrides the generic brief's MAIN-worktree destination. Only this report
and a temporary, subsequently removed `.lake/abi-scratch/GAPP8bAudit3.lean` were
written. No source, frozen file, manifest, generated file, graph status or git state
was changed.

There are no new frozen anchors, providers or SIGNED declarations. Provider/frozen
type equality and seal-body probes are inapplicable; no anchor is being sealed.
The landed signed `perturbation_analytic` is unchanged and outside implementation
scope. Its narrower signature does not narrow the new UNSIGNED exports.

## Node and declaration verdicts

All names have prefix `KAM.Planetary.SecularForm.`; Lean line numbers refer to
AnalyticNodes.lean.

| Node / clause | Declaration | Verdict | Literal comparison |
|---|---|---|---|
| `stepP:p8:pa-unif` | `perturbation_unif`:81 | PASS | Positive common radius below rho/2, complex squared separation bound for every real angle, real squared-distance equality, distance lower bound and collision freedom. All real angles strengthen the compact-cell bound. |
| Periodicity in pa-hol and parent | `perturbationC_periodic`:123 | PASS | Increment any real angle coordinate by 2π at every complex slow point, for both models. No separation premise needed. |
| `stepP:p8:pa-hol` | `perturbation_hol`:347 | PASS | Holomorphic in complex slow variables per real angle, jointly continuous, coordinate-periodic, real and equal to the actual physical composition at real points. Principal power and bilinear-square formulas are the literal inherited definition bodies. |
| Real regularity and derivative subclauses of pa-avg | `perturbation_avg`:367 | PASS as a component | Holomorphy, reality, real analyticity and all real derivatives. Still not the whole complex-domain node by itself; it is no longer the handoff's named complete export. |
| Complex derivative subclause of pa-avg | `perturbation_avg_complex`:489 | PASS as a component | Every order and every complex polydisc point, with complex iterated derivatives and the exact normalized average. |
| `stepP:p8:pa-avg` | `perturbation_avg_node`:577 | PASS | One declaration contains all regularity/reality clauses and the complex derivative identity, plus the stronger additional real derivative formula. Proved by pairing the preceding two results. |
| `bpP:p8:perturbation-analytic` | `perturbation_analytic_full`:534 | PASS | One radius before both models, all angles, points, pairs and orders, carrying all of (a), (b), (c), including the complex derivative identity at :564–565. Radius below rho/2 strengthens the parent source. |

The four-node slice in GAP-PLAN-P.md is complete. The wider historical P810 table
assigns other nodes to other modules; those are not additional assignments to this
new module. The pa-circ input is landed and used through `exists_radius`.

## Hypotheses, quantifiers and definition attachment

The controlling records are docs/graph/P/DEPGRAPH.md:14809–14819 (parent),
:14872–14882 (pa-unif), :14909–14919 (pa-hol), and :14936–14946 (pa-avg).
They were compared to blueprint-P/parts/p8-secular-form.tex:17–22, 33–34 and 39–51.
In particular line 44 asserts “for all α” on the complex domain distinguished from
its real slice at line 22. The new named pa-avg export contains exactly

```lean
∀ k : ℕ, ∀ x ∈ polydisc D a r, iteratedFDeriv ℂ k (secularC D b) x =
  avg (fun t => iteratedFDeriv ℂ k (perturbationC D b t) x)
```

Full multilinear derivatives supply the source's coordinate partial derivatives
by evaluation on coordinate vectors. The slow coordinate ordering (ξ,Λ,η), versus
the displayed derivative subscript (ξ,η,Λ), is a coordinate dictionary only.

`Data` contains n>0 and positive G, m0, masses; `axes` means positive increasing
axes. These are standing source data, with no analytic or dynamical conclusion
assumed in a field. pa-hol takes exactly the upstream positive radius, chart-domain
bound and separation context. pa-avg's NODE directly lists pa-hol's analytic
conclusions, whereas the concrete physical-family exports take the earlier
geometric context and derive those analytic facts internally. This is sourced
context of the same proposition, not an extra unsourced premise. These exports
are not generic parameter-integral lemmas for arbitrary functions satisfying
only holomorphy and continuity. The parent bundle discharges the entire context
from the original positive data and axes. No averaged derivative identity or
regularity conclusion is assumed to prove itself.

The radius is chosen before b, t, x, i, j and k; no existential is moved inside
any of those choices. Adjacent universal quantifiers (including point/order and
point/angle in individual clauses) sometimes appear in a different textual order
but have identical scope. The radius proof uses `exists_radius` then min with
rho/4. Its geometry uses m, a and κ=G*m0 through action, rho, center and planetC;
the independent perturbation factors G and 1/m0 do not enter its selection.
Thus it respects the source's dependence on (m,κ,a), and both models use it.

| New definition | Classification |
|---|---|
| private `assembleLM`:258 | Literal linear coordinate assembly on the entire product carrier. No fallback, restricted surrogate or junk value. |
| private `assembleCLM`:267 | Continuous linear realization of the same assembly on the finite dimensional carrier. No change of object or domain. |

There are no new abbrevs or structures. Definitions are under expose. Inherited
Slow/CSlow use products of Fin-indexed real/complex functions; polydisc is exactly
the three coordinate bounds and realDisc its real-inclusion preimage. Frozen
Assemble and SecularAverage were read: (I,p,q)=(Λ,η,ξ), with the exact (2π)^(-n)
integral over [0,2π]^n. AnalyticRegularity.lean:27–34 defines principal complex
power -1/2 and the moving model's bilinear momentum square without conjugation.

## Proof review

Uniformity preserves separation while shrinking the radius. Collision freedom
uses the actual product-chart domain and chart-region image to get positive
central radii; positive squared separation handles distinct pairs, including
reversed pairs. Periodicity follows from the chart's coordinate periodicity.

The private generalized integral derivative lemma bounds the jointly continuous
derivative on a compact neighborhood and applies dominated differentiation.
Finite-order induction uses local equality on an open domain and multilinear
currying, including order zero. The slice lemma uses affine translation and a
continuous linear inclusion. For real points, analyticity is obtained on the
actual open chart/collision-free preimage, not postulated on the integral.

For complex points, :402–448 proves joint real smoothness of the actual chart
composition and principal power on the slit-plane domain. The same integral
induction is applied with carrier CSlow and codomain ℂ. At :489–531, complex
holomorphy supplies complex smoothness; scalar restriction commutes with the
integral via a linear isometry, whose injectivity recovers the complex derivative
identity. The normalization survives scalar multiplication. The new export
:577–590 pairs the two proved conclusions without new premises or proof steps.

## Independent checks

Every Lean/Lake invocation was sequential, with LEAN_NUM_THREADS=1 and nice -n 5,
including lint's ABI probes. No budget override, clean, update or cache fetch.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
[empty], exit 0

git diff --check inp...HEAD
docs/tracks/P/audits/GAP-P8b-handoff.md:38: trailing whitespace.
+  it.
exit 2

git diff --check inp...HEAD -- KAM/Planetary/SecularForm/AnalyticNodes.lean
[empty], exit 0

LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp8b KAM.Planetary.SecularForm.AnalyticNodes
[inp-gate] slot 2 acquired 02:19:36 for KAM.Planetary.SecularForm.AnalyticNodes
Build completed successfully (9121 jobs).
exit 0
```

Only inherited unused-variable warnings in Kepler/Energy, Poincare/Chart,
Kepler/Mass and Poincare/Holomorphic were replayed; no AnalyticNodes warning.

The scratch probe imported AnalyticNodes and ran `#check @` and `#print axioms`
for all seven public theorems; the elaborated types were read.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP8bAudit3.lean
'KAM.Planetary.SecularForm.perturbation_unif' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbationC_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_hol' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_avg_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_analytic_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_avg_node' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.AnalyticNodes
replaying KAM.Planetary.SecularForm.AnalyticNodes
exit 0
```

Source inspection: 593 lines, maximum 100 Unicode characters; module/copyright,
public imports, docstring and public section present. No forbidden token,
EuclideanSpace or set_option; every helper is private. Repository declaration-name
scan finds no other declaration with any of the seven new public short names;
all exports lie in the intended namespace, with no harmful root shadow.
Recursive KAM import traversal visits 75 modules and 47 frozen modules. Every
reachable frozen module is a manifest SEALED definition; no provider, frozen
theorem or DRAFT_SORRY anchor is reachable.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1195 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint failure is the expressly permitted generated-root freshness check;
it is not a package finding. No generated file was regenerated. The scratch probe
was removed. Final report whitespace validation passed; final git status lists
only this new report as an auditor-created worktree change.

## Documentation notes, errata and limits

No suspected false pinned-source claim or frozen-statement defect was found.
GAP-PLAN-P.md:341 says “each complex angle”; blueprint :40 and the graph specify
real angles and complex slow variables. The implementation follows the controlling
sources. The plan's :342 realDisc derivative target is narrower than the source;
the module now supplies the complex target as well.

The handoff's introductory 435-line count and round-3 591-line count are stale
(actual 593). Its pa-avg row names the correct combined export but displays only
the real formula; the theorem itself also states the complex formula. Its :36–38
description of pa-avg's SOURCE_HYPOTHESES is imprecise in the way explained above.
The existing trailing space is documentation only and left untouched. None of
these notes is a failed node. No source correction or mathematical deviation was
introduced by this audit. There is no remaining scoped theorem gap identified;
this report does not seal any anchor or certify a track I/N/P headline.
