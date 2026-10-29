# GAP-P8b independent audit 2

Overall: **FAIL for the handoff's literal named-export mapping**, solely for
`stepP:p8:pa-avg -> perturbation_avg`. **PASS for the repaired full proposition and proof
coverage of all four nodes.** The round-1 mathematical coverage gap is repaired: the new
`perturbation_avg_complex` proves the complex-domain derivative identity and the full bundle
includes it. The remaining failure is that the handoff still names the old, narrower theorem
as the complete pa-avg export. It is not a proof-soundness failure or an outstanding complex
identity. See the distinction and concrete completion below.

Audited HEAD: `890e319b28e92944a8701b35e7d4e33d4a23cbee`.
Observed `inp`: `11e9fefe883876d090d86c4b32c39ed01ca02df2`.
Three-dot merge base: `c2be145a358746329fa8147c2f951d8bfc7ecbfb`.
The complete `git diff inp...HEAD` contains AnalyticNodes.lean (577 added lines),
the prior audit (211), and the handoff (48). All were read; only the named Lean module
was audited as implementation. Audit 1's HEAD and its 435-line count are historical.

Authority read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied audit brief,
docs/tracks/P/statement.md, the handoff and audit 1, GAP-PLAN-P.md:335–344,
the four graph NODE records, and their cited blueprint text. The explicit user path overrides
the generic brief instruction to write in the main worktree. Only this report and a removed
probe in `.lake/abi-scratch/` were written. No source, manifest, generated root or git state
was changed by the auditor.

There are no new frozen anchors, providers or SIGNED declarations in this package.
Provider/frozen type equality and seal-body probes are inapplicable. The existing signed
`perturbation_analytic` and its design signature are unchanged and outside implementation scope.
No anchor is sealed by this audit.

## Per-node and per-public-declaration verdicts

Names have prefix `KAM.Planetary.SecularForm.`; line numbers refer to AnalyticNodes.lean.

| Node / clause | Declaration | Verdict | Literal comparison |
|---|---|---|---|
| `stepP:p8:pa-unif` | `perturbation_unif`:81 | PASS | A positive common radius below rho/2; separation on all real angles and complex polydisc points; real squared separation, length bound and collision freedom. Stronger angle range than the compact cell. |
| Periodicity in pa-hol and parent | `perturbationC_periodic`:123 | PASS | Every real angle coordinate can increase by 2π at every complex slow point; both models. |
| `stepP:p8:pa-hol` | `perturbation_hol`:347 | PASS | Complex holomorphy, joint continuity, periodicity, reality and physical equality for both models. Principal powers and bilinear squares are literal definition bodies. |
| `stepP:p8:pa-avg`, as mapped in handoff | `perturbation_avg`:367 | FAIL as a standalone literal node export | Its derivative clause is still only on realDisc, with real derivatives of real functions. Its other clauses are correct. The missing complex clause is now proved elsewhere, as the next row records. |
| Complex derivative clause of pa-avg | `perturbation_avg_complex`:489 | PASS | Every order k, every x in polydisc, complex iterated derivatives of secularC and perturbationC, with the exact normalized average. This is the round-1 repair. Together with perturbation_avg it establishes the whole node in the module. |
| `bpP:p8:perturbation-analytic` | `perturbation_analytic_full`:534 | PASS | Common radius before both models, angles, points, pairs and derivative orders; all (a), (b), (c), including complex derivatives at :564–565. Stronger radius bound than the proposition. |

Thus slice completeness under the focus's “in the proof or as an export” criterion passes.
The stricter question “does the named declaration state that node's literal conclusion?”
still fails for the handoff's pa-avg name. This report does not silently treat the old theorem
as if its type had changed. Updating the handoff/graph binding to the proved pair (or the
corresponding projection of the full bundle), or adding a single combined pa-avg export,
would resolve this mapping issue; no further complex differentiation proof is needed.
`perturbation_avg_complex` alone supplies the derivative clause, not all the regularity clauses.

## Source fidelity, premises and definitions

The parent NODE at docs/graph/P/DEPGRAPH.md:14809–14819 specifies original positive data,
then a radius, then real angles and complex slow points. The step records at :14872–14882,
:14909–14919 and :14936–14946 were checked against blueprint-P/parts/p8-secular-form.tex:39–51.
The blueprint distinguishes N from N_R at :21–22 and says at :44:
“\partial^\alpha_{(\xi,\eta,\Lambda)}S=\langle\partial^\alpha\hat f\rangle for all \alpha”.
In particular the complex carrier is necessary. The new theorem states exactly

```lean
∀ k : ℕ, ∀ x ∈ polydisc D a r, iteratedFDeriv ℂ k (secularC D b) x =
  avg (fun t => iteratedFDeriv ℂ k (perturbationC D b t) x)
```

Full complex multilinear derivatives give the source coordinate partial derivatives by
application to coordinate vectors. Ordering the slow product as (ξ,Λ,η) instead of the
subscript's (ξ,η,Λ) changes only that coordinate dictionary. Every order and point is covered.

Data contains only n>0, G>0, m0>0 and positive masses; axes supplies positive increasing axes.
There are no conclusion-shaped fields. The separation/radius premises of pa-hol are precisely
upstream geometric context. Both average lemmas retain that sourced context and derive the
analytic hypotheses internally. They are specialized physical-family lemmas, not generic
parameter-integral theorems. The full bundle discharges all geometric premises from Data and
axes. No derivative identity or analytic conclusion is assumed to prove itself.
The handoff :36–38 is imprecise when it says pa-avg's SOURCE_HYPOTHESES lists separation:
that record lists pa-hol's analytic conclusions, whereas separation is upstream context.

The witness radius is chosen before b, t, x, i, j and k. Its construction uses exists_radius,
then min with rho/4; geometric inputs involve m, a and κ=G*m0 through action, rho and the chart.
The separate perturbation prefactors G and 1/m0 are not used to select it. No angle-dependent,
point-dependent, order-dependent or model-dependent radius is substituted. Universal binder
reordering does not move an existential across any of these choices.

| New definition | Classification |
|---|---|
| private `assembleLM`:258 | Literal linear coordinate assembly on the entire product carrier; no junk/fallback. |
| private `assembleCLM`:267 | Its continuous linear realization on the same finite dimensional carrier; no domain substitution. |

No new abbrev or structure. Both definitions lie under expose. Inherited objects were read
for attachment: Slow/CSlow are products of Fin-indexed real/complex functions; polydisc uses
exactly the three coordinate bounds; realDisc is the real-inclusion preimage. Frozen Assemble
and SecularAverage were read: (I,p,q)=(Λ,η,ξ), with the literal (2π)^(-n) integral.
perturbationC (:27–30 of AnalyticRegularity.lean) uses principal s^(-1/2) and the moving
bilinear momentum square, without conjugation. No fallback value is used in lieu of an
analytic object on the claimed domain.

## Proof review and repair

Uniformity shrinks the existing valid radius; the chart-region image gives positive central
radii, and positive squared separations give pair collision freedom, including reversed pairs.
The general real integral-derivative lemma bounds the jointly continuous derivative on a
compact neighborhood, then uses dominated differentiation. Its induction handles order zero
and higher orders through continuous multilinear currying and local equality on the open set.
The slice lemma uses an affine translation and the continuous linear inclusion.

The added proof at :402–486 proves joint real smoothness on real-angle × complex-polydisc,
composing the actual holomorphic chart and the principal power on its slit-plane domain.
It applies the existing real integral induction with S=CSlow and E=ℂ. At :489–531,
holomorphy supplies complex smoothness; restriction of complex multilinear derivatives to ℝ
commutes with the integral via a linear isometry, whose injectivity recovers equality of the
complex derivatives. This preserves the complex point carrier throughout, unlike round 1.
The normalization is carried through constant scalar multiplication. No missing derivative
continuity or integrability condition is inserted as a public premise.

## Independent checks

All auditor Lean/Lake invocations were sequential, with LEAN_NUM_THREADS=1 and nice -n 5.
No heartbeat, recursion-depth or synthesis-budget override, clean, update or cache fetch.

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
[inp-gate] slot 1 acquired 02:04:10 for KAM.Planetary.SecularForm.AnalyticNodes
Build completed successfully (9121 jobs).
exit 0
```

Only inherited unused-variable warnings in Kepler/Energy, Poincare/Chart, Kepler/Mass and
Poincare/Holomorphic were replayed; none from AnalyticNodes.

The scratch probe imported AnalyticNodes and ran `#print axioms` and `#check @` on each of the
six public theorems. The elaborated types were read, including the old real restriction and
new complex clause. Probe command and exact axiom output:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP8bAudit2.lean
'KAM.Planetary.SecularForm.perturbation_unif' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbationC_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_hol' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_avg_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_analytic_full' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.AnalyticNodes
replaying KAM.Planetary.SecularForm.AnalyticNodes
exit 0
```

The probe was removed. Module inspection: 577 lines, maximum 100 Unicode characters;
required module header, copyright, public imports, docstring and public section present.
No forbidden token, resource override, EuclideanSpace, reused public short name or root shadow.
All helpers are private and all six public theorems are in the intended namespace.
A recursive KAM import scan visits 75 modules and 47 frozen modules, all manifest SEALED
and all definition modules; no provider or DRAFT_SORRY anchor is reachable.

Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1195 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint failure is the explicitly permitted generated-root freshness check.
The full-diff whitespace issue is separate from lint and was left untouched under report-only scope.

## Errata, deviations and limits

No suspected false pinned-source or frozen-statement claim was found. No source correction
was introduced. GAP-PLAN-P.md:341 says “each complex angle”; the controlling blueprint :40
and graph specify real angles and complex slow variables. The implementation follows those
controlling sources. The plan :342 only requested the realDisc derivative formula; the new
complex theorem and full bundle now also deliver the broader source clause.

The handoff is stale (435 lines, five exports, old commit, no complex theorem). Its pa-avg
mapping must be read with the precise failure above. The whitespace finding is documentation
only. Generated-root freshness is expressly excluded as a package finding by the brief and
handoff; no generated file was repaired. All observations concern this package, not the
closure of a track I/N/P headline or the updating of graph status.
