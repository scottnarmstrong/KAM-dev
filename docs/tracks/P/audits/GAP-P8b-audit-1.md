# GAP-P8b independent audit 1

Overall verdict: **FAIL for literal graph closure**. The new Lean proofs pass the targeted build,
kernel replay and public-theorem axiom checks. Two of the four assigned nodes are incomplete as
literal exports: `stepP:p8:pa-avg` and `bpP:p8:perturbation-analytic` restrict the derivative
identity to real points instead of the source's complex polydisc. This is a statement-coverage
failure, not a counterexample to the proved real identity.

Audited HEAD: `e89eae66d0a4d9ba6aacbd572e6488b42ca26060`.
Compared against `inp` at `537fc2a837002555fbe2766678b1c8454274228f` using the full
`git diff inp...HEAD`. Its sole change is the new 435-line
`KAM/Planetary/SecularForm/AnalyticNodes.lean`.

Scope and authority: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied package audit brief,
docs/tracks/P/statement.md, the handoff's AUDIT FOCUS, the four NODE records in
`docs/graph/P/DEPGRAPH.md`, their cited blueprint text, and GAP-PLAN-P.md lines 335–344.
The explicit user instruction puts this report inside this package worktree, overriding the
brief's generic MAIN-worktree output instruction. Only this report and temporary files under
`.lake/abi-scratch/` were written; no source or git state was changed.

There are no provider exports, new frozen anchors, or SIGNED declarations in this package.
Provider/frozen type equality and a copied seal-body probe are therefore not applicable.
The existing signed `perturbation_analytic` in Analytic.lean is unchanged. Its narrower design
contract is not authority to narrow these new UNSIGNED graph exports.

## Node and public declaration results

All declaration names below have prefix `KAM.Planetary.SecularForm.`.

| Node / clause | Declaration and source line | Verdict | Comparison |
|---|---|---|---|
| `stepP:p8:pa-unif` | `perturbation_unif`, 81 | PASS | Positive radius strictly below rho/2; uniform separation for every real angle and complex point; real squared separation, distance bound and collision-free product-chart image. Radius precedes every angle/point/pair. Stronger than just the compact angle-cell bound. |
| Periodicity clause of `stepP:p8:pa-hol` and `bpP:p8:perturbation-analytic` | `perturbationC_periodic`, 123 | PASS | Any real angle coordinate may be incremented by 2π at every complex slow point in the polydisc. Both models; no separation assumption needed. Source angles are real. |
| `stepP:p8:pa-hol` | `perturbation_hol`, 346 | PASS | Complex holomorphy per real angle, joint continuity on all real angles times the complex polydisc, coordinate periodicity, real values and equality to the physical compositions. The principal-power and moving-model bilinear-square formulas are the actual unfolded body of perturbationC, not missing assumptions. |
| `stepP:p8:pa-avg` | `perturbation_avg`, 366 | FAIL | Holomorphy, reality and real analyticity are present. The last clause only quantifies `x ∈ realDisc D a r`, using `iteratedFDeriv ℝ` of the real functions. No derivative identity at a general complex slow point is proved or exported. |
| `bpP:p8:perturbation-analytic` | `perturbation_analytic_full`, 396 | FAIL | One common radius and both models carry (a), (b), holomorphy/reality/real analyticity in (c), but lines 424–426 retain precisely the same real-point derivative restriction. Thus the bundle does not supply the literal full (c). |

All four design-assigned nodes were checked. Two pass and two fail; the extra periodicity
export passes. The module contains exactly these five new public theorems and no public definitions.

## Exact failing clause and required completion

`docs/graph/P/DEPGRAPH.md:14943–14945` gives pa-avg's context and scope:

> SOURCE_HYPOTHESES: hat f holomorphic in w' on N(rho_*), jointly continuous and 2pi-periodic (Step pa-hol)
> SOURCE_QUANTIFIERS: w' in N(rho_*)
> SOURCE_CONCLUSION: (c): S holomorphic on N(rho_*), real at real points, real analytic on N_R(rho_*), d^alpha S=<d^alpha hat f>

`blueprint-P/parts/p8-secular-form.tex:40` quantifies over `w' ∈ N(rho_*)`;
line 44 asserts the derivative identity “for all α”. Line 51 invokes the parameter-integral
and derivative facts for holomorphic functions on that complex domain. N and N_R are explicitly
distinguished at lines 21–22. The parent NODE repeats those clauses.

In contrast, AnalyticNodes.lean:373–375 states only

```lean
∀ k : ℕ, ∀ x ∈ realDisc D a r, iteratedFDeriv ℝ k (secular D b) x =
  avg (fun t => iteratedFDeriv ℝ k
    (fun y : Slow n => perturbation D b (assemble y.2.1 t y.2.2 y.1)) x)
```

The bundle repeats this at lines 424–426. Full real multilinear derivatives do contain all
real coordinate partial derivatives, but that does not expand their carrier to complex points.
No private proof in this module establishes the complex identity either: the integral induction
has real scalar field and the applied integral argument has carrier Slow n.

To complete the literal nodes, add the identity for every order and every `x ∈ polydisc D a r`
for the complex functions `secularC` and `perturbationC`, with complex multilinear derivatives
(or an equivalent explicit complex partial-derivative formulation), and include it in the
bundle. Alternatively a source/graph scope change would require an explicit ruling; this audit
does not silently reinterpret N as N_R. The GAP plan's requested realDisc identity is delivered,
but it is narrower than the controlling literal-source audit focus.

## Premises, quantifiers, constants and definitions

Data n contains only n>0, positive G, m0 and masses. Membership in axes supplies positive,
strictly increasing axes. These are exactly the standing source data, with no analytic,
collision-free or averaged-derivative conclusion bundled into Data.

The positive radius, r<rho and separation assumptions in perturbation_hol are the upstream
pa-unif context explicitly listed by its NODE. perturbation_avg reuses that geometric context
and proves the needed holomorphy itself rather than accepting pa-hol's conclusions as arguments.
Its direct binders therefore differ from the immediate pa-avg hypothesis list; they are sourced
upstream conditions, and the full bundle discharges them from the original data. There is no
unsourced premise or circular use of the desired averaged derivative formula. The handoff's
claim that pa-avg's SOURCE_HYPOTHESES itself lists separation is imprecise: it lists pa-hol's
analytic conclusions. This distinction does not fix the missing complex-domain conclusion.

The common radius is obtained before angles, points, pairs and the Bool model selector. It does
not depend on an angle, a point, a derivative order or a choice of model. The geometry used to
choose it involves masses, axes and G*m0=κ through action, rho and planetC; the later factors G
and 1/m0 in the perturbation do not enter the radius construction. The source restriction on
constant dependence is respected. Reordering adjacent universal quantifiers or choosing the
Bool selector before them does not change their scope.

Every new definition is private:

| Definition | Line | Classification |
|---|---|---|
| `assembleLM` | 257 | Literal real-linear assembly/reordering `(t,(ξ,Λ,η)) ↦ assemble Λ t η ξ` on the entire product carrier. No fallback. |
| `assembleCLM` | 266 | The continuous linear realization of assembleLM on the same finite dimensional carrier. No fallback or restricted-domain surrogate. |

Inherited objects were checked as context, not re-audited as new code: Slow/CSlow are products
of Fin-indexed real/complex functions; polydisc has exactly the three coordinate bounds;
realDisc is its real-inclusion preimage; secular is the literal frozen secularAverage with
(I,p,q)=(Λ,η,ξ); avg has factor (2π)^(-n). perturbationC uses principal complex power -1/2
and the moving-model bilinear square, with no conjugation. Frozen Assemble and SecularAverage
were read. No frozen theorem is being implemented by this package.

## Proof review

The separation radius is shrunk by min with rho/4, maintaining the old bound and supplying
strict r<rho/2. Real collision freedom derives positive central radii from the actual chart
region and positive pair lengths from squared separation; reversed pairs are handled by
symmetry. No collision-freedom premise is smuggled into the public uniformity result.

The private generalized integral derivative proof obtains a compact neighborhood and a bound
on the continuous derivative, then applies dominated differentiation. The iterated proof uses
local equality on the open domain, derivative/integral induction, and the continuous
multilinear currying equivalence. The slice proof is an affine translation followed by a
continuous linear inclusion. The applied smoothness domain is the actual preimage of the
open chart/collision-free domain. These arguments establish the stated real formula without
extra proof assumptions. They do not establish its complex-domain extension.

## Independent checks

All Lean/Lake checks were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The gate itself applies nice to lake build. No heartbeat, recursion or synthesis-budget override
was used. No clean, update, cache fetch, generated-root edit or state-changing git operation occurred.

1. Full diff and protection checks:

```text
git diff inp...HEAD
  sole diff: KAM/Planetary/SecularForm/AnalyticNodes.lean, 435 insertions
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
  [empty], exit 0
git diff --check inp...HEAD
  [empty], exit 0
```

2. Targeted compile gate:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp8b KAM.Planetary.SecularForm.AnalyticNodes
[inp-gate] slot 1 acquired 01:28:29 for KAM.Planetary.SecularForm.AnalyticNodes
Build completed successfully (9121 jobs).
exit 0
```

Replayed pre-existing unused-variable warnings came from Kepler/Energy.lean,
Poincare/Chart.lean, Kepler/Mass.lean and Poincare/Holomorphic.lean. No warning was emitted
for AnalyticNodes.lean.

3. An untracked scratch probe imported AnalyticNodes and ran `#print axioms` and `#check @`
for every new public theorem:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP8bAudit.lean
'KAM.Planetary.SecularForm.perturbation_unif' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbationC_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_hol' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_analytic_full' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The elaborated types confirm the domain restriction recorded above. The probe is removed.

4. Kernel replay, one invocation for the only new lemma module (no provider module exists):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.AnalyticNodes
replaying KAM.Planetary.SecularForm.AnalyticNodes
exit 0
```

5. Source hygiene: 435 total lines, maximum line length 100 Unicode characters. Module header,
copyright, public imports, module docstring and public section are present; definitions are
under expose. No forbidden escape or resource option, EuclideanSpace, reused new public short
name or harmful root shadow was found. All five exports reside in the intended namespace;
helper declarations are private. Recursive KAM import traversal reaches 47 frozen definition
anchors, all SEALED, and no frozen theorem or provider. The imports therefore bring no
DRAFT_SORRY anchor or provider into production.

6. Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1195 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the expected generated-root freshness check, expressly allowed by this
brief and the handoff. It is not a package finding and the generated file was left untouched.

## Source defects, deviations and limits

No suspected false pinned-source claim or frozen-statement defect was found. The failure is a
narrower new export than the blueprint, with exact locators above. The GAP plan line 341 says
“each complex angle”; the controlling blueprint and graph specify real angles and complex slow
variables. The real-angle periodicity proved here is correct for those sources; no complex-angle
extension is claimed. The design's realDisc derivative target likewise does not close the
source's complex-polydisc derivative target.

This audit changes no theorem, graph status or anchor state. The passed checks establish the
soundness of the delivered statements; they do not turn the two failed literal nodes into
proved graph nodes, nor seal any track I/N/P headline.
