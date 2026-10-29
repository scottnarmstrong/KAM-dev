# Independent package audit: GAP-P10a

Audited HEAD: `67f7f681d2178e83ec6223c1781121dd5c221736`; comparison branch `inp`:
`8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`. The full `git diff inp...HEAD` adds only
`KAM/Planetary/Nondegeneracy/GoodAxesNodes.lean` (244 lines). The pre-existing untracked
handoff was read and left untouched. This report follows the user's explicit destination override.

Scope: only that new Lean module, with imported definitions and proofs inspected as dependencies.
Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, handoff/AUDIT FOCUS,
the GAP-P10a section of GAP-PLAN-P.md (414–426), P810 design/node table, track P statements,
and every listed graph record with its cited blueprint lines. No provider or frozen theorem
anchor is assigned to this unsigned graph-gap package. Provider/frozen exact-type comparison
and a seal-body probe are therefore inapplicable; no frozen headline is claimed seal-ready.

## Verdict

**PASS WITH NOTES** for the assigned GAP-P10a graph slice. All new proofs compile and
kernel replay succeeds; all 12 public declarations have only the three permitted axioms.
The two presentation notes below were checked with fresh elaborating source-form consumer
probes. There is no unpaid source hypothesis or missing mathematical clause in the assigned
slice. The lint exception is exactly the permitted stale generated root. No frozen anchor
is proved or sealed by this package.

## Node and declaration review

Names are in `KAM.Planetary.Nondegeneracy`; line numbers refer to GoodAxesNodes.lean.
All supplied hypotheses are source standing data, dimension restrictions, or membership in the
source domain. None takes a proved dependency's output as an extra premise. `Data.hn` is
positive dimension, already implied by the source's n≥2; it contains no spectral conclusion.
The exports are unsigned additions, so the older narrower signed exports are not substituted
for these node contracts.

| Node | Declaration / line | Statement assessment | Reason |
|---|---|---|---|
| `stepP:p10:sa-loc` | `sorted_local_branch`, 37 | PASS | DEPGRAPH 18364–18391; blueprint 52. Fixed D,a∈U first, then positive radius and analytic ordered branches. Exports equality to sorted sigma and full SO diagonalization throughout a ball contained in U. Stronger than the listed local-branch conclusion. |
| `bpP:p10:conv#data`, U openness | `isOpen_simpleAxes`, 56 | PASS | DEPGRAPH 17520–17551; blueprint 15–21. Proves openness from local branches; no simplicity assumption on a separately chosen point is added to the global theorem. |
| sorted strict order helper | `sorted_strictMono_simple`, 63 | PASS | Simple spectrum plus monotone sorted spectrum gives StrictMono on U; membership is the source hypothesis. |
| `stepP:p10:sa-n2` | `simpleAxes_two_eq_axes`, 70 | PASS WITH NOTES | DEPGRAPH 19242–19268; blueprint 52. Exports U₂=A₂. The record also spells out positive discriminant; see N1 concerning its equivalent formulation. |
| `bpP:p10:sorted-analytic` | `sorted_analytic_node`, 77 | PASS | DEPGRAPH 18335–18362; blueprint 48–53. Joint analyticity, StrictMono at all a∈U, and U₂=A₂ for every two-planet data set. The final universal over E is stronger than a single fixed-data specialization. |
| `bpP:p10:conv#data`, inclusion | `goodAxes_subset_simpleAxes`, 85 | PASS | G⊆U, using the actual good polynomial and discriminant. |
| `bpP:p10:conv#data`, G openness | `isOpen_goodAxes`, 89 | PASS | n≥2 is exactly the standing source restriction; obtains openness internally from good_set. |
| `bpP:p10:conv#data`, fast frequency | `nu_action_eq`, 94 | PASS | Literal nu at action(D,a), sqrt(G*m0)*a_i^(-3/2), for each positive ordered axis and index. Source data precede a and i. No rescaled frequency or alternate mass convention. |
| `stepP:p10:n2-t` | `n2_t_node`, 118 | PASS | DEPGRAPH 18017–18043; blueprint 101. All three clauses, including strict t>r−3, with t=sigma₀/sigma₁ and r=trace²/det. Negativity, strict ordering and trace/determinant identities are proved dependencies inside the body. |
| action ratio helper | `action_ratio_eq`, 146 | PASS | Exact mass ratio and sqrt(axis ratio), under axes membership alone. Positivity justifies all divisions. |
| `bpP:p10:n2` | `n2_node`, 162 | PASS | DEPGRAPH 17954–17985; blueprint 93–103. Ratio identity, exact r formula, strict r bound, t≥r−3, hierarchy implies r>6 and NR₄/Phi₄≠0, and both divergence clauses. See N2 for uniform quantifiers. |
| `bpP:p10:good-set` | `good_set_node`, 211 | PASS WITH NOTES | DEPGRAPH 18393–18425; blueprint 122–127. Open/dense/null complement; simple and locally analytic spectrum at every good point; NR₄(2sigma); positive compact-uniform lower bound over every k∈K₄; closed sup-ball clause. See N3 for witness order and membership. |
| `stepP:p10:weyl-pert` (skipped) | landed `weyl` | PASS, status verified | DEPGRAPH 17696–17722 explicitly PROVED, with weyl ref and local-to-parent ruling. No new export required by the handoff's skip rule. |
| `stepP:p10:gp-choice` (skipped) | landed `good_point` | PASS, status verified | DEPGRAPH 18138–18166 explicitly PROVED, with good_point ref and local-to-parent ruling. |
| `stepP:p10:gp-loc` (skipped) | landed `good_point` | PASS, status verified | DEPGRAPH 18168–18198 explicitly PROVED, with good_point ref and local-to-parent ruling. |
| `stepP:p10:gp-nr` (skipped) | landed `good_point` | PASS, status verified | DEPGRAPH 18200–18229 explicitly PROVED, with good_point ref and local-to-parent ruling. |

These rows cover the GAP-P10a node list and all 12 new public declarations. The skipped rows
verify published graph status, not a new independent audit of their unchanged proofs.
The larger historical conv#data record also contains landed axes/action/spectrum/norm data;
this assignment explicitly requests its listed supplements, not replacement proofs of that
entire historical record.

## Definitions, carriers, and statement details

No new `def`, `abbrev`, `structure`, instance, or notation occurs. Local `set K` in n2_node
is a proof-local positive real expression, not a public object or bundled hypothesis.
Imported objects checked: Vec=Fin n→ℝ; Mat is a matrix on Fin n; axes are positive strictly
increasing vectors; action=m_i*sqrt(G*m0*a_i); nu=(G*m0)^2*m_i^3/I_i^3; sigma is the
increasing spectrum of the actual Hermitian coeffs matrix; simpleAxes/goodAxes use the
actual discriminant/good polynomial. k4 contains all nonzero integral modes of l1 length≤4.
No theorem relies on a totalized division/square-root fallback: the relevant axes, masses,
and denominators are positive or proved nonzero. Local branches are actual SO frames and
spectral diagonalizations, rather than arbitrary analytic labels.

N1. The sa-n2 export writes set equality rather than a separate positivity conjunct. The
discriminant definition (GoodPolynomial.lean:37–38) is a finite product of squared real
differences. Thus U₂=A₂ gives nonzero discriminant at every a∈A₂, and nonnegative plus
nonzero is positive. A fresh probe derives the graph's explicit positive-discriminant clause
using only this export and the product-of-squares definition. This is an equivalent source
conclusion, not an extra hypothesis or a missing mathematical inequality. Retaining an
explicit positive-discriminant companion would make the graph correspondence easier to read.

N2. n2_node quantifies fixed D and a∈A₂ for the pointwise clauses, then every M, a positive
ε, and every b∈A₂ with b₀/b₁<ε. Both r(b)>M and t(b)>M use that same ε; it is uniform
in b, and the actual witness 1/K², K=(|M|+3)m₀/m₁, depends only on D,M. The initial a
is unused in this witness. This is the source divergence assertion in epsilon form, not a
point-dependent threshold. Indices 0,1 correspond to source planets 1,2.

N3. Metric balls on Fin n→ℝ use the Pi sup norm, exactly B_inf in the source. The export
names the radius `a0 : ℝ` and the centre `r : Vec n`, and places the two existential witnesses
in the reverse order from source notation. No universal quantifier intervenes, so this has
no effect on dependence or strength. Although centre∈G is not a separate conjunct, the
positive radius places the centre in its own closed ball, and the subset clause gives centre∈G.
A fresh consumer probe recovers the source order ∃centre∈G, ∃radius>0 with the exact ball
inclusion. All universal data/a*/eta quantifiers precede both witnesses. Compact lower
bounds quantify K before c and then every a∈K,k∈K₄. Empty K legitimately allows c=1.

## Independent checks

All Lean-bearing commands were serialized and used `LEAN_NUM_THREADS=1`, `nice -n 5`.
The initial lint scan was paused before its ABI phase while the build finished, then replaced
by the complete serialized lint invocation below; no overlapping auditor Lean jobs ran.

1. Full comparison and protected paths:

   ```text
   git diff --stat inp...HEAD
    KAM/Planetary/Nondegeneracy/GoodAxesNodes.lean | 244 +++++++++++++++++++++++++
    1 file changed, 244 insertions(+)
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   [empty; exit 0]
   git diff --check inp...HEAD
   [empty; exit 0]
   ```

2. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp10a KAM.Planetary.Nondegeneracy.GoodAxesNodes
   [inp-gate] slot 1 acquired 01:56:56 for KAM.Planetary.Nondegeneracy.GoodAxesNodes
   Build completed successfully (9149 jobs).
   exit 0
   ```

   The gate replays the existing snapshot; no clean/full rebuild was requested. Replayed
   dependency warnings concern unused variables in Kepler.Energy, Poincare.Chart,
   Kepler.Mass, LocalAnalytic.Unique and Weyl; deprecated ite/if lemmas in Coefficients
   and Definiteness; a haveI style suggestion in Definiteness; and an unused simp argument
   in SymmetricRelation.Analytic. No warning was reported in the audited new module.

3. Fresh probe, containing `#print axioms` of all 12 declarations and the two source-form
   consumers described in N1 and N3:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP10aAudit.lean
   exit 0
   ```

   Exact axiom output (namespace prefix `KAM.Planetary.Nondegeneracy.` omitted here):

   ```text
   'sorted_local_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
   'isOpen_simpleAxes' depends on axioms: [propext, Classical.choice, Quot.sound]
   'sorted_strictMono_simple' depends on axioms: [propext, Classical.choice, Quot.sound]
   'simpleAxes_two_eq_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
   'sorted_analytic_node' depends on axioms: [propext, Classical.choice, Quot.sound]
   'goodAxes_subset_simpleAxes' depends on axioms: [propext, Classical.choice, Quot.sound]
   'isOpen_goodAxes' depends on axioms: [propext, Classical.choice, Quot.sound]
   'nu_action_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'n2_t_node' depends on axioms: [propext, Classical.choice, Quot.sound]
   'action_ratio_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'n2_node' depends on axioms: [propext, Classical.choice, Quot.sound]
   'good_set_node' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.GoodAxesNodes
   replaying KAM.Planetary.Nondegeneracy.GoodAxesNodes
   exit 0
   ```

   One invocation, after probe completion. The new module is both the package target and
   the sole new lemma module; there is no provider module to add.

5. Complete source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1197 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole lint finding is the explicit generated-root exception in the audit brief and
   handoff. It is recorded, not treated as a substantive package failure; KAM.lean was left
   untouched. No forbidden-token, line-length, file-size, module-header, or anchor finding.

6. Static checks: audited file has 244 lines, no line over 100 characters, and zero matches
   for sorry/admit/axiom/unsafe/opaque/EuclideanSpace or any set_option command. Copyright,
   module command, public imports, module docstring and public exposed section are present.
   A repository scan of theorem/lemma/def/abbrev/structure names finds no other declaration
   with any of these 12 short names. All exports are nested under the intended namespace;
   no root declaration, notation or instance is installed.

7. Import closure: recursively inspected 103 local modules. No provider occurs; all 47
   imported frozen modules contain SEALED definitions, and no frozen theorem module or
   DRAFT_SORRY theorem is imported. The relevant frozen definitions were read; provider
   type matching and sealing checks have no assigned anchor in this package.


## Errata, deviations, and limits

No suspected defect in a pinned mathematical source or blueprint was found in this scoped
review. The source passages relevant to this audit are the cited blueprint statements; no
new paper-PDF audit was performed. N1 and N3 are equivalent presentation differences,
not source corrections. No repository Lean code, protected file, manifest, generated root,
or git state was changed by the auditor. Only this report is added; temporary probes are
removed after use. The package closes the assigned graph slice only; it does not establish
P-PLANAR, P-FIXED, or any frozen physical headline.
