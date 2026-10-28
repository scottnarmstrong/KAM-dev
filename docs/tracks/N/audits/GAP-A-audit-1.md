# GAP-A independent audit 1

Audit date: 2026-10-28. Scope: exactly the two appended Lean modules in
`git diff inp...HEAD`; HEAD `9988913f8a0c5e52ec86a1157e6fc8d004f020ef`,
comparison branch `inp` at `d69dedecde7104870d7281ffe9dba51228f5e523`.
The explicit user destination overrides the generic brief's main-worktree destination.
No production code, graph, frozen file, manifest, generated root or README was edited.

Overall verdict: **PASS WITH NOTES** for GAP-A. The four graph gaps are filled by
these exports together with their landed prerequisites; no frozen anchor is
being sealed by this package. The remaining hygiene note is the explicitly
permitted generated-root staleness.

## Scope and statement review

These are unsigned graph-step exports, not providers of frozen theorem anchors.
Provider/frozen exact-type and seal-body probes are therefore inapplicable. In particular,
this audit does not certify N-PARTIAL-CONVEX or any Track I/N/P headline as seal-ready.
Read: AGENTS.md, PLAN, DECISIONS, package brief, GAP-A handoff including AUDIT FOCUS,
all four graph NODE blocks including SOURCE_CONCLUSION and LEAN_NOTE, their cited
blueprint statements, N/P track statements, the partial-convex frozen theorem and
exponent definitions, and the landed constants/character/homological interfaces.

Abbreviations below: N = `KAM.Nekhoroshev`, C = `N.PartialConstants`,
P = `KAM.Planetary`; TE = `KAM/Nekhoroshev/Partial/ThresholdExplicit.lean`,
R = `KAM/Planetary/PlanarTorsion/Homological/Reality.lean`.

| Node / role | Declaration(s) and locator | Statement verdict | Reason |
|---|---|---|---|
| stepN:p11:final-time | N.nthr_final_time, TE:94 | PASS | Exact positive C_T,c_2, closed form of landed blockTime, right-hand divergence along positive μ→0, positive μ_f, eventual lower bound and time comparison. Matches N graph:18752–18779 and blueprint p11c:174. |
| stepN:p11:final-mu | N.nthr_final_mu, TE:181 | PASS WITH NOTES | Explicit five formulas, positive nested six-way minimum, all five source inequalities, and time comparison; κ represents source k. Matches N graph:18721–18750 and blueprint p11c:173. See faithful-restatement notes below. |
| stepP:p11b:ho-def | P.ho_def_conj, R:39; P.ho_def_real, R:55 | PASS | Exact quotient conjugation and imaginary-part-zero/equality to landed p11c_chi for the unprojected finite sum. Together with landed chi_div_ne, chi_eq_sum and chi_family, fills the precise reality gap recorded at P graph:30490–30516, blueprint p11b:140. |
| stepP:p11b:ho-eq | P.ho_eq_forward, R:74; P.ho_eq_reversed, R:89 | PASS | Both signs exported in landed p11c_bracket convention; F_0 is landed p11c_average. Reality equality identifies this generator with the original complex sum. Matches P graph:30518–30546, blueprint p11b:141. |
| final-time helper | N.nthr_blockTime_closed, TE:64 | PASS | Uses actual blockTime, not a replacement definition; proof expands rTheta, eps, K and cancels m1/M1=m/Mc. |
| final-mu helper | N.nthr_rpow_lt_of_lt, TE:58 | PASS | Elementary positive-power monotonicity with explicit positivity premises, distinct helper name. |
| final-mu helper | N.nthr_rpow_split_le, TE:167 | PASS | Elementary power rearrangement; its positive C premise is redundant but harmless. No source result replaced by this conditional arithmetic helper. |
| ho-def helper | P.neg_mem_chiModes, R:33 | PASS | Genuine symmetry of the existing finite mode carrier under negation. |
| ho-eq helper | P.p11c_bracket_antisymm, R:82 | PASS | Canonical symplectic antisymmetry, valid even for arbitrary total functions under Lean's total fderiv convention. No differentiability conclusion is inferred from that convention. |

### Faithful restatements, hypotheses, and proof review

* C.thrCT and C.thrC2 reproduce the printed constants exactly. The new theorem
  uses the existing blockTime and original partialTimeExponent/partialDriftExponent.
  Its proof sets y=μ^(-1/(2n)), proves y^n=μ^(-1/2), and derives the eventual
  exponential lower bound from a_n<1/(2n). The limit concerns the displayed lower
  bound, exactly as in the source. μ_f is existential because the source selects
  it by a limit; it is not a missing numerical formula.
* The five μ thresholds are exposed definitions. The nested binary min is the
  printed μ_0=min{μ_a,…,μ_f}, substituted directly into positivity and the universal
  bound; there is no separately named μ_0 or equality binder. This is definitionally
  the same threshold specification. All fixed data precede μ_f and μ.
* TE:181 generalizes integer k≥1 to real κ>0, keeping it distinct from c.kappa μ.
  Instantiate κ=(k:ℝ); source hk:1≤k supplies positivity. This is a stronger arithmetic
  result, not an extra source restriction. c.d μ is definitionally μ^b_n; the fourth
  inequality uses μ^(-2b_n), exactly as printed. No μ-rescaling changes its strength.
* TE:196 explicitly obtains μ_f from nthr_final_time. The final-mu statement retains
  its positive witness and time comparison, rather than repeating the entire lower-bound
  and divergence conjunction. Consumers needing that full conjunction can use
  nthr_final_time; all five μ_0 inequalities and all printed formulas are present.
* The N premises are only n≥2 and positivity of ρ,g,m,Mc (and κ). PartialConstants
  contains only numerical fields, no hidden proof fields. Source nonempty G is used
  upstream to obtain numerical bounds; these arithmetic results need no G hypothesis
  or upper frequency bound, and even do not require m≤Mc.
* R:39 uses the existing character conjugation theorem. R:55 pairs k with -k in
  chiModes, then proves equality to p11c_chi through the landed chi_eq_sum. The new
  chiComplex is the unprojected source sum, not an alternate generator with assumed reality.
* Reality/conjugation hold for all real frequencies and actions, even resonant ones,
  because total complex division respects conjugation. This algebraic strengthening
  does not assert a nonzero resonant divisor. On the source domain NR4 supplies
  nonvanishing through the existing chi_div_ne; analytic frequency and QuarticFamily
  supply analytic coefficients through existing chi_family. R alone intentionally
  exports the missing algebraic reality component, not a duplicate analytic theorem.
* Both bracket equations need only QuarticFamily, NR4, and I∈O; analytic frequency
  dependence is unnecessary when differentiating in z at fixed I. The forward proof
  applies landed chi_bracket, and the reverse proof uses the actual canonical
  symplectic form. No hard proof step or desired conclusion is assumed.

## Definition classification (all eight new definitions)

| Definition | Intended object and whole-carrier behavior | Verdict |
|---|---|---|
| C.thrCT, TE:31 | Literal printed C_T using existing s,m,r0,Mc,A,cK,kappaC. | PASS |
| C.thrC2, TE:35 | Literal printed c_2 with sqrt n. | PASS |
| C.thrMuA, TE:38 | 2π eps0/kappaC. | PASS |
| C.thrMuB, TE:41 | ρ^(1/b_n), real power. | PASS |
| C.thrMuC, TE:44 | (π s cK/(3 sqrt n))^(2n), natural power. | PASS |
| C.thrMuD, TE:48 | (cK/(256 κρR0))^(1/γ1), γ1=1/(2n)-2b_n. | PASS |
| C.thrMuE, TE:52 | (cK/R0)^(1/γ2), γ2=1/(2n)-b_n. | PASS |
| P.chiComplex, R:29 | Actual finite sum of the existing characters over existing chiModes, before real projection. | PASS |

No new abbrev, structure, instance, fallback branch, or carrier substitution. Real
powers, inverse, sqrt and complex division use standard total Lean operations on
all inputs. Positivity/exponent restrictions ensure the source meaning wherever
N results are used; NR4 ensures divisor nonvanishing for the P analytic/bracket
claims. No result exploits a junk value to claim the source analytic equation.

## Validation receipts

All Lean/Lake invocations below were sequential, with `LEAN_NUM_THREADS=1` and
`nice -n 5`; no parallel Lean probe was run while the build, replay or lint was active.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gapa KAM.Nekhoroshev.Partial.ThresholdExplicit KAM.Planetary.PlanarTorsion.Homological.Reality
   ```

   Exit 0. Exact completion output: `Build completed successfully (9149 jobs).`
   Gate: `[inp-gate] slot 3 acquired 21:19:40` for these two modules. Replayed
   pre-existing unused-variable/deprecation/simp warnings in Threshold, Algebra,
   Energy, Chart, Mass, Characters/{Factor,Basic,Average}, and Homological;
   no warning or error from either audited module.

2. Fresh untracked probe, removed after validation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPA_Audit.lean
   ```

   Exit 0. `#check @...` and `#print axioms ...` covered all 11 new public
   theorem/lemma declarations. Additional elaborated examples checked the d-power
   identity, exact C_T and μ_d bodies, source integer-k positivity coercion, and
   equality of the unprojected generator to p11c_chi. Exact axiom output:

   ```text
   'KAM.Nekhoroshev.nthr_rpow_lt_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.nthr_blockTime_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.nthr_final_time' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.nthr_rpow_split_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.nthr_final_mu' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.neg_mem_chiModes' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.ho_def_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.ho_def_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.ho_eq_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_bracket_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.ho_eq_reversed' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. One kernel replay invocation for both new lemma modules:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.ThresholdExplicit KAM.Planetary.PlanarTorsion.Homological.Reality
   ```

   Exit 0. Exact output:

   ```text
   replaying KAM.Planetary.PlanarTorsion.Homological.Reality
   replaying KAM.Nekhoroshev.Partial.ThresholdExplicit
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the brief-permitted generated-root staleness. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (950 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No substantive lint failure. KAM.lean was left untouched as required.

5. Static and integrity checks:

   ```sh
   git diff inp...HEAD
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   git diff --check
   ```

   Full diff: exactly 256 added lines in TE and 98 in R (354 total); no landed
   file changed. Protected-path diff empty; both whitespace checks exit 0 with
   empty output. Both modules have copyright, module, public imports, module
   docstring, exposed public noncomputable section, and proper namespaces.
   All lines are ≤100 Unicode characters and both files are <1500 lines.
   Forbidden-token/override/EuclideanSpace scan returned no matches. A declaration
   scan of the remaining KAM sources found no reused short name for any of these
   19 declarations; none is declared in the root namespace.

   Recursively inspected local KAM import closure: 150 module names (including
   external leaves), 58 frozen imports. All 58 match manifest entries of kind
   definition and state SEALED; no provider or frozen theorem import. Thus no
   DRAFT_SORRY dependency is hidden by a direct-import-only check. The new exposed
   bodies and the axiom outputs also rule out proof escape through new definitions.


## Source defects, deviations, and limits

No suspected defect in the cited blueprint or pinned-source assertion was found.
The declared adaptations are the faithful real-κ generalization, inlining the
six-way minimum, and stronger global algebraic reality statements described above.
No deviation was introduced by this audit. The graph's existing NOT_STARTED statuses
and old LEAN_NOTEs were read as the baseline gap inventory; they were not edited.
No signed statement was changed. No claim is made about completion of the larger
partial-convex or planetary theorem chains.
