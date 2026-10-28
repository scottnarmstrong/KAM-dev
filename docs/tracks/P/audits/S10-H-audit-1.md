# Independent package audit S10-H, audit 1

Overall verdict: **PASS WITH NOTES for the scoped GoodAxes package**. All four signature exports are complete and pass statement and proof review. No mathematical failure or helper-name collision was found. This package supplies infrastructure, not a provider of a frozen theorem; no frozen anchor is certified seal-ready here.

Audited HEAD `d01c86f791dc902df018133cb135a336ac1a9eb2`, branch `inp-s10h`; comparison ref `inp` was `e04920e857d1c6b35cd388f3fe3f9d9cd21e8149`. Scope is only `KAM/Planetary/Nondegeneracy/GoodAxes.lean` and `GoodAxes/*.lean`, as instructed in the handoff. The report is deliberately in `/root/code/KAM-inp-s10h/docs/tracks/P/audits/S10-H-audit-1.md`, following the user's explicit path over the generic brief's main-worktree default.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package brief and handoff, design row S10-H and Appendix A, both design audits (located in `docs/tracks/P/design/`), the relevant Part 10 blueprint and Part 9 interfaces, track P statement and frozen planar/fixed theorem statements and relevant carriers. The signature file is absent in this package worktree; used the current `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, SHA-256 `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching revision-2 design audit. The four types match textually after whitespace normalization and were independently elaborated as fresh declarations with exact applications of the exports. No added premises, changed constant dependence, or altered carriers.

## Verdict and scope notes

| Contract / anchor | Verdict | Scope |
|---|---|---|
| `Nondegeneracy.n2` | PASS | Exact trace/determinant signature, all four conjuncts. |
| `Nondegeneracy.sorted_analytic` | PASS | Exact analytic-on-simple-locus signature. |
| `Nondegeneracy.good_point` | PASS | Exact quantifiers over all Data and epsilon in (0,1). |
| `Nondegeneracy.good_set` | PASS | Exact openness, density, null complement and closed-cube signature. |
| Frozen anchor / provider type and seal-body checks | N/A | No provider or frozen theorem belongs to S10-H; fresh signature-application probes replace seal probes for these implementation exports. P-PLANAR/P-FIXED closure remains outside scope. |

**N1 — inherited comparison baseline:** `git diff inp...HEAD` reports multiple merge bases, selecting `92d3a376fcd065e7c1fd1fc9e5ad33a00c70868a`. Its full diff contains 120 files, not just S10-H. The required protected-path diff is **not empty**: KAM.lean (65 added imports), frozen AveragingMean/AveragingMost proof seals, and their manifest state transitions. These are not attributed to S10-H: `git diff --name-only 4385696f^ HEAD` lists exactly the six GoodAxes files, and `git diff 4385696f^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Package-parent `4385696f^` is `92fc1f156341edef851e411c4ee31483cac7f38b`. Thus the literal whole-branch empty-diff hygiene condition fails; the scoped S10-H commits preserve protected paths. This audit does not approve inherited out-of-scope changes.

**N2 — implementation scope versus blueprint prose:** complete means the four exports allocated by design row S10-H, plus the public helpers below. The Part 10 sorted-analytic lemma's additional sentence “Moreover U2=A2” is not an extra S10-H signature: upstream `SecularSpectrum.n2` supplies discriminant positivity and `sigma_two_lt` supplies strict ordering. Part 10 n2 also discusses asymptotic divergence and the action-ratio identity beyond this four-conjunct export; no new asymptotic-limit theorem is claimed here. Likewise good_set's prose about local analyticity and uniform compact nonresonance is supported by cooperating spectral/analytic results, not bundled into this export. This respects the revision-2 design audit's explicit boundary between allocated signatures and all blueprint prose.

## Declaration inventory

All names below have prefix `KAM.Planetary.Nondegeneracy`. Helpers are assessed against their own stated algebraic or conditional contract; conditional inputs are discharged in the public package results.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| `good-set topology` | `convex_axes` (GoodAxes.lean:33) | PASS | Positive ordered cone is convex, including empty dimension. |
| `good-set topology` | `isConnected_axes` (GoodAxes.lean:49) | PASS | Explicit witness i+1 and convexity give connectedness. |
| `bpP:p10:good-set` | `good_set` (GoodAxes.lean:54) | PASS | Exact signature; good_point excludes the zero branch; density supplies the closed cube. |
| `gp-loc / sa-loc` | `eq_of_monotone_prod` (Block.lean:33) | PASS | Monotone enumerations identified via polynomial roots with multiplicities. |
| `gp-loc` | `blockZero` (Block.lean:45) | PASS | Definition: exact zero border on its entire carrier; exposed, no fallback. |
| `gp-loc` | `blockZero_zero_left` (Block.lean:48) | PASS | Literal zero first row. |
| `gp-loc` | `blockZero_zero_right` (Block.lean:50) | PASS | Literal zero first column. |
| `gp-loc` | `blockZero_succ_succ` (Block.lean:53) | PASS | Literal Q lower block. |
| `gp-loc` | `blockZero_isHermitian` (Block.lean:56) | PASS | Symmetry preserved by zero bordering. |
| `gp-loc` | `charpoly_blockZero` (Block.lean:65) | PASS | Reindex to block diagonal; characteristic polynomial X times charpoly Q. |
| `gp-loc` | `snoc_zero_monotone` (Block.lean:75) | PASS | Nonpositive sorted entries remain ordered when zero is appended. |
| `stepP:p10:gp-loc` | `sorted_blockZero` (Block.lean:90) | PASS | Correct spectral order: sorted Q followed by zero, although zero is first in matrix coordinates. |
| `gp-loc` | `sigma_neg` (Induction.lean:35) | PASS | Derived from definite and positive coercivity; no assumed negativity. |
| `gp-choice` | `peelError_cons` (Induction.lean:41) | PASS | Literal peel error equals full matrix minus bordered outer matrix. |
| `gp-loc` | `sorted_congr` (Induction.lean:47) | PASS | Matrix equality transports sorted spectra; proof irrelevance handles Hermitian witnesses. |
| `gp-choice / gp-loc / gp-nr` | `peel_step` (Induction.lean:52) | PASS | Outer nonresonance is an induction input; inner t and nonresonance are proved, for any positive upper bound c. |
| `stepP:p10:gp-base` | `good_point_two` (Induction.lean:106) | PASS | Axes (min(epsilon/2,c/2),1), c=m1^2/(16*m0^2), satisfy hierarchy and n2 threshold. |
| `bpP:p10:good-point` | `good_point` (Induction.lean:133) | PASS | Exact signature; induction quantified over physical data and reindexed outer masses. |
| `stepP:p10:n2-r` | `ratio_formula` (N2.lean:34) | PASS | Trace/determinant identities; positivity discharges all denominator conditions. |
| `stepP:p10:n2-r` | `ratio_gt` (N2.lean:54) | PASS | Strict bound retained. |
| `stepP:p10:n2-t` | `sigma_ratio_ge` (N2.lean:80) | PASS | Increasing negative eigenvalues give inverse ratio <1; requested non-strict bound retained. |
| `stepP:p10:n2-nr` | `action_ratio_ge` (N2.lean:101) | PASS | Axis threshold implies action ratio at least 4 using positive masses and square roots. |
| `stepP:p10:n2-nr` | `nr4_of_hier` (N2.lean:129) | PASS | Rules out ratios 2 and 3 via t+1/t>4 and upstream nr4_two_iff. |
| `bpP:p10:n2` | `n2` (N2.lean:162) | PASS | All four conjuncts exactly match the signature. |
| `stepP:p10:gp-choice` | `exists_gap` (Resonance.lean:30) | PASS | Finite positive lower bound; empty set legitimately uses 1. |
| `stepP:p10:gp-nr` | `nr4_of_forall` (Resonance.lean:43) | PASS | Injectivity proved by k=e_i-e_j, with integer l1 norm 2. |
| `stepP:p10:gp-nr` | `nr4_perturb` (Resonance.lean:61) | PASS | Conditional helper: gap dominates 4e; pure last-coordinate resonance excluded by last eigenvalue <0. |
| `stepP:p10:sa-loc` | `sorted_eq_of_frame` (SortedAnalytic.lean:33) | PASS | Orthogonal diagonalization identifies characteristic products and ordered roots. |
| `bpP:p10:sorted-analytic` | `sorted_analytic` (SortedAnalytic.lean:41) | PASS | Exact signature; local analytic ordered branches coincide with sorted eigenvalues. |

## Definition classification and proof review

The only new definition/abbreviation/structure is `blockZero` (`GoodAxes/Block.lean:45`): the literal matrix with zero first row and column and Q in successor coordinates, for every input matrix Q and every dimension. No junk value, exceptional fallback, spectral oracle, assumption-bearing structure, or hidden instance is introduced. It lies under the exposed public section. The inherited `Data` holds only positive physical constants/masses and a positive dimension. `Vec n = Fin n → ℝ`; indices for resonance are `Fin n → ℤ`. Metric balls on Vec use its Pi max norm, so the final closedBall is the required closed cube. The Weyl comparison instead uses the explicit Euclidean operator norm `op2`; no norm substitution occurs.

The key induction step (`Induction.lean:52–102`) obtains a finite positive gap from outer nr4, then chooses t in the nontrivial right-neighbourhood of zero with t<c, t≤1, t≤a_i/2 and C*t^(3/2)<gap/4. The peel constant is fixed before t. It constructs the exact error and bordered matrix; Hermitian proofs are derived, not assumed. `sorted_blockZero` correctly moves the zero eigenvalue to the *last* sorted slot. Weyl gives componentwise displacement ≤op2(E)≤frobenius(E)≤C*t^(3/2). Full-system definiteness proves the last eigenvalue strictly negative. In `nr4_perturb`, nonzero truncated k uses gap minus 4e; zero truncated k uses its nonzero last coefficient and strict negativity. Injectivity follows separately from the order-two difference vectors. The two-planet base chooses positive a0 small enough for both the hierarchy and the literal mass threshold. No induction conclusion is installed as a standing assumption.

`sorted_analytic` uses local_analytic and characteristic-product uniqueness to identify ordered branches pointwise on a neighbourhood, then transfers AnalyticAt. `good_set` uses a proved good point to exclude the identically-zero branch of `good_set_dichotomy`, applies the connectedness of axes, and chooses radius rho/4 to place the closed cube of radius 2*(rho/4) in the open intersection.

Dependencies are consumed as designed: S9-2 supplies two-planet trace, determinant and ordering facts; S9-G supplies k4, nr4, good equivalence and dichotomy; S10-W supplies weyl; S10-P supplies peel and outerData; S10-Z is consumed through GoodPolynomial's analytic-zero dichotomy. LocalAnalytic and Norms provide the local frame and ordered-spectrum algebra. A recursive scan of 91 reachable KAM modules found no provider and no frozen theorem import (only frozen definitions), so no DRAFT_SORRY theorem is imported. All 28 new public theorems have only the standard allowed axioms, independently checked below.

No other KAM declaration uses any of the new helper short names. The only repeated short export names are n2 and good_set in the intentionally distinct namespace `KAM.Planetary.SecularSpectrum`; the fully qualified names do not collide. This includes explicit scans for eq_of_monotone_prod, blockZero, exists_gap, sigma_neg, convex_axes, isConnected_axes, sorted_congr, sorted_eq_of_frame and all other declarations in the inventory.

## Independent validation

All auditor-controlled Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean, update, cache fetch, generated-file rewrite or state-changing git was run.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10h KAM.Planetary.Nondegeneracy.GoodAxes
[inp-gate] slot 1 acquired 15:20:16 for KAM.Planetary.Nondegeneracy.GoodAxes
Build completed successfully (9137 jobs).
exit 0
```

The gate waited before acquiring its slot. Output replayed upstream unused-variable/deprecation/style warnings in Kepler, Poincare.Chart, SecularForm.Coefficients, SecularSpectrum.Definiteness, LocalAnalytic.Unique and Nondegeneracy.Weyl. No elaboration error or resource override.

2. Fresh signature applications and all public theorem axioms:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10HAudit.lean
exit 0
```

The probe copied the four literal signature types under fresh names and applied the corresponding export to precisely its required arguments. The exact `#print axioms` output follows:

```text
'KAM.Planetary.Nondegeneracy.convex_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.isConnected_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.good_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.eq_of_monotone_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.blockZero_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.blockZero_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.blockZero_succ_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.blockZero_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.charpoly_blockZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.snoc_zero_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sorted_blockZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sigma_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.peelError_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sorted_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.peel_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.good_point_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.good_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.ratio_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.ratio_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sigma_ratio_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.action_ratio_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.nr4_of_hier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.n2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.exists_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.nr4_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.nr4_perturb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sorted_eq_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sorted_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation after the probe finished:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.GoodAxes KAM.Planetary.Nondegeneracy.GoodAxes.N2 KAM.Planetary.Nondegeneracy.GoodAxes.Block KAM.Planetary.Nondegeneracy.GoodAxes.SortedAnalytic KAM.Planetary.Nondegeneracy.GoodAxes.Resonance KAM.Planetary.Nondegeneracy.GoodAxes.Induction
replaying KAM.Planetary.Nondegeneracy.GoodAxes
replaying KAM.Planetary.Nondegeneracy.GoodAxes.SortedAnalytic
replaying KAM.Planetary.Nondegeneracy.GoodAxes.Block
replaying KAM.Planetary.Nondegeneracy.GoodAxes.N2
replaying KAM.Planetary.Nondegeneracy.GoodAxes.Induction
replaying KAM.Planetary.Nondegeneracy.GoodAxes.Resonance
exit 0
```

4. Repository lint, run after kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (769 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the brief-permitted stale generated root (`KAM.lean is out of date`); all remaining lint gates pass. Root regeneration is left to the orchestrator, as required.

Additional static checks: no forbidden proof escape, EuclideanSpace, or set_option in the six scoped files; all have copyright, module, public imports, module docstring and exposed public section. File lengths are facade 81, Block 99, Induction 158, N2 173, Resonance 122, SortedAnalytic 54, all well below 1500. `git diff --check inp...HEAD -- KAM/Planetary/Nondegeneracy/GoodAxes.lean KAM/Planetary/Nondegeneracy/GoodAxes` exits 0 with only the multiple-merge-base warning. The public theorem/definition inventory contains 28 theorems and one definition.

## Suspected defects, deviations and handoff

No new suspected mathematical defect in the blueprint or pinned sources was found by this implementation audit. Existing blueprint text at `blueprint-P/parts/p10-nondegeneracy.tex:108–109` quotes Fej04r p.58's “par un raisonnement analogue à ci-dessus” and records the missing scales/nonresonance transfer as a source gap. The present explicit peeling induction fills that assigned proof obligation; this is the already declared route, not a new source allegation. The pinned PDF was not independently re-audited here. No source or hypothesis was silently repaired.

Remaining notes are N1 (whole-branch protected-path baseline) and N2 (allocated signature versus broader prose), plus the permitted stale generated root lint exception. No S10-H code change is requested. Only this report was added to the repository; auditor-created scratch probe/log files were removed after recording the results.
