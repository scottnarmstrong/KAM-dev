# T21 independent package audit 1

**Overall verdict: PASS WITH NOTES.** The signed full `patch` and geometric helper pass. The only hygiene exception is the expected generated-root check, recorded below with the actual lint result. This is an infrastructure package: no frozen theorem is sealed or proved by T21, and this audit does not certify downstream P12-C or the planetary headline.

## Scope and authority

Audited worktree: `/root/code/KAM-inp-p11c-t21`; HEAD `e743c7e4d5495f5476da88acaffc298cf6b03b6e`; comparison `inp` at inspection `68928d00aa4d02c9b2a11f2b9673d8bd47616645`. Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T21-handoff and its AUDIT FOCUS, P11C/P1213 designs, the P11C design audit, current signed declarations, Part-11b patch and Part-12 consumer statements, track-P statement, actual Birkhoff predicate and relevant frozen definitions. The user's exact report destination overrides the generic brief's main-worktree destination. Audit-only production scope: `KAM/Planetary/PlanarTorsion/Patch.lean`.

`git diff inp...HEAD` has 18 files and 2,348 insertions (2,456 diff lines). Git warns `multiple merge bases, using 22796f6f8617014ca48cc9028f9ca78aaad0ec4a`. The inherited Birkhoff and Generic files are dependency context, not additional package verdicts. `git show --stat HEAD` attributes only the 191-line Patch file to T21. The full three-dot protected-path diff for `KAM/Frozen manifest KAM.lean README.md` is empty. The initially untracked T21 handoff is preserved.

Current SHA-256:

- Patch: `402cd7fd40a1768a8873f28ee8b9832125c92be7d97d38f580f4e96fd3cad270`.
- P11C design: `8693b4c33b78a6d52c251999b15e08fc68d588b9250e2e4bbe3e64b4510a6437`.
- `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`: `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`.

## Declaration and node coverage

All names below are in `KAM.Planetary`. The design node table L148 maps exactly one graph record to T21: `bpP:p11b:patch`; no additional T21 proof-step record is omitted. Its implementation uses the full patch export rather than replacing it by geometry alone.

| Node / obligation | Lean declaration and Patch line | Verdict | Reason |
|---|---|---|---|
| combined frozen-action frequency | `p11c_combinedFrequency`, L33 | PASS | Exact signed definition body, including fast frequency and slow factor 2. |
| same-patch output certificate | `PlanarFrequencyPatch`, L38 | PASS | Exact signed body; positive-volume compact action image, analytic R-nondegenerate map, NR4 and uniform finite type. |
| action dictionary | `p11cPa_action_eq`, L54 | PASS | Actual secular data action equals physical `p.actions`, by reflexivity. |
| axis dictionary | `p11cPa_axis_eq`, L57 | PASS | Actual inverse-axis formula, by reflexivity. |
| axis/action inverse | `p11cPa_axes_actions`, L60 | PASS | Uses upstream inverse on the positive ordered axis cone. |
| frequency transport | `p11cPa_freq_eq`, L65 | PASS | Actual `p11cSecularData`, with signed spectral bridge on axes. |
| Euclidean normalization | `p11cPa_euclid`, L73 | PASS | Equality of literal square-root sums; no ambient carrier change. |
| nonempty unit sphere | `p11cPa_unit`, L77 | PASS | Concrete first coordinate vector in dimension 2. |
| strict jet-sup extraction | `p11cPa_jet_attain`, L82 | PASS | Strict lower bound produces an order and unit direction; order zero handled separately. |
| `bpP:p11b:patch` | `patch`, L102 | PASS | Exact signed type; all geometry, determinant, frequency and Birkhoff clauses on one joint patch. |
| geometric projection | `torsion_patch_geometry`, L180 | PASS | Exact signed type and a projection of the full patch. |

The two definition bodies are text-identical to signatures L762–779. The theorem statements, including binder order, are text-identical to signatures L782–791 and L662–668. Independent elaboration also checked fresh copies with bodies `by exact KAM.Planetary.patch p hp aStar ha eta he` and the corresponding geometric helper. Whole-polymorphic `type_of%` examples against those copies pass. No extra source premise or weakened signed conclusion was introduced.

## Proof and consumer review

At L114–124, `Nondegeneracy.interface` is instantiated with **`p11cSecularData p hp`**, dimension 2 and the actual two functions `![p11c_phi4 p, fun a => (p11c_beta p a).det]`. Analyticity and independent nonzero witnesses come from T20, rather than assuming a simultaneously good point. The interface itself intersects the spectral good set with these further nonzero conditions. Its outer closed ball lies in the requested neighborhood and actual axis cone. T17 `remain` supplies a strictly positive determinant lower bound on the inner compact ball; `beta_properties` supplies symmetry.

The frequency transport L138–148 first proves equality on the open action image using the inverse-axis identity and `p11c_sigma_eq_sigma`. R-nondegeneracy and analyticity then transfer on that image. Balls use the ordinary Pi max norm, so these are the source cubes, while derivative unit directions and coefficient vectors use the explicitly identified Euclidean length. No `EuclideanSpace` carrier is introduced.

NR4 at L149–156 includes every nonzero integer mode of l1 length at most 4, not just coordinate modes. The proof derives strict positive integer l1 length from nonzero k, casts the bound to upstream `k4`, and rewrites the actual spectrum. The lower bound is uniform over the inner ball.

For every order mu >= mu0, L157–172 uses upstream monotonicity to bound `betaMu` below by its positive base amount. A bounded-below infimum gives a bound on each jet maximum at each unit c and I. Choosing exported beta = upstream beta / 2 makes the comparison strict, permitting supremum extraction of an actual j <= mu and unit v. The zero-order case uses the concrete unit vector and its derivative value is direction-independent. Equality on an open neighborhood of I justifies transporting all iterated derivatives. Thus no maximum-attainment, differentiability, or finite-type conclusion is assumed as a new hypothesis.

At L173–177 the same a0 and r feed `birkhoff_form`, with outer open ball `ball a0 (2*r)` and inner closed ball `closedBall a0 r`. Positivity of r gives the strict collar inclusion. The returned `PlanarBirkhoffResult` is the signed output predicate, including one actual T for both physical perturbations, action preservation, equivariance, physical collision-free image, the actual Omega = 2 sigma and beta, and the frozen `HasSecularBirkhoffForm` normalization. This pays the T21 portion of P1213 design row P12-C L233 and upstream row L58. It does not certify P12-C's separate jet dictionary, physical assembly, closed-cylinder radius choice, stability application or P-G sealing obligations. The signed patch deliberately exports a positive B lower bound rather than an equality naming the compact minimum; that is sufficient for the consumer's determinant bound. It retains all four signed frequency clauses. Use of `interface` instead of `interface_stability` therefore does not drop a T21 signed obligation; perturbation stability remains downstream work.

**T20 fix-round note.** This checkout's Generic is the 135-line pre-append version; it does not contain `p11cGe_phi4_ne_zero_iff_nr4` or `p11cGe_phi4_ne_zero_iff_good`. The current sibling T20 worktree has those appended bridges (the latter explicitly identifies the adapter's nonzero locus with `SecularSpectrum.good` on `p11cSecularData`). T21 neither references nor needs those appended declarations to prove its signed result: the upstream interface directly supplies good-spectrum NR4 and separately imposes the actual adapter's nonvanishing as an extra analytic condition. Its local frequency bridge is `p11c_sigma_eq_sigma`, already imported. This scoped PASS does not retroactively discharge the earlier T20 audit's missing-locus finding; retain the append-only repair when integrating the source-correspondence package.

## Definition and hypothesis classification

- `p11c_combinedFrequency`: literal total arithmetic formula, not a choice or fallback. Real division is total at zero, but all patch claims concern the positive action image. No theorem uses an off-domain zero-denominator value.
- `PlanarFrequencyPatch`: output-only proposition, not an input structure or premise. All its geometry, analytic, nonresonance and finite-type clauses are proved by `patch`. No new structure, abbreviation, instance or choice definition is added.
- `patch` and geometry assume only physical positivity (`p.Valid`), an axis-cone point, typing data and positive neighborhood radius. Support lemmas use domain guards, typing or their explicitly stated strict numerical jet bound; the latter is a distinct helper, proved usable from upstream finite type inside `patch`. There is no conclusion-shaped hypothesis in a source-facing result.

A recursive textual KAM import-closure check found 315 modules, **zero provider imports and zero frozen theorem modules**. Only frozen definitions occur; there is no DRAFT_SORRY theorem import to excuse by manifest state. Every new theorem short name has one declaration occurrence in KAM; helpers have the distinctive `p11cPa_` prefix. No root declaration, notation or instance shadow is introduced.

## Independent validation

All Lean/Lake commands were serialized and used `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource overrides, clean, cache fetch, dependency mutation or generated-root repair was used.

1. Targeted gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t21 KAM.Planetary.PlanarTorsion.Patch
   ```

   Exit 0. Output begins `[inp-gate] slot 2 acquired 00:15:56 for KAM.Planetary.PlanarTorsion.Patch` and ends `Build completed successfully (9361 jobs).` Dependencies replay pre-existing warnings (unused variables/simp arguments, deprecated tactics); no Patch warning or default-heartbeat failure occurred.

2. Signature/body/axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T21Audit.lean
   ```

   Exit 0, no warnings/errors, including fresh signed theorem bodies, exact whole-type examples and both expected definition equalities by rfl. Exact axiom output:

   ```text
'KAM.Planetary.p11cPa_action_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPa_axis_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPa_axes_actions' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPa_freq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPa_euclid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPa_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPa_jet_attain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.torsion_patch_geometry' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay (one invocation; T21 has no separate provider or helper module):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Patch
   ```

   Exit 0. Exact output: `replaying KAM.Planetary.PlanarTorsion.Patch`.

4. Static checks: 191 lines; maximum Unicode line width 98; required copyright/module/public imports/module docstring/public section present; definitions exposed by the section attribute. Forbidden proof escapes, resource overrides and EuclideanSpace are absent. Full diff added-text scan likewise found none. Protected-path three-dot diff is empty. Signature text comparison passes for all four signed declarations.

5. Lint result and final workspace checks are recorded below.

## Errata, deviations and limits

No new suspected pinned-source or blueprint defect is established by T21. No production deviation was introduced by this audit. The earlier design's note about the nonzero-locus adapter is retained as the integration note above, not silently repaired. The exact signed target does not require an exported determinant-minimum equality or the full upstream stability theorem. No independent re-audit of pinned PDFs or inherited T16/T17/T19/T20 proofs is claimed. The permitted axioms of `patch` cover its actual transitive proof dependencies and contain no sorryAx.

## Lint and final receipt

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1149 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint failure occurred. The generated KAM.lean was left untouched. This is the reason for PASS WITH NOTES rather than an unqualified overall PASS.

`git diff --check` exits 0. The report also passes `git diff --no-index --check /dev/null <absolute-report-path>`. Auditor scratch probe and logs were deleted after their evidence was copied here. Final status contains only the new audit report and the pre-existing untracked T21 handoff; no tracked production file changed. Report destination is the requested package worktree, not `/root/code/KAM-inp`.
