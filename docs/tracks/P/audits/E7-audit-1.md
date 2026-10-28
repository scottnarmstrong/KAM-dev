# E7 independent package audit 1

Audit date: 2026-10-28. Worktree `/root/code/KAM-inp-p14-e7`; audited HEAD
`bd819d083124558f56762996622bf6f53fc263d1`. Scope: only
`KAM/Planetary/Exponential/Perturbation.lean` (323 lines). The user's explicit output path
overrides the generic brief's main-worktree destination. Only this report is a persistent
audit edit; temporary probes live in this worktree's `.lake/abi-scratch/`.

## Verdict

**FAIL against the requested no-reused-public-short-name criterion.** The mathematical
implementation and the two signed export statements pass the source review. The remaining
finding is a naming-contract conflict, not a mathematical refutation or extra hypothesis:
the signed name `perturbation` is already used elsewhere in KAM. Do not rename the export
silently, since the user also requires the signature exactly. An explicit reconciliation
of those requirements is needed before an unqualified package PASS.

E7 has no provider or frozen theorem export. Provider/frozen type-equality and seal-body
probes are therefore not applicable; this package alone does not seal P-EXP-SAFE. Its two
ordinary exports are checked against the actual P14 signatures instead.

## Authority and comparison boundary

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief, E7 handoff,
`docs/tracks/P/statement.md`, P14 design and both design audits, the E7 signatures at
`/root/code/KAM-inp/.drafts/design/P14Signatures.lean:301` and `:322`, and blueprint
`blueprint-P/parts/p14a-amd-expsafe.tex:160–234`. Read the relevant frozen
`IsPartialPerturbation`, `partialComplexDomain` definitions and P-EXP-SAFE anchor as context.
The design's node table at lines 154–161 deliberately keeps all seven `pt-*` steps internal.

Required comparison: `git diff inp...HEAD`. Git warns:

```text
warning: inp...HEAD: multiple merge bases, using 8818c4c32b9f77bf31896effa86133faf231e133
```

The broad comparison contains 33 files (4604 insertions, 98 deletions), including inherited
packages. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
only `KAM.lean` differs, with 19 inherited imports. Frozen files, manifest and README have
no delta. For attribution, `git diff 625de02f..HEAD --stat` identifies only the 323-line E7
module; the corresponding protected-path diff is empty. Thus the literal branch-wide
empty-diff check fails, but E7 did not introduce those generated-root edits. No repair or
root regeneration was performed.

## Declaration and node ledger

All names below are in `KAM.Planetary`. Locations refer to the audited Lean file.

| Node / role | Declaration or proof location | Verdict | Reason |
|---|---|---|---|
| pc-share analytic input / Ch3 | `chart_perturbation_analytic`, 41 | PASS | Literal signed header; specializes the actual analytic product-chart perturbation to G=m0=1 and normalizes `mul_one`. |
| pt-input core | `perturbationCore`, 48 | PASS | Literal closed action/AMD bounds and one radian fundamental cell; see classification below. |
| pt-input inclusion | `perturbationCore_subset`, 51 | PASS | Unconditional projection to enlargedCylinder; final proof combines it with E3 real_domain. |
| pt-input closedness | `isClosed_perturbationCore`, 54 | PASS | Finite coordinate inequalities and continuous quadratic AMD. |
| pt-input compactness / x-top | `isCompact_perturbationCore`, 84 | PASS | Closed and bounded in finite dimension; no positivity or nonemptiness premise. Negative A gives an empty set; the proof handles n=0 explicitly. |
| pt-rho geometry | `exists_shift_mem_core`, 148 | PASS | Floors each real fast angle by 2π; real fast actions and slow coordinates remain unchanged. Max norm of all imaginary coordinates is strictly below rho. |
| lattice inverse helper | `fastShift_neg_add`, 187 | PASS | Literal cancellation for all phases and integer shifts. |
| lattice zero helper | `fastShift_zero_eq`, 193 | PASS | Literal zero shift, both blocks. |
| pt-neg helper | `isPartialPerturbation_neg_of`, 199 | PASS | Negates all four frozen clauses; conditional helper receives the already proved positive perturbation, not an unproved source claim. General slow count k is retained. |
| Ch3 domain periodicity | `chartSafe_shift_iff`, 207 | PASS | Chart-domain preservation and physical chart equality from poincareProd_lattice; reverse uses the negative shift. |
| Ch3 perturbation periodicity | `fMov_poincareProd_shift`, 217 | PASS | Actual physical chart perturbation is invariant, not a replacement model. |
| tube membership helper | `mem_periodicOrbitSet_self`, 222 | PASS | Zero shift proves inclusion for every set K. |
| pt-input | internal `perturbation`, 238–244 | PASS | chartSafe is open, core compact and collision-free; E6 tube receives the proved analytic and periodic input. |
| pt-rho | internal `perturbation`, 246–286 | PASS | rho=min(kappa,r/2)>0; compact image C of core × closedBall provides B0=max(1,B'). Every point in F reduces by a lattice shift into C, giving F⊆T and the uniform bound. |
| pt-def | internal `perturbation`, 288–292 | PASS | P=fc/B0 on T, zero elsewhere; B0>0 proved. |
| pt-p12 | internal `hPos`, 295–300 | PASS | Complex differentiability by restriction/congruence and norm at most one by the actual compact bound. |
| pt-p3 | internal `hPos`, 301–304 | PASS | E6 real trace gives fc(cx w)=f(w), division by a real positive B0 preserves reality. |
| pt-p4 | internal `hPos`, 305–307 | PASS | E6 periodicity supplies both translated membership in T and equality of fc values; does not assume translated membership without proof. |
| pt-neg assembly | `perturbation`, 308–309 | PASS | Applies the proved negation helper to hPos. |
| perturbation (i),(ii) | `perturbation`, 226–321 | Mathematical PASS; naming FAIL | Signed header is literally identical; both signs and every real workingCylinder trace are proved. Constants precede all downstream coupling/initial-data choices. Reuses the public short name. |

The 12 public theorems and one public definition are all listed. The two signed
declarations have character-for-character identical headers before `:=` to the signature
file. Additional helpers have distinct purposes and source/typing premises; no helper
replaces a signed export with a conditional result. No graph node assigned to E7 is missing.
There is no exported lemma falsely claiming a graph-node conclusion while proving only a
substep. Openness/invariance of F need not be exported separately: the actual restrictions
and translated-tube membership establish the four required frozen clauses directly.

## Definition classification and the reported deviation

`perturbationCore` is the only new public def/abbrev/structure. It is a **literal geometric
set**, valid on its entire carrier, without fallback: fast angles in [0,2π], closed fast
actions in [lower−2*kappa,upper+2*kappa], and chartAMD≤A. Its compactness theorem even covers
inadmissible/empty parameter choices.

Blueprint line 175 defines G'=∏(lower−2κ,upper+2κ); line 228 defines
`K_*={w: lambda in [0,2pi]^n, Lambda in closure G', Gamma(w) <= A+}`. Setting's
`enlargedCylinder B kappa A` already has the **2*kappa** closed bounds. Under the actual
admissibility/enlargement inputs the intervals have positive width, so these are exactly
the closure bounds, not a smaller core or strengthened premise. Blueprint line 160 defines
Gamma as the sum of half the squared slow coordinates; that is precisely `chartAMD`.
The signature's A is the enlargement parameter A+, not B.outerAMD or an independent
smaller threshold. Thus the handoff's claimed deviation is a faithful coordinate spelling
of the prescribed core; it is not a mathematical deviation requiring stronger input.

Local objects are genuine constructions: x0 is the real part, k the integer floor shift,
rho the prescribed minimum, T the E6 tube, C the compact thickening image, B0 a real
normalizer, and F the literal frozen partialComplexDomain. Local P has a zero extension
outside T exactly as blueprint line 230 requests. Every analytic, norm, reality and
periodicity use first proves its argument is in T, so no conclusion exploits the exterior
zero branch. The compact thickening image supplies the same needed rho-neighborhood bound
without assuming a global bound on the infinite periodic orbit set.

The import closure contains 107 KAM modules and 69 frozen definition modules, with no
provider or frozen theorem-anchor module. Hence there is no DRAFT_SORRY theorem dependency
and no imported theorem-anchor manifest state to waive. No conclusion-shaped field or
hypothesis was found; `EnlargedData` supplies only the source enlargement inequalities.

## Hygiene findings

**F1 — reused public short name, contractual FAIL.** At Lean line 226, `perturbation`
duplicates `KAM/Apost/PerturbationTorsion.lean:325` and
`KAM/Planetary/SecularForm/Basic.lean:52`. Fully qualified names differ, so this is not a
Lean name collision or proof defect. The current helper's result differs from the handoff:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-p14-e7 KAM.Planetary.Exponential.Perturbation
```

Exit 0:

```text
short-name check OK (no reused public short name)
```

Inspection of the helper explains this: it removes all names appearing in live
`*Signatures.lean` files before searching for duplicates. A separate unexempted source scan
of every E7 short name finds exactly the two occurrences above. That helper exemption does
not satisfy this user's explicit “no reused public short name” focus. The owner/orchestrator
must reconcile the signed-name requirement with the naming rule. No name was changed here.

Static audit: 323 lines, maximum line length 100 Unicode characters; no forbidden escapes,
EuclideanSpace, resource overrides, private axiom, or fallback premise. Copyright, module,
public imports, module docstring and exposed public noncomputable section are present.

## Mechanical validation receipts

All Lean/Lake checks are serialized with LEAN_NUM_THREADS=1 and nice -n 5. No clean,
update, cache fetch, package mutation, frozen edit or production edit was performed.

Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e7 KAM.Planetary.Exponential.Perturbation
```

Exit 0, after a shared-gate wait. The wrapper runs `nice -n 5 lake build`.
Final output:

```text
[inp-gate] slot 3 acquired 18:46:45 for KAM.Planetary.Exponential.Perturbation
Build completed successfully (9153 jobs).
```

Dependency warning output (terminal styling and repeated linter hints omitted):

```text
KAM/Kepler/Energy.lean:106:35: Variable name `hm` is not explicitly referenced.
KAM/Kepler/Energy.lean:106:48: Variable name `hκ` is not explicitly referenced.
KAM/Planetary/Poincare/Chart.lean:212:42: Variable name `hm` is not explicitly referenced.
KAM/Planetary/Poincare/Chart.lean:212:55: Variable name `hκ` is not explicitly referenced.
KAM/Planetary/Poincare/Chart.lean:247:37: Variable name `hm` is not explicitly referenced.
KAM/Planetary/Poincare/Chart.lean:247:50: Variable name `hκ` is not explicitly referenced.
KAM/Kepler/Mass.lean:147:57: Variable name `hκ` is not explicitly referenced.
KAM/Kepler/Mass.lean:157:52: Variable name `hκ` is not explicitly referenced.
KAM/Kepler/Mass.lean:500:5: Variable name `hw` is not explicitly referenced.
KAM/Kepler/Mass.lean:524:52: Variable name `hm` is not explicitly referenced.
KAM/Kepler/Mass.lean:524:65: Variable name `hκ` is not explicitly referenced.
KAM/Planetary/Exponential/RealDomain.lean:164:49: Variable name `hB` is not explicitly referenced.
KAM/Planetary/Exponential/ComplexTube.lean:135:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead
```

No warning was attributed to E7. This was the mandated incremental target build, not a
forced rebuild of the library.

Fresh signature/axiom/root-shadow probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E7Audit.lean
```

Exit 0. The probe copied each exact signed theorem header into a fresh `example`, with
body `chart_perturbation_analytic m hm` or `perturbation B hB hd`, respectively. Both
elaborated. The unexempted root-shadow check inspected actual environment constants
belonging to the E7 module. Exact output:

```text
'KAM.Planetary.chart_perturbation_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.perturbationCore_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isClosed_perturbationCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isCompact_perturbationCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_shift_mem_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastShift_neg_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastShift_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isPartialPerturbation_neg_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chartSafe_shift_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fMov_poincareProd_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_periodicOrbitSet_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.perturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
shadow check OK (no package name shadows a root constant)
```

Kernel replay, one invocation for the one audited module (it contains both signed exports
and all helper lemmas):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.Perturbation
```

Exit 0. Complete checker output:

```text
replaying KAM.Planetary.Exponential.Perturbation
```

Lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted stale-generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (823 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Thus lint is PASS WITH NOTES under this brief's exception, not an unqualified exit-zero
receipt. The frozen guard and ABI checks pass. KAM.lean was left untouched.

Final checks: `git diff --check` exits 0 with no output; a direct whitespace check of this
untracked report also passes. The only new persistent audit file is this report; the
pre-existing untracked E7-handoff remains untouched. E7Audit.lean and the two E7 validation
logs were deleted from `.lake/abi-scratch/` after recording their results. No heartbeat
failure occurred. All mathematical checks pass; the overall contractual FAIL remains F1.

## Source/blueprint issues and limits

No new suspected pinned-source erratum was found. No pinned-paper theorem is newly
certified by this scoped implementation audit. The already recorded pc-share issue remains
a documentation issue: `blueprint-P/parts/p7-kepler-poincare.tex:207` says “whose proof gives
analyticity as well as C∞”, whereas the cited smoothness statement alone does not imply
analyticity (P14 design line 345). E7 actually imports and applies
`analyticOnNhd_fMov_poincareProd`, so this is discharged by a stronger proved supplier,
not an extra assumption. The core spelling is faithful, as explained above.

Uncertainties/required follow-up: reconcile F1; account separately for inherited generated
root differences in the branch-wide comparison. This audit does not re-audit E3/E6 or seal
the frozen planetary headline.
