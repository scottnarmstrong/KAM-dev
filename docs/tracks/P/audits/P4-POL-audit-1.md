# Independent P4-POL package audit 1

Overall verdict: **PASS WITH NOTES** for P4-POL. All assigned polar contracts and
proof checks pass. Notes are the explicitly permitted stale generated root and
nonblocking unused-binder/simp warnings. No blocking mathematical or hygiene defect
was found. This package contains no frozen anchor or provider to seal.

## Scope and authority

Audited only `KAM/Planetary/PGMeasure/Polar.lean` at HEAD
`a7a32949d351e47a9f51f1ae3f2fdb2e85889c85`, using `git diff inp...HEAD`.
The comparison adds exactly this 742-line module. At inspection, `inp` was
`31f0bfbf70c07b1eefd006237f331c00e003a0e5`; the merge base was
`872a014af58890f96058190624e431a0ed0228a5`.
The untracked prover handoff was an input, not part of the committed diff.
The user's explicit report destination overrides the generic brief's MAIN-inp destination.
No implementation, frozen, manifest, generated, or git-state changes were made.

Read AGENTS.md, PLAN, DECISIONS, the independent package brief and P4-POL handoff;
P45 design (including F6, package row and Revision 4), design audits 1–4,
`/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, Track P statement,
blueprint P4 lines 167–186, frozen P-G and the relevant frozen coordinate,
cylinder, cell, action and lattice definitions. Inspected the reused Setting,
Collar, P1 chart and P7 polar interfaces. Revision 4 concerns extension agreement;
this module introduces no extension object and is unaffected by that amendment.

Audited file SHA256:
`94889b1ff9d95df4e3eebd3746c81bf0248f01e72b923d5bda5aa1d36f8eaaf1`.
Shared signature SHA256:
`6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402`.
Design SHA256:
`fe084af07ac93f216e4f98e0ff5284319c5a544ee6df073af2069e9639d47559`.

This is infrastructure, with no provider export or frozen anchor to seal.
The frozen `properlyDegenerateKAM` proof remains outside scope and unpaid;
package acceptance cannot be read as P-G or campaign closure. Accordingly the
brief's frozen/provider type-equality and seal-body probes are inapplicable.
Instead, the five theorem contracts are copied from the authoritative signature
file under fresh names and applied directly to the actual exports, with every
explicit binder in order. All seven assigned declaration headers match after
whitespace normalization; both definition bodies match the intended formulas.

## Declaration and node review

Names below are in `KAM.Planetary`; locators refer to Polar.lean.
Every new public declaration has its own row. Helpers without a separate blueprint
statement are classified as auxiliary facts supporting the indicated source node.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| `bpP:p4:s-disc#chart` | `oscillatorPolar` (38) | PASS | Exact general a,b formula, using frozen assemble and real block projections. |
| P7 bridge | `oscillatorPolar_eq_polarMap` (43) | PASS | Exact signature; definitional equality on the entire carrier, proved by rfl. |
| `bpP:p4:s-disc#chart` | `polarCellMap` (46) | PASS | Exact formula; scales all angle coordinates by 2π and leaves actions fixed. |
| `stepP:p4:dm-jac`, auxiliary | `hasFDerivAt_oscillatorPolar` (115) | PASS | Actual derivative witness with explicit fast and slow coordinates; only positive slow actions required. |
| Chart coordinates | `oscillatorPolar_fst_castAdd` (165) | PASS | Fast positions unchanged. |
| Chart coordinates | `oscillatorPolar_snd_castAdd` (169) | PASS | Fast actions unchanged. |
| Chart coordinates | `oscillatorPolar_fst_natAdd` (173) | PASS | Slow q = sqrt(2R) sin ψ, in frozen position block. |
| Chart coordinates | `oscillatorPolar_snd_natAdd` (178) | PASS | Slow p = sqrt(2R) cos ψ, in frozen momentum block. |
| Auxiliary coordinate extensionality | `phase_ext_blocks` (184) | PASS | Equality from equality of all coordinates; no mathematical existence step assumed. |
| Cell coordinates | `polarCellMap_fst_castAdd` (245) | PASS | Fast angle multiplication by 2π. |
| Cell coordinates | `polarCellMap_snd_castAdd` (249) | PASS | Fast actions unchanged. |
| Cell coordinates | `polarCellMap_fst_natAdd` (253) | PASS | Correct period-one sine coordinate. |
| Cell coordinates | `polarCellMap_snd_natAdd` (258) | PASS | Correct period-one cosine coordinate. |
| `bpP:p4:disc-measure` (a), auxiliary | `polarCellMap_injOn` (306) | PASS | Positive slow actions and half-open unit angle cell; no bounds on fast actions added. |
| Chart lattice, auxiliary | `oscillatorPolar_lattice` (330) | PASS | Equality modulo frozen fastShift yields fullShift; exact 2π integer lattice. |
| `stepP:p4:dm-jac`, auxiliary | `abs_det_fderiv_oscillatorPolar` (353) | PASS | Unit absolute determinant from the actual P1 symplectic determinant theorem. |
| `bpP:p4:disc-measure` (a) | `disc_measure_chart` (360) | PASS | Exact four-part signature: analytic symplectic chart, cell injection, unit Jacobian, lattice injection. |
| `bpP:p4:disc-measure` (a), area formula | `disc_measure_image` (383) | PASS | Exact measurable-image and volume statements for every measurable X in the positive-action unit cell. |
| `bpP:p4:disc-measure` (b), `stepP:p4:dm-cell`, F6 | `disc_measure` (635) | PASS | Exact numeric volume AND null complement of the specified positive-action polar image. |
| `bpP:p4:disc-measure` (c), `stepP:p4:dm-shell` | `disc_measure_shell` (670) | PASS | Exact oscillatorAction sublevel union, coefficient b*l/(r²/2), and original premises. |

The extra helper outputs are useful stronger infrastructure, not replacement
versions of source results with stronger premises. The main contracts keep all
binders, quantifiers, carriers and constants. They even allow zero block dimensions
and arbitrary measurable V, extending the positive-dimensional bounded source setting.
No finite-volume, nonempty-domain, or conclusion-shaped premise was added.

## Definition classification

There are six definitions, no new abbrev, structure, instance or chosen witness.

| Definition | Classification and whole-carrier behavior |
|---|---|
| `oscillatorPolar` (public, 38) | Intended explicit oscillator coordinate map. Real.sqrt is total, so negative slow actions collapse in those components; every analytic/Jacobian/injectivity use is guarded by strictly positive slow actions. No theorem exploits a negative-action fallback. At a=b it is literally the existing P7 polarMap. |
| `polarCellMap` (public, 46) | Intended composition of oscillatorPolar with P1 angleScale(2π), on the whole phase carrier. |
| `angCLM` (private, 53) | Actual angle-coordinate continuous linear projection. |
| `actCLM` (private, 58) | Actual action-coordinate continuous linear projection. |
| `discPre` (private, 409) | Literal product description: fast actions in V, slow actions in the supplied box, angles in [0,1)^(a+b). No fallback. |
| `capBox` (private, 598) | Literal product with selected coordinate in (0,l] and others in (0,c). Empty/nonpositive intervals have their usual set meaning; volume formulas remain ENNReal identities. For b=0 no selected j exists. |

## Adversarial proof and restoration review

The block derivative differentiates sqrt only at positive action and gives identity
on the fast block. Its slow block preserves the frozen symplectic sign; the proof
uses sin²+cos²=1 and sqrt(2R)*sqrt(2R)⁻¹=1. The P1 determinant theorem therefore gives
absolute determinant 1. P1 IsChart.comp applies oscillatorPolar after angleScale;
the composite has conformal factor 2π and determinant (2π)^(a+b), rather than
(2π)^(2*(a+b)). The actual Mathlib change-of-variables theorem is applied to X
with a Fréchet derivative and InjOn on X. Measurability of the image is proved,
not assumed, and no open-set requirement is silently imposed on the half-open cell.

F6 is paid at set level: exists_preimage (505) chooses an argument for each nonzero
oscillator, reconstructs actions (p²+q²)/2, and puts every angle in the half-open
cell. The image maps into the frozen product-of-discs cylinder cell (454).
cell_diff_subset (623) bounds the uncovered set by the finite union of slow centres;
volume_centres (583) proves it null through coordinate hyperplanes. The numeric
volume then follows from the image formula and the actual joinedActions product
volume. The converse inclusion and null coverage, rather than numeric volume alone,
justify equality. No rectangular replacement for the oscillator discs is made.

The shell proof also includes the null-centre set explicitly. Its capBox cover and
finite union estimate give b*l*c^(b-1); the b=0 case is handled separately before
cancellation with c=r²/2>0. ENNReal arithmetic retains validity for infinite volume V.
The unused upper-shell premise hlr is retained in the exact source signature; it
is harmless. hr is passed to disc_measure in the actual proof.

`git diff c0c8e4e HEAD -- KAM/Planetary/PGMeasure/Polar.lean` has 12 insertions and
7 deletions: comment/line wraps, plus the local abbreviation
`w = u.1_j*v.2_j - u.2_j*v.1_j` in oscillatorPolar_symplectic (237–242).
Substituting that abbreviation reproduces the prior linear_combination expression.
All declaration names and all theorem contracts are restored; no truncated suffix
remains. The new file has 742 lines versus 737 in c0c8e4e. This is faithful restoration
with a proof-local algebra refactor, not byte identity or exclusively whitespace edits.

## Hygiene and independent validation

All Lean/Lake validation is serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The targeted build used the required compile gate; its slot wait was allowed to finish.
No heartbeat, recursion-depth or synthesis-budget override was used.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4pol KAM.Planetary.PGMeasure.Polar
```

Exit 0. Exact terminal summary: `Build completed successfully (9120 jobs).`
The output replayed existing unused-variable warnings in Collar, Hamiltonian Algebra/Chart,
Kepler Energy/Mass and Poincare Chart. Polar warnings were unused binders at
370:8, 370:51, 371:28, 372:8, 372:10 and 671:41, plus an unused simp argument at
735:12. These are nonblocking; no options were added to suppress them.

### Exact signature and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4POLAudit.lean
```

Exit 0. The temporary module publicly imports only the audited module and copies
the authoritative types for `oscillatorPolar_eq_polarMap`, `disc_measure_chart`,
`disc_measure_image`, `disc_measure` and `disc_measure_shell`; their proof bodies
apply the matching export to the original explicit binders. All five elaborate.
An initial audit-harness run exited 1 because it used plain `import` before public
declarations; changing the scratch import to `public import` resolved the visibility
errors. No package change was needed. The successful run emitted exactly:

```text
'KAM.Planetary.oscillatorPolar_eq_polarMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasFDerivAt_oscillatorPolar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolar_fst_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolar_snd_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolar_fst_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolar_snd_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phase_ext_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarCellMap_fst_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarCellMap_snd_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarCellMap_fst_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarCellMap_snd_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarCellMap_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolar_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.abs_det_fderiv_oscillatorPolar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disc_measure_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disc_measure_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disc_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disc_measure_shell' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.Polar
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.PGMeasure.Polar
```

Polar is the sole new lemma module; there is no separate provider module.

### Imports and source hygiene

A recursive scan of the 74-module KAM import closure found zero provider imports
and zero frozen theorem imports. Every imported frozen anchor was checked against
`manifest/frozen-anchors.json`: exactly 52 definitions, all SEALED; no DRAFT_SORRY.
The new file has the required copyright, module, public imports, module docstring,
and exposed public section. All six definitions are in the exposed section.
It has 742 lines, no line over 100 characters, and no forbidden proof escape,
resource override or EuclideanSpace occurrence.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
`git diff inp...HEAD --check` and `git diff --check` exit 0 with no output.
No state-changing git command was run.

### Repository lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the brief's explicitly permitted stale generated root.
Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (628 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Thus module hygiene, frozen-anchor guard and all 144 ABI hashes pass independently.
KAM.lean was intentionally not regenerated. The reported lint exit is not described
as a literal exit-0 lint result.

The audit probe and its three logs were removed after their receipts were copied
into this report. Only this report was added by the auditor; the pre-existing
untracked handoff was preserved. Final report whitespace and protected-path checks
pass, and the audited Polar.lean hash remains unchanged.




## Uncertainties, suspected errata and deviations

No new suspected pinned-source or blueprint defect was found in this package's
assigned polar nodes. The older F6 omission is resolved by the current conjunction.
Revision 4's recorded extension-domain source imprecision is outside P4-POL;
this report neither reopens nor claims to discharge it. No source statement,
normalizer, action domain, frozen declaration or production module was altered.
The existing P7 Poincaré chart and its action domain remain unchanged; this package
extends only the oscillator formula to arbitrary block sizes and proves the broader
positive-slow-action chart directly. The previously known generated-root lint
exception is recorded in the validation receipts. No unproved consumer or headline
closure follows from this scoped infrastructure audit.
