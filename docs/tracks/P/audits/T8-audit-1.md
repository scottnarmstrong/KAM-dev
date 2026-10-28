# T8 independent package audit 1

**Overall verdict: PASS WITH NOTES for the T8 signed infrastructure interface.**
No frozen anchor/provider belongs to this package; no seal-readiness claim is made
for any track headline. Notes concern the signed real-part representation and
the expected generated-root lint exception.

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-t8`.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief,
`docs/tracks/P/audits/T8-handoff.md`, the P11C design and its independent design audit,
the standalone signed declarations, track P statements, Part 11b L120–164, and the
three corresponding graph records. Inspected the frozen `Phase`,
`hamiltonianVectorField`, and `oscillatorAction` definitions and the imported
quartic/character interfaces.

Implementation scope is exactly:

- `KAM/Planetary/PlanarTorsion/Homological.lean` (215 lines).
- `KAM/Planetary/PlanarTorsion/Homological/Extract.lean` (136 lines).

The user's exact report destination overrides the generic brief's MAIN-worktree
output instruction. No source, frozen file, manifest, generated root or README was edited.
Only this report is a lasting auditor edit; disposable probes/logs were under
`.lake/abi-scratch/`. No state-changing git operation was performed.

Audited HEAD: `488d568995b2f6264c5030e34abea1a820f37cba`.
Observed `inp`: `48e9326d764f4bb7e1704209fddf71863ec4eb9e`.
`git diff inp...HEAD` warns about multiple merge bases and selects
`b6dab3a6fc8453330a4abaa465a782e1aa713798`; the other base is
`a7c0963c945c6fee75ed7a7f0a3dc7e46cbd190f`.
The requested comparison contains 11 new Lean files / 1,554 inserted lines:
the two scoped T8 files (351 lines) and nine inherited T7 character files
(1,203 lines). The latter are dependencies, not independently re-audited packages.
The protected-path diff under the requested three-dot comparison is empty.
Choosing the other base yields unrelated prior integration changes, including the
AMD seal and generated imports; these are not T8 edits.

| Input | SHA-256 |
|---|---|
| `Homological.lean` | `75a6504cabbdc24d89dc4b55b6ee8f40e9e5c0b6d61eeab494a4dfc9b342c2d0` |
| `Homological/Extract.lean` | `7b9ca67190b2dfe80f226923c0835534d9ca007dcffb69cee7aa6b085b1f95a0` |
| P11C design | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |

## Declaration and node review

All names below are in `KAM.Planetary`. `H` denotes `Homological.lean`;
`E` denotes `Homological/Extract.lean`.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:homological`, SIGNED definition | `p11c_chi`, H:31 | PASS | Definition body and binders exactly match signature L429–432, including real-part projection. |
| `bpP:p11b:homological`, SIGNED theorem | `homological`, H:206 | PASS | Type exactly matches signature L434–438; analytic real quartic witness and forward bracket equation, no added premise. |
| `stepP:p11b:ho-def`, finite carrier | `chiModes`, H:37 | PASS | Precisely nonzero integer modes with l1 order at most four. |
| finite carrier specification | `mem_chiModes`, H:41 | PASS | Coordinate cutoff is proved equivalent to the intended l1 cutoff; no missing modes. |
| `stepP:p11b:ho-def`, finite sum | `chi_eq_sum`, H:51 | PASS | Equality holds for all I,z and arbitrary frequency maps, using character support; no NR4 assumption needed here. |
| `stepP:p11b:ho-def`, divisors | `chi_div_ne`, H:69 | PASS | Nonzero complex divisor follows exactly from source NR4 and I in O. |
| `stepP:p11b:ho-eq`, reconstruction | `chiModes_sum`, H:78 | PASS | Real part of the nonzero-character sum is exactly F minus its average; not itself a proof of reality of the divided complex sum. |
| quartic coefficient extraction | `charprod_extract`, H:94 | PASS | One-plane character products have constant complex quartic coefficients. Polynomial representation and homogeneity are proved from T7. |
| coefficient definition | `chiCoeff`, H:119 | PASS | Finite real coefficient formula; extraction coefficients are fixed before the action variable. |
| `stepP:p11b:ho-def`, analyticity | `chiCoeff_analytic`, H:125 | PASS | Analyticity follows from F coefficients, analytic frequency and nonvanishing divisors on O; no hidden normal-form premise. |
| `stepP:p11b:ho-def`, real quartic witness | `chi_family`, H:141 | PASS | Constructs an actual QuarticFamily equal to signed p11c_chi on O, by real coefficient extraction. See representation note below. |
| `stepP:p11b:ho-eq`, equation | `chi_bracket`, H:180 | PASS | Differentiates the finite sum, uses character_bracket, cancels only proved nonzero divisors and reconstructs F minus average. |
| coordinate adapter | `quarticVec`, E:30 | PASS | Exact complex coordinate vector (x0,y0,x1,y1). |
| coordinate scaling | `quarticVec_smul`, E:33 | PASS | Real phase scaling agrees with complex coordinate scaling. |
| monomial adapter | `quarticVec_prod`, E:37 | PASS | Coordinate exponent product is exactly the signed real monomial embedded in C. |
| homogeneous polynomial helper | `quartic_extract`, E:43 | PASS | A supplied polynomial representation and degree-four scaling imply a quartic monomial expansion. These are helper inputs proved at its call site, not assumed homological conclusions. |
| family constructor | `quartic_of_coeffs`, E:112 | PASS | Packages arbitrary analytic real monomial coefficients as an actual QuarticFamily, with equality for every I,z. |

The design node table L112–114 maps exactly three nodes to T8: homological,
ho-def and ho-eq. They are covered by the signed aggregate theorem and the
supporting proofs above. No additional graph node is assigned to Extract.
No unsigned export named after a graph node substitutes a weaker statement.

**Representation and consumer note.** Blueprint L136 and ho-def L140 write a
complex sum and prove it real by conjugating paired modes. The approved signed
interface instead defines its real part. This package follows that exact
interface and proves real analytic quartic coefficients directly. It does not
export, or prove locally, that the unprojected divided complex sum has zero
imaginary part; `chiModes_sum` is a reconstruction statement for the undivided
characters, so the handoff's phrase “reality/reconstruction” must not be read as
such an export. This is an interface-level alternate route, not an extra premise
or a claim that the literal complex identity has been formalized.

Consumers in signatures L456–467 (quartic flow), L477–487 (normal form),
L503–508 (full lift), and L594–604 (Birkhoff output) use precisely a real
QuarticFamily agreeing with signed p11c_chi and its real bracket equation.
They do not require an identity for the unprojected complex sum. The reversed
bracket identity used at blueprint L162 follows from existing frozen-form
algebra: `symplecticForm_hamiltonianVectorField` and
`symplecticForm_antisymm`. A scratch consumer probe checks that deduction without
new assumptions. Thus neither conjugate-pair algebra nor a second signed bracket
export is required by the narrowed interface's consumers. This audit does not
certify the later flow/normal-form/Birkhoff packages themselves.

`chi_bracket` is stronger than the signed aggregate's corresponding clause: it
does not need openness of O or analytic dependence of frequency. They are only
needed by the original package contract / quartic coefficient assertion.
The retained unused hO is a warning, not a change in signature.

## Definition classification and premise audit

There are four new definitions and no new structures, abbreviations, instances
or bundled assumptions:

| Definition | Whole-carrier classification |
|---|---|
| `p11c_chi` | Exact signed total real-part tsum. Character support reduces it to a finite sum even outside O. Complex division is total at zero; analytic/bracket claims use NR4 and I in O, so no claim relies on a zero-divisor fallback. |
| `chiModes` | Fixed finite nonzero l1 ball in Z². Coordinate box bounds lose no point, proved by mem_chiModes. |
| `chiCoeff` | Literal finite coefficient formula for arbitrary fixed complex extraction array c. It claims to represent chi only for the array constructed in chi_family, not for arbitrary c. |
| `quarticVec` | Literal complex embedding of all four real phase coordinates, on every phase point. |

The local QuarticFamily in `quartic_of_coeffs` assigns zero to unused exponents;
its eval reads only degree-four exponents, so these values are harmless and never
replace an intended physical value. Choice in chi_family selects constant
polynomial coefficients indexed by a,k,b; it does not select action-dependent
coefficients without analytic control. Every helper premise is typing, analytic,
nonresonance, polynomial representation, or homogeneity data discharged by its
caller. No homological equation, real-quartic output or future normal-form result
is assumed.

The recursive KAM import closure from the two modules has 74 modules and contains
no provider and no frozen theorem module (hence no DRAFT_SORRY theorem). Frozen
definitions are used literally. The signed source premises are exactly the
analytic frequency map and NR4 on O; there is no simply-connectedness,
Diophantine, frequency lower bound, or uniform small-divisor constant added.

## Verification

Commands ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no concurrent
Lean job was launched by this auditor. Builds used the prescribed shared gate.
Default heartbeats were retained.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t8 KAM.Planetary.PlanarTorsion.Homological`

   Exit 0. After waiting for a slot, output included:

   ```text
   [inp-gate] slot 2 acquired 20:20:47 for KAM.Planetary.PlanarTorsion.Homological
   Build completed successfully (9120 jobs).
   ```

   Both scoped modules are in this target's dependency closure. The scoped warning
   is unused `hO` at H:206:43. Replayed dependency warnings concern unused variables
   in Kepler/Poincare and deprecated names / an unused simp argument in T7.
   No elaboration error or resource override occurred.

2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T8Audit1.lean`

   Exit 0. The probe copied the signed definition under a fresh name and checked
   `example : @auditSignedChi = @p11c_chi := rfl`. It copied the signed theorem
   type verbatim and proved it using `exact homological hO F freq hf hnr`, then
   checked `example : type_of% @auditSignedHomological := @homological`.
   It also elaborated the consumer's reversed-bracket identity using only existing
   symplectic algebra. Frozen/provider seal probes are inapplicable: this package
   supplies infrastructure, not a provider or frozen theorem export.

   Exact axiom output (all 17 public declarations):

   ```text
   'KAM.Planetary.p11c_chi' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chiModes' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.mem_chiModes' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chi_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chi_div_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chiModes_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.charprod_extract' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chiCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chiCoeff_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chi_family' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.chi_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.homological' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.quarticVec' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.quarticVec_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.quarticVec_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.quartic_extract' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.quartic_of_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Homological KAM.Planetary.PlanarTorsion.Homological.Extract`

   Exit 0. Exact output:

   ```text
   replaying KAM.Planetary.PlanarTorsion.Homological
   replaying KAM.Planetary.PlanarTorsion.Homological.Extract
   ```

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`

   Exit 1, solely for the generated-root exception explicitly allowed by the audit
   brief. Exact complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (913 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden-token, module, line-length, frozen-anchor or ABI failure occurred.
   `KAM.lean` was not regenerated.

5. Static and final integrity checks:

   - Text comparison against the standalone signature file: `p11c_chi EXACT MATCH: True`;
     `homological EXACT MATCH: True` (complete definition versus complete theorem type).
   - Scoped forbidden-token scan for sorry/admit/axiom/unsafe/opaque/EuclideanSpace
     and all set_option commands: no matches (rg exit 1 means no matches).
   - Scoped maximum Unicode line lengths: H=98, E=95; file lengths H=215, E=136.
     Both have copyright, module, public imports, module documentation and an exposed
     public noncomputable section. No new root declaration or global instance.
   - Repository and Mathlib declaration scans: no reused public helper short name.
     The signed `KAM.Planetary.homological` shares only its short name with the
     pre-existing `KAM.NormalForm.homological`; these are distinct namespaces and
     this is not a newly chosen helper name.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0,
     empty diff; stderr only the multiple-merge-base warning recorded above.
   - `git diff --exit-code -- KAM/Frozen manifest KAM.lean README.md KAM/Planetary/PlanarTorsion/Homological.lean KAM/Planetary/PlanarTorsion/Homological/Extract.lean`:
     exit 0, no output.
   - Final SHA-256 recheck: both audited files, the design and the standalone signed
     interface are unchanged from the values above.
   - `git diff --check`: exit 0, no output. Report validation found 17 declaration
     rows, all three assigned graph nodes, no pending check text, no trailing
     whitespace or control characters, and the exact requested absolute path.
   - All five auditor-created probe/log/hash files were removed from
     `.lake/abi-scratch/` after their receipts were recorded here.
     Final status has only the new audit report and the pre-existing untracked
     `docs/tracks/P/audits/T8-handoff.md`; no tracked modification.

## Errata, deviations and limits

No suspected pinned-source mathematical defect was found in this T8 scope.
Primary PDFs were not independently re-audited; fidelity is to the supplied
signed interface, design, blueprint and literal frozen definitions. The
real-part representation and reversed-bracket deduction are documented above;
neither changes a signed declaration. Earlier P11C design-audit notes about graph
provenance/helper scheduling do not identify a defect in these two modules.
No frozen anchor is proved or sealed by this infrastructure package, and no
track I/N/P headline closure follows from this audit.
