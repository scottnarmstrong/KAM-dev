# T19 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the five-file T19 slice. All three signed theorem
exports pass statement fidelity, proof review, mass-ratio uniformity and determinant checks.
T19 is infrastructure, not a provider or a frozen-anchor seal; no frozen anchor is certified by
this report. The protected-path three-dot gate is **not empty**, as detailed below.

## Scope and authority

Audited HEAD: `d74db2d8a2ace1493c1f084a871138d80988b961`.
Comparison `inp`: `59edd171dd710945df5da652f50dd7269ea990bf` at inspection.
Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T19-handoff.md, track-P statement.md,
P11C-LEAN-DESIGN.md (especially rows 138–143, T19 row 225, warning 264), its design audit,
the signed file, and blueprint-P/parts/p11b-planar-torsion.tex:230–247.
The user's exact worktree report path overrides the generic brief's main-worktree destination.

Only these production files are audited:

| File relative to KAM/Planetary/PlanarTorsion/ | Lines | Maximum line length |
|---|---:|---:|
| Asymptotics.lean | 165 | 99 |
| Asymptotics/Homogeneity.lean | 135 | 99 |
| Asymptotics/Limits.lean | 68 | 99 |
| Asymptotics/Normalize.lean | 154 | 95 |
| Asymptotics/Relative.lean | 61 | 93 |

The complete scoped diff is 583 added source lines, with no preexisting declaration replaced.
Upstream definitions and T18 exports were read to check the inputs, not audited as a second package.
The existing frozen oscillatorAction is `(p²+q²)/2`; beta_def retains the factors 8 and 4.
No frozen theorem is a T19 target, so provider/frozen type equality and seal-body tests are
inapplicable. The analogous fresh signed-type application probes were run for all three exports.

## Findings and comparison provenance

**N1 — comparison history, not a T19 proof defect.** `git diff inp...HEAD` warns
`multiple merge bases, using 8d9661151e8698898da4f393fe7715ee38d239e7`.
The other merge base is `6595ad862b46d11c9f73fefe54ec24894fd0b850`.
The full comparison has 103 changed paths (14,016 insertions, 335 deletions), including
inherited packages and audits outside the explicit T19 scope. The scope inventory and every
line of the five-file T19 diff were checked; unrelated implementations are not certified.

The required literal command
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **nonempty**:
it includes the P-G seal body, its DRAFT_SORRY-to-SEALED manifest state, and 59 generated-root
insertions. Their last modifying commits in this history are `9fc6965a` (P-G seal) and
`6595ad86` (root regeneration), respectively; they are inherited integration content.
`git diff inp HEAD -- KAM/Frozen manifest README.md` is empty. The endpoint KAM.lean diff
contains missing later imports, consistent with the stale generated-root warning.
`git log inp..HEAD -- KAM/Frozen manifest KAM.lean README.md` reports only merge `fdf79752`.
Thus the blanket three-dot protected-path gate does not pass literally; these differences
must not be attributed to a T19 source edit or silently omitted. No protected file was changed
by this audit. This report approves only the expressly requested T19 slice.

**N2 — generated root.** Lint's stale KAM.lean exception is permitted by the brief. The auditor
did not regenerate it. Exact lint and replay results are recorded below.

## Signed exports and graph completeness

All names below are in `KAM.Planetary`. Signed theorem headers are identical to the supplied
signature file after whitespace normalization, including binder names/order, premises, carriers,
constants and conclusion conjunctions. The source was only line wrapped. Authority:
`/root/code/KAM-inp/.drafts/design/P11CSignatures.lean:635–644,752–759,809–814`, SHA-256
`6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`.

| Node / signed export | Lean declaration and locator | Verdict | Reason |
|---|---|---|---|
| bpP:p11b:asymptotics | asymptotics, Asymptotics.lean:34 | PASS | Four relative O(alpha²) limits, physical mass factors, exact -117/16 and degree -2 homogeneity. |
| Uniformity clause | asymptotics_uniform_ratio, Asymptotics.lean:70 | PASS | C and alpha0 precede every PlanarData; only ratio is fixed; common constants for all four errors. |
| General axes | asymptotics_general_axes, Asymptotics.lean:133 | PASS | Literal signed conclusion; a0³/a1⁷ and mass-ratio-only constants. No unsigned alpha0≤1 requirement. |
| stepP:p11b:as-in | imported as_in, AsymptoticEntries/Inputs.lean:124 | PASS (interface) | T18/T18b export includes Q limits, negative Delta, relative O(alpha^(1/2)), and A/B limits. No T19 redefinition. |
| stepP:p11b:as-pi | imported as_pi, AsymptoticEntries/Projector.lean:76 | PASS (interface) | Pointwise bounds, sign, projector identity and O(alpha^(5/4)), O(alpha^(5/2)) remain available. |
| stepP:p11b:as-c | imported as_c, AsymptoticEntries/Coeffs.lean:62 | PASS (interface) | Six coefficient estimates and pair-numerator clauses remain available. |
| stepP:p11b:as-ent | imported as_ent, AsymptoticEntries/Entries.lean:32 | PASS (interface) | Three corrections and three absolute leading estimates, with only p.Valid. T19 uses the final three. |
| stepP:p11b:as-det | p11cAs_det, Asymptotics/Limits.lean:27; asymptotics | PASS | Absolute O(alpha⁵) remainder implies the literal relative O(alpha²) result; homogeneity supplied separately and in signed export. |

These are all six graph rows mapped jointly to T18/T19 by the design. The first four steps
are established upstream and publicly imported; the determinant, homogeneity and uniformity
are established here. No unsigned T19 export bearing a graph-node short name substitutes a
weaker conclusion. The planned T20 consumer needs the nonzero negative leading determinant;
the exact relative estimate supplies it. No production Generic module exists in this checkout,
so this is verification of its designed input, not a claim that T20 has compiled or closed.

## Every additional public declaration

| Role / node clause | Declaration and locator within Asymptotics/ | Verdict | Reason |
|---|---|---|---|
| Projector scaling | p11cAs_projector_of_Q, Homogeneity.lean:24 | PASS | Positive proportional Q matrices give equal explicit projectors; valid even for the totalized degenerate formula. |
| Axis scaling | p11cAs_Q_smul, Homogeneity.lean:52 | PASS | Q scales by (s sqrt(s)) inverse on positive ordered axes. |
| Axis scaling | p11cAs_coeffs_smul, Homogeneity.lean:85 | PASS | All six coefficients scale by inverse s²; action powers handled explicitly. |
| Algebra helper | p11cAs_beta_def_smul, Homogeneity.lean:122 | PASS | Linearity in all six coefficients, arbitrary real scalar and matrix; stronger than physical specialization. |
| Homogeneity | p11cAs_beta_smul, Homogeneity.lean:127 | PASS | Exact degree -2, source positivity/axis premises only. |
| Normalized data | p11cAs_unit, Normalize.lean:27 | PASS | Literal structure value (1,1,[r,1]). |
| Normalized validity | p11cAs_unit_valid, Normalize.lean:29 | PASS | Positive ratio proves physical validity. |
| Normalized kappa | p11cAs_unit_kappa, Normalize.lean:33 | PASS | Kappa is exactly 1 for every real r. |
| Mass scaling | p11cAs_Q_ratio, Normalize.lean:36 | PASS | Positive scalar G*m1/sqrt(kappa) cancels in the projector. |
| Action powers | p11cAs_act_rpow, Normalize.lean:70 | PASS | Positive alpha and valid masses, real exponents adding to 2; direct identity. |
| Mass powers | p11cAs_mass_rpow, Normalize.lean:83 | PASS | Positive bases, e+f=2; ordinary rpow multiplication. |
| Mass scaling | p11cAs_coeffs_ratio, Normalize.lean:87 | PASS | Exact 1/m0 scaling for all six coefficients at positive alpha. |
| Mass scaling | p11cAs_beta_ratio, Normalize.lean:143 | PASS | Exact 1/m0 matrix scaling; no asymptotic or compactness assumption. |
| Relative error definition | p11c_relativeError, Relative.lean:26 | PASS | Exact signed definition on positive-side neighborhood of zero. |
| Error conversion | p11cAs_rel, Relative.lean:30 | PASS | Generic conditional helper with explicit nonzero leading coefficient; proved algebraically, not used as an assumed result. |
| Explicit constants | p11cAs_rel_explicit, Relative.lean:48 | PASS | Positive C, delta≤1 and all 0<alpha<delta from IsBigO; no new physical premise. |

Together with p11cAs_det and the three signed exports, this covers all 20 new public declarations:
18 theorems and two definitions. Helper names all use the package prefix p11cAs_; a source scan
found each of the 20 names declared exactly once throughout KAM. No harmful root shadow exists.

## Definitions and proof review

The only new definitions are p11c_relativeError and p11cAs_unit; there are no new structures,
abbreviations, bundled assumptions, instances, hidden input fields, or fallback definitions.
The relative-error predicate is exactly the signed ratio-minus-one IsBigO predicate on its
whole function carrier. Lean division is total at zeros; its use in these asymptotic theorems
is legitimate because the leading coefficients are nonzero and alpha is eventually positive.
p11cAs_rel proves that fact before division. The normalized structure is the intended object
for every real r, with validity proved only when r>0. No junk value is used to prove a claim.

For the determinant, write the leading entries as A0=k0*alpha, B0=k1*alpha^(3/2),
D0=k2*alpha². Limits.lean:32–49 bounds
`(A-A0)D + A0(D-D0) - (B-B0)(B+B0)` by O(alpha⁵). Symmetry identifies B with the 10 entry.
The coefficient is
`k0*k2-k1² = -9/(4*m0²)-81/(16*m0²) = -117/(16*m0²)`.
The rpow product is proved for alpha>0 and the final identity is checked by field algebra.
No determinant sign or asymptotic conclusion is assumed.

For uniformity, Normalize.lean:143 proves the exact identity
`beta(p,[alpha,1]) = m0^(-1) • beta(unit(ratio),[alpha,1])`.
Only normalized data are passed to asymptotics before choosing the constants.
Asymptotics.lean:78–86 extracts four positive constants, sums them, and takes the minimum
of their radii. The physical-data universal binder is introduced afterwards. Each normalized
relative error equals the physical relative error exactly: entries scale by m0^(-1), and
the determinant by m0^(-2). G and the absolute planet-mass scale cancel. This proves genuine
uniformity over arbitrarily varying positive physical scales at the fixed ratio.

For general axes, a=a1 • [a0/a1,1], beta scales by a1^(-2), and its 2x2 determinant by
a1^(-4). Multiplication by (a0/a1)^3 gives exactly a0³/a1⁷. All canceled factors are nonzero
by the source positivity premises. The fixed-p BigO helper legitimately has p-dependent constants;
it is the normalized use that removes that dependence from the signed uniform theorem.

## Independent checks

All auditor Lean/Lake invocations were sequential, used LEAN_NUM_THREADS=1 and nice -n 5.
The build used the prescribed gate; no clean, cache fetch, update, root regeneration, or git
mutation was performed. Probe files lived only under this worktree's .lake/abi-scratch/.

Build command (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t19 KAM.Planetary.PlanarTorsion.Asymptotics
```

Relevant output:

```text
[inp-gate] slot 3 acquired 23:55:59 for KAM.Planetary.PlanarTorsion.Asymptotics
Build completed successfully (9265 jobs).
```

The build replayed existing upstream unused-variable, unused-simp and deprecation warnings;
there were no errors or proof holes. No heartbeat budget override was used.

Probe command (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T19Audit.lean
```

The scratch probe copied each signed theorem header verbatim from the signature file and
proved it with `by exact asymptotics p hp`, `by exact asymptotics_uniform_ratio ratio hratio`,
and `by exact asymptotics_general_axes ratio hratio`, respectively. It also copied the signed
relative-error definition and proved equality with the production definition by rfl.
It ran #print axioms on every new declaration, including both definitions. Exact output:

```text
'KAM.Planetary.asymptotics' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.asymptotics_uniform_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.asymptotics_general_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_projector_of_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_Q_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_coeffs_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_beta_def_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_beta_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_unit_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_unit_kappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_Q_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_act_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_mass_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_coeffs_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_beta_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_relativeError' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cAs_rel_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Asymptotics KAM.Planetary.PlanarTorsion.Asymptotics.Homogeneity KAM.Planetary.PlanarTorsion.Asymptotics.Normalize KAM.Planetary.PlanarTorsion.Asymptotics.Relative KAM.Planetary.PlanarTorsion.Asymptotics.Limits
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.PlanarTorsion.Asymptotics.Homogeneity
replaying KAM.Planetary.PlanarTorsion.Asymptotics.Relative
replaying KAM.Planetary.PlanarTorsion.Asymptotics.Limits
replaying KAM.Planetary.PlanarTorsion.Asymptotics.Normalize
replaying KAM.Planetary.PlanarTorsion.Asymptotics
```

Lint command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1121 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All substantive lint gates pass; the exit code is not represented as zero.

The import traversal found 58 frozen modules, all definition modules with manifest state
SEALED, and no frozen theorem module or provider module. Thus no DRAFT_SORRY anchor or
provider quarantine breach occurs in T19's transitive project dependencies.
Code scans found no sorry/admit/axiom/unsafe/opaque, EuclideanSpace, resource overrides, or
_root_ declarations in the five audited files. Every file has the required copyright, module,
public imports, module docstring and public section; the definitions are exposed through the
section attribute. File and line sizes are listed above. The scoped `git diff --check` exits 0.

## Errata, deviations and remaining limits

No new suspected source defect, blueprint contradiction or mathematical deviation was found
in the T19 slice. This audit checks the local pinned blueprint and its physical normalization;
it does not claim a fresh review of every printed CP11/Arnold formula.
The design audit's historical provenance and DAG notes do not alter these four signed surfaces.
The T18/T18b interface supplies the input clauses without assuming the determinant or uniformity.
This is not an independent re-audit of T18's implementation or a campaign headline closure.

The only lasting auditor edit is this report at the user's exact absolute worktree path.
The preexisting untracked T19-handoff.md is retained unchanged. Scratch probes and audit logs
are removed after their results are copied here. No new approval request or source repair is needed.
