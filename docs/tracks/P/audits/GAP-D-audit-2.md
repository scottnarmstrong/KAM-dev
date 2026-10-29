# GAP-D independent audit 2 — delta audit

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gapd`.
Audited HEAD: `294f2ea91804f097dbfaaf0ecb491105d5264e72`.
Comparison branch `inp` at inspection: `6a70a8ed0010c7b98e583b3a3d8929a1c5337ab8`.
Round-1 baseline: `8100ff3a`; fix: `294f2ea9`.

**Overall: PASS WITH NOTES. Round-1 finding F1 is resolved.**
`birkhoff_form_full` exports clause (a), T16's complete normal-form package,
and the explicit lift-map formula for the same existential witnesses. It has
exactly T16's input hypotheses. The independent Lean projection back to
`PlanarBirkhoffResult` elaborates. No new mathematical or statement-completeness
failure was found in this delta. The only hygiene exception is the expressly
permitted stale generated `KAM.lean`.

There is no GAP-D provider or frozen theorem anchor to seal. Provider/frozen
signature and seal-body probes are therefore inapplicable. PASS refers to the
requested GAP-D attachment and composed-map specialization, with T16's signed
interface and the existing T11 flow results as dependencies. It does not claim a
new proof of the general arbitrary-family lift proposition or an overall campaign
theorem.

## Scope and comparison

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local handoff and its
AUDIT FOCUS, round 1, and `.drafts/handoff-GAP-D.md` (Round 2 fix). Compared the
literal node conclusions at `docs/graph/P/DEPGRAPH.md:30761` and `:31004` with
`blueprint-P/parts/p11b-planar-torsion.tex:166`–176 and 205–222. Read the track-P
statement and the relevant existing Birkhoff, chart, lift, physical perturbation,
phase/assembly and frozen `HasSecularBirkhoffForm` definitions. The exact report
destination in the user's prompt overrides the generic brief's MAIN-worktree
report destination.

Only `KAM/Planetary/PlanarTorsion/BirkhoffClauses.lean` is audited as proof code.
Round-1 deductions are retained; this audit focuses on F1 and the two new exports.
The signed T16 results and BYPASSED bt-rot/bt-rot#lift are not reopened.

`git diff inp...HEAD` has three new files: the 295-line Lean module, the
237-line round-1 report and the 43-line handoff (575 insertions, no deletions).
`git diff 8100ff3a..HEAD` has only the Lean file, **110 insertions, zero deletions**.
More precisely, two lines are inserted in its module documentation and the two
new theorems are appended before the namespace/section endings. Thus the change
is additive and preserves every previous declaration byte-for-byte; it is not
literally an EOF-only text append. No proof or signature from round 1 was edited.

## Node and declaration verdicts

All names below are in `KAM.Planetary`. GAP-D adds no signed declaration; searches
of `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` find neither new name
nor the older GAP-D exports. The unchanged T16 signature remains authoritative.

| Node / role | Declaration and current line | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:birkhoff-form`, requested joint attachment | `birkhoff_form_full`, 225 | PASS | One set of witnesses retains all `PlanarBirkhoffResult` conclusions and attaches clause (a) to each actual transformed physical perturbation. F1 resolved. |
| `bpP:p11b:lift-map`, composed T16 map | `birkhoff_form_full`, 238–281 | PASS WITH NOTES | The same T and chi satisfy the explicit coordinate identity, chart/injection, action preservation and angle covariance. Existing T11 supplies the flow interpretation; the new theorem specializes to T16's chi. |
| Universal attachment helper | `p11cG_attach`, 189 | PASS | Arbitrary T with source geometric data; no Hamiltonian identity, periodicity or normal-form conclusion is assumed. |
| Clause (a) alone, unchanged | `birkhoff_form_hamiltonian`, 77 | PASS | Round-1 deduction unchanged; the new joint export supplies its previously missing linkage. |
| Explicit identity, unchanged | `lift_map_explicit`, 126 | PASS | Integral and frame-derivative formula retained exactly and used for the joint witnesses. |
| Map properties alone, unchanged | `lift_map_properties`, 149 | PASS | Valid separate specialization, now supplemented by the joint export. |
| Split helper, unchanged | `p11cG_split`, 42 | PASS | Physical product-chart identities and preservation of fast actions. |
| Periodicity helper, unchanged | `p11cG_periodic`, 62 | PASS | Product-chart lattice invariance under the exact radian fast shift. |

## F1 verification: the public conclusion retains the witnesses

The binder telescope at lines 225–230 agrees with `birkhoff_form` at
`Birkhoff.lean:42`–48: p, positivity data hp, a0, rho, and hgoodK; r and C are
positive and chosen before arbitrary admissible Oa. No simple-connectedness,
normal form, analyticity, periodicity or Hamiltonian splitting premise was added.
Constants therefore retain T16's dependence; the result is independent of either
coupling parameter.

Lines 231–246 keep O', its open/compact containment data, F, chi, their quartic
and homological identities, the same T, its composition equation, negative
frequencies, analytic symplectic chart, injection, fast-action preservation,
translation covariance, and product-chart/collision domain clauses.

For each fhat in the two-element set, lines 247–261 retain the complete T16
conclusion: analyticity of fhat composed with T, P0 identified with the original
secular value at zero, the sixth-order estimate on K with the same C and r,
and the frozen Birkhoff predicate on interior K for every permitted mu0 and r0.
The same fhat and T then occur in periodicity and the physical Hamiltonian
identities at lines 262–269. No second existential T or chi appears. The explicit
formula at lines 270–281 is outside the fhat quantifier but inside that same
existential T, so both physical perturbations share it.

The proof at lines 282–290 destructs T16 once. Its final constructor exports
`hf fhat hmem` intact together with `hat fhat hmem`, rather than projecting only
the analyticity component as in round 1. The last identity follows by rewriting
that very hT and applying the existing universal `lift_map_explicit`.

An independent scratch example with T16's exact theorem type applied only
`birkhoff_form_full`, destructed its witnesses, and reconstructed
`PlanarBirkhoffResult` with `(hf fhat hmem).1`. This elaborated at default budgets,
confirming that no original result clause was lost in the expanded conjunction.

The formula has g_l as the integral of the action derivative at fixed slow
argument along the flow. Its correction is the sum of Y.2_i times
rho_ki times partial_l rho_kj times Y.1_j, exactly
`y-tilde^T (rho^T partial_l rho) x-tilde`. Assembly uses `(I,phi,p,q) =
(Lambda,lambda,y,x)`. The arbitrary-point formula is an identity of the existing
total definitions; actual flow/chart properties are asserted on T16's tube.

## Helper hypotheses and definitions

`p11cG_attach` assumes p.Valid, O', r, arbitrary T, fast-action preservation,
covariance under every real angle translation, and image membership in the
product-chart domain together with NoCollision. These are T16 source-data
conclusions, not the periodicity or Hamiltonian conclusions it proves.
NoCollision is unused by this deduction but is legitimate stronger geometric
source data, already supplied by T16; it adds no premise to the main result.
The proof applies covariance to `2*pi*k`, uses product-chart lattice invariance,
and applies the two physical Hamiltonian splitting identities. It does not
assume T is a Birkhoff map, analytic, or already normalized.

There are **no new def, abbrev or structure declarations**, in either the delta
or the whole GAP-D module. No new fallback or choice-based object is introduced.
Existing `p11c_hatFix` and `p11c_hatMov` are the physical perturbations composed
with `poincareProd`; the tube uses the slow length sqrt(sum of squares).
`Phase d` is the pair of `Fin d -> Real` spaces, and `assemble` has the frozen
canonical ordering. No carrier or norm substitution is made.

The chart representation note from round 1 remains: `IsChart 1` means analytic
plus symplectic, and `InjOn` supplies global injection on the open tube. These
imply the mathematical analytic diffeomorphism onto the image through invertible
symplectic derivative and the inverse function theorem; the exports do not
construct a separately named analytic inverse. The existing flow fallback outside
its existence region is not used to prove chart properties there.

## Independent validation

All Lean/Lake/checker commands ran sequentially, with `LEAN_NUM_THREADS=1` and
`nice -n 5`. No heartbeat, recursion-depth or synthesis override was used.

Targeted compile gate, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gapd KAM.Planetary.PlanarTorsion.BirkhoffClauses
[inp-gate] slot 1 acquired 00:23:55 for KAM.Planetary.PlanarTorsion.BirkhoffClauses
Build completed successfully (9326 jobs).
```

Upstream unused-variable/tactic/deprecation warnings were replayed; no warning
was attributed to BirkhoffClauses.

Elaborated axiom and T16-projection probe, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPD2Probe.lean
'KAM.Planetary.p11cG_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cG_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkhoff_form_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lift_map_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lift_map_properties' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cG_attach' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkhoff_form_full' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, single invocation, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.BirkhoffClauses
replaying KAM.Planetary.PlanarTorsion.BirkhoffClauses
```

Lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1148 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Exit **1**, solely the stale generated root exception explicitly allowed by the
brief. The generated root was not edited or regenerated.

Additional current checks:

- File length 295 physical lines; maximum Unicode line length **99**, satisfying
  both the 1500-line file cap and the 100-character line limit.
- Module copyright, `module`, public imports, module docstring and public section
  present. No forbidden token, EuclideanSpace or resource override in the module.
- All seven public short names occur only in this file when searching KAM and
  Mathlib sources. No reused helper name or harmful root shadow was found.
- Direct imports remain Mathlib and Birkhoff. Recursive source import inspection
  covers 280 KAM modules and finds no provider or frozen theorem module import;
  frozen imports are definitions. No DRAFT_SORRY theorem is imported.
- `git diff --check inp...HEAD`: exit 0, empty output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
- `git diff --numstat 8100ff3a..HEAD`: exactly `110 0` for BirkhoffClauses.

## Errata, deviations and remaining scope

No new suspected pinned-source or blueprint mathematical defect was found.
F1's interface deviation is repaired; there is no remaining delta failure.
T16's inherited signed representation choices, the chart/injection formulation,
and the generic lift-node versus T16-specialization distinction remain the notes
specified above. No claim is made that this delta exports separately named
blueprint construction radii or independently reproves upstream frame/flow facts.

Only this report was written in the repository. The scratch probe was removed
after validation. No protected source, manifest, generated file or git state was
changed by the auditor.
