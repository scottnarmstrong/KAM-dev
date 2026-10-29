# S8 independent package audit 1

**Overall verdict: PASS WITH NOTES.** All S8 proof and signature checks pass;
the only note is the explicitly permitted stale generated root. Scope: only
`KAM/Planetary/SecularBox/SlowFlow.lean` (S8, `sb_slow`).

## Scope and evidence

Reviewed AGENTS.md, PLAN, DECISIONS, the package audit brief, S8 handoff,
P14 design S8 and node table (lines 247–252, 394), both P14 design audits,
P14Signatures.lean lines 495–504, blueprint-P/parts/p14b-secular-box.tex
lines 222–265, the track statement's P-SECULAR-BOX section, relevant frozen
anchors/definitions, and the ODE supplier interfaces.

HEAD: `3f56dc4871d12d1e00ec3b863b92ef3a07b7004d`.
SlowFlow SHA-256: `b31be7e9892153e08c1c741175971782cb1b7d1f8857d7c9f2aec7630059043a`.
`git diff inp...HEAD` was read in full: Field (244 lines), Rotation (188),
SlowFlow (204). Git reports multiple merge bases and selects
`0f347d6926a79e37d59d1e5fd044af61862721ae`. HEAD itself adds only SlowFlow;
Field/Rotation are inherited S7 context, outside this audit's verdict.
The initially observed inp ref was `b5e58ec5e766134ead4e306f3ed3c4dc0da81acd`;
this shared branch may advance independently.

S8 is infrastructure, with no provider export or frozen theorem seal body.
Provider/frozen-type and seal-body checks therefore do not apply to S8.
The downstream `secularBoxSafety` and `secularBoxAtCitedMasses` anchors are
DRAFT_SORRY; this audit does not certify their closure or seal readiness.

## Declaration and node ledger

All names are in `KAM.Planetary`; `sbSlow*` declarations are private.

| Node / declaration | Lean declaration / lines | Verdict | Reason |
|---|---|---|---|
| bpP:p14:sb-slow | sb_slow, 117–200 | PASS | Exact signed telescope and conclusion; global reduced solution, initial condition, slice membership and AMD conservation. |
| stepP:p14:sb-sl-1 | sb_slow, 125–141 | PASS | Open affine preimage; initial point membership; C-infinity composition reduced to C2 and ham_smooth_c1. |
| stepP:p14:sb-sl-2 | sb_slow, 143 | PASS | gen_maximal on actual open slow slice and actual Hamiltonian field. |
| stepP:p14:sb-sl-3 | sbSlow_conserved, 79–115; sb_slow, 145–152 | PASS | Two-sided coordinate derivatives, sb_field cancellation, reduced-field identity, interval-local constancy. |
| stepP:p14:sb-sl-4 | sb_slow, 154–189 | PASS | Closed AMD level set, finite-dimensional boundedness, strict inclusion in slice, confinement for the whole maximal interval. |
| stepP:p14:sb-sl-5 | sb_slow, 190–200 | PASS | Both continuation directions with t_star=0; Tp=top, Tm=bot; actual all-time derivative predicate. |
| membership helper | sbSlow_mem_iff, 33–40 | PASS | Literal unfolding of S and the frozen actions/axes. |
| affine slice definition | sbSlowG, 44 | PASS | Correct complete affine embedding, all I,y. |
| affine smoothness helper | sbSlow_g_contDiff, 46–49 | PASS | Globally smooth finite-coordinate affine map. |
| fast projection helper | sbSlow_fast, 51–52 | PASS | Exact fast-action projection. |
| slow momentum projection helper | sbSlow_slow_snd, 54–55 | PASS | Exact second slow block. |
| slow position projection helper | sbSlow_slow_fst, 57–58 | PASS | Exact first slow block. |
| slice membership helper | sbSlow_mem_g, 60–66 | PASS | All axis inequalities retained. |
| AMD definition | sbSlowA, 69 | PASS | Literal quadratic AMD sum on all Phase 2. |
| AMD bridge helper | sbSlow_amd_g, 71–73 | PASS | Equality to frozen secularAMD at the embedded point. |
| AMD continuity helper | sbSlow_continuous_A, 75–76 | PASS | Polynomial continuity. |

No assigned node is omitted. No unsigned public theorem is introduced; the only
public declaration is the signed sb_slow. No helper short name is reused and no
root declaration shadows another name.

## Fidelity and refutation checks

Whitespace-normalized declaration headers agree exactly with both the current
external signature and the design appendix: binder order, implicit w0,
hypotheses, constants, carriers, field, slice, and conservation equality.
No positivity premise on mu was added: the theorem validly retains all real mu.
No result is assumed through a hypothesis, instance or bundled conclusion.

The blueprint explicitly asks for continuity of y. The signed predicate supplies
HasDerivAt at every real time, which implies Continuous y; a fresh Lean probe
checks this implication. This meets the S9 quadrature consumer's curve-regularity
need without weakening the blueprint. The derivative uses the literal
reducedSecularH and the correct (xi,eta) coordinate order.

The compact set is in Phase 2 only; unbounded lifted fast angles are never
claimed compact. Its implemented coarse bounding radius 1+2*A0 replaces the
blueprint's sqrt(2*A0) estimate but still proves boundedness of the same level
set. Each nonnegative summand is at most A0, so the assumed strict AMD bound
and hI imply 50*Gamma_i < 50*(16373/2500000) < 87/100 < I_i.
All four axis constraints transfer from w0. Zero AMD is allowed: no division by
AMD or positive-AMD assumption occurs. Both negative and positive times are
handled, and the interval constancy proof uses openness/connectedness only on
the maximal interval, avoiding the obsolete whole-line constancy supplier
identified in P14 design audit 1 (F5, resolved by audit 2).

S7 fix-round focus: S8 does not call sb_pred, sb_omega or an omega-continuity
export. At SlowFlow:138–141 it obtains the reduced C2 Hamiltonian and C1 field
from sb_smooth_prop:317 and ham_smooth_c1:59. For conservation it uses the
existing sb_field and secular_field_components at SlowFlow:89–98. Thus no
unpaid S7 regularity fact is being assumed; append-only S7 regularity/omega
exports are unnecessary for this package. Omega continuity remains an S9/S7
consumer issue outside this verdict.

## Definition classification

Exactly two new definitions, both private and exposed through the file's
`@[expose] public noncomputable section`:

- sbSlowG I y = assemble I 0 y.2 y.1: intended affine embedding over the entire
  carrier; no branch, fallback or junk value.
- sbSlowA y = sum_i (y.2 i^2+y.1 i^2)/2: intended AMD polynomial everywhere;
  bridge to frozen secularAMD proved, no replacement of the frozen law.

The local I,h,W,y0,K are exact abbreviations/sets inside the proof, not new
public definitions. Membership in W is literal S membership of the slice;
K is the full quadratic level set.

## Validation

All runs below are independent auditor runs, serialized, with
LEAN_NUM_THREADS=1. No resource-budget override was used.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s8 KAM.Planetary.SecularBox.SlowFlow
   ```

   The gate internally runs nice -n 5 lake build. Exit 0; output:

   ```text
   [inp-gate] slot 2 acquired 21:04:01 for KAM.Planetary.SecularBox.SlowFlow
   Build completed successfully (9118 jobs).
   ```

2. Signature, application-body, continuity and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8Audit.lean
   ```

   Exit 0. The probe imports SlowFlow, copies the exact external signed sb_slow
   telescope under the fresh name s8AuditSigned, and proves it with
   `exact sb_slow saturn mu hs hw hA hI`. It then elaborates
   `example : type_of% @s8AuditSigned := @sb_slow`.
   Thus both explicit application and full type compatibility are checked
   without importing the draft signatures or introducing a probe sorry.
   A further example proves Continuous y from IsSolutionIn F W univ y using
   `(hy t (mem_univ t)).2.continuousAt` at each t. Exact axiom output:

   ```text
   'KAM.Planetary.sb_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.s8AuditSigned' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   sb_slow is every new public theorem in the audited files.

3. Kernel replay (one invocation; no other S8 lemma module exists):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.SlowFlow
   ```

   Exit 0; complete output:

   ```text
   replaying KAM.Planetary.SecularBox.SlowFlow
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the expected generated-root exception permitted by the
   audit brief. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (940 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated file was edited or regenerated. No other lint diagnostic occurred.

5. Static and repository checks:

   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty;
     only the multiple-merge-base diagnostic noted above.
   - `git diff --check inp...HEAD`: exit 0, same diagnostic, no whitespace errors.
   - Scope scan: 204 lines, maximum Unicode line width 99; no sorry, admit,
     axiom, unsafe, opaque, EuclideanSpace or set_option token.
   - Module header, copyright, public imports, module docstring, exposed
     definitions, public section and namespace all present.
   - Recursive local-import inspection visits 72 KAM modules and finds zero
     provider or frozen theorem imports. Therefore no DRAFT_SORRY anchor is
     imported, directly or transitively; manifest-state exceptions are unused.
   - Only the report is a persistent auditor edit. Existing untracked
     S8-handoff.md was left untouched; temporary scratch artifacts are removed
     after validation.

## Errata, deviations, limitations

No suspected new pinned-source or blueprint defect found in the S8 slice.
The coarse compactness radius above is a harmless proof-estimate variation,
with no statement deviation. No frozen statement was repaired or replaced.
No pinned PDF was newly audited: the slow-flow node is marked “Ours” in the
blueprint. Supplier theorem bodies beyond necessary dependency inspection are
not independently recertified by this narrowly scoped audit.
