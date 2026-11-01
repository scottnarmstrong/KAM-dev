# Certifier v2: confirmed fixes from the 31 October review

Date: 31 October 2026. Reviewed source revision:
`bbf13193ed4dd15dfe141e2f7cd9902b48b818ea`.
Status: findings F1, F3 and F4 are repaired and F2 is repaired by an additive engine, on branch `v2-fixes`
(table below, handoff [V2-FIXES](../handoffs/V2-FIXES.md)). The sections below keep the findings as reviewed.
Companion: [improvements](CERTIFIER-V2-IMPROVEMENTS.md).

| Fix | State | Commit | Where |
|---|---|---|---|
| F1 | applied | `41767c75` | `scripts/apost_sharp/check_modconstb_v2.py` |
| F2 | applied as an additive engine: `routeBRefined` and every existing module are unchanged | `d552c3c7`, `d4643f72` | `Frame/MajorantsLN.lean`, `V2/RouteBLN.lean`, `V2/RouteAllLN.lean`, `V2/Tests/RouteBLN.lean` |
| F3 | applied | `07b2a566` | `scripts/certifier/v2_adapter.py`, regression `scripts/certifier/check_v2_adapter.py` |
| F4 | applied | `07b2a566` | the two-frequency routines, regression `scripts/apost_sharp/check_smalldiv_shapes.py` |

The review found no soundness defect in the inspected v2 interfaces. It found
three concrete test/tooling/checker issues and one unsupported-input trap in
untrusted numerical tooling. The first three findings received independent
source review; alternative explanations for the constant mismatch were tested.
This was a focused review, not a complete proof audit or an application replay.

## What this means for SO-2 and SO-3

**These findings do not establish a fundamental mathematical problem with either
lunar subproject, and they do not call for restarting either project.** They
also do not independently certify either final lunar result.

- **SO-2:** the [overnight log](../OVERNIGHT.md), entry **31 October, 05:05**,
  reports `lunar_barriers_65_v2` and `lunar_spin_confinement_65_v2`
  kernel-checked on the working branch. It reports the spin band
  `|p(t) - 1| ≤ 2755/100000`, an initial window `(0.9934, 1.0066)`, standard
  axioms, and 1,100 heavy theorems checked. The **05:41** entry places the
  package in independent audit, with landing and the D40 freeze still to follow.
  These are campaign-reported results, not heavy computations repeated by this
  review. The generated main-branch percentage and package table lag this log.
- **SO-3:** the same log's **05:41** entry reports all emitted-book CHECK passes
  successful, including the seven base sub-checks, refined claims/core and graph
  check. Lean emission and kernel checking are listed next. This is not yet a
  reported kernel certificate of the final lock theorem. The **04:2x** entry
  records a wider internal graph window using the existing `_check` assembly
  helper, with the headline literals unchanged and the adjustment for owner
  review. This review did not re-audit that adjustment.
- The earlier advice to complete an application was a recommendation about
  public integration and reproducibility. It should not be read as claiming
  that SO-2 had no successful kernel run or that SO-3's mathematics had failed.

The two-frequency sharp-site specialization fits the lunar use case. General
three-frequency support is an expansion for other applications, not a missing
prerequisite for SO-2/SO-3. Likewise, fixed-frequency certificate output is an
additional API, not a replacement demanded by the lunar isoenergetic route.

## F1. Align the inputs in the route-B constant comparison

**Classification:** test regression; no theorem defect found. Priority: high
for reliable regression testing. Direct lunar implication: the comparison
script is unreliable until corrected; no passing lunar proof is invalidated.

Evidence at the reviewed revision:

- [thresholds_v2.py](../../../scripts/apost_sharp/thresholds_v2.py), lines
  451–452: `dk_cap` defaults to true and replaces `sK` by `sK - D["mu"] / 2`.
- [check_modconstb_v2.py](../../../scripts/apost_sharp/check_modconstb_v2.py),
  `mkp`, line 140: the input to the Lean-formula evaluator uses `D["sK"]`.
- Its `main` passes only the `selfcons` option. The two evaluations therefore
  use different caps despite the comparison's intended identical-input contract.

Reproduction from the repository root:

```sh
nice -n 10 python3 -B -I scripts/apost_sharp/check_modconstb_v2.py
```

Observed: exit 1, `R1 cross-check: MISMATCH`, across all 16 comparison cases.
The same run reports zero monotonicity violations in 6,423 sampled trials.
An independent probe setting `dk_cap=False` in the design evaluation gives
exact equality of all compared constants and conditions in all 16 cases;
the parent reviewer reproduced that result. This refutes the suspected
Lean-versus-design formula error in these cases.

**Repair:** make `mkp` respect the same cap convention as `stageB`, or explicitly
select the raw-cap convention in this low-level test. Prefer testing both
conventions. Do not remove the theorem's legitimate `σK - μ/2` cap to make a
test pass.

**Acceptance:** both conventions compare equal on matched inputs; fixed and
isoenergetic cases, stage zero, and self-consistency on/off remain covered;
the unmodified test command exits zero. Deliberately mismatching the cap must
still be detected.

## F2. Stop requiring the unused route-B torsion majorant

**Classification:** unnecessary rejection and computation; no unsound acceptance.
Priority: medium, with potentially useful application cost savings. Direct lunar
implication: conditional on choosing refined B; no new requirement for an A run.

[RouteBCore.lean](../../../KAM/CertificateSharp/V2/RouteBCore.lean), line 103,
states that `bT` is not used by route B. Its numerical core and
[refHypB_of](../../../KAM/CertificateSharp/V2/RouteBRefined.lean), lines 89–95,
consume the frame bounds `bL`, `bN`, `bNt`, without `bT`.

However, [refinedBTest](../../../KAM/CertificateSharp/V2/RouteBEngine.lean),
lines 38–40, calls `checkFrameMajorants`. That checker includes `checkFrameT`,
which constructs torsion models and checks their sup majorant; see
[Frame/Majorants.lean](../../../KAM/CertificateSharp/Frame/Majorants.lean),
lines 157–174.

The review's Lean probes establish:

1. The toy's tangent and normal bounds pass.
2. Its ordinary `bT` passes, whereas `bT=0` fails `checkFrameT`.
3. Changing only `bT` leaves `checkHamClaim` and `refinedBCore` unchanged.
4. The full refined-B checker rejects the modified witness.

The following is the central rejection probe; use a scratch module importing
`KAM.CertificateSharp.V2.Tests.RouteAll`, with the indicated namespaces open:

```lean
open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2
example : checkTorusCertificateV2 routeBRefined toyB
    {toyRefinedBWit with R := {toyRefinedBWit.R with bT := 0}} = false := by
  decide +kernel
```

**Repair:** introduce frame facts/checks for the three bounds B needs, and adapt
the B soundness bridge. Keep A's torsion-majorant check. Keep B's base check of
the inverse of the averaged extended torsion: that is a different, necessary
nondegeneracy obligation.

**Acceptance:** ordinary B certificates still pass; varying only unused `bT`
does not affect B acceptance; understated required frame bounds still fail;
the new engine soundness theorem has standard axioms only. Measure the saved
work on a bounded representative shard before claiming application speedups.

## F3. Make the optimizer adapter import the landed mirror

**Classification:** portability failure in untrusted tooling. Priority: high
for reuse. Direct lunar implication: affects this optimizer entry point, not
every lunar producer or the Lean checker.

[v2_adapter.py](../../../scripts/certifier/v2_adapter.py), line 15, defaults
to `/home/scott/KAM-dev-worktrees/sharp-plus/scripts/apost_sharp`. At the
reviewed checkout that historical worktree is absent, while the mirror exists
at `scripts/apost_sharp/thresholds_v2.py`. Calling `_load()` in a fresh Python
process raises `ModuleNotFoundError: No module named 'thresholds_v2'`.

**Repair:** derive the default from the adapter's own file location. Preserve
the explicit `KAM_V2_DIR` override and load the requested module unambiguously;
do not silently reuse an unrelated module already cached under the same name.
Restore any temporary `sys.path` modification even when import fails.

**Acceptance:** a fresh-process import works from a relocated checkout without
the override; a valid override works; an invalid override gives a useful error.
No dependency on a personal worktree remains in the default path.

## F4. Reject unsupported dimensions in the small-divisor design routine

**Classification:** unsupported-input validation in untrusted numerical tooling.
Priority: medium. Direct lunar implication: the tested trap is outside the
two-frequency lunar use case.

[smalldiv.py](../../../scripts/apost_sharp/smalldiv.py), `S_finite`, reads only
`omega[0]` and `omega[1]`. Its caller `c_freq` nevertheless accepts an `n`
argument, which changes a prefactor without changing that two-dimensional sum.

With `gamma=.01`, `tau=2`, `delta=.05`, `n=3`, `N=20`, these two inputs return
the identical finite value `0.002305976303529929`:

```python
(1, sqrt(2), 1 + sqrt(2))
(1, sqrt(2), 8)
```

The first vector has the exact three-way resonance `(1,1,-1)`. This probe does
not supply a Diophantine proof and is not a counterexample to checker
soundness: it demonstrates that a two-dimensional design function silently
ignores part of a purported three-dimensional input. The trusted enhanced
[siteOk](../../../KAM/CertificateSharp/V2/SmallDivQ.lean) explicitly rejects
unsupported dimensions/exponents.

**Repair:** reject `n != 2` and vectors whose length is not two until a genuine
higher-dimensional implementation exists. Apply corresponding shape guards to
other two-frequency design entry points and validate nonfinite scalar inputs.

**Acceptance:** the unsupported examples raise a clear error; valid
two-frequency benchmarks retain their values. A future higher-dimensional
routine must sum over all coordinates and justify its tail separately.

## Verification scope and integration

The review ran 14 new Lean examples, including the F2 checks and rejection of
a degenerate B schedule, zero majorant witnesses, a zero small-divisor
constant, an inexact clock, and unsupported enhanced-site dimension/exponent.
All passed at default elaboration limits, using existing compiled imports:
about 12 seconds wall, 2.04 GiB peak Lean RSS. Axiom reports for v2 soundness
and both combined-engine toy torus results listed only `propext`,
`Classical.choice`, `Quot.sound`. Axiom inspection is not a fresh replay of
the entire imported proof closure.

The A/B mirror scripts also ran. No heavy application certificate was replayed,
no source was repaired, and no Mathlib compiled artifacts were changed. The
original local receipts are archived at
`/home/scott/kam-audits/v2-20261031-bbf13193`; this path is provenance, not a
portable dependency. Source anchors and reproduction instructions above make
the findings reviewable without that local archive.

Coordinate any checker change with the active lunar integration. The overnight
log explicitly holds checker-side landings while SO-DATA3 lands; an unrelated
optimization should not invalidate a completed expensive build. The Python
fixes and a B-only checker repair need not force an A-based application to
regenerate its numerical data. Decide the actual dependency impact before
landing, rather than assuming it from a shared directory name.

No pinned mathematical-source erratum was established by this review.
