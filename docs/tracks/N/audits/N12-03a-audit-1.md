# N12-03a independent package audit 1

Overall verdict: **FAIL (hygiene)**. The supplied-bounds Picard construction is mathematically sound and passes elaboration, axiom inspection, and kernel replay. Two new source lines violate the required 100-character limit. The branch also fails `git diff --check` because of a blank line at EOF. No Lean soundness defect was found. Source-node completion has the qualification below; this is not a seal or averaging-root closure.

## Scope and authority

Audited only `KAM/Nekhoroshev/Averaging/PicardFamilies.lean`, at HEAD `4a33d5aec5ae4a2b0924e711f76e7cb18db6c59a`, against `inp` = `ef8fc426c638557035e6101216aad4ef8b8a570e`, using `git diff inp...HEAD`. That diff contains exactly this new 332-line module. SHA-256: `e21fd91163ed40f5228ca45e0f6a685bdba9d2b39551faced8bc7046446aa202`.

Read AGENTS, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the package handoff/AUDIT FOCUS, N12 design row and proof plan, both design audits (located in `docs/tracks/N/design/`), the signatures, track N statement, Part 12 L37, and the two relevant graph packet contracts. The user's explicit absolute report destination overrides the brief's generic MAIN-worktree destination. No production source or git state was changed. The pre-existing untracked handoff was preserved. No subagents were used.

**Anchors:** none in this package. There is no provider export or frozen theorem to seal. Frozen-type equality and explicit-binder seal probes are therefore not applicable. All four imports are Mathlib modules; no provider or frozen theorem, including a DRAFT_SORRY anchor, is imported.

## Findings

**F1 — blocking hygiene, small mechanical correction.** `PicardFamilies.lean:136` has 102 Unicode characters; line 318 has 101. The explicit audit focus requires lint including 100-character lines, and the brief permits only the stale generated-root exception. Wrap both lines, retaining their proof expressions. No proof refactor or resource increase is indicated. The auditor leaves production files unchanged.

**N1 — whitespace.** `PicardFamilies.lean:332` is an extra blank line at EOF. Remove it. `git diff --check inp...HEAD` exits 2, as recorded below.

**N2 — signature and source-coverage boundary.** The handoff correctly reports that `/root/code/KAM-inp/.drafts/design/N12Signatures.lean` has no signatures for this subpackage. Its `ext_dep` starts at line 97; it is the assembled C1 local-dependence contract, not the theorem proved here. The current signatures SHA-256 is `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369`. Exact subpackage signature equality cannot be certified against a nonexistent signature. Against design row N12-03a at `N12-LEAN-DESIGN.md:275` (“trap and contract bounded continuous families”), this API passes with notes.

In particular, `PicardBounds` contains quantitative construction inputs, not an assumed fixed point, trajectory, convergence theorem, derivative, or variational solution. This is a legitimate conditional infrastructure helper. It must not be substituted for the full source-facing `ext_dep` theorem. Graph packet `N-p12.nodes.md:2810–2812` starts with “F C1 on open W” and concludes “choose compact B ... r=delta/2 and a>0 ...”. The module instead accepts `a,r,ρ,L,Λ` and their bounds, permits a=0 and empty initial balls, and does not select these data from an open W. Consequently **the complete source node `ext-dep#picard` is only partially implemented** here. To close that node, the later assembly must select positive parameters, derive boundedness/Lipschitz control from C1 data on a compact ball, and attach the trap to W. The design's proof plan at lines 316–318 already requires this. Do not mark the entire packet node proved using `picard_family` alone.

The source's finer `closedBall x (δ/2)` trapping assertion is not a conjunct of `picard_family`. The exposed integral estimate gives displacement ≤aL for every iterate step and for the fixed family using its integral equation, so this can be recovered after choosing aL<δ/2. It is not an assumed extra result. The matrix-family branch of complete contraction belongs to N12-03b; initial-data derivatives and derivative convergence belong to N12-03b/c. No completion of those packages is claimed.

## Declaration and node review

All names below are in `KAM.Nekhoroshev`. PASS rows concern mathematical content; the module-level F1 still blocks package acceptance.

| Node / role | Declaration (source line) | Verdict | Reason |
|---|---|---|---|
| Quantitative input | `PicardBounds` (42) | PASS | Six fields are precisely nonnegative time/bound, radius budget, field bound, Lipschitz bound, and aΛ<1. No hard conclusion bundled. |
| Family domain | `PicardBase` (51) | PASS | Closed time interval times closed initial ball. |
| Closed constraint | `PicardTrap` (54) | PASS | Pointwise closed-ball condition on bounded continuous families. |
| Carrier | `PicardSpace` (58) | PASS | Subtype of the preceding closed constraint, with inherited sup metric. |
| Closedness | `isClosed_picardTrap` (60) | PASS | Intersection of continuous-evaluation preimages of a closed ball. |
| Complete family carrier | `CompleteSpace (PicardSpace ...)` instance (67) | PASS | Completeness inherited from the closed subset when E is complete; no C1 subtype. |
| Integration extension | `picardIntegrand` (73) | PASS | Continuous time clamp; actual F evaluated on the family. |
| Picard formula | `picardFun` (78) | PASS | Actual oriented interval integral plus initial point. |
| Integrand regularity | `continuous_picardIntegrand` (82) | PASS | Only continuity of F on the trap and range containment used. |
| Operator regularity | `continuous_picardFun` (89) | PASS | Parametric integral continuity in time and initial point. |
| Integral bound | `norm_integral_picardIntegrand_le` (98) | PASS | Norm ≤ L|t|≤aL, including negative t. |
| Trap preservation | `picardFun_mem` (110) | PASS | Triangle inequality and r+aL≤ρ. |
| Self-map | `picardMap` (126) | PASS | Bounded continuous map with range in the trap. |
| Evaluation bridge | `picardMap_apply` (140) | PASS | Definitional equality with the actual integral operator. |
| `ext-dep#complete-contraction`, nonlinear branch | `contractingWith_picardMap` (146) | PASS | Factor Real.toNNReal a * Λ equals aΛ by a≥0; genuine sup metric contraction. Completeness and fixed family supplied by instance and `picard_family`. |
| Seed | `picardStart` (182) | PASS | Initial family y₀(t,x)=x; range inclusion follows from radius budget. |
| Total extension | `picardExt` (199) | PASS WITH NOTES | Explicit clamp in time and identity outside the initial ball; domain guards prevent fallback use in ODE claims. |
| On-domain evaluation | `picardExt_of_mem` (202) | PASS | Clamp is identity for t∈[-a,a]. |
| Integrand bridge | `picardIntegrand_eq` (207) | PASS | Equality holds for initial x in the ball, for every real integration time. |
| Family regularity | `continuousOn_picardExt` (212) | PASS | Joint continuity asserted only on the closed rectangle. |
| Iteration bridge | `picardExt_picardMap` (223) | PASS | Actual integral recursion on the advertised rectangle. |
| Seed displacement | `dist_picardStart_le` (230) | PASS | Initial operator displacement bounded by aL. |
| `ext-dep#picard`, quantitative family component | `picard_family` (251) | PASS WITH NOTES | Continuous trapped iterates and limit, exact recursion/equation, uniform geometric rate and interior time derivative. Does not select source parameters; see N2. |

## Definition classification and proof assessment

The nine new structure/definition/abbreviation declarations are all accounted for above. `PicardBounds` is a source-derived quantitative specification. `PicardBase`, `PicardTrap`, and `PicardSpace` are the intended domain, closed constraint, and carrier. `picardIntegrand`, `picardFun`, and `picardMap` are the actual clamped integral construction; `picardStart` is the actual initial family. `picardExt` is an explicit total extension, not an alternative flow. Its identity fallback outside the initial ball is documented and is never used to establish a guarded ODE assertion. Global u₀=x holds even outside the ball; no global recursion or regularity is claimed there.

The helper definitions are polymorphic over normed real spaces, with Bochner integrals using Mathlib's total definition. The theorem delivering a genuine solution and FTC, `picard_family`, explicitly assumes CompleteSpace E; it is not a claim about noncomplete-space integration. Degenerate parameters a=0 or r<0 give legitimate degenerate/empty-domain cases, not a way to obtain the source's positive-time existence. Source applications must make the positive choices described in N2.

The contraction proof explicitly verifies interval integrability from continuity before subtracting the two integrals. Pointwise Lipschitz control is lifted via the bounded-continuous-function sup distance, yielding aΛ. `picardStart` supplies nonemptiness of the complete trap. Mathlib's fixed-point theorem and a priori iterate bound yield the exact rate `a*L*(a*Λ)^m/(1-a*Λ)`; the denominator is strictly positive. The integral equation at t=0 gives y(0,x)=x although not a separate output conjunct. The FTC proof uses continuity on the trap, integrability on uIcc(0,t), and an interior neighborhood; no endpoint two-sided derivative is promised for the clamped extension.

Generic Banach-space carriers strengthen the finite-dimensional construction without changing max-norm Pi applications. No EuclideanSpace, norm conversion, extra regularity hypothesis on DF, hidden uniqueness premise, or wider-dependence constant was introduced. Omitting `KAM.ODE.Existence` is a valid direct Mathlib route; there is no use of that module to audit. Fixed-point uniqueness is available from Mathlib, but no new uniqueness theorem is exported here and no source-facing uniqueness claim is credited.

## Independent verification

Checks were run sequentially, with `LEAN_NUM_THREADS=1`. All Lean/Lake invocations used nice priority 5, including lint's inherited ABI subprocess. No clean, update, cache fetch, root regeneration, resource override, or protected edit was performed.

Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1203a KAM.Nekhoroshev.Averaging.PicardFamilies
[inp-gate] slot 1 acquired 07:54:06 for KAM.Nekhoroshev.Averaging.PicardFamilies
⚠ [2723/2723] Replayed KAM.Nekhoroshev.Averaging.PicardFamilies
Build completed successfully (2723 jobs).
exit 0
```

The gate runs `nice -n 5 lake build` internally. Warnings only: unused section variables at 60, 82, 202, 207, and a `haveI` style suggestion at 267. No elaboration error or heartbeat failure. The replayed build receipt is supplemented by fresh kernel replay below.

A temporary `.lake/abi-scratch/N1203aAudit.lean` imported this module and ran `#print axioms` for every one of its 13 public theorems:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1203aAudit.lean
'KAM.Nekhoroshev.isClosed_picardTrap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuous_picardIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuous_picardFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.norm_integral_picardIntegrand_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.picardFun_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.picardMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.contractingWith_picardMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.picardExt_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.picardIntegrand_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuousOn_picardExt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.picardExt_picardMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.dist_picardStart_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.picard_family' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

Kernel replay (one invocation; this package has no separate provider/lemma modules):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.PicardFamilies
replaying KAM.Nekhoroshev.Averaging.PicardFamilies
exit 0
```

Full source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
Lean lines over 100 characters:
/root/code/KAM-inp-n1203a/KAM/Nekhoroshev/Averaging/PicardFamilies.lean:136:102
/root/code/KAM-inp-n1203a/KAM/Nekhoroshev/Averaging/PicardFamilies.lean:318:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (459 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

Only the stale-root line is an allowed exception. F1 prevents a passing lint verdict. The frozen guard and ABI checks did finish successfully; the prover's handoff listed those successful subchecks but did not disclose the current overlong-line failures.

Static checks: 332 lines <1500; copyright, module header, public imports, module docstring, public noncomputable section and exposed definitions are present. Inspection/search found no sorry, admit, axiom, unsafe, opaque, resource option, forbidden ambient type, provider import, or frozen import in this file.

```text
git diff --exit-code inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output)
exit 0

git diff --check inp...HEAD
KAM/Nekhoroshev/Averaging/PicardFamilies.lean:332: new blank line at EOF.
exit 2
```

## Errata, deviations and handoff

No new suspected defect in a pinned external mathematical source was found; this focused audit does not independently re-audit the averaging papers or their inherited errata. No false blueprint assertion was exposed. N2 is an implementation/coverage boundary, with exact source text and locations above, rather than a source correction. The pre-existing signature omission and direct Mathlib route are disclosed deviations from the expected signature/dependency plan. No audit-induced mathematical deviation.

Required follow-up: wrap lines 136/318 and remove the EOF blank line, then rerun lint and diff checks; preserve explicit ownership of the source-parameter selection when assembling N12-03c. Independent proof/axiom/kernel checks pass for the present module, but they do not certify downstream applicability before that assembly exists. Only this report is delivered; the temporary axiom probe is removed before handoff.

## Orchestrator addendum (hygiene fix, 2026-10-28)
F1 and N1 are fixed in the commit after this audit: lines 136 and 318 are wrapped (no line now exceeds 100 characters)
and the extra blank line at EOF is removed. Verified by the orchestrator (no Codex delta round for a whitespace-only
fix): whitespace-stripped file contents are identical before and after; the module rebuilds through the compile gate;
`lake env leanchecker KAM.Nekhoroshev.Averaging.PicardFamilies` exits 0; `git diff --check` is clean. The audit's
mathematical verdict (sound, elaborates, axioms standard, kernel replay) stands: **PASS WITH NOTES** after this fix.
