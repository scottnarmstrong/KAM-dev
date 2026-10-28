# P5-REM independent package audit 1

Verdict: **PASS WITH NOTES** for P5-REM's two exported contracts, `schwarz_order_five` and `uniform_remainder`, with the validation receipts below. No frozen anchor is proved by this package; provider/frozen-type and seal-body tests are not applicable. This is infrastructure approval, not P-G sealing or track closure.

## Scope and authority

Audited HEAD `6ea225e3dd432b780011f07228316a24ae4b4c46`. Read AGENTS.md, PLAN, DECISIONS, the package-audit brief, P5-REM handoff and its AUDIT FOCUS, track-P statement, P5 blueprint, P45 design including Revision 4, all four prior design audits, shared signatures, the P-G frozen telescope and its relevant source definitions. The explicit user destination overrides the brief's generic main-worktree destination.

The required `git diff inp...HEAD` includes 24 files / 3338 additions inherited from P5-EX/P5-JET and emits `warning: inp...HEAD: multiple merge bases, using 05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`. Per the handoff's narrower focus, `git diff inp-p5jet...HEAD` isolates exactly one file, `KAM/Planetary/PGAssembly/Remainder.lean`, 356 additions. Only that file's implementation is audited; imported definitions/interfaces are inspected for applicability, without claiming independent audits of the inherited packages.

Input SHA256:

- Remainder.lean: `aaca9a563d31089117bc13965844d5912c792fd9d61447109628f13c26ec8fa6`.
- P45-LEAN-DESIGN.md: `fe084af07ac93f216e4f98e0ff5284319c5a544ee6df073af2069e9639d47559`.
- Shared `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`: `6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402`. The shared signature file and prior design audits are absent at the handoff's nominal local paths; their actual main-worktree paths were read. No signature stubs were imported into the validation probe.

## Declaration-by-declaration review

All names below are in `KAM.Planetary`; line numbers refer to Remainder.lean. Implementation helpers have their own names and do not replace a source theorem with a conditional variant.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| ur-schwarz / factorization helper | `schwarz_quotient_bound` (37) | PASS | Analytic order >=5 gives a removable quotient at zero; maximum principle applies to the smaller closed disc, wholly inside the holomorphic domain. No extra vanishing assumption. |
| stepP:p5:ur-schwarz | `schwarz_order_five` (102) | PASS | Literal signature equality with shared S:820 and design:1517. Smaller-circle bounds converge as R' increases to R. `hM` is redundant but matches the design. |
| Tube inclusion helper | `actionNbhd_mono_quarter` (126) | PASS | Positive delta gives quarter-tube inclusion in half-tube using the actual witness definition of actionNbhd. |
| Radius helper | `pgOscRadius_lt_one` (133) | PASS | Radius <= delta/4, with delta<1. No new premise. |
| ur-bound / average | `complexAverage_norm_le` (139) | PASS | Normalized torus-box integral cancels volume (2*pi)^a exactly; uses extension bound on every integrand point. |
| ur-bound / holomorphy | `complexAverage_differentiableOn` (165) | PASS | Restricts the imported jointly holomorphic average to fixed I on the full oscillator ball. |
| ur-schwarz / holomorphy | `remainder_slice_differentiableOn` (173) | PASS | Same restriction for the actual average-minus-jet-polynomial remainder. |
| ur-bound / Cauchy | `jet_norm_le` (182) | PASS | All derivative orders bounded by (n/(epsilon/2))^n MP on a closed ball strictly inside the epsilon ball. Operator norm and Pi/product max norms retained. |
| Coordinate helper | `norm_single_le_one` (194) | PASS | Sup-norm coordinate unit bound; valid for every existing Fin b index. |
| Coordinate helper | `norm_yvec_le_one` (200) | PASS | Product max-norm bound for (0,e_j), the exact jet directions. |
| Multilinear helper | `mlin_apply_le` (205) | PASS | Operator norm applied to vectors each of norm <=1, including order zero via empty product. |
| Oscillator helper | `norm_cOsc_le` (211) | PASS | Absolute bound for (x_j^2+y_j^2)/2 from product/Pi norm <=1. |
| ur-bound / polynomial | `cPoly_norm_le` (225) | PASS | Bounds constant, b quadratic terms and b^2 quartic terms; discards the favorable factor 1/2 safely. Inputs are coefficient bounds, not an assumed remainder estimate. |
| Polynomial identity | `pgRemainder_eq_cPoly` (259) | PASS | Unfolds actual appended fast/slow blocks; holds on the whole carrier, without analytic-domain guards. |
| stepP:p5:ur-bound | `remainder_bound` (272) | PASS | Coarse M1 on the half-radius open ball, uniform over mu in [0,mu0] and I in the half-tube. Handles diagonal beta factor 1/3 and mixed fourth derivatives. |
| Constant helper | `remainder_const_pos` (304) | PASS | MP>0 and nonnegative remaining terms ensure strictly positive M1. |
| bpP:p5:uniform-remainder; ur-bound, ur-schwarz | `uniform_remainder` (311) | PASS WITH NOTES | Literal shared S:649/design:1346 signature, with data-only positive constants, closed oscillator ball and quarter action tube. Internal radius shrink is described below. |

## Definitions, assumptions, and mathematical checks

There are **no new top-level def, abbrev, structure, instance, or auxiliary axiom declarations** in the audited file. Local `set` expressions are ordinary abbreviations for explicit constants/functions. The locally updated quotient equals g(z)/z^5 away from zero and the analytic factor at zero; local analytic factorization proves that assigned center value is the removable value. It is not a junk fallback used to fake holomorphy. Local R and M1 are finite real expressions built from positive fixed data.

Inspected inherited definitions: `PGData` (Setting.lean:44) bundles exactly the P-G source telescope, with no remainder estimate field; `PGExtension` is a previously proved produced witness, not a new premise. `pgOscRadius=min(r0/2,delta/4)>0`; `complexAverage` is the literal normalized integral of that extension; `jetP0`, `jetOmega`, `jetBeta`, `jetPolynomial`, `pgRemainder`, `cOsc`, `cPoly` are evaluations/derivatives/polynomials of that integral. Their use stays in the guaranteed mu interval and complex tubes. The average uses oscillator order (q,p), but the polynomial is symmetric in the two squares, and the second-factor coordinate directions agree with the jet definitions. No equality with unconstrained frozen boundary values is assumed.

Let epsilon=pgOscRadius d, A2=(2/(epsilon/2))^2 MP, A4=(4/(epsilon/2))^4 MP. The proof takes

```
R  = epsilon/2
M1 = MP + (MP + b*A2 + b^2*A4)
r1 = epsilon/4
CQ = M1/R^5
```

These depend only on d, before mu, I and x. The Cauchy/coefficient bounds give |Q|<=M1 on |x|<R for every I in the half-tube. For x!=0, g(t)=Q(t*x) is bounded on |t|<R/|x|. `remainder_jet_tube` (JetsRegular.lean:146) and the actual `iteratedDeriv_line_eq_iteratedFDeriv` convert all orders 0..4 into the required zero line jet. Since |x|<=epsilon/4<R, t=1 is strictly inside this disc; Schwarz gives M1/R^5*|x|^5 exactly. At x=0 the order-zero jet gives Q(0)=0. Thus no boundary limit in x, normalization of a zero vector, unproved compactness assertion, or loss of uniformity is hidden.

The import closure contains 67 KAM modules, including 20 frozen definition modules, **no frozen theorem module and no provider**. Therefore neither a DRAFT_SORRY anchor nor another provider is imported. Axiom checks below independently test all 17 new theorems, including their transitive proof dependencies.

## Notes and source/blueprint fidelity

**N1 — Nonblocking radius/proof-text precision.** Blueprint `blueprint-P/parts/p5-pg-assembly.tex:72` says “Take r1:=epsilon_an/2”; line 73 then says “bounded by M1/r1^5 on the boundary circles” for a function only stated holomorphic on |t|<r1, and the proposition at lines 65–66 includes |x|<=r1. On an inner circle of radius R'<r1 the directly available bound is M1/(R')^5; a limit is needed to obtain the open-disc constant, and the endpoint needs continuity in a larger domain (available here) or a smaller output radius. The Lean proof explicitly uses inner circles and their limit, then chooses output epsilon/4 inside coarse-bound radius epsilon/2. This is a documented proof-plan deviation, not a weakened proposition: lines 65–66 allow any positive r1<=epsilon_an and data-only finite CQ. Recommended source clarification: distinguish the coarse-bound radius R=epsilon_an/2 from the final radius r1=R/2, and state the R' increases to R argument. No frozen statement is implicated.

**N2 — Existing Revision-4 source wording.** The design Revision 4 and design audit 4 already record the overly broad “P~=P at real points” claim at blueprint line 30 and its graph counterpart. The corrected agreement holds only on the real closed cylinder. Remainder.lean never invokes agreement at exterior real points; it operates entirely on the constructed complex average and proved vanishing jets. This package introduces no further source assumption. This note does not reopen or independently certify the whole P5-EX proof.

No new pinned-paper erratum is established by this scoped audit. CP10 (60)'s missing proof is already an explicit source gap at blueprint lines 68–69; the package supplies the uniform analytic-remainder argument rather than assuming it.

## Independent validation receipts

1. Targeted build, run once:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5rem KAM.Planetary.PGAssembly.Remainder
   ```

   Exit **0**. Output includes `[inp-gate] slot 2 acquired 12:04:01 for KAM.Planetary.PGAssembly.Remainder` and `Build completed successfully (9113 jobs).` Existing replayed warnings: four unused simp arguments in JetsPoly.lean:213,215 and nine unused-variable warnings in Jets.lean:75–79,98. The handoff's claim that only Jets:98 warnings occur is incomplete; these inherited warnings are not blockers and no warning points into Remainder.lean.

2. Signature/proof-application probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5RemAudit.lean
   ```

   Exit **0**, no errors or warnings. A Python comparison first confirmed `literal signature equality = True` for both main contracts, comparing complete source text before `:=` with the shared signature file. The probe copied just these two original signatures under fresh names, proved them by direct applications of the implementation with exactly their explicit binders (`hR hM hg hbound hjet`, and `d`), and elaborated `example : type_of% @<implementation> := @<fresh theorem>` for each. This checks the actual design contracts without importing any sorry-based design draft. There is no frozen seal in this package to test.

   The same single probe printed axioms for **all 17 declarations in the table**. Every line has precisely this axiom list:

   ```text
   [propext, Classical.choice, Quot.sound]
   ```

   In particular:

   ```text
   'KAM.Planetary.schwarz_order_five' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.uniform_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation for the sole package module (all 17 declarations reside in it):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Remainder
   ```

   Exit **0**. Exact output:

   ```text
   replaying KAM.Planetary.PGAssembly.Remainder
   ```

   Captured at `/tmp/P5-REM-audit-1-leanchecker.log`.


4. Controlled full lint rerun:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely for the stale generated root explicitly excepted by the audit brief. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (575 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Captured at `/tmp/P5-REM-audit-1-lint.log`. No forbidden tokens, overrides, oversized files, or module/ABI defects were reported. Remainder.lean has 356 total lines, its copyright/module/public imports/docstring/public section are present, and direct forbidden-token scanning found no match. The initial lint attempt had not explicitly set the requested environment; it was stopped during the non-Lean frozen-guard stage, before ABI elaboration, and is not counted as a validation receipt. The successful full rerun above inherited both the thread limit and nice priority. The build was waiting for a gate slot during that initial attempt; no audit Lean jobs overlapped. All audit Lean/Lake invocations used LEAN_NUM_THREADS=1 and nice priority, with no heartbeat, recursion, or synthesis-budget override.

5. Final integrity:

   ```text
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check
   ```

   Both exit **0**; protected-path diff has no content (only the already recorded multiple-merge-base warning). No generated-root repair was attempted. The temporary `.lake/abi-scratch/P5RemAudit.lean` probe was removed. The report has 17 declaration rows, balanced code fences, no trailing whitespace, and a terminal newline. Final status contains only this newly written audit report and the pre-existing untracked P5-REM handoff; no tracked implementation change was made.

Files written: **only** `/root/code/KAM-inp-p5rem/docs/tracks/P/audits/P5-REM-audit-1.md`. No state-changing git command was used. No blocking uncertainty remains within the scoped package; independent re-audits of P5-EX/P5-JET, downstream consumer closure, provider completion, and frozen P-G sealing are outside this verdict.


