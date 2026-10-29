# N11-O independent package audit 1

Overall verdict: **PASS WITH NOTES** for N11-O's complete signed helper slice.
All six new public theorems pass the proof, signature, axiom and kernel checks.
The notes are the expressly permitted stale generated root, the intentional unused signed
binder and an inherited blueprint API citation. No corrective Lean change is required.
This is ready for package integration; it is not a seal of the partial-convex frozen anchor.

Scope: only `KAM/Nekhoroshev/Partial/Threshold.lean`, HEAD
`1366d5f3c41aeb3b21be54a3c7054e307cf9de53`, compared with `inp`
`b0e2f8831ae1de9b2eeb0890b7697d19e55626f1` using the full `git diff inp...HEAD`.
That diff adds exactly this 195-line file. During the audit inp advanced to
`48e9326d764f4bb7e1704209fddf71863ec4eb9e`; a final three-dot comparison still adds
only the identical 195-line Threshold.lean (merge base
`f5376c6dffbc49d970aeb4f9b37796a46f764133`). The untracked prover handoff was present initially.
The user's explicit absolute report path overrides the generic brief's main-worktree destination.
Only this report and temporary `.lake/abi-scratch/` probes are audit edits; no state-changing git.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package brief, N11-O handoff, N11 design,
both design audits, the exact external signatures, relevant Part-11 blueprint statements,
track-N statement and frozen partial-convex anchor/definitions. The signature file hashes to
`23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4`, exactly the revision-2
design-audit snapshot. Audited module SHA-256:
`d8dedb757e5351595a52da35234bcaae707f93b2b76105fc992799205271b4c9`.

## Declaration and node ledger

Unqualified names below have prefix `KAM.Nekhoroshev`. Lines refer to Threshold.lean.

| Node / obligation | Declaration | Verdict | Reason |
|---|---|---|---|
| Constants positivity support | `PartialConstants.nthr_pos` (36) | PASS | Positive numerical inputs yield all nine derived positivities, including coth and cK; no dynamical premise. |
| Constants / power identity | `PartialConstants.nthr_K_eq` (55) | PASS | Exact K=cK μ^(-1/(2n)) for positive μ and positive scale factors. In fact it does not require ε≤ε0, a stronger identity than the blueprint's restricted presentation. |
| `bpN:p11:ext-rpow`, polynomial support | `nthr_rpow_le_eventually` (66) | PASS | Any real X and δ<1, positive a. Uses decay of y^(-(1-δ)); absolute-value majorization also handles negative X. No graph-node-named substitute. |
| `bpN:p11:ext-rpow`, exponential support | `nthr_exp_eventually` (83) | PASS | Exact eventual y^n exp(y^τ)≤C exp(a y/6), C,a>0 and τ<1; no unnecessary τ>0. Uses the correct root asymptotic declaration. |
| `stepN:p11:final-mu`, `stepN:p11:final-time` | `nthr_key` (105) | PASS | Six comparisons for abstract numerical constants and arbitrary real κ. A single μ0>0 is extracted before μ; stronger than the source-data-specialized target. |
| N11-O signed target / same two assembly steps | `threshold` (185) | PASS | Declaration text before the body is byte-identical to external signature lines 737–743, including unused hne. Exactly the six prescribed conclusions, with original factors and exponents. |
| `bpN:p11:constants` (shared B/O numerical slice) | `threshold`, helpers above | PASS | Uses the literal existing PartialConstants formulas; proves small-μ applicability rather than introducing surrogate constants or assuming comparisons. |
| Frozen root `bpN:p0:partial` | `partialConvex_nekhoroshev` | OUTSIDE PACKAGE | Anchor remains DRAFT_SORRY. This helper package does not claim provider or frozen-root closure. |

Design row N11-O (design:369) assigns only Threshold.lean. The node table (design:282–290)
reserves final-empty/data/given/orbit/sign/drift/order for provider assembly and assigns
threshold specifically to final-mu/time. Both assigned steps are proved here. The imported
exponents and literal constants are N11-B results, not missing N11-O exports. No new unsigned
export takes a graph-node name while weakening that node.

The first four conjuncts are exactly the signed block inputs hε, hd, hκ and hSL
(external signatures:720–736). The fifth is the final drift comparison, and the sixth
compares the frozen physical time μ⁻¹ exp(μ^(-partialTimeExponent n)) with blockTime.
Thus the design's provider assembly (design:394–406; blueprint p11c:175–179) can consume
all promised numerical facts without a new premise. Actual block/provider proof closure
is outside this audit, and is not inferred from these interface checks.

## Definitions, hypotheses and proof review

No new def, abbrev, structure, instance or global notation is introduced. All six additions
are public theorems. Proof-local lets/sets T,D,E,c1,C0,y are ordinary abbreviations of the
frozen exponents and literal formulas, with no fallback or replacement object. Existing
PartialConstants (Constants.lean:48–76) is numerical data only; constants projects n,ρ,g,m,Mc
from PartialData. PartialData (Constants.lean:79–104) contains the frozen source premises,
not thresholds or stability conclusions. Frozen HasDefiniteFastPart explicitly includes
0<g and 0<m, even on empty domains; threshold extracts those facts directly. It therefore
does not need hne, but retains that exact signed binder. No m≤Mc premise is smuggled into
this numerical argument.

Let E=1/(2n), D=partialDriftExponent n and T=partialTimeExponent n. The proved imported
exponents theorem gives 0<T<D and 2D<E. With y=μ^(-E), the proof derives, under μ>0,
K=cK*y, d=y^(-D/E), κ(μ)=c1*y and μ^(-T)=y^(T/E). Thus 2D/E<1, D/E<1 and T/E<1.
Positivity of every divisor used in order-sensitive cancellation is established. Negative
powers are rewritten only at positive bases. The two radius comparisons preserve the
factor 256*k*ρ*R0 and the final factor 1/2.

The exponential argument splits c1*y/6 into two equal budgets c1*y/12: one absorbs
y^(T/E), the other absorbs y^n/C0. The exact blockTime identity is
C0*exp(c1*y/6)/(y^n*μ), with C0>0 and all constants independent of μ. This proves the
sixth conjunct with its μ⁻¹ prefactor intact. Pullback along the positive-side power
limit and intersection with the two elementary smallness neighborhoods produces a
single positive interval (0,μ0). The body of nthr_key depends only on c and κ, proving
the intended numerical uniformity more explicitly than the bundled threshold type alone.
There is no chosen initial point, perturbation, orbit, sign or future confinement in this
construction. The source's explicit minimum formula for μ0 is replaced by an existential
neighborhood witness, as expressly permitted by the signed target; no consumer needs
that explicit minimum formula.

## Independent verification

All audit Lean/Lake actions are serialized with LEAN_NUM_THREADS=1 and nice -n 5;
no heartbeat, recursion or synthesis budget changes. Build uses the prescribed gate;
a gate wait is not reported as a proof failure.

1. Targeted build (exit 0):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11o KAM.Nekhoroshev.Partial.Threshold
   ```

   ```text
   [inp-gate] slot 2 acquired 20:15:06 for KAM.Nekhoroshev.Partial.Threshold
   ⚠ [2903/2903] Replayed KAM.Nekhoroshev.Partial.Threshold
   warning: KAM/Nekhoroshev/Partial/Threshold.lean:185:41: Variable name `hne` is not explicitly referenced.
   Build completed successfully (2903 jobs).
   ```

   The warning's remaining output consists of the standard unused-binder hint; no
   suggested linter override was applied.

2. Exact signature/body and axiom probe (exit 0):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11OAudit.lean
   ```

   The probe imports only the production Threshold module, copies the signed threshold
   type under fresh name audit_threshold_copy with body `by exact threshold a hne`,
   and elaborates `example : type_of% @audit_threshold_copy := @threshold`.
   A separate Python text comparison of the complete declaration prefix before `:=`
   prints `SIGNED threshold text equality: True`.
   All six fresh `#print axioms` outputs are:

   ```text
   'KAM.Nekhoroshev.PartialConstants.nthr_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.PartialConstants.nthr_K_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.nthr_rpow_le_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.nthr_exp_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.nthr_key' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay (one invocation, exit 0):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.Threshold
   ```

   ```text
   replaying KAM.Nekhoroshev.Partial.Threshold
   ```

4. Lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, with the following complete diagnostic output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (909 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The sole failure is exactly the package brief's permitted generated-root exception.
   The frozen-anchor guard and ABI elaboration both passed independently in this run;
   no unrelated substantive lint failure was waived.

5. Final report whitespace, protected-path and scratch-cleanup checks:

   `git diff --check` and
   `git diff --no-index --check /dev/null docs/tracks/N/audits/N11-O-audit-1.md`
   both exit 0. The protected-path three-dot diff is empty. The temporary
   `.lake/abi-scratch/N11OAudit.lean` is deleted. Final worktree status contains only
   this untracked report and the pre-existing untracked N11-O handoff.

Static hygiene: 195 lines, maximum Unicode line width 97; module/copyright/docstring,
public imports and public section are present. No forbidden proof escape, resource override
or EuclideanSpace token occurs. All five nthr_ helper short names occur in declarations
only in this module; threshold is the required signed name in KAM.Nekhoroshev, not a
root declaration. No harmful root shadow or added typeclass instance. A recursive local
KAM import scan visits 38 files, including 23 frozen definition modules; there are no
provider or frozen theorem imports, so no SEALED-theorem exception is needed.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
No generated file was repaired or regenerated. Production declaration checks use the
compiled module, not the placeholder design proof bodies.

## Source defects, deviations and limits

One inherited documentation/API defect is still visible at
`blueprint-N/parts/p11a-partial-route.tex:41`: “Real.tendsto_exp_div_rpow_atTop”.
The asymptotic theorem is root-level, with no Real alias. This is audit-1 F4, already
corrected in the revision-2 design and correctly implemented here with
`tendsto_exp_mul_div_rpow_atTop`; the stale blueprint locator is nonblocking. No new
pinned mathematical-source defect is identified by this numerical package audit.

The earlier design's N11-G reconciliation gate and N3 open-ball/adjoint-locator notes
remain outside this module; this verdict does not discharge them. No additional source
premise, changed norm, carrier, constant dependence, numerical coefficient, time scale,
frozen exponent or conclusion was introduced. The unused hne warning is an intentional
consequence of exact signature fidelity. Provider/frozen-type and seal-body probes are
inapplicable because this package supplies no provider export; the frozen partial-convex
anchor is still DRAFT_SORRY and is not seal-ready on the strength of N11-O alone.
