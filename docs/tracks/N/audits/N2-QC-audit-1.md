# Independent N2-QC package audit 1

Overall verdict: **PASS WITH NOTES** for N2-QC infrastructure and its N-QC-shaped result. No new anchor is sealed by this package; the existing N-QC anchor is already SEALED. The notes concern the permitted stale generated root, comparison ancestry, and existing blueprint coordination text. No mathematical or statement-fidelity defect was found in the audited module.

## Scope and authority

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-n2q`.
HEAD: `821a18fbbd08b8af17a75e84d161e13231d760c0`.
Compared `inp`: `46bfbcb5e40e5540583d781ad736c36bd2abd4ab`.
Compared `inp-n2d`: `bc60dc051f53844b4dc67fd31e4b6ca5f7c49198`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the prescribed package-audit brief, handoff and AUDIT FOCUS, track-N statement, Part-2 blueprint and relevant Part-0 definitions/theorem, N2 design and its prior audit, original signatures, frozen QC/realPart/frequency definitions, existing QuasiConvex implementation, and N2-DERIV interfaces.

The user's explicit path instruction overrides the generic brief's main-worktree destination. Only this report is a lasting edit. The pre-existing untracked handoff is left untouched. Disposable probes use this worktree's `.lake/abi-scratch/` and are removed at closeout.

The handoff limits the audit to `KAM/Nekhoroshev/QcZero/QCResults.lean`. `git diff inp...HEAD` reports multiple merge bases and selects `25f3d65bb0d5a30674a6e5286c44befb321e7e9d`; the other merge base is `480b27e8c29c3a91d1217a359cfcb66e548594b2`. The requested diff has three changed paths: inherited `.drafts/handoff-N2-DERIV.md`, inherited `Derivative.lean`, and `QCResults.lean`. The requested `inp-n2d...HEAD` comparison additionally contains unrelated merged packages and generated-root history; it is not literally a one-file branch diff. Restricting either comparison to QCResults gives the same new 67-line module. The protected-path diff against `inp` is empty. N2-DERIV and N2-KERNEL are dependencies, not independently re-audited packages here.

The prior design audit is located at `/root/code/KAM-inp/docs/tracks/N/design/DESIGN-N2-design-audit-1.md` (not the handoff's audits-directory spelling). The original signatures are `/root/code/KAM-inp/.drafts/design/N2Signatures.lean`; this worktree's design Appendix A contains them. Current SHA-256 values:

- QCResults: `399677d1c2fc9f5dc75efff59b740e7c030ce745d698d7bda0201fe2acbcb188`.
- Design: `42377b6eccc4cac2f9f35feaabd620ea56ded53d38052dfbff84ada06eb7a726`.
- Part-2 blueprint: `ed9954f4a8313436ba58be47d1f061022b49cdf3ad04ba72b0c9467412dce73d`.
- Original signatures: `6f0af532d88555f0dd089b07298270823eecafd6d46efa540eeda7f8ef87a57a`.

## Declaration ledger

All names are in `KAM.Nekhoroshev`; locations refer to QCResults.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| `bpN:p2:n0` | `n0`, L23–26 | PASS | Frozen QC requires nonzero frequency at every member; the empty coordinate type has only the zero vector. Thus U is empty. Does not falsely assert that QC itself is impossible on empty U. |
| `stepN:p2:qb-unpack` | `qb_unpack`, L33–42 | PASS | Exactly unpacks positive m, open U, real C², nonzero frequency and max-norm coercivity; derives dimension positivity from nonzero frequency. No extra premise. |
| `stepN:p2:qb-deriv` | `qb_deriv`, L44–49 | PASS | Uses the genuine `qc_deriv` derivative with open/C²/membership supplied by frozen QC. Arbitrary real lambda, including zero, is a sound strengthening of its use under positive lambda. |
| `stepN:p2:qb-pos` | `qb_pos`, L51–56 | PASS | Schwarz/quadratic identity supplied by `qd_sym`; coercivity and nonzero v give strictly positive `m * ‖v‖²`. No lambda premise is needed. |
| `bpN:p2:qc-bij` | `qc_bij`, L59–62 | PASS | Exact frozen-shaped pointwise bijectivity under QC, membership and positive lambda, for every n. Uses the existing analytic theorem exactly as the design permits. |
| `stepN:p2:qb-concl` | `qc_bij`, L59–62 | PASS WITH NOTES | Supplies the exact conclusion by the existing analytic route. Does not call `qc_kernel`, `qb_deriv` or `qb_pos`, and therefore is not evidence of those dependency edges in its proof body. This route is explicitly authorized by the design. |
| Existing N-QC anchor | `quasiConvex_isoenergetic_derivative` | PASS WITH NOTES | Already SEALED in the manifest. Type equality and existing provider seal-body compatibility checked below; no anchor/body/manifest change is part of this package. |

Each of the five written theorem signatures, through `:=`, is byte-identical to its declaration in the original design signatures. Elaborated binders were also inspected. All dimension, h, U, m and I data remain universally quantified as intended. No existential constant, altered norm, additional regularity, lower frequency bound or quantitative inverse radius appears.

The apparent weakening of the displayed quantitative positivity step is harmless: `qb_unpack` retains the full lower bound, and `qd_sym` identifies its derivative expression with the literal double sum. A scratch example recovers `m * ‖v‖² ≤ ∑ i, ∑ j, v i * real_hessian_matrix h I i j * v j` for every perpendicular v, including v=0.

## Definition and hypothesis classification

There are **no new definitions, abbreviations, structures, instances or axioms** in QCResults. All five declarations are theorems. Frozen `IsStrictlyQuasiConvex`, `realPart` and `frequencyMap` are consumed directly, without restatement or a replacement predicate.

The inherited `real_hessian_matrix` is the actual second real derivative in coordinate directions; `bordered_map` is the explicit continuous linear map on the two ordered finite-dimensional product carriers. Neither is redefined here. Their complete definition audits belong to N2-DERIV/N2-KERNEL. QCResults uses the derivative and Hessian identities only where the QC predicate provides C² on an open neighborhood, so no proof exploits totalized `fderiv` outside its genuine derivative locus. The zero-dimensional result needs no derivative claim: all vectors on Fin 0 agree by subsingleton elimination.

The sole direct import is `KAM.Nekhoroshev.QcZero.Derivative`. Recursive source inspection finds 11 project modules in the production import closure, with **no provider and no frozen theorem module**. Thus no DRAFT_SORRY anchor or quarantined provider is imported by this package. The frozen anchor/provider imports used by the disposable ABI probe are allowed audit-only imports; that anchor is manifest state SEALED.

No conclusion-shaped premise, bundled unpaid mathematical step, alternate carrier, global norm instance, or junk-value fallback is introduced.

## Verification receipts

All audit-owned Lean operations were serialized. Targeted build and the final verification invocations use `LEAN_NUM_THREADS=1` and niceness 5. No clean, update, cache fetch, library rebuild or budget override was used.

### Targeted build

Command:

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n2q KAM.Nekhoroshev.QcZero.QCResults
```

The gate invokes `nice -n 5 lake build`. Exit **0**, output:

```text
[inp-gate] slot 1 acquired 07:19:32 for KAM.Nekhoroshev.QcZero.QCResults
Build completed successfully (2363 jobs).
```

No warnings. This is the prescribed targeted build using the existing build overlay; the jobs count is Lake's reported dependency-job count.

### Type, binder, seal-body and axiom probe

Command:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N2QCAudit1.lean
```

Exit **0**, no errors or warnings. The probe imports QCResults and the SEALED frozen N-QC module. It checks both:

```lean
example : type_of% @KAM.Nekhoroshev.quasiConvex_isoenergetic_derivative :=
  @KAM.Nekhoroshev.qc_bij
example : type_of% @KAM.Nekhoroshev.quasiConvex_isoenergetic_derivative :=
  @KAM.Provider.Nekhoroshev.quasiConvex_isoenergetic_derivative
```

A fresh anonymous copy of the entire frozen declaration type elaborates with the literal seal body:

```lean
by exact KAM.Provider.Nekhoroshev.quasiConvex_isoenergetic_derivative hqc hI hlam
```

These are exactly its three explicit binders in order. This is compatibility evidence for the existing provider, not a new seal request. Another example proves the full quantitative quadratic lower bound from `qb_unpack` and `qd_sym`. `#check @...` confirms all five elaborated parameter lists retain the intended section premises and no additional assumptions.

Exact `#print axioms` output for the five new public theorems:

```text
'KAM.Nekhoroshev.n0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.qb_unpack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.qb_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.qb_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.qc_bij' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The existing provider and frozen export also each report precisely `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or additional axiom occurs.

### Source lint and mechanical checks

Final command:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with exactly:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (446 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated-root warning is the brief's explicit allowed exception. No generated file was changed. The current file count is 446, rather than the handoff's historical 445. No other lint failure appears, including the 100-character limit.

Process deviation: an initial `sh scripts/lint_sources.sh` invocation omitted the explicit thread/niceness prefix; its internal ABI check completed before a corrective stop could act. It produced the same output and exit 1. This was an auditor command-prefix error; the complete final lint invocation above was rerun with the required settings. No audit-owned Lean processes overlapped. No production code deviation was introduced.

Additional checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty output apart from the multiple-merge-base warning; exit 0.
- `git diff --check inp...HEAD`: exit 0, only that ancestry warning.
- `git diff --check`: exit 0, no output.
- QCResults: 67 physical lines, longest line 95 Unicode characters; copyright, `module`, public import, module docstring and public section present.
- Direct scan of QCResults: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option` or `EuclideanSpace` token.

## Source and blueprint observations

No suspected pinned-source erratum, false frozen statement, or mathematical blueprint defect was found in this module. This audit compares the approved blueprint/frozen objects/design with the implementation; it does not claim a fresh independent review of BM11's pinned PDF or its unselected uniform inverse-radius assertion.

One existing, nonblocking coordination discrepancy from the design audit remains: `blueprint-N/parts/p2-qc-zero.tex:6` calls the general kernel lemma “cited by track I as the isoenergetic gate”, whereas `blueprint-I/parts/p3-iso-local-charts.tex:415` says that argument “is not needed.” This affects claimed consumer history, not the N2-QC statements or proofs. A future authorized documentation update should describe the kernel as available infrastructure rather than claim that active dependency.

Proof-route bookkeeping: `blueprint-N/parts/p2-qc-zero.tex:60` says “Lemma ... gives bijectivity” through the general kernel core. QCResults instead calls `isoenergetic_bijective_of_qc`, as explicitly allowed by the N2 design. The conclusion is exact and the existing proof uses the same kernel-pairing mathematics, but this package does not establish a direct Lean dependency from `qc_bij` to `qc_kernel` or to the new qb receipts. Do not infer those edges merely from the node labels.

Uncertainties: no unresolved mathematical or type blocker in scope. Broader graph updates, independent re-audits of N2-DERIV/N2-KERNEL, quantitative inverse estimates, and any new frozen closure remain outside this package audit.

## Kernel replay and closeout

Command (one invocation after the axiom/type probe completed):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Nekhoroshev.QuasiConvexIsoenergeticDerivative KAM.Nekhoroshev.QcZero.QCResults
```

Exit **0**, exact output:

```text
replaying KAM.Nekhoroshev.QcZero.QCResults
replaying KAM.Provider.Nekhoroshev.QuasiConvexIsoenergeticDerivative
```

The disposable `.lake/abi-scratch/N2QCAudit1.lean` probe was deleted. Final whitespace/integrity checks passed: report has no trailing whitespace, QCResults retains the recorded SHA-256, `git diff --check` exits 0, and status lists only the pre-existing untracked handoff and this new report. No production, frozen, manifest, generated-root, README, dependency, or git-history edit was made.

**Handoff:** one report file, at the exact requested worktree path. Approach: refute-first declaration/source comparison, proof inspection, import-closure inspection, exact signature and frozen-type checks, quantitative bridge probe, axiom inspection, targeted build, full source lint and kernel replay. All required checks are complete; only the expressly permitted stale-root lint exception and the nonblocking notes above remain.
