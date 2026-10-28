# N12-10a independent package audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Nekhoroshev.Averaging.FlowDefs` and `bpN:p12:s-flow#data`. All seven public declarations satisfy the assigned design contracts; no mathematical or proof defect found. The note is the expressly permitted stale generated-root lint diagnostic.

No frozen anchor is proved by N12-10a. Provider/frozen-type and seal-body tests are **not applicable** to this infrastructure-only package. Neither `averaging_mean` nor `averaging_most` is certified seal-ready by this report; both remain `DRAFT_SORRY` in the manifest.

## Scope and authority

Audited on 2026-10-28 in `/root/code/KAM-inp-n1210a`:

- HEAD: `cb412a7391c69b01b768cee85f70af5681e7978b`.
- Comparison ref `inp`: `ef8fc426c638557035e6101216aad4ef8b8a570e`.
- Read AGENTS, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the supplied handoff. The user's exact report destination overrides the brief's generic MAIN-worktree destination.
- Contract: `docs/tracks/N/design/N12-LEAN-DESIGN.md`, row N12-10a at line 284, Appendix A lines 563–588, and `blueprint-N/parts/p12-averaging.tex:48`.
- Read both design audits from their actual location, `/root/code/KAM-inp/docs/tracks/N/design/DESIGN-N12-design-audit-{1,2}.md`; these are under `design/`, rather than the `audits/` location mentioned in the handoff. Audit 2 resolves audit 1's corrector-series finding, which is outside FlowDefs.
- Compared against `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`. The local design Appendix A equals this file exactly. The signatures file is absent from this worktree's `.drafts/`, so the MAIN copy was read without editing it.
- Read the track statement's averaging section, relevant frozen definitions and averaging roots, and the consumed `HoloReal`, `Setting`, `Maximal`, and `Hamiltonian` interfaces.

`git diff inp...HEAD` contains new `Setting.lean` (112 lines), `Field.lean` (219), and `FlowDefs.lean` (93). As instructed by AUDIT FOCUS, the verdict covers **only FlowDefs**. Setting/Field are dependency context, not independently certified packages here. No delegation, production edits, state-changing git, generated-root regeneration, or cache/package changes were performed. Temporary Lean probes were restricted to `.lake/abi-scratch/` and removed after use.

Snapshot hashes:

```text
98ec1bd6c42709e2607a1f3e3e4f3262b44aa76b665a2b6b3f9b001f0b2b41b6  KAM/Nekhoroshev/Averaging/FlowDefs.lean
d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370  docs/tracks/N/design/N12-LEAN-DESIGN.md
0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369  /root/code/KAM-inp/.drafts/design/N12Signatures.lean
```

## Declaration and definition ledger

All public names below are in `KAM.Nekhoroshev`, and implement `bpN:p12:s-flow#data`. Each of the six definition bodies and the theorem's complete telescope/conclusion matches the design signatures exactly. There are no new abbreviations, structures, or global instances in FlowDefs.

| Node / stage | Declaration (FlowDefs line) | Verdict | Classification / reason |
|---|---|---|---|
| s-flow#data | `avgMaximal` (35) | PASS | Noncomputable guarded choice of the existing `IsMaximalSolution` predicate with EReal endpoints. Totalization `(0,0,const x)` is exactly the design fallback; valid-data existence excludes it. |
| s-flow#data | `avgTm` (41) | PASS | Exact first projection, the left endpoint, on the whole carrier. |
| s-flow#data | `avgTp` (43) | PASS | Exact second endpoint projection on the whole carrier. |
| s-flow#data | `avgFlow` (45) | PASS | Evaluation of the chosen trajectory, with design order `h f R ε t x`. Values outside its time domain carry no solution assertion. |
| s-flow#data | `avgFlowDomain` (47) | PASS | Exactly initial membership in `avgDomain n R` and time membership in `eIoo avgTm avgTp`. Real-time/EReal-endpoint distinction preserved. |
| s-flow#data | `avgOmega` (51) | PASS | Exact time slice `{x | (t,x) ∈ avgFlowDomain ...}`. |
| s-flow#data | `avgMaximal_spec` (73) | PASS | Existing maximal predicate for the literal frozen Hamiltonian field; only standing analytic data, ε and initial membership. No differentiability or supplied-flow premise. |
| Private openness helper | `isOpen_avgDomain` (54) | PASS | Product of all angles and open action ball; no positivity premise needed to prove openness. |
| Private analytic scaling helper | `data_smul` (58) | PASS | Proves `Data n R s |ε| h (ε f)` from size-one analytic perturbation data; preserves holomorphy, boundary continuity, periodicity, reality and norm bound. |

The ambient phase is `(Fin n → ℝ) × (Fin n → ℝ)` with its existing Pi/product norm. `avgH h f ε` unfolds to the frozen `realHamiltonian h (fun w => (ε : ℂ) * f w)`. No replacement field, norm instance, source-domain enlargement, or altered equation is introduced.

## Proof and fallback refutation checks

At lines 60–71, multiplication by a real constant retains all analytic perturbation clauses. The size is `|ε|`, using `‖(ε : ℂ)‖ = |ε|`, so the proof also works for negative ε and ε=0. The blueprint subsection states nonnegative ε; the theorem validly extends this to every real ε, as the exact design signature requires.

At lines 78–83, `holo_input (data_smul d ε)` supplies C∞ regularity of the actual `avgH` on the open `Wdom`. Its C² consequence gives C¹ regularity of the actual Hamiltonian field by `ham_smooth_c1`, then restriction uses `avgDomain_subset_Wdom d`. Nothing about derivatives or differentiable dependence is assumed through a hidden field of `AveragingData`: its fields are only dimension, positive radii, frozen analytic predicates and frequency rank.

At lines 84–90, `gen_maximal` proves existence on the open original domain through `hx`. The existential is repackaged as the exact product predicate tested by `avgMaximal`, and `Classical.choose_spec` proves the chosen triple satisfies it. Proof irrelevance permits the simplification between proofs of that same existential. The unused uniqueness half of `gen_maximal` remains available upstream: the predicate already asserts agreement with every solution through x on an interval containing zero. No uniqueness or existence is postulated in the definition's input.

Consequently, under `d` and `hx`, the fallback branch cannot occur. When no triple exists, the specified totalization is intentional and has equal endpoints, hence an empty `eIoo`. When a triple exists, `IsMaximalSolution` supplies endpoints straddling zero, the initial value, the true solution law and maximality. Off-interval values of the chosen total curve remain arbitrary, as allowed by the design. No theorem here asserts a solution law at such values.

A Lean probe copied the exact design `avgMaximal_spec` signature under `example` and proved it by `exact avgMaximal_spec d ε hx`. Additional examples derived `avgFlow ... 0 x = x` and `x ∈ avgOmega ... 0` from its actual maximal predicate. All elaborated without warnings. The initial definition-text comparison harness overran the final `avgOmega` block into the following private helper; bounding the block at its blank line confirmed the exact match. This was a harness issue, not a source discrepancy.

## Independent validation

All Lean/Lake/checker invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No resource overrides were used. These are independent auditor reruns, not copied prover receipts.

Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1210a KAM.Nekhoroshev.Averaging.FlowDefs
```

Exit 0; complete output:

```text
[inp-gate] slot 2 acquired 08:05:18 for KAM.Nekhoroshev.Averaging.FlowDefs
Build completed successfully (2953 jobs).
```

Exact-signature, initial-value/domain and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1210aAudit.lean
```

Exit 0, no warnings. The probe issued `#print axioms` for the sole new public theorem and all six definitions; complete Lean output:

```text
'KAM.Nekhoroshev.avgMaximal_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgMaximal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgTm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgTp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgFlowDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay (the sole audited module contains both helpers and the public theorem; no separate lemma module):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.FlowDefs
```

Exit 0; complete output:

```text
replaying KAM.Nekhoroshev.Averaging.FlowDefs
```

Import inspection: all four direct imports are public, as required. A recursive traversal of source import directives found 50 local KAM modules including FlowDefs, with 26 frozen definition modules, **zero providers and zero frozen non-definition modules**. Thus no DRAFT_SORRY theorem is imported and no SEALED-theorem exception is needed. The only instance attribute is local `Classical.propDecidable`.

The module has 93 total lines, copyright/authors, `module`, public imports, module docstring and `@[expose] public noncomputable section`. A direct token/option scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or `set_option`. All definitions are covered by the exposed section.

Lint command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the stale-root exception explicitly allowed by the audit brief. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (469 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All other lint checks pass. `KAM.lean` was left untouched.

Protected-path comparison:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0 with empty output. No protected-path changes. Final report whitespace and workspace checks are recorded below after cleanup.

## Findings, uncertainties and handoff

No new blueprint/source defect, suspected frozen defect, or implementation deviation found in the audited surface. No pinned PDF was independently re-audited: this package's contract is the local maximal-flow construction and proved ODE/holomorphy interfaces. The design's inherited Nei76 maximum-error issue and its declared later repair concern subsequent estimates, not this existence/choice package.

Flow regularity, differentiable dependence on initial conditions, determinant one, transport and averaging estimates remain separate obligations. This PASS WITH NOTES certifies the N12-10a surface only. It does not certify N12-01, N12-10b, the entire `bpN:p12:flow` lemma, either provider, or the campaign roots.

Only delivered file: `/root/code/KAM-inp-n1210a/docs/tracks/N/audits/N12-10a-audit-1.md`.

Final cleanup: removed `.lake/abi-scratch/N1210aAudit.lean`; no probe artifacts retained. `git diff --check` and `git diff --check inp...HEAD` exit 0 with no output; an explicit report trailing-whitespace check passes. Final status contains only the pre-existing untracked `N12-10a-handoff.md` and the new audit report. The FlowDefs hash remains the snapshot hash above.
