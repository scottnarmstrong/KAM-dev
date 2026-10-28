# P23-04 independent audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.cover` and package P23-04. No material statement, proof, definition, or import defect found. The notes concern the retained unused `hη` binder and the expected stale generated root. This is an infrastructure package: there is no frozen theorem anchor or provider export to seal, and no planetary headline closure is claimed.

## Scope and authority

Audited `/root/code/KAM-inp-p2304`, HEAD `4f40f9c20caa0d0ea16872033056f5be75821cf5`, against `inp` / merge base `4f65a1f8055d14808ab27ed9bff2e18d69eac46c`, using `git diff inp...HEAD`. The complete tracked delta is one new file, `KAM/Planetary/TwoScale/Cover.lean` (94 lines). The pre-existing untracked `P23-04-handoff.md` was read and preserved.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the shared `.drafts/briefs/inp-audit-package.md`, the P23-04 handoff and AUDIT FOCUS, Revision 2 of `docs/tracks/P/design/P23-LEAN-DESIGN.md`, its two design audits, shared `.drafts/design/P23Signatures.lean`, Track P statement conventions, and blueprint `p3b-two-scale-limit.tex` L150–160. The handoff says “p3a cover”; the actual cover statement and proof are in **p3b**, as the design node map correctly records. The explicit user destination overrides the generic brief's MAIN-worktree destination.

Production audit scope is exclusively `KAM/Planetary/TwoScale/Cover*`. No new frozen type or frozen definition is used in this theorem. Provider/frozen type equality, seal-copy elaboration and imported frozen-anchor manifest states are therefore not applicable. Instead, a fresh-name copy of the exact design signature was elaborated with body `by exact KAM.Planetary.cover hlam hη hlip hbound`.

## Declaration and node verdicts

| Node | Lean declaration / proof location | Verdict | Reason |
|---|---|---|---|
| `bpP:p3:cover` | `KAM.Planetary.cover`, Cover.lean L29–92 | PASS | Exact signature match to Revision 2 Appendix A L1182–1191 and shared signatures L799–808; ambient max norm, all constants, quantifiers and premises retained. Actual `Equiv` supplies both inverse laws. |
| `stepP:p3:cv-ext` | Local witnesses `G`, `hG`, `hGg`, L39–42 | PASS | Calls landed `KAM.mcshane` on arbitrary X with the same nonnegative Lipschitz constant; no nonemptiness, closedness or global bound premise. |
| `stepP:p3:cv-bij` | Local `hbi`, `hinj`, `hsurj`, `F`, L44–77 | PASS | Triangle/reverse-triangle inequalities give exact factors 1±lam. Lower factor is positive. Surjectivity uses the proved contraction on the complete nonempty ambient Pi space, then `Equiv.ofBijective`. |
| `stepP:p3:cv-loc` | Local inverse displacement argument, L79–92 | PASS | For x=F.symm y, x−y=−G x. The bound at y∈X and global Lipschitz estimate give (1−lam)‖x−y‖≤η, divided only by a strictly positive denominator. |

The only new public declaration is `cover`; the step rows name local proof obligations, not separately exported lemmas. There are no extra premises, wider constant dependencies, assumed inverse, or conclusion-shaped fields. The blueprint's initial set-distance inequality follows from `Metric.infDist_le_dist_of_mem hy`, then `dist_eq_norm`; it needs no additional analytic estimate. An extension named `g_e` can be recovered as F−id; the proof already constructs it as G. The exact designed export intentionally returns F and the quantitative bounds.

For η=0 the same positive-denominator inequality forces zero inverse displacement. For X=∅ all base-point conclusions are vacuous while McShane and contraction still construct a global equivalence. For N=0, the ambient function space is a nonempty complete singleton; no coordinate or positive-dimension premise is required. No division by η or use of an attained supremum occurs. The unused `hη` premise is explicitly present in the approved design signature and is harmless: when X is nonempty its consequence is already forced by hbound; when empty it is unnecessary.

## Definition and dependency classification

No new public `def`, `abbrev`, `structure`, or instance. The local `F := Equiv.ofBijective ...` is the intended global equivalence on its entire carrier, with forward function x+G x and genuine inverse. `set x := F.symm y` only names an existing inverse point. The existential extension G is guaranteed to agree with g on X and be Lipschitz everywhere; its arbitrary behavior off X is constrained exactly as needed, not used as a junk fallback.

Imports are `public import Mathlib` and `public import KAM.Measure.McShane`. Read McShane's extension contract and imports: it imports Mathlib components only, with no provider or frozen theorem anchor. No production import of draft signatures or DRAFT_SORRY theorems occurs. The design row also listed Measure.Lipschitz; omitting that unused dependency is harmless because this package makes no measure claim. Banach fixed-point existence is furnished by Mathlib's `ContractingWith.fixedPoint_isFixedPt` on a complete nonempty space, not an assumed conclusion.

## Independent verification

All Lean/Lake invocations were sequential, under `LEAN_NUM_THREADS=1` and `nice -n 5`, without resource overrides, dependency fetching or library rebuild from scratch.

1. Exact signature comparison: extracted the command from `theorem cover` to its proof separator and compared byte-for-byte with both design Appendix A and the shared signature file. Output:

```text
Appendix A EXACT SIGNATURE MATCH
draft signatures EXACT SIGNATURE MATCH
lines: 94 max characters: 94
```

2. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2304 KAM.Planetary.TwoScale.Cover
```

Exit **0**. Output:

```text
[inp-gate] slot 1 acquired 06:58:42 for KAM.Planetary.TwoScale.Cover
⚠ [9048/9048] Replayed KAM.Planetary.TwoScale.Cover
warning: KAM/Planetary/TwoScale/Cover.lean:30:32: Variable name `hη` is not explicitly referenced.
Build completed successfully (9048 jobs).
```

The additional standard warning text suggests renaming/removing the unused binder; no change was made to the exact signature.

3. Exact-signature application and axioms probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2304Audit1.lean
```

Exit **0**, output:

```text
'KAM.Planetary.cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'p2304_audit_signature' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or other extra axiom. The probe imports only the audited module, states its exact signature under a fresh name, applies all four explicit binders in order and prints both axiom sets. It is removed after verification.

4. Kernel replay, one invocation for the sole new lemma module (no provider module exists):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.Cover
```

Exit **0**, complete output:

```text
replaying KAM.Planetary.TwoScale.Cover
```

5. Full source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (440 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is the stale generated root explicitly permitted by the audit brief. All other lint checks passed, including the 100-character line limit. No root regeneration was performed.

6. Static and integrity checks:

- `git diff --check inp...HEAD` and `git diff --check`: exit **0**, no output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit **0**, empty output.
- Independent scoped scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, `set_option`, new definitions or instances; one public theorem, `cover`.
- Module header, copyright, public imports, module docstring and exposed public section are present. File has 94 lines, longest line 94 Unicode characters; no size or line-length violation.
- The audit probe was deleted. Final report whitespace and required-section checks passed. Final status contains only the pre-existing untracked handoff and this new audit report; no tracked production change was made.

## Uncertainties, errata and deviations

No suspected mathematical source or blueprint defect in the scoped cover statement/proof. The handoff's “p3a cover” locator should read `blueprint-P/parts/p3b-two-scale-limit.tex` L150–160; the quoted cover label is correct. This is a documentation locator note, not a claim that a pinned paper is defective. No fresh external-paper audit was required for this source-free extension argument. No production, frozen, manifest, generated-root or README edits were made, and no mathematical deviation was introduced.

Future P23-21 measure consumers still need their own implementation and applicability audit. This PASS covers the exact cover contract and its three proof steps only.
