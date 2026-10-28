# A3 independent package audit 2 — rename delta

**Rename delta: PASS; round-1 N1 is resolved. Overall package verdict: PASS WITH NOTES**, retaining the generated-root lint exception and existing unused-premise warning. A3 is infrastructure, contains no provider, and does not seal a frozen anchor.

Audit date: 2026-10-28. Worktree and exact output destination: `/root/code/KAM-inp-p14-a3`. HEAD: `4d0b4580cb6499e96f2c57406374b3a2b9830783`; inspected `inp`: `ccd0fdc16c5e59bc83b9bda4321d2d85eadb8825`. Round-1 implementation baseline: `865c070da1367fa43c5541643392fe2990b308eb`. Rename commit: `bc0955ba886a41d3c79396c726453329565d0103`.

## Scope and exact delta

Read AGENTS.md, PLAN.md, DECISIONS.md, the shared `inp-audit-package.md` brief, local A3 handoff and AUDIT FOCUS, and A3-audit-1.md. Revisited the A3 design row, declaration table and Appendix A contract, blueprint `blueprint-P/parts/p14a-amd-expsafe.tex:93–104`, track-P statement, and frozen `AmdConfinement` target. This is a delta audit of the accepted round-1 proof, with fresh build, namespace/type/axiom probes, import checks and kernel replay. The user's explicit local report path overrides the generic brief's main-worktree destination.

`git diff inp...HEAD` adds Closure.lean (227 lines), A3-audit-1.md (160 lines) and A3-handoff.md (23 lines). `git diff --name-status 865c070d HEAD` reports the Lean file modified and those two documentation files added. Thus the **entire repository delta is not literally only a rename**: it also records the existing audit and handoff in commit `4d0b4580`. The complete Lean implementation delta is exactly the authorized rename:

```diff
-are continuous.  `closure`: the outer low-AMD region is open, and the collar is sequentially
+are continuous.  `amd_closure`: the outer low-AMD region is open, and the collar is sequentially
-theorem closure (B : AMDBox n) (hB : B.Admissible) {delta : ℝ} (hd : 0 < delta)
+theorem amd_closure (B : AMDBox n) (hB : B.Admissible) {delta : ℝ} (hd : 0 < delta)
```

A Python assertion compared the current file byte-for-byte with `git show 865c070d:KAM/Planetary/AMD/Closure.lean` after exactly these two replacements: PASS. No other statement, proof, import, definition or helper changed. `git show --stat bc0955ba` changes only Closure.lean, two insertions and two deletions.

The shared, untracked design contract `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:191` currently declares `amd_closure`. Both public theorem headers, up to `:=`, match that file byte-for-byte; `negativeEnergyDomain`'s definition matches byte-for-byte too. The shared signature file is outside this branch's tracked delta; its historical edit is not certified by commit `bc0955ba`. Its current contents and the implementation agree.

SHA-256 inputs:

```text
Closure.lean: 3125f054727c42690be8968a8d2410d98ced1b42823bebdf4f1525c87de2fb5b
shared P14Signatures.lean: 24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88
```

## Declaration ledger and definitions

Names are in `KAM.Planetary`; private helper names below are their source names.

| Node | Declaration | Verdict | Delta finding |
|---|---|---|---|
| closure(a), domain | `negativeEnergyDomain` | PASS | Unchanged; literal positive-radius, negative-energy set on its whole carrier, including n=0; no fallback. |
| closure(a), cl-a | `element_continuity` | PASS | Unchanged statement and proof; signed type/application probe passes. |
| closure, cl-a/b/c | `amd_closure` | PASS | Only public name changed; signed type/application probe passes; N1 resolved. |
| cl-a | `cl_continuous_planeSq` | PASS | Unchanged private proof. |
| cl-a | `cl_continuous_planeLength` | PASS | Unchanged private proof. |
| cl-a | `cl_continuous_bodyQ` | PASS | Unchanged private proof. |
| cl-a | `cl_continuous_bodyP` | PASS | Unchanged private proof. |
| cl-a | `cl_continuous_len` | PASS | Unchanged private proof. |
| cl-a | `cl_continuous_cross` | PASS | Unchanged private proof. |
| cl-a | `cl_continuousOn_energy` | PASS | Unchanged private proof. |
| cl-b | `cl_pe_facts` | PASS | Unchanged A1 application. |
| cl-b | `cl_le_amd` | PASS | Unchanged nonnegative-deficit sum bound. |

The only def/abbrev/structure is the unchanged `negativeEnergyDomain`. No extra premises, conclusion-shaped hypotheses, altered carriers or new instances appear. A0/A1 consumption and A3 completeness are unchanged. The round-1 proof-route deviations remain: upper action bound rather than upper-minus-delta for the negative energy margin, and the summed-deficit bound rather than `ecc_bound` for positive angular momentum. Neither changes the signed conclusion. The unused `hmargin` remains in the signed telescope.

## Namespace, signatures and axioms

Fresh probe `.lake/abi-scratch/A3Round2Probe.lean` was a module importing `KAM.Planetary.AMD.Closure`. It contained the literal round-1 shadow expression and an additional equality check:

```lean
namespace KAM.Planetary
example (s : Set ℝ) : Set ℝ := closure s
example (s : Set ℝ) : closure s = _root_.closure s := rfl
end KAM.Planetary
```

It also inspected `Lean.getEnv` using the explicitly constructed name `KAM.Planetary.closure`, and raised an error if that declaration existed. This checks the imported environment, including aliases and transitive imports. The check passed; source search found only the new `amd_closure` declaration and no retained old alias. N1 is closed.

The same probe copied both current signed theorem headers under fresh names, proved them by exact applications with all explicit arguments in order (`@amd_closure n B hB delta hd hmargin hAMD` and `@element_continuity n m`), checked `type_of%` equality against each implementation, and proved the domain's literal body by `rfl`. It never imported the admitted signature draft.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A3Round2Probe.lean
exit 0
KAM.Planetary.closure absent from imported environment
'KAM.Planetary.amd_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.element_continuity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An initial scratch harness used a checked name quotation for the intentionally absent declaration, so Lean rejected that quotation as an unknown constant. Replacing it with an explicit `Lean.Name` construction produced the successful absence check above. No production source was changed.

## Build, replay and hygiene

All Lean/Lake invocations were serial, with `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper supplies nice). No resource overrides, clean, cache download, package mutation or git-state changes were used.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-a3 KAM.Planetary.AMD.Closure
exit 0
[inp-gate] slot 2 acquired 16:09:36 for KAM.Planetary.AMD.Closure
⚠ [9099/9099] Replayed KAM.Planetary.AMD.Closure
warning: KAM/Planetary/AMD/Closure.lean:125:5: Variable name `hmargin` is not explicitly referenced.
Build completed successfully (9099 jobs).

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.Closure
exit 0
replaying KAM.Planetary.AMD.Closure
```

The build's diagnostic also suggests removing/renaming the unused binding or disabling its linter. None of those changes was made; the signed telescope remains intact.

Fresh recursive import traversal finds 53 KAM modules including the target; 48 are frozen definitions and all have manifest state SEALED. No provider or frozen theorem is imported. The module remains 227 lines with its copyright, module command, public imports, docstring and exposed public section. Forbidden-token/override/EuclideanSpace scan passes. No other `amd_closure` declaration was found in the planetary sources.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output
git diff --check inp...HEAD
exit 0; no output
```

Repository lint receipt:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
exit 1
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (777 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only lint failure is generated-root staleness, expressly permitted by the audit brief. The generated root was not regenerated. This is the remaining package-level note; the namespace repair itself passes without qualification.

Cleanup and final integrity: removed the audit-owned scratch probe. The only worktree change is this report. Rechecked the implementation and shared-signature hashes above unchanged, checked report whitespace and balanced fences, and reran `git diff --check` successfully. No production, frozen, manifest, generated or other report file was edited.

## Limitations, errata and disposition

No new suspected pinned-source, blueprint or frozen-statement defect was found. The older design table (`P14-LEAN-DESIGN.md:113`) and historical handoff still say `closure`; read these historical names under the explicit orchestrator rename ruling and updated shared signature. This audit did not edit those documents or introduce any implementation deviation. No new pinned-PDF verification or downstream consumer integration is claimed. A3's local PASS does not close AMD confinement or any campaign theorem.
