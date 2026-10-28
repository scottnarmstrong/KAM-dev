# A3 independent package audit 1

**Overall verdict: PASS WITH NOTES.** The A3 implementation is complete and its signed statements are proved. There is a confirmed namespace compatibility finding (N1); resolve the naming policy through a design note before broad integration. No frozen anchor is seal-ready on the strength of A3 alone.

Audit date: 2026-10-28. Scope: only `KAM/Planetary/AMD/Closure.lean`, package A3 of P14 (tracks I/N/P campaign). This is an infrastructure audit; A3 contains no provider and proves no frozen anchor directly.

## Inputs and scope

- Worktree: `/root/code/KAM-inp-p14-a3`; HEAD `865c070da1367fa43c5541643392fe2990b308eb`; comparison `inp` at inspection: `5efa28d3bf58caf43e0c7e810e9c642396381cf7`.
- `git diff inp...HEAD`: one added file, `KAM/Planetary/AMD/Closure.lean`, 227 lines. SHA-256 `504d31860f8b5cc5dbb2b3dd03d9096add3c67d235b9bbafd3a91a4dcbad82b9`.
- Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local A3 handoff and its AUDIT FOCUS, P14 design row A3 and Appendix A, both P14 design audits, blueprint `p14a-amd-expsafe.tex` lines 93–104, track-P statement, relevant frozen definitions and the frozen `AmdConfinement` target.
- Signed source: `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, SHA-256 `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`; design SHA-256 `a283ad509cb312a6c3ea06b6d94ce031903d7d05a5604d23553c17b9b7050ef7`. These match the revision-2 audit inputs.
- The user's exact local output path overrides the generic brief's MAIN-worktree destination. Existing untracked `A3-handoff.md` was preserved. No production, frozen, manifest, generated-root or git-state edits were made. Temporary probes were confined to `.lake/abi-scratch/`.

## Declaration and node ledger

All names below are in `KAM.Planetary`; private names are implementation helpers.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| p14:closure(a), domain | `negativeEnergyDomain` | PASS | Definition byte-identical to signed source; exactly all positive radii and negative Kepler energies. |
| p14:closure(a), cl-a | `element_continuity` | PASS | Signed telescope exactly preserved modulo whitespace. Openness and action/AMD continuity on the full domain, for arbitrary fixed masses. |
| p14:closure, cl-a/b/c | `closure` | PASS WITH NOTES | Exact signed telescope; outer openness and sequential collar closure proved. Naming compatibility finding below. |
| cl-a, polynomial | `cl_continuous_planeSq` (private) | PASS | Finite sum of coordinate squares is continuous. |
| cl-a, radius | `cl_continuous_planeLength` (private) | PASS | Square root composed with planeSq. |
| cl-a, projection | `cl_continuous_bodyQ` (private) | PASS | Position coordinate projections. |
| cl-a, projection | `cl_continuous_bodyP` (private) | PASS | Momentum coordinate projections. |
| cl-a, radius | `cl_continuous_len` (private) | PASS | Composition of the preceding maps. |
| cl-a, momentum | `cl_continuous_cross` (private) | PASS | Polynomial cross product, continuous everywhere. |
| cl-a, energy | `cl_continuousOn_energy` (private) | PASS | Radius denominator nonzero on the stated positive-radius carrier; mass is fixed. |
| cl-b, A1 use | `cl_pe_facts` (private) | PASS | Projects positive action, energy identity and nonnegative deficit from `elements i (hp i)`. |
| cl-b, sum | `cl_le_amd` (private) | PASS | Each nonnegative action deficit is bounded by their finite sum, the literal physicalAMD. |

The A3 slice is complete: its sole new definition and both public theorems are accounted for. A0 supplies the literal outer/collar definitions; A1 supplies elements. There are no added premises, instances, constants with enlarged dependence or conclusion-shaped assumptions. Continuity is split into the companion public theorem exactly as assigned by the design. No provider/frozen-type seal probe applies: A3 is not a provider package and must not seal `amdConfinement`.

## Definition classification and proof review

`negativeEnergyDomain` (line 68) is the only new def/abbrev/structure. It is a literal set predicate on `Phase (n*2)`, with no defaults, selected branches or fallback values. Its body is intended on its entire carrier, including n=0. The theorem's arbitrary fixed masses do not cause a continuity defect: division by the fixed mass in energy is a scalar constant even at zero; variable denominators are guarded by positive radius and negative energy. No physical interpretation of a zero-mass orbit is asserted.

For outer openness (lines 137–160), the proof rewrites the literal low-AMD region as a finite intersection of domain, positive cross-product, open action-interval and AMD-sublevel conditions. Admissibility supplies positive masses in the reverse membership implication.

For sequential closure (lines 161–227), `elements` gives nonnegative deficits and `E_i=-m_i^3/(2 Lambda_i^2)`. The collar gives a uniform negative energy bound using the looser upper action bound `B.upper i`. Each deficit is at most total AMD, yielding the cross-product lower bound

```text
C_i >= B.lower i - (B.initialAMD + n*delta) + delta > 0.
```

Strict positivity follows from admissibility's low-AMD bound, nonnegative square root and hAMD. Continuous energy and cross product pass these uniform bounds to the positive-radius limit first; only then are action and AMD continuity used there. The proof never evaluates an unguarded limit through the singular energy denominator. The final strict action bounds follow from delta>0 and the AMD bound from hAMD.

This changes the internal route of blueprint cl-b (line 102): it uses upper rather than upper-minus-delta in the energy margin, and the summed-deficit estimate rather than `ecc_bound` for positive angular momentum. Both suffice for the exact parent contract; no A2 dependency is needed. These are proof-route deviations, not weakened statements or source errata. `hmargin` is unused and retained to preserve the signed telescope; it is a redundant source premise, not an added premise.

## Verification receipts

All Lean/Lake commands were serial within this audit, with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource-budget override was used. Static/read-only inspection was allowed while waiting. The initial gated build request waited without starting Lake and was canceled (exit 143) solely to permit serial probes against the existing build; the completed targeted-build receipt is below.

1. **Fresh signed-type/application probes:**

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A3Signatures.lean
exit 0
'KAM.Planetary.closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.element_continuity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The probe copied both signed theorem headers under fresh names and proved them by exact applications of the implementation with all explicit binders in order (and explicit implicit n/delta through `@`). It then checked `example : type_of% @audit_name := @KAM.Planetary.name` for both. A separate rfl example checked the domain's literal body. This establishes the implementation's full type equality to the signed contracts, without importing or trusting the admitted design file. Header comparison independently returned True for both statements; definition byte comparison returned True.

2. **Kernel replay:**

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.Closure
exit 0
replaying KAM.Planetary.AMD.Closure
```

One invocation covers the sole new module, including its private implementation lemmas; no additional lemma module was added by A3.

3. **Import and static checks:** recursive traversal of KAM imports found 53 KAM modules, including 48 frozen modules, all manifest state SEALED and all definitions. No provider import and no frozen theorem import (hence no DRAFT_SORRY import). No new public name pre-exists elsewhere in KAM; topological-name shadowing is separately reported as N1. No forbidden escape, override or EuclideanSpace token occurs in the new source. Module header, interface imports, docstring and exposed public noncomputable section are present; 227 lines is below the cap. No new instances or nonstandard ambient types.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output

git diff --check inp...HEAD
exit 0; no output
```

4. **Repository lint:**

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
exit 1
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (777 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole lint failure is the generated-root staleness explicitly allowed by the audit brief. No generated root was regenerated.

5. **Targeted build:**

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-a3 KAM.Planetary.AMD.Closure
exit 0
[inp-gate] slot 1 acquired 15:58:48 for KAM.Planetary.AMD.Closure
⚠ [9099/9099] Replayed KAM.Planetary.AMD.Closure
warning: KAM/Planetary/AMD/Closure.lean:125:5: Variable name `hmargin` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmargin

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9099 jobs).
```

The wrapper runs `nice -n 5 lake build` under the required shared compile gate. The reported unused hmargin warning is consistent with the proof review and does not change the signed interface. No linter option was set by this audit.

6. **Cleanup and final integrity:** removed all audit-owned A3 probe sources, import inventory and logs under `.lake/abi-scratch/` after incorporating receipts here. Final report has balanced code fences, no trailing whitespace and no pending placeholders. Source SHA-256 was rechecked unchanged; `git status --short` contains only the new audit report and the pre-existing untracked handoff. No git-state mutation occurred.


## Compatibility finding and disposition

**N1 — Medium: `KAM.Planetary.closure` shadows topological closure.** Implementation line 124 and signed design line 714 introduce the short name `closure` in `KAM.Planetary`. This is a defect in the chosen interface name, not a discrepancy between implementation and signed signature.

Three fresh probes used exactly this body, with the indicated import and expression:

```lean
import KAM.Planetary.AMD.Closure
namespace KAM.Planetary
example (s : Set ℝ) : Set ℝ := closure s
end KAM.Planetary
```

| Import | Expression | Exit | Result |
|---|---|---|---|
| `KAM.Planetary.AMD.Setting` | `closure s` | 0 | Baseline topological closure resolves. |
| `KAM.Planetary.AMD.Closure` | `closure s` | 1 | Resolves to the AMD theorem and fails. |
| `KAM.Planetary.AMD.Closure` | `_root_.closure s` | 0 | Qualification restores topological closure. |

Exact failing output:

```text
.lake/abi-scratch/A3ShadowAfter.lean:3:39: error: Application type mismatch: The argument
  s
has type
  Set ℝ
but is expected to have type
  AMDBox ?m.1
in the application
  closure s
```

Each ran as `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A3Shadow{Before,After,Qualified}.lean`, separately and serially (the braces here abbreviate three actual filenames). It fails by deterministic local-name resolution, not ambiguity. An example of existing topological syntax that becomes fragile if A3 is imported is `KAM/Planetary/PGAssembly/ExtensionTube.lean:122` (`z ∈ closure (cylinder V r ...)`); this audit does not claim its present import chain already includes A3.

**Recommendation:** rename the AMD theorem through an explicit design note, for example to `amd_closure`, updating the signed interface and consumers together. Do not retain an alias named `KAM.Planetary.closure`, which preserves the problem. Alternatively a deliberate keep decision must require `_root_.closure` for topology in affected namespace scopes. No rename was performed. The existing signed contract and the elementary proof remain valid, so this is recorded as PASS WITH NOTES, not a mathematical counterexample.


## Limitations and errata

No suspected pinned-source or frozen-statement defect was found in the audited slice. This audit checks the local elementary proof against the signed design and blueprint; it makes no new independent pinned-PDF claim. A3 alone does not close the AMD confinement theorem, the P14 campaign, or any frozen anchor. Upstream default-resource release gates and the N-root proof gap discussed by design audit 2 remain outside A3.
