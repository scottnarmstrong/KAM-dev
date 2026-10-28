# E8 independent package audit 1

Audit date: 2026-10-28. **Overall verdict: PASS WITH NOTES**. Independent checks are recorded below. No mathematical or E8 contract finding. The note concerns the permitted stale generated root; no frozen anchor is sealed by this package.

## Scope and authority

Audited only `KAM/Planetary/Exponential/UniformData.lean`, 167 lines, SHA-256 `40ddbee8b3557e943a013bb47a5c3bc34fcbf6e3280a34af7f00737ee51a4f62`. Comparison: `git diff inp...HEAD`, HEAD `ef224888f9971ffa0cf5ef9d61ad78633234d472`, current inp `e2088d57c609cc20f1033b70a41e064402222f53`. The entire committed delta is this one added file.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, E8-handoff.md and its AUDIT FOCUS, P14 design E8/node rows and proof plan, both P14 design audits (especially F4 and its closure), the revised signature at `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:333`, blueprint `p14a-amd-expsafe.tex:239–245`, graph packet `P-p14a2.nodes.md:799–884`, track-P statement conventions, and consumed definitions/APIs. The user's exact report path overrides the generic brief's MAIN-worktree output instruction.

There is no E8 frozen theorem or provider: the packet explicitly records `FROZEN_FILE: -` and `FROZEN_DECL: -`. Provider/frozen type matching and a frozen seal body are therefore not applicable. This report certifies the ordinary E8 theorem and its two proof steps, not a planetary headline or downstream consumer proof.

## Declaration and graph ledger

Names below are in `KAM.Planetary`; line numbers refer to the audited Lean file.

| Node / role | Declaration or internal proof | Verdict | Evidence |
|---|---|---|---|
| `bpP:p14:uniform-data` | `uniform_data`, L79–163 | PASS | Exact revised signature, including positive radius via UniformData and delta≤pi; source premises only. |
| `stepP:p14:ud-cell` | `udCell_isCompact`, L74–77; `hCc,hCW,hδpos,hδπ,hDW,hDc,hM,hL`, L88–109 | PASS | Full literal conclusion: compact base cell, positive capped radius, compact closed neighborhood inside W, common norm and Lipschitz bounds. Not merely the exported compactness lemma. |
| `stepP:p14:ud-transl` | `hmemC,key,hW'`, L110–156; bounds L157–163 | PASS | Floor shift, normalized center, translated ball in neighborhood, W membership and F equality; norm and Lipschitz bounds transferred. |
| Coordinate helper | `udZero_fst`, L36 | PASS | Fast position component of the zeroed point is zero. |
| Coordinate helper | `udZero_fst_natAdd`, L40 | PASS | Slow position component is unchanged. |
| Coordinate helper | `udZero_snd`, L45 | PASS | Momentum block is unchanged. |
| Translation helper | `udShift_fst_castAdd`, L51 | PASS | Fast position shift is exactly 2πk. |
| Translation helper | `udShift_fst_natAdd`, L55 | PASS | Slow position shift is zero. |
| Translation helper | `udShift_snd`, L59 | PASS | Momentum shift is zero. |
| Auxiliary definition | `udAngle`, L63 | PASS | Literal fast-angle insertion on the whole carrier. |
| Continuity helper | `udAngle_continuous`, L65 | PASS | Joint addition/insertion continuity; no hypotheses. |
| Compactness helper | `udCell_isCompact`, L74 | PASS | Continuous image of compact Icc×Q, even for arbitrary Q not zero-normalized. |

## Fidelity and refutation analysis

The `uniform_data` telescope and conclusion are byte-identical to the revised signatures file (from `theorem uniform_data` through the type, before the proof separator). A fresh independent declaration of that exact telescope, `auditE8Expected`, elaborates using `uniform_data hW hF hWp hFp hQ hQ0 hQW`. Both directions of `example : type_of% @auditE8Expected := @uniform_data` and the converse elaborate. No admitted signature file is imported. This tests binder order, implicit arguments, carriers and the entire conjunction, independently of text comparison.

The source's compact Q in R^(3n) is represented by its zero-fast-angle embedding in Phase(n+n). `hQ0` is typing/representation data, not a new analytic assumption. `hQW` is exactly cylinder inclusion in W. Zeroing is identity on this embedded Q and preserves every non-fast-angle coordinate. All field premises are the blueprint's openness, C1 regularity, domain invariance and periodicity. No hard step is assumed. Witnesses depend only on W,F,Q and the ambient dimension. No planet-count positivity is needed: empty Q and n=0 are harmless, so this is slightly more general than the physical setting.

For `ud-cell`, Lean calls the base cell `C`, whereas the blueprint calls its closed neighborhood `C`. Rename Lean's base cell C0 and neighborhood D for comparison: C0 is exactly image([-π,3π]^n×Q), `hCW` proves C0⊆W, δ=min(δ₀,π)>0, D=cthickening δ C0⊆W, and `hDc` establishes compactness in the finite-dimensional max-norm phase space. `KAM.ODE.gen_lip` supplies bounds on all of D. There is no compactness claim about the full unbounded fast cylinder.

For `ud-transl`, k_i=floor(x_i/(2π)). L129–132 establish k_i·2π≤x_i<(k_i+1)·2π, hence the literal normalized range 0≤x_i−2πk_i<2π; the proof uses its weaker [-π,3π] consequence to put the center in C0. Slow coordinates and momenta, and therefore the zeroed Q point, are unchanged. `mem_cthickening_of_dist_le` and `dist_sub_right` prove the entire translated δ-ball is in D. The blueprint's ball-translation equality is implemented pointwise by subtraction/addition cancellation and translation isometry; there is no missing geometric cut requiring another public export. `hWp` and `hFp` are applied at the translated point already known in W. The Lipschitz estimate uses the same k for both points in a given ball, with `edist_sub_right`, so no discontinuity of the floor map is relevant. The radius cap is explicitly constructed and returned; the distance-to-center argument actually works without using that cap beyond choosing δ.

## Definition classification and hygiene

The only new definition is `udAngle lam = (Fin.append lam 0, 0)`: the intended fast-angle vector for every input, exposed by the public expose section, with no fallback or junk branch. There are no new abbrevs, structures, instances, or bundled assumptions. Local sets C and cthickening δ C and floor k have their literal intended meanings.

Static recursive traversal found 67 local KAM modules, including 48 frozen definition anchors, all SEALED; no provider and no frozen theorem input, direct or transitive. Existing ordinary dependencies were inspected as suppliers, not re-audited as new package code. The file is a proper public Lean module with copyright, module declaration, public imports, docstring and exposed public section. All ten declaration short names occur as declarations only in this file throughout KAM. No root-level declaration or shadow is introduced. No forbidden tokens, EuclideanSpace, resource overrides, or file-size violation were found.

## Verification receipts

All Lean/Lake commands from this audit were sequential, under `LEAN_NUM_THREADS=1` and `nice -n 5` (the compile wrapper supplies nice). No library rebuild from scratch, package-cache mutation, generated-root update, or state-changing git command was performed.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e8 KAM.Planetary.Exponential.UniformData` — exit 0. Output includes `[inp-gate] slot 2 acquired 18:08:05 for KAM.Planetary.Exponential.UniformData` and `Build completed successfully (9113 jobs).` Replayed pre-existing unused-variable warnings: Kepler/Energy L106 (hm,hκ), Poincare/Chart L212,L247 (hm,hκ), Kepler/Mass L147,L157 (hκ), L500 (hw), L524 (hm,hκ). No warning from the audited file.
2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E8Audit1.lean` — exit 0. Exact signature checks passed. All requested axiom output follows:

```text
'KAM.Planetary.udZero_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.udZero_fst_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.udZero_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.udShift_fst_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.udShift_fst_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.udShift_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.udAngle_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.udCell_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.uniform_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.udAngle' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.UniformData` — exit 0. Complete output:

```text
replaying KAM.Planetary.Exponential.UniformData
```

This single invocation covers the package's only new module, including all helpers; there is no provider module to add.

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` — exit 1 solely for the expressly permitted stale generated root. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (822 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module checks, frozen-anchor guard and all 144 frozen ABI hashes pass. No source lint finding in E8. The generated root is intentionally unchanged.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` — exit 0, empty output. `git diff --check` — exit 0, empty output. New-name declaration scan: exactly one declaration occurrence per new short name; file line count 167; forbidden-token scan empty.

## Uncertainties, errata and deviations

No suspected E8 blueprint or pinned-source defect; no mathematical deviation. Design-audit F4 is implemented and closed. This is a local proof/contract audit, not a fresh pinned-PDF audit. No downstream theorem closure is inferred. Both internal graph rows are complete under the handoff's explicit policy allowing inline proofs; no separately exported translation theorem is required. The generated-root exception is recorded above and left for the orchestrator. Only this report persists; temporary audit probes/logs are removed.
