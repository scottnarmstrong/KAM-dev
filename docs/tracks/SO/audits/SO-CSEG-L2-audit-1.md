# Independent audit SO-CSEG-L2 — audit 1

Date: 2026-10-30. Worktree: `/root/code/KAM-inp-csegl3`.
Audited HEAD: `0cd3651565c7a7bd0f16b3a2f187c23c1bea473c`.
Compared branch `inp`: `5023c2eb1a0a41c2e0c52e0cf78545d149d98a49` at the initial comparison.
Method: independent, refute-first, report/scratch only; no repairs, commits, root regeneration or dependency changes.
The prompt's exact report destination overrides the generic brief's main-worktree destination.

## Verdict and scope

**PASS WITH NOTES for SO-CSEG-L2 (M2 computation and assembly infrastructure).**
All 12 specified theorem statements match the audited design; the one specified definition matches literally.
The additional reconstruction helper is sound. Both modules build, all 34 new public theorems have allowed
axioms, and both modules pass kernel replay. No frozen anchor is implemented or sealed by this package;
provider/frozen-type probes and seal-body checks are therefore N/A. This is not an I/N/P theorem-closure verdict
or certification of lunar data. Production-scale R7 remains a CAL-2 obligation.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external inp-audit-package.md brief, the named handoff
including AUDIT FOCUS, SO-CSPLIT §3.4/§8/R7, and SOCsplitSignatures §E plus the four relevant §F bridges.
The SO design and landed checker bodies are the direct source for these computational helpers; unrelated
I/N/P frozen statements and literature blueprints are not their specification.

The complete `git diff inp...HEAD` contains only four additions: the two Stage modules (208/203 lines),
`.drafts/handoff-SO-CSEG-L2.md` (85 lines), and the named handoff (100 lines). Both handoffs and all changed Lean
bodies were inspected. No landed declaration changes. Protected-path diff, including KAM/Root, is empty.

## Findings and production fitness

1. **No semantic blocker.** `modelMatMul_eq_of_entries` requires exactly r rows and c columns of M. Its helper
   reconstructs only valid in-bounds entries; zero/default lookup behavior cannot discard malformed extra rows.
   No shape premise on A/B is invented: this is equality of the existing total computation, not an enclosure claim.
   `gramModels_eq_of_entries` checks both index bounds. For a > b it applies h to b,a using
   `Nat.le_of_not_le`; it does not assume mathematical symmetry of key-dependent computations. A separate
   dimension-two probe confirmed entry (1,0) is E 0 1.
2. **Usable M2 assembly, with explicit arguments.** Entry theorems assemble matrices, Gram defect rows assemble
   the exact Gram result, torsion stages reconstruct the bordered matrix, and the four bridges reach the landed
   checkGram/checkTorsion/checkFrameT/checkFrameN Bools. Keys, dimensions, cfgLow, sigma-minus-mu margins,
   frequency scaling, Omega/negation placements, and downward thresholds are preserved. Stage premises are
   deliberately conditional computational equalities; fixtures supply them. They are not a substitute for
   proving a certificate's stages. No additional logical bridge is missing for this scoped M2 chain.
3. **R5/R7 limitation, independently observed.** An initial audit-only probe using
   `apply torsionModels_eq_of_stages <;> assumption` and the analogous frameN application timed out at whnf
   under the default 200000 heartbeats (scratch lines 71/77). Explicit applications with all ordinary arguments
   and all stage proofs succeeded at default settings, with no budget override. Production generators must use
   the explicit instantiation prescribed by SO-CSPLIT R5. This is an elaboration design signal for inference-heavy
   applications, not a failure of the landed explicit proofs. No production-scale cost conclusion follows.
4. **Literal wording caveat for “no simp over a landed body.”** The torsion proof uses unfold/rw, not simp.
   The Gram/frame/Bool bridges use the design's restricted simp-only lists. The added structural helper at
   Kernel/Stage:57 does use ordinary `simp [modelMatrixEntry, ...]` on the landed lookup body, after extensionality
   and proven bounds. Thus a blanket prohibition on *any* simp on *any* landed definition is not literally met;
   the substantive requirement to avoid simplifying heavy checker arithmetic is met. No heavy body is decided
   by this helper. This small extra proof is not verbatim design code and should remain visible to reviewers.
5. **Tests are limited fixtures.** Products carry nonzero radii; staged and monolithic results agree exactly.
   Gram/torsion use n=1 and mostly empty/zero data. They do not exercise the lower triangle, nontrivial truncation,
   packed advice, or certificate-level corner residuals. The generic proofs cover those carriers, but production
   templates still need actual stage proofs, SO-CSEG-A equality reflection, L3 product splitting and CAL-2/G7
   measurement with production imports. Gram-entry/BG-entry product splitting and separate add/transpose/Omega
   rewrites are emitter work; this file does not supply named convenience lemmas for every such subterm.
6. **Documentation counts.** Handoff:65 says “13 stage premises”; there are 15: radius, composition, L, Gi, DL,
   and ten products [4,0]–[4,9]. Handoff:49's “11 Stage theorems ... [plus helper]” undercounts the actual 13
   production theorems including the helper. These are reporting defects, not signature or proof defects.
   The prior short-name collision is no longer reproduced (fresh checker exit 0).

## Declaration-by-declaration review

Names below are in `KAM.Certificate`; line locators are relative to `KAM/CertificateSharp/`.
Every theorem row passed the axiom probe; every source-specified production theorem also passed a fresh
application at the independently copied design type.

| Node | Declaration | Verdict | Reason / note |
|---|---|---|---|
| M2 §E | `matMulEntry` (Kernel/Stage:36) | PASS | Literal modelMatMul entry; degree 0, sum order and key ++ [i,j,k] unchanged. |
| M2 §E | `modelMatMul_eq_buildMat` (Kernel/Stage:42) | PASS | Definitional equality (rfl). |
| M2 extra helper | `buildMat_modelMatrixEntry` (Kernel/Stage:47) | PASS | Additional helper; exact rectangular shape prevents reliance on missing-entry defaults. |
| M2 §E | `modelMatMul_eq_of_entries` (Kernel/Stage:59) | PASS | Both dimensions required; nested map congruence and reconstruction give exact list equality. |
| M2 §E | `matMulEntry_eq_of_products` (Kernel/Stage:70) | PASS | Replaces each bounded product under List.ofFn; retains toDeg and modelSum. |
| M2 §E | `gramModels_eq_of_entries` (Kernel/Stage:81) | PASS | Upper-triangular premises only; lower triangle uses E b a and b ≤ a. |
| M2 §E | `gramDefectRows_eq_of_entries` (Kernel/Stage:94) | PASS | Explicit congrArg crosses the List.ofFn and sumUp binders without evaluating products. |
| M2 §E | `gramCheck_eq_of_rows` (Kernel/Stage:110) | PASS | Retains shape gate, all bounds, maxima, and failure branch. |
| M2 §E | `torsionModels_eq_of_stages` (Kernel/Stage:123) | PASS | All 15 premises and keys [4,0] through [4,9] match landed dependency order. |
| M2 §E | `frameNModels_eq_of_stage` (Kernel/Stage:157) | PASS | Reuses L, Gi and torsion product [4,0], retaining Omega. |
| M2 §F | `checkGram_of_gramCheck` (Kernel/Stage:168) | PASS | Successful exact Gram equation implies landed Bool. |
| M2 §F | `checkTorsion_eq_of` (Kernel/Stage:174) | PASS | Exposes landed torsionAvgCheck with original sigmaT - mu. |
| M2 §F | `checkFrameT_eq_of` (Kernel/Stage:182) | PASS | Exposes landed torsion-block row corners, preserving n and rounding direction. |
| M2 §F | `checkFrameN_eq_of` (Kernel/Stage:192) | PASS | Exposes both N row and transpose-column corner checks and both bounds. |
| M2 toy | `stageW` (Tests/Stage:47) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stagePi` (Tests/Stage:49) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageCfg` (Tests/Stage:52) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageK` (Tests/Stage:61) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageH` (Tests/Stage:64) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageB` (Tests/Stage:66) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageWit` (Tests/Stage:68) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageBox` (Tests/Stage:70) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageC` (Tests/Stage:73) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageO` (Tests/Stage:76) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageA` (Tests/Stage:80) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stageBm` (Tests/Stage:82) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stage_product0` (Tests/Stage:84) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_product1` (Tests/Stage:89) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_entry` (Tests/Stage:95) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_matMul` (Tests/Stage:106) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_matMul_whole` (Tests/Stage:114) | PASS | Independent monolithic kernel computation of the same result as the staged recipe. |
| M2 toy | `stage_gramEntry` (Tests/Stage:121) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_gramModels` (Tests/Stage:124) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_gramBG` (Tests/Stage:131) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_gramRows` (Tests/Stage:135) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_gramCheck` (Tests/Stage:145) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_gramCheck_whole` (Tests/Stage:149) | PASS | Independent monolithic kernel computation of the same result as the staged recipe. |
| M2 toy | `stageT` (Tests/Stage:156) | PASS | Literal fixture; definition classification below. |
| M2 toy | `stage_eps` (Tests/Stage:158) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_ms` (Tests/Stage:160) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_L` (Tests/Stage:165) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_Gi` (Tests/Stage:168) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_DL` (Tests/Stage:170) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_N0` (Tests/Stage:174) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_torsion` (Tests/Stage:178) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_torsion_whole` (Tests/Stage:189) | PASS | Independent monolithic kernel computation of the same result as the staged recipe. |
| M2 toy | `stage_frameN` (Tests/Stage:195) | PASS | Kernel-proved stage or composition of generic lemmas with proved literal stages. |
| M2 toy | `stage_frameN_whole` (Tests/Stage:199) | PASS | Independent monolithic kernel computation of the same result as the staged recipe. |
| M2 toy instance | `DecidableEq CC` (Tests/Stage:41–43) | PASS | Structural derived equality, confined to test import closure. |
| M2 toy instance | `DecidableEq CertPoly` (Tests/Stage:41–43) | PASS | Structural derived equality, confined to test import closure. |
| M2 toy instance | `DecidableEq CertModel` (Tests/Stage:41–43) | PASS | Structural derived equality, confined to test import closure. |

## Definitions and inputs

There are no new abbrevs, structures, predicates packaging analytic assumptions, or selected witnesses.
`matMulEntry` is a literal definition on all natural-number indices, with exactly the existing modelMatMul
entry semantics, including existing missing-entry semantics. Its body is byte-identical to signatures:551–555;
`modelMatMul_eq_buildMat` is rfl. All other new defs are test literals or explicit constructors:
`stageW`, `stagePi`, `stageCfg`, `stageK`, `stageH`, `stageB`, `stageWit`, `stageBox`, `stageC`, `stageO`,
`stageA`, `stageBm`, `stageT`. In particular, stageCfg's `none` is the intended direct-arithmetic fixture
configuration and stageO is intentionally empty, not a fallback for an unproved analytic object.

For each of these 14 definitions:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

The three derived equality instances are structural decision procedures, not assumptions of mathematical
results. They are not imported by production code in this snapshot. Production Stage has no DecidableEq or
LawfulCertArith hypothesis: only the intended CertArith operations are needed for computation equality.
All ambient binders are typing/data: α : Type, CertArith α, natural dimensions and indices, concrete checker
inputs, and the literal-result parameters. No analytic norms, constants or quantifiers are weakened. Every
logical production input is expanded below (the cited design is the source for these conditional helpers).
No STANDING/RULED/EXCESS logical premise is present. Test theorems have no logical inputs.

| Expanded logical binder | Bin | Authority / meaning |
|---|---|---|
| `buildMat_modelMatrixEntry.hrows` | SOURCE | rectangular-list reconstruction at Stage:47–49; literal shape/stage equation, not an analytic conclusion. |
| `buildMat_modelMatrixEntry.hcols` | SOURCE | rectangular-list reconstruction at Stage:47–49; literal shape/stage equation, not an analytic conclusion. |
| `modelMatMul_eq_of_entries.hrows` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `modelMatMul_eq_of_entries.hcols` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `modelMatMul_eq_of_entries.h` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `matMulEntry_eq_of_products.h` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `gramModels_eq_of_entries.h` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `gramDefectRows_eq_of_entries.h` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `gramCheck_eq_of_rows.hshape` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `gramCheck_eq_of_rows.hrows` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.heps` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hms` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hL` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hGi` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hDL` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hN0` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hDG1` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hDG2` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hDGi0` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hDGi1` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hDN1` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hDN2` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hXN1` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hTb` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `torsionModels_eq_of_stages.hY` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `frameNModels_eq_of_stage.hL` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `frameNModels_eq_of_stage.hGi` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `frameNModels_eq_of_stage.hN0` | SOURCE | signatures §E, lines 557–653; literal shape/stage equation, not an analytic conclusion. |
| `checkGram_of_gramCheck.h` | SOURCE | signatures §F, lines 678–715; literal shape/stage equation, not an analytic conclusion. |
| `checkTorsion_eq_of.hg` | SOURCE | signatures §F, lines 678–715; literal shape/stage equation, not an analytic conclusion. |
| `checkTorsion_eq_of.ht` | SOURCE | signatures §F, lines 678–715; literal shape/stage equation, not an analytic conclusion. |
| `checkFrameT_eq_of.hg` | SOURCE | signatures §F, lines 678–715; literal shape/stage equation, not an analytic conclusion. |
| `checkFrameT_eq_of.ht` | SOURCE | signatures §F, lines 678–715; literal shape/stage equation, not an analytic conclusion. |
| `checkFrameN_eq_of.hg` | SOURCE | signatures §F, lines 678–715; literal shape/stage equation, not an analytic conclusion. |
| `checkFrameN_eq_of.he` | SOURCE | signatures §F, lines 678–715; literal shape/stage equation, not an analytic conclusion. |
| `checkFrameN_eq_of.hM` | SOURCE | signatures §F, lines 678–715; literal shape/stage equation, not an analytic conclusion. |

Logical input counts: SOURCE 36, STANDING 0, RULED 0, EXCESS 0. Typing/data binders are separate from these logical inputs.

## Independent validation

All Lean-bearing commands were serialized by this auditor with LEAN_NUM_THREADS=1. Builds used the required
compile gate; each gate invokes nice -n 5 lake build. There was no clean/full rebuild or cache/dependency mutation.
Replayed dependency warnings were outside both new files.

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-csegl3 KAM.CertificateSharp.Kernel.Stage
# exit 0: Build completed successfully (3267 jobs).
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-csegl3 KAM.CertificateSharp.Tests.Stage
# exit 0: Built KAM.CertificateSharp.Tests.Stage (3.5s)
# Build completed successfully (3268 jobs).
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/CsegL2Audit.lean
# initial inference-heavy probe exit 1: two default-heartbeat whnf timeouts; see finding 3.
# revised explicit-argument probe exit 0, no diagnostics.
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.CertificateSharp.Kernel.Stage KAM.CertificateSharp.Tests.Stage
# exit 0:
# replaying KAM.CertificateSharp.Tests.Stage
# replaying KAM.CertificateSharp.Kernel.Stage
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-csegl3 KAM.CertificateSharp.Kernel.Stage KAM.CertificateSharp.Tests.Stage
# exit 0: short-name check OK (no reused public short name)
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md
# exit 0, empty output
git diff inp...HEAD --check
# exit 0, empty output
```

Signature check: extract each theorem header from the design and production source up to `:=`, remove
whitespace only, and compare: 12 HEADER_MATCH, no mismatch; matMulEntry BODY_MATCH (raw bytes).
The successful probe copies all 12 design headers to fresh theorem names and applies the corresponding
production theorem with explicit arguments/proofs. It also checks the dimension-two lower-triangle entry.
Scratch imports only the test module, opening the same namespaces and typing variables; it imports no design
module or its provisional proofs. Probe and profiling files are removed after checks.

Pinned SHA256 values:

```text
SOCsplitSignatures.lean 42e25f3f5904e40af5ba7b6d01bfd7c741b41578539aa9a23e98705593e199e9
Kernel/Stage.lean       f43ec6b247bb0ab3754ba4bb070178d81575bdac808c083ed58cad4ef50e8414
Tests/Stage.lean        15230d7660710a8842f1e76e0e453a5e5a6c90365c15bc01f3b390d39c2719f9
```

### Exact axiom output

Generated `#print axioms` for every theorem declared in both changed modules, not just the handoff subset:

```text
'KAM.Certificate.modelMatMul_eq_buildMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.buildMat_modelMatrixEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelMatMul_eq_of_entries' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.matMulEntry_eq_of_products' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.gramModels_eq_of_entries' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.gramDefectRows_eq_of_entries' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.gramCheck_eq_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsionModels_eq_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.frameNModels_eq_of_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkGram_of_gramCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorsion_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkFrameT_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkFrameN_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_product0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_product1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_matMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_matMul_whole' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_gramEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_gramModels' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_gramBG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_gramRows' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_gramCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_gramCheck_whole' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_ms' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_L' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_Gi' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.stage_DL' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_N0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_torsion_whole' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_frameN' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.stage_frameN_whole' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Lint and timing

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
# exit 1, solely the allowed generated-root exception:
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/CertificateSharp.lean)
check_lean_modules: PASS (1690 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

Both files have copyright/module/public imports/module docstrings/exposed public sections. They contain no
forbidden proof escape or resource override; module lengths are 208 and 203, maximum line width 99 each.
The independent fresh count is 1690 Lean files (the handoff's earlier count was 1688). Root staleness is left
for the orchestrator exactly as authorized; the audit did not regenerate it.

Fresh toy timing command (exit 0):

```sh
# Exact Tests/Stage source copied to scratch, with no import of Tests/Stage itself:
LEAN_NUM_THREADS=1 nice -n 5 lake env lean -Dprofiler=true .lake/abi-scratch/CsegL2Profile.lean
```

Selected exact profiler output:

```text
import took 3.54s
type checking took 190ms
type checking took 112ms
type checking took 286ms
type checking took 300ms
type checking took 113ms
	blocked (unaccounted) 16.4s
	elaboration 388ms
	import 3.54s
	tactic execution 359ms
	type checking 3.29s
```

This run gives 3.29 s cumulative type checking and an individual reported interval of 1.28 s, so it does
not reproduce the handoff's 1.1–1.5 s / no declaration above 0.5 s timing claim. Profiler intervals are
unnamed here; they do not identify a slow residual or isolate staged-versus-whole cost. The typechecking
and replay results establish correctness of the fixtures; cheap residuals at production scale remain
unestablished by this audit. CAL-2/G7 is still required. No timing option was added to source files.


## Errata, deviations, and closeout

No suspected pinned mathematical-source or blueprint falsehood found. The design's “stated, sorry” entries
are specifications whose proofs this package supplies, not production proof holes. Retain the documentation
count corrections and the narrow simp wording caveat above. The only implementation addition beyond the
specified declarations is buildMat_modelMatrixEntry; the four §F bridges are placed in Stage as disclosed.
No deviation introduced by this audit. Only this report is a repository edit; temporary probes are deleted.
No frozen files, manifests, generated roots, README or source modules were changed.
