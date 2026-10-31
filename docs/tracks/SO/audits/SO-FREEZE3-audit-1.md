# SO-FREEZE3 independent identity audit 1

Date: 2026-10-31. Worktree: `/root/code/KAM-inp-sodata3`.
Audited committed HEAD: `1e0e888c1f45c141fa32f184b68a6e8c91c16377` (`inp-sofreeze3`).
Comparison: `git diff inp...HEAD`, with inp and merge base both `9517d71e792b9580977ef388b0c4a1f2b248bf87`.
The user's exact report destination overrides the generic brief's main-worktree destination.

## Verdict and boundary

**PASS WITH NOTES for the requested declaration-identity audit, for each of the thirteen anchors.** Independently compared complete source bodies match the approved snippets after exactly the listed literal substitutions and D-SOF-5/6 formatting/proof-body deviations. This includes the complete B/window wrappers, not merely their declaration substrings. Manifest hashes, closures, states, identities and the unchanged 158 existing entries pass.

**Approval-date provenance is UNVERIFIED. Full Phase A is INCOMPLETE at the audited commit; no theorem is seal-ready or proved.** The three theorem exports are manifested `DRAFT_SORRY`, their providers contain no export, and Q11 is absent from this commit. This audit does not approve a seal or a completed Phase A. The identity-check script also has two confirmed false-acceptance/exit-status defects, reported below; its output alone is insufficient evidence.

Read: AGENTS.md, PLAN, DECISIONS, the supplied generic package-audit brief, SO-FREEZE3-handoff.md, FREEZE.md, both freeze proposals, the SO-FREEZE3 implementation brief, all thirteen frozen files, all three provider stubs, the manifest delta, and all four new freeze-tool/input files. SO's approved proposals and the specific identity focus control this audit; unrelated I/N/P theorem anchors are not its source contract. No source-literature theorem audit or Phase B proof audit is claimed.

## Findings

### F1 — approval date cannot be confirmed; ruling references need a durable locator

Every new manifest `author_approval.approved_at`, every added frozen module docstring, and `docs/tracks/SO/freeze/cfg.json:4` say `2026-10-31`. The branch's DECISIONS records D40 on **2026-10-30**, but contains neither D46 nor D48. Inspected main `5d13118ad89e2545b5a6140f1d4f424786bcd43e` and current inp likewise provide no D46/D48 entry. FREEZE.md:90–92 expressly acknowledges the unverified date.

The supplied implementation brief `/root/code/KAM-inp/.drafts/briefs/offload-main/SO-FREEZE3.md`, “Authority” and “Final literals”, explicitly states that D46 fixed 2.755% and waived rule B's tightness clause, and that D48 was the owner's “yes freeze these numbers”. It lists all final literals. This is sufficient supplied task authority for comparing those literals; the previous SO-DATA3 rule-B tightness finding is not carried forward as an unresolved numerical objection here. **That brief does not date either ruling.** A current date, commit date, or generation timestamp does not establish the approval date.

Disposition: the literal/text comparison passes relative to the supplied authority; `approved_at = 2026-10-31` is **not confirmed**, and the manifest reference `docs/DECISIONS.md D40, D46, D48` is not fully resolvable in the audited repository. Before treating the metadata as final, record the actual dated approvals or an authoritative dated reference. If the date differs, the owner/orchestrator must handle the affected frozen bytes and hashes under the frozen-file policy. The auditor made no such edits and does not substitute 2026-10-30 by inference.

### F2 — `check_identity.py` is not a fail-closed identity gate

Two concrete defects in `docs/tracks/SO/freeze/check_identity.py`:

1. **Lines 60–62:** B and window use `sub(blk) in ...`, a substring test. It accepts extra commands or a changed wrapper outside the retained declaration. This does not establish the requested whole-wrapper identity.
2. **Line 63 / end of script:** it prints `MISMATCH` on failure but never returns a failing exit status. A shell/CI command can therefore succeed when it has detected nonidentity.

Confirmed with a scratch Python harness that mocks `Path.read_text` for the window file; it never writes or regenerates frozen sources:

```
virtual append: public def audit_extra : Nat := 0
  ALL IDENTICAL; exit 0
virtual replacement: lunarPLo < lunarPHi :=  ->  lunarPLo ≤ lunarPHi :=
  MISMATCH; exit 0
```

**Tool verdict: FAIL as an automated acceptance gate.** The checked-in files themselves do not contain either mutation. This audit compensates with independent full-file equality for all thirteen files, including B/window imports, visibility, namespace/section closings, proof/suffix markers, and absence of extra commands. Hence this tool defect does not change the current declaration-text verdict. No repair was authorized or made.

### N1 — Q11 and Phase B are explicitly unfinished at the audited commit

`git diff inp...HEAD -- KAM/SpinOrbit KAM.lean KAM/Root README.md` is empty. In that committed snapshot, Model still declares the seven model names and Barrier still declares the landed `SoBarrier`; the new frozen modules declare the same full names. In particular the written-out frozen invariant field is not yet substituted into landed consumers. Importing both surfaces is not a valid integration route until Q11 resolves the duplicates and adapts the constructors. The missing READY-A/READY-B markers and empty providers correctly reflect this state.

This known integration boundary is not a byte-identity failure, and no data rebuild or Q11 implementation was attempted by this audit. The handoff's projected 7.5-hour rebuild was not independently measured here. No heavy SO data module was rebuilt or replayed for this identity audit.

### N2 — concurrent worktree edits are outside this pinned identity verdict

The worktree was clean at audit start. During the audit, external edits appeared in `KAM/SpinOrbit/{Model,Barrier}.lean`, `KAM/SpinOrbit/Graph/{Inverse,Rot}.lean`, and `KAM/SpinOrbit/Data/CsegSupport.lean`; later, all three `KAM/Provider/SpinOrbit/*.lean` stubs were modified externally as well. The auditor did not make or revert them. They are outside `git diff inp...HEAD` and outside this identity acceptance. In particular they must not be silently treated as an audited completion of Q11.

The thirteen frozen targets, the initially empty provider stubs and manifest were checked against HEAD before the concurrent provider edits, with no drift. At closeout the frozen targets and manifest still match the pinned commit; the now-dirty provider sources are excluded. The targeted build ran while the stubs were empty. Later provider artifacts are mutable: at closeout LunarWindow.ilean already lists a new provider theorem, while the other two still list no declarations. Consequently the later kernel-module receipt cannot certify that every provider replay input was the original empty stub. It is recorded as a successful artifact replay, with provider source/artifact identity excluded from this audit. The lint output below was captured while the width scan still saw the committed CsegSupport lines, before those concurrent formatting edits. It is an exact execution receipt for that scan, not a claim that a later dirty worktree has those same width errors. No potentially heavy final-data build or root regeneration was started to assess concurrent integration work.

### N3 — empty stub style

All three stubs are empty modules with the copyright and module docstring, with no imports or declarations. They are quarantined correctly and the module checker accepts them. They omit `public section`, despite the literal wording of AGENTS rule 3 for every Lean file. This has no visibility effect in an empty stub, but should be recorded as a style omission rather than claiming every header element is present. Frozen files themselves have the prescribed public sections and exposed definition bodies.

## Per-declaration identity verdicts

`F = KAM/Frozen/SpinOrbit/`. Every export below has prefix `KAM.SpinOrbit.`; every anchor ID is `spinorbit.d40.<export-short-name>.v1`. “PASS WITH NOTES” refers to identity only, with F1 and the draft/integration limitations retained.

| Node / approved locator | Declaration | Frozen path under F | State | Verdict and reason |
|---|---|---|---|---|
| Proposal 1 §1.1; proposal 2 §1.1 | `soEcc` | `Defs/SoEcc.lean` | SEALED definition | PASS WITH NOTES: literal `549/10000 : ℝ`, exact carrier/body. |
| P1 §1.2; P2 §1.1 | `soEps` | `Defs/SoEps.lean` | SEALED definition | PASS WITH NOTES: literal `69/200000 : ℝ`. |
| P1 §1.3; P2 §1.1 | `soCoeffPoly` | `Defs/SoCoeffPoly.lean` | SEALED definition | PASS WITH NOTES: generic field and all seven polynomial rows, plus prescribed zero branch, match; one D-SOF-5 docstring split. |
| P1 §1.4; P2 §1.1 | `soA` | `Defs/SoA.lean` | SEALED definition | PASS WITH NOTES: `soCoeffPoly soEcc m`. |
| P1 §1.5; P2 §1.1 | `soModes` | `Defs/SoModes.lean` | SEALED definition | PASS WITH NOTES: `Finset.Icc 1 7`. |
| P1 §1.6; P2 §1.1 | `soV` | `Defs/SoV.lean` | SEALED definition | PASS WITH NOTES: negative epsilon, seven-mode sum, period-one `2π(2q-mφ)`, Real carrier unchanged. |
| P1 §1.7; P2 §1.1 | `soField` | `Defs/SoField.lean` | SEALED definition | PASS WITH NOTES: `(p,-deriv_q V,1)` on `(q,p,φ)`, exact derivative and coordinate order. |
| P1 §1.8; P2 §1.1 | `SoBarrier` | `Defs/SoBarrier.lean` | SEALED structure | PASS WITH NOTES: all seven fields and interval-wise written-out invariance match. |
| P2 §1.2 and final-literal brief | `lunarPLo` | `Defs/LunarPLo.lean` | SEALED definition | PASS WITH NOTES: `9934 / 10000 : ℚ`, interim comment removed exactly as directed. |
| P2 §1.2 and final-literal brief | `lunarPHi` | `Defs/LunarPHi.lean` | SEALED definition | PASS WITH NOTES: `10066 / 10000 : ℚ`, interim comment removed. |
| P2 §1.3 A; D46/D48 substitutions | `lunar_barriers` | `Theorems/LunarBarriers.lean` | DRAFT_SORRY | PASS WITH NOTES: both band occurrences `[97245/100000,102755/100000]`, all conclusions and wrapper match; two docstring splits. FROZEN_UNPROVED. |
| P2 §1.3 B; D46/D48 substitutions | `lunar_spin_confinement` | `Theorems/LunarSpinConfinement.lean` | DRAFT_SORRY | PASS WITH NOTES: `≤ 2755/100000`, source binders and global-solution uniqueness unchanged; one docstring split. FROZEN_UNPROVED. |
| P2 §1.3 window | `lunarPLo_lt_lunarPHi` | `Theorems/LunarWindow.lean` | DRAFT_SORRY | PASS WITH NOTES: exact window nonvacuity statement and complete A-style wrapper. FROZEN_UNPROVED. |
| Provider stub | `KAM.Provider.SpinOrbit.LunarBarriers` (module) | outside F | Empty | PASS quarantine; no provider export exists; N3. |
| Provider stub | `KAM.Provider.SpinOrbit.LunarSpinConfinement` (module) | outside F | Empty | PASS quarantine; no provider export exists; N3. |
| Provider stub | `KAM.Provider.SpinOrbit.LunarWindow` (module) | outside F | Empty | PASS quarantine; no provider export exists; N3. |

No new helper theorem or additional Lean declaration is present. Structure-generated constructors/projections are the ordinary consequences of the identical `SoBarrier` declaration.

### Theorem binder and conclusion audit

| Anchor | Expanded input binder | Bin | Exact source |
|---|---|---|---|
| `lunar_spin_confinement` | `q₀ : ℝ` | TYPING | P2 §1.3, line 229. |
| same | `p₀ : ℝ` | TYPING | Same. |
| same | `φ₀ : ℝ` | TYPING | Same. |
| same | `hp.1 : (lunarPLo : ℝ) < p₀` | SOURCE | Same initial-window premise. |
| same | `hp.2 : p₀ < lunarPHi` | SOURCE | Same initial-window premise. |

Counts for B: SOURCE 2, STANDING 0, TYPING 3, RULED 0, EXCESS 0. A and the window theorem have no input binders; all five counts are zero for each. The D46/D48 changes are conclusion/literal substitutions, not new hypotheses.

A retains the two existential barriers, strict global ordering and strict placement below/above the fixed window. B first exhibits one global solution `z`, then bounds its momentum for every real time, then quantifies over global solutions `y` and asserts `y=z`. No constant dependence, norm, quantifier order, endpoint strictness or local-versus-global uniqueness was changed. The window statement remains in ℚ, while A/B cast it into ℝ at the same places as the approved text. No assumption hides a certificate success, barrier existence or desired conclusion.

For **each** of the three draft anchors:

```
DECLARATION_FIDELITY: PASS relative to the approved snippets and supplied final-literal authority
DRAFT_ALLOWLIST: PASS
PROOF_STATUS: FROZEN_UNPROVED
```

The identity/type probes below do not pay any proof obligation. Provider=frozen-type and seal-body-copy probes are N/A: there is no provider theorem or seal body to compare. Creating a replacement theorem to make such a probe pass would misrepresent Phase B.

## Definition classification

| Definition / structure | Classification | Whole-carrier body check |
|---|---|---|
| `soEcc`, `soEps` | Literal scalar parameters | Exact prescribed real values. |
| `soCoeffPoly` | Literal polynomial family on any supplied Field and all natural modes | All seven formulas match; `_ => 0` is explicitly approved source semantics, not an invented fallback. |
| `soA` | Literal specialization | Applies that family at the prescribed eccentricity for every natural mode. |
| `soModes` | Literal finite index set | Exactly inclusive modes 1 through 7. |
| `soV` | Literal real trigonometric function | Exact negative sign, coefficients, normalization and all real angle inputs. |
| `soField` | Literal derivative-defined real vector field | Exact coordinate formula on every real triple. Standard total `deriv` is the approved definiens, not a replacement solution. |
| `SoBarrier` | Source-defined structure/predicate data | `P`, continuity, two periodicities, written-out interval invariance, lower and upper bounds all preserved, for arbitrary real `lo,hi`. The structure does not assert existence of a barrier. |
| `lunarPLo`, `lunarPHi` | Literal rational constants | Exact final values specified by the supplied authority. |

For each: BODY_MATCH OK, PUBLIC_CARRIER OK, WELL_DEFINEDNESS N/A_LITERAL, CHARACTERIZATION N/A_LITERAL, CHOICE_INDEPENDENCE N/A, DEFINITION_VERDICT PASS for this source-identity scope. No characterization-defined object, arbitrary selected solution or result-shaped assumption package is introduced. Approval-date provenance remains F1 and is not validated by these semantic checks.

## Manifest, wrappers, deviations and quarantine

Independently parsed old/new manifests: **158 → 171**, precisely 13 additions, no removal and no change to any existing entry; schema_version, manifest_state and seal_limits unchanged. There are ten SEALED definitions/structure and three DRAFT_SORRY theorem entries. The generic brief's empty protected-path diff is inapplicable to these explicitly authorized new frozen files and manifest entries; there is no change to a pre-existing frozen anchor.

For every new entry, independently recomputed actual file hashes or complete theorem prefix/suffix hashes, all definition-closure file hashes, and transitive frozen-import closure membership match. Each source group is exactly `spinorbit.<short-name>`, NOT_SPLIT, and each contract ID is the same `spinorbit.<short-name>` at version 1. The implementation module/export pairs are exactly:

| Anchor | Module | Export named in manifest |
|---|---|---|
| A | `KAM.Provider.SpinOrbit.LunarBarriers` | `KAM.Provider.SpinOrbit.lunar_barriers` |
| B | `KAM.Provider.SpinOrbit.LunarSpinConfinement` | `KAM.Provider.SpinOrbit.lunar_spin_confinement` |
| window | `KAM.Provider.SpinOrbit.LunarWindow` | `KAM.Provider.SpinOrbit.lunarPLo_lt_lunarPHi` |

Closure, as actual transitive imports and recorded hashes:

- Model = SoEcc, SoEps, SoCoeffPoly, SoA, SoModes, SoV, SoField (7 files).
- B = model + LunarPLo + LunarPHi (9); **no SoBarrier**.
- A = B's closure + SoBarrier (10).
- Window = LunarPLo + LunarPHi (2).

Each frozen file has exactly one manifest owner. No frozen definition imports implementation code. Each theorem privately imports only its own provider stub. At the pinned snapshot, no other production module imports a new draft theorem or provider. Each DRAFT body is exactly the single `by sorry` inside its unique proof markers; empty draft allowlist arrays grant no extra import/escape sites.

All added copyright/module-docstring/approval/sealing paragraphs are identified in FREEZE.md §“Header lines”. The headers consistently quote the same unverified date (F1). No other source-body difference was found after the following explicit deviations:

- D-SOF-5: exactly four one-space-to-newline docstring splits (one SoCoeffPoly, two A, one B); undoing only these restores the approved documentation bytes. No binder or code token changes.
- D-SOF-6: approved proof-region bare `sorry` becomes guard-required `by sorry`, retaining exactly one manifested hole. This is not sealing.
- D-SOF-7: the draft common source_group becomes one NOT_SPLIT group per declaration. This is recorded metadata/guard adaptation; no source theorem or mathematical hypothesis is split or changed.

Neither freeze generator was executed to regenerate repository files. The supplied check_identity.py did execute read-only; its limitations are F2.

## Verification receipts

All audit Lean/Lake operations used `LEAN_NUM_THREADS=1` and `nice -n 5`, one operation at a time. No heartbeat, recursion-depth or synthesis override was used. No library clean/update/cache operation occurred. Compile, lint, type/axiom probe and kernel replay were serialized. The root and SO data targets were not built for this audit.

### Targeted build

```
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-sodata3 \
  KAM.Frozen.SpinOrbit.Theorems.LunarBarriers \
  KAM.Frozen.SpinOrbit.Theorems.LunarSpinConfinement \
  KAM.Frozen.SpinOrbit.Theorems.LunarWindow
[inp-gate] slot 1 acquired 07:20:27
warning: ...LunarBarriers.lean:33:8: declaration uses `sorry`
warning: ...LunarSpinConfinement.lean:32:8: declaration uses `sorry`
warning: ...LunarWindow.lean:28:8: declaration uses `sorry`
Build completed successfully (2112 jobs).
exit 0
```

This target closure covers the thirteen frozen files and three stubs. The warnings are the three manifested draft holes, not theorem closure.

### Text identity and independent checks

```
python3 docs/tracks/SO/freeze/check_identity.py
13 lines IDENTICAL
ALL IDENTICAL
exit 0
```

An audit-only scratch script independently reconstructed expected complete files directly from the two proposals, literal substitution table, listed imports and common wrapper, without running or trusting gen_frozen.py. It removed only the identified added header paragraphs, undid exactly the four documented line splits and normalized the single draft-body form. Its full equality checks include every byte outside those enumerated additions/deviations:

```
python3 .lake/abi-scratch/SO-FREEZE3-independent.py
Independent full-file comparison: PASS (13), including B/window wrappers, imports, markers, no extra commands
Checker virtual mutation extra-command: ALL IDENTICAL; exit 0
Checker virtual mutation wrong-literal: MISMATCH; exit 0
```

Separate read-only Python checks output:

```
independent manifest file/prefix/suffix/closure hashes: PASS (13); existing entries unchanged: 158
approved proposal bytes unchanged from inp: PASS
```

### Exact types, bodies and axioms

Command: `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SO-FREEZE3-Types.lean`.
Exit 0. The scratch file imports only the three frozen theorem modules. It verifies source defining equations by `rfl` for every scalar/polynomial/function definition, checks the entire invariant-field type, and applies each manifested draft export at its independently reconstructed exact approved type. These three applications check declaration fidelity only and inherit sorryAx; they are not claimed as proofs.

`#print axioms` output, abbreviated only by using short export names:

| Export | Exact axiom set |
|---|---|
| `soEcc` | `[propext, Classical.choice, Quot.sound]` |
| `soEps` | `[propext, Classical.choice, Quot.sound]` |
| `soCoeffPoly` | `[propext, Quot.sound]` |
| `soA` | `[propext, Classical.choice, Quot.sound]` |
| `soModes` | `[propext, Classical.choice, Quot.sound]` |
| `soV` | `[propext, Classical.choice, Quot.sound]` |
| `soField` | `[propext, Classical.choice, Quot.sound]` |
| `SoBarrier` | `[propext, Classical.choice, Quot.sound]` |
| `SoBarrier.mk` | `[propext, Classical.choice, Quot.sound]` |
| `lunarPLo` | `[propext, Classical.choice, Quot.sound]` |
| `lunarPHi` | `[propext, Classical.choice, Quot.sound]` |
| `lunar_barriers` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `lunar_spin_confinement` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `lunarPLo_lt_lunarPHi` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

The last three axiom closures are **not standard-only**; sorryAx is authorized solely for these manifested draft bodies. There is no provider export whose axiom closure could be certified. No proof promotion is justified by the build, probe or kernel replay.

### Lint

```
env LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
exit 1
Lean lines over 100 characters:
KAM/SpinOrbit/Data/CsegSupport.lean:16:107
KAM/SpinOrbit/Data/CsegSupport.lean:18:109
KAM/SpinOrbit/Data/CsegSupport.lean:19:106
KAM/SpinOrbit/Data/CsegSupport.lean:20:106
KAM/SpinOrbit/Data/CsegSupport.lean:22:101
KAM/SpinOrbit/Data/CsegSupport.lean:23:110
KAM/SpinOrbit/Data/CsegSupport.lean:68:101
KAM/SpinOrbit/Data/CsegSupport.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Frozen.lean)
check_lean_modules: PASS (3408 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (171 frozen declarations)
```

The eight width paths above are shortened from the absolute worktree paths in the actual output. These are pre-existing SO-DATA3 lines and were not changed by this audit; N2 records subsequent external edits. The root exception is expressly permitted by the package brief; no root was regenerated. There are no new frozen-file width errors. Maximum new Lean file size is 46 physical lines. No new forbidden proof escape, resource override, non-frozen sorry, or ambient-type substitution was found. The intentional three frozen draft holes are the only new sorries. N3 qualifies literal provider-stub style compliance.

`git diff --check inp...HEAD` exited 0. The protected implementation/root diff against the committed snapshot is empty as recorded above. The target identity files and manifest, separately compared to HEAD during this audit, had no worktree drift.

### Kernel replay

One invocation, serialized after lint and the type/axiom probe; the concurrent-provider artifact qualification in N2 applies:

```
env LEAN_NUM_THREADS=1 flock /mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock \
  systemd-run --user --scope -p MemoryMax=10G -p MemorySwapMax=0 \
  nice -n 5 lake env leanchecker --verbose \
  KAM.Frozen.SpinOrbit.Defs.SoEcc \
  KAM.Frozen.SpinOrbit.Defs.SoEps \
  KAM.Frozen.SpinOrbit.Defs.SoCoeffPoly \
  KAM.Frozen.SpinOrbit.Defs.SoA \
  KAM.Frozen.SpinOrbit.Defs.SoModes \
  KAM.Frozen.SpinOrbit.Defs.SoV \
  KAM.Frozen.SpinOrbit.Defs.SoField \
  KAM.Frozen.SpinOrbit.Defs.SoBarrier \
  KAM.Frozen.SpinOrbit.Defs.LunarPLo \
  KAM.Frozen.SpinOrbit.Defs.LunarPHi \
  KAM.Frozen.SpinOrbit.Theorems.LunarBarriers \
  KAM.Frozen.SpinOrbit.Theorems.LunarSpinConfinement \
  KAM.Frozen.SpinOrbit.Theorems.LunarWindow \
  KAM.Provider.SpinOrbit.LunarBarriers \
  KAM.Provider.SpinOrbit.LunarSpinConfinement \
  KAM.Provider.SpinOrbit.LunarWindow
exit 0
```

All listed modules were reported:

```
replaying KAM.Provider.SpinOrbit.LunarWindow
replaying KAM.Provider.SpinOrbit.LunarSpinConfinement
replaying KAM.Provider.SpinOrbit.LunarBarriers
replaying KAM.Frozen.SpinOrbit.Theorems.LunarWindow
replaying KAM.Frozen.SpinOrbit.Theorems.LunarSpinConfinement
replaying KAM.Frozen.SpinOrbit.Theorems.LunarBarriers
replaying KAM.Frozen.SpinOrbit.Defs.LunarPHi
replaying KAM.Frozen.SpinOrbit.Defs.LunarPLo
replaying KAM.Frozen.SpinOrbit.Defs.SoBarrier
replaying KAM.Frozen.SpinOrbit.Defs.SoField
replaying KAM.Frozen.SpinOrbit.Defs.SoV
replaying KAM.Frozen.SpinOrbit.Defs.SoModes
replaying KAM.Frozen.SpinOrbit.Defs.SoA
replaying KAM.Frozen.SpinOrbit.Defs.SoCoeffPoly
replaying KAM.Frozen.SpinOrbit.Defs.SoEps
replaying KAM.Frozen.SpinOrbit.Defs.SoEcc
```

This replays each listed module’s compiled declarations against its imports. It validates well-formed compiled definitions and manifested draft terms, not theorem proof closure. The three frozen theorems still have the printed sorryAx dependency. No heavy data module is among these targets. The later dirty provider sources are not accepted by this receipt, and no claim is made that every provider artifact replayed remained byte-identical to the pinned empty stub. At closeout, all three provider oleans were present; their ilean declaration maps were empty for A and B and nonempty for Window. This is explicitly an artifact replay result, not a Phase B source/seal audit.

## Pinned manifest identity appendix

All entries use approval version 1 and the unverified `approved_at` date discussed in F1. Complete manifest fields and expected closure membership were compared; the following hashes identify the audited elaborated declarations.

| Manifest ID | ABI SHA256 | File hash or theorem prefix SHA256 |
|---|---|---|
| `spinorbit.d40.soEcc.v1` | `65e9f453942205cb210df8f1fb54519e6bcb406d9add3f87e5ddcf962339d82a` | `e5dada171ea7c50e37e658c222d8292154907d7ec8625b6f0a3002a670bb3c79` |
| `spinorbit.d40.soEps.v1` | `27c5834addc5c77bf22d60788c3741791d0e5aded0055e48b3e5a9182a840868` | `cfaa0e6010e7b98c78ebe34b81560b41faf5b6526af66a12bdcc95703fbaa287` |
| `spinorbit.d40.soCoeffPoly.v1` | `37382ab82ab9e28d93e4dbf704d2ea37eb31c9a1e399ed9f18c4f76b7fddc5b8` | `8ada63c0d1ad7be58673c7e679888dab263fbf3c655cf0fb0bdffa8b2aca5502` |
| `spinorbit.d40.soA.v1` | `4b0fc27216fdfcfedeaba8402561bb19a9e38c367feea4554081ca6de3b7417b` | `ed7781fffac57114da0cd5c09e4fbfd5a6650e83cf9e4384c2fbc1a83bdb38a4` |
| `spinorbit.d40.soModes.v1` | `50c5fa3573029713c2672612ad3238577e0078ba814777566cc27db8bb9de9c3` | `88ea21b220cd3fa63e01914013112aeb24483b877b1ad115c976609ebf7e0b6e` |
| `spinorbit.d40.soV.v1` | `2da5bf701745baf86e234efdacc64cdfd86361225265ab86c9ba524578772d08` | `8818d9989f36f2bd75208bdf625e838e8b77e9f78dba7a29397d5894742c2caf` |
| `spinorbit.d40.soField.v1` | `8201e171233188fecf7ed819919466ddd7b929300c9ebe5190cbda88fe4f2bb3` | `77931cc9a1f1c403537d2b98bcfcd1a51477ec546f94c60d6fed9adc9e4d9f42` |
| `spinorbit.d40.SoBarrier.v1` | `95b8c0567f81a4fa58cd2c6a75f9c706df77ab1761d0d4bca69b905dffeef8d8` | `048b9c73be0f7c4f59511e7b2d8db4c57f519b56077327ab1ddee5844a687da7` |
| `spinorbit.d40.lunarPLo.v1` | `aa9b2a72788933782eb53fbf611f886d4d3555fa96bf152667ec2953c1b7b254` | `ef87955d0ab32ed824d28a52706f0ce0e11ce14b9f560318325303424f89c65a` |
| `spinorbit.d40.lunarPHi.v1` | `cd2ad51619d95842dc9deb6b2f13edc1471a35fa3b781f583f9101e4dae6a2bc` | `61091cec9fb8e4bfcdac5a2f1bd1fc91049556420097ec64ab4d7fda14065d8d` |
| `spinorbit.d40.lunar_barriers.v1` | `65230c7382ca07c9a69a6d51cf06a520f9589d5fa0e3ec155a9415f23bead7f8` | `ea168c589ee92939566e7376155729c2ebffc9ee88fcf2ab0fd768ceee1c3a74` |
| `spinorbit.d40.lunar_spin_confinement.v1` | `1024652814efd6d51aa5477400d573c54432bf9eb60607830da285b354dc88de` | `055cf4fcfb121c94551f62219b85ffda4c8bacfc29525ecdf9747e601227a963` |
| `spinorbit.d40.lunarPLo_lt_lunarPHi.v1` | `2072d9a341480545df396b56c0030e0e04d4dd8db990a2ebdd3367e12c25b436` | `b7c3b6c9809279c21f2e4a54558b922384db4a803892873a7bc81f78712ba338` |

The three theorem suffix hashes are each `82fffec8a7bd503242e8ee1117e463982ec052c8e1b2de510fef566b666e802f`. The independent recomputation includes the complete prefixes/suffixes and every closure file hash, not only the ABI values.

## Source evidence and closeout

SHA256 of the source snapshots read:

| Source | SHA256 |
|---|---|
| `docs/tracks/SO/FREEZE-PROPOSAL.md` | `0d1a42ae3cd8dd479e1f9bba19f2632d065b7b47687c6a79b288c4e85e5b27c5` |
| `docs/tracks/SO/FREEZE-PROPOSAL-2.md` | `002e74fbc7cf9480524f394e8651bf7a2266c939cd771d7d7ccd340e1c723210` |
| `/root/code/KAM-inp/.drafts/briefs/offload-main/SO-FREEZE3.md` | `0bd25878ca16ece631541b8812c364bee1ccaf1c997eac42112e0de81c4f5b74` |

No new suspected mathematical erratum in a pinned publication was identified in this identity audit. F1 is an unresolved provenance/date issue; F2 is a defect in the new project identity tool. D-SOF-5/6/7 and N3 are recorded deviations/style qualifications. No source hypothesis, theorem conclusion, literal, frozen byte, manifest value, provider body, generated file or existing implementation was repaired by this auditor.

The audit is complete at its requested identity scope. It establishes neither completion of Q11 nor Phase A/Phase B READY status. The only repository file written by this auditor is this report; all audit-created scratch files are deleted after recording their evidence. Concurrent source edits are preserved and excluded from acceptance. Final report whitespace and target-snapshot checks are run after this closeout text is written.
