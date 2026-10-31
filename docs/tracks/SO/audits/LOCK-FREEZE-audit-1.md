# LOCK-FREEZE audit 1 — identity only

**Verdict: PASS WITH NOTES for Phase A identity; no seal-readiness or theorem-closure claim.** All eight approved declaration texts match FREEZE-PROPOSAL-LOCK §1 byte for byte. The four theorem anchors remain `DRAFT_SORRY` / **FROZEN_UNPROVED**, with empty providers. All 179 elaborated ABI hashes reproduce; the 171 pre-existing manifest records are unchanged. No identity blocker found.

## Scope and frozen inputs

Audit date: 2026-10-31. Worktree: `/root/code/KAM-inp-lockdesign`.
Snapshot `frozen-v1`: HEAD `7deabe9f547710a132d810b2dca2f3bd046bd7f8`; `inp` and merge base `da762768b12d9c8ccaac85a084b32bc2a5407e95`. Initial worktree was clean. Reviewed `git diff inp...HEAD`: 16 files, 892 insertions, 11 deletions, including all new anchors/stubs, manifest additions, handoff, and the two rename files.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external package brief and LOCK-FREEZE-handoff.md. The user's identity-only scope supersedes the generic seal audit: frozen/manifest additions are intended; no provider proof, seal probe, certificate, blueprint proof, kernel replay, or semantic correctness audit is claimed. The report destination follows the user's explicit absolute path, overriding the generic brief's main-worktree destination.

Authority: proposal revision 3 §1 and recommended §2 answers; route D45; approval D49. The local decisions file ends at D45. Independently retrieved `git show b17bf0c0418cdf56989d9799f86feefbfcf6449c:docs/DECISIONS.md`, SHA-256 `8cb0ac6ad249ea16da328555a316b1b2c8414742b2038d5ce17adde850b58ff8`, whose D49 says:

> **Lock:** freeze FREEZE-PROPOSAL-LOCK §1 exactly (`IsSyncOrbit`, `lunarSyncOrbit`, `libAction`, `lunarOmega = 8/65`, `lunarSyncOrbit_spec`, `_unique`, `_bound`, and `lunar_sync_lock` with 129/10000, 21/100, 26/1000). It is sealed after LOCK-DATA lands.

D48 concerns landing LOCK-DATA; it is not the approval cited by the eight manifest additions.

Method: focused tier-2 correspondence audit. First pinned the revision and file digests, then mechanically extracted and compared the eight declarations, inspected wrappers/imports/manifest metadata, and tested candidate mismatches against the raw approved blocks and D49. No production files were changed. Scratch probes and an olean overlay stayed under `.lake/abi-scratch/lock-audit-1/` and were removed after recording evidence. No agents were delegated.

## Declaration ledger

All exports below are in `KAM.SpinOrbit`. IDs have prefix `spinorbit.lock.` and suffix `.v1`.

| Anchor / declaration | State | Identity verdict | Evidence / classification |
|---|---|---|---|
| `IsSyncOrbit` | SEALED definition | PASS | Literal predicate; exact C², period 1, oddness and frozen `soField` equation, §1.1. |
| `lunarSyncOrbit` | SEALED definition | PASS WITH NOTES | Exact approved classical-choice definition, including `if h : ∃ ψ, IsSyncOrbit ψ … else 0`; existence/uniqueness semantics not certified here. |
| `libAction` | SEALED definition | PASS | Exact π, Ω, tuple projections, derivative and squares/division, §1.1. |
| `lunarOmega` | SEALED definition | PASS | Exact rational `8 / 65 : ℚ`. |
| `lunarSyncOrbit_spec` | DRAFT_SORRY | PASS WITH NOTES | Exact §1.2 statement; FROZEN_UNPROVED. |
| `lunarSyncOrbit_unique` | DRAFT_SORRY | PASS WITH NOTES | Exact ψ then h binders and global equality; FROZEN_UNPROVED. |
| `lunarSyncOrbit_bound` | DRAFT_SORRY | PASS WITH NOTES | Exact φ binder, 17/1000000 and 27/200000 bounds; FROZEN_UNPROVED. |
| `lunar_sync_lock` | DRAFT_SORRY | PASS WITH NOTES | Exact initial-action strict threshold, global trajectory, tube bounds, strict quarter-turn bound and trajectory uniqueness; FROZEN_UNPROVED. |
| Four `KAM.Provider.SpinOrbit.Lunar*` modules | Empty stubs | PASS WITH NOTES | No declarations, exports, premises or imports; providers do not yet inhabit the frozen types. |
| `Lock.syncOrbit_spec`, `_unique`, `_bound` | Existing proved helpers, renamed | PASS (identity) | The two files are exactly the base files after the three literal name substitutions. No other proof/type/body edits. |

The comparison preserves internal whitespace and UTF-8 bytes, including source docstrings and `open Classical in`; it excludes the added module wrapper and, for theorem signatures, the added `:=` plus marked proof body. Physical source files contain no newline-normalization difference. All four proof regions contain exactly `by sorry` after trimming surrounding indentation/newlines.

Wrapper additions are exactly the described copyright/module/import/module-doc/section/namespace/end scaffolding, frozen markers, and proof attachment. `open Real` in LibAction resolves the approved `π`; ABI reproduction checks its elaborated identity. `IsSyncOrbit` imports the existing frozen `SoField`; it does not redefine the field. The definition modules import no draft theorem/provider. Each theorem imports only the frozen definitions it needs and its own empty provider. The stubs are empty modules, so have no public declarations requiring a public section.

## Binder and literal identity

These bins classify correspondence to the approved Lean text, not mathematical source sufficiency. No additional implicit or instance binders appear in the new signatures; ABI checks include elaborated instances/coercions.

| Theorem | Outer binder | Bin | Approved location |
|---|---|---|---|
| `lunarSyncOrbit_spec` | None | — | §1.2 first theorem |
| `lunarSyncOrbit_unique` | `ψ : ℝ → ℝ` | TYPING | §1.2 second theorem |
| `lunarSyncOrbit_unique` | `h : IsSyncOrbit ψ` | SOURCE | §1.2 second theorem |
| `lunarSyncOrbit_bound` | `φ : ℝ` | TYPING | §1.2 third theorem |
| `lunar_sync_lock` | `q₀ : ℝ` | TYPING | §1.2 headline |
| `lunar_sync_lock` | `p₀ : ℝ` | TYPING | §1.2 headline |
| `lunar_sync_lock` | `φ₀ : ℝ` | TYPING | §1.2 headline |
| `lunar_sync_lock` | `h₀ : libAction lunarOmega lunarSyncOrbit (q₀,p₀,φ₀) < 129/10000` | SOURCE | §1.2 headline |

Counts: SOURCE 2; STANDING 0; TYPING 5; RULED 0; EXCESS 0, relative to §1. `IsSyncOrbit ψ` expands to the exact approved C²/periodic/odd/equation conjunction. Existential z, universal t/y, trajectory premises and equality are inside the exact conclusion, with unchanged order and scope. No consumer bridge was added or presumed.

Definitions: BODY_MATCH and PUBLIC_CARRIER identity are OK for all four. `IsSyncOrbit`, `libAction`, and `lunarOmega` are literal definitions. `lunarSyncOrbit` is an approved choice/fallback definition: its full body matches, but WELL_DEFINEDNESS, CHARACTERIZATION, CHOICE_INDEPENDENCE and semantic DEFINITION_VERDICT are outside this identity audit and are not passed. In particular, reproducing the approved fallback does not prove existence or canonical uniqueness. The frozen `_spec` and `_unique` remain unpaid draft results.

## Manifest and rename checks

Parsed the old and new manifests and asserted exact Python-object equality of the first 171 records, followed by exactly eight additions (179 total). Checked new IDs, kinds, exports, source revision/ranges, D45/D49 approval/ruling references, four SEALED versus four DRAFT_SORRY states, definition closure hashes, whole-file or prefix/suffix hashes, provider module/export mappings and empty allowlists through direct inspection and the frozen guard. No pre-existing frozen file changes occur in the diff. All 171 baseline frozen files also match the current `inp` cache worktree sources byte for byte.

The rename is mechanically exact: replacing `lunarSyncOrbit_spec`, `lunarSyncOrbit_unique`, `lunarSyncOrbit_bound` with `syncOrbit_spec`, `syncOrbit_unique`, `syncOrbit_bound` in each base file yields its HEAD bytes. Locations: PO/Orbit.lean declarations at 136, 147, 213; Assembly.lean uses at 325, 327. Search of the landed Lock directory finds only the new helper names. Frozen exports retain the owner-approved old names in `KAM.SpinOrbit`; landed helper exports stay in `KAM.SpinOrbit.Lock`. This identity audit does not reprove the landed helpers or certify the planned Phase B bridges. LOCK-DATA must retain this rename on merge, as the handoff states.

## Verification

The user corrected the missing `KAM-inp-sodata3` cache path during this audit. Used `/root/code/KAM-inp/.lake/build/lib/lean` at inp da762768 and package caches `/root/code/KAM-inp/.lake/packages/*/.lake/build/lib/lean`, read-only. No `.lake/build` was created here. A scratch tree of file symlinks supplies unchanged KAM oleans while the twelve new module outputs are real scratch files. This is necessary because Lean resolves the KAM package from its first search-path root; a sparse overlay initially failed to locate `SoField.olean`. Rebuilding the scratch overlay resolved that setup failure; no frozen/source change was made.

Capped scope command:

```sh
systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 \
  env LEAN_NUM_THREADS=1 python3 .lake/abi-scratch/lock-audit-1/run.py
```

The driver invokes exactly one Lean child at a time, with these project options:

```sh
nice -n 5 lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dlinter.unusedVariables=true -Dlinter.unusedSectionVars=true \
  -Dlinter.unusedSimpArgs=true -Dlinter.unnecessarySimpa=true \
  -Dlinter.deprecated=true -R . -o "$scratch/oleans/$module.olean" "$module.lean"
```

`LEAN_PATH` is scratch oleans, inp oleans, then package olean directories. No Lake build, library rebuild, cache deletion, resource override in Lean, generated-root edit or state-changing git command was performed. External campaign processes were left untouched; this audit launched at most one Lean process at a time.

| New module (relative to KAM/) | Exit | Seconds | Output |
|---|---:|---:|---|
| `Provider/SpinOrbit/LunarSyncOrbitSpec.lean` | 0 | 0.53 | Empty. |
| `Provider/SpinOrbit/LunarSyncOrbitUnique.lean` | 0 | 0.39 | Empty. |
| `Provider/SpinOrbit/LunarSyncOrbitBound.lean` | 0 | 0.4 | Empty. |
| `Provider/SpinOrbit/LunarSyncLock.lean` | 0 | 0.43 | Empty. |
| `Frozen/SpinOrbit/Defs/IsSyncOrbit.lean` | 0 | 2.4 | Empty. |
| `Frozen/SpinOrbit/Defs/LunarSyncOrbit.lean` | 0 | 2.29 | Empty. |
| `Frozen/SpinOrbit/Defs/LibAction.lean` | 0 | 2.18 | Empty. |
| `Frozen/SpinOrbit/Defs/LunarOmega.lean` | 0 | 1.08 | Empty. |
| `Frozen/SpinOrbit/Theorems/LunarSyncOrbitSpec.lean` | 0 | 2.04 | Only `declaration uses 'sorry'` warning. |
| `Frozen/SpinOrbit/Theorems/LunarSyncOrbitUnique.lean` | 0 | 1.89 | Only `declaration uses 'sorry'` warning. |
| `Frozen/SpinOrbit/Theorems/LunarSyncOrbitBound.lean` | 0 | 1.9 | Only `declaration uses 'sorry'` warning. |
| `Frozen/SpinOrbit/Theorems/LunarSyncLock.lean` | 0 | 1.92 | Only `declaration uses 'sorry'` warning. |

Exact compile warnings (all other module output empty):

```text
KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitSpec.lean:28:8: warning: declaration uses `sorry`
KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitUnique.lean:28:8: warning: declaration uses `sorry`
KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitBound.lean:27:8: warning: declaration uses `sorry`
KAM/Frozen/SpinOrbit/Theorems/LunarSyncLock.lean:31:8: warning: declaration uses `sorry`
```

Mechanical checks and outputs:

- Declaration extraction/comparison: `IDENTITY OK: 8/8 declaration byte comparisons including attached docstrings; 171 old manifest entries unchanged; 2/2 files exact rename substitution`.
- Raw encoding/base-source check: `RAW UTF-8 IDENTITY OK; four exact by sorry bodies; all 171 base frozen files equal cache worktree sources`.
- `git diff --check inp...HEAD`: exit 0, no output.
- `python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json`: exit 0, `FROZEN-ANCHOR GUARD OK`.
- ABI probe: generated the same import list, `pp.all true`, `pp.oneline false`, boundary markers, `#print` definitions and `#check @` theorems as `scripts/abi_hashes.py`; invoked direct capped `nice -n 5 lean -R .` with the overlay. Used the script's same boundary splitting/location-prefix removal/SHA-256 algorithm. Exit 0: `ABI HASHES OK (179 frozen declarations)`; zero drift, including all 171 baseline entries.

`sh scripts/lint_sources.sh` ran inside the same capped scope, with a scratch-only `lake` shim forwarding exactly `lake env lean …` to `nice -n 5 lean …` against the read-only overlay; other Lake invocations were blocked. This avoids creating a local build or changing package state. Exit 1; exact combined output (stdout then stderr):

```text
check_lean_modules: PASS (3420 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (179 frozen declarations)
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Frozen.lean)
```

Only the expected generated-root freshness check fails. No forbidden escape, draft-anchor use, provider-import, size or formatting finding was emitted. The ABI step of lint independently repeats the supplied `scripts/abi_hashes.py --check` algorithm through the shim and passes. The root was not regenerated.

A separate transient probe imports the eight new anchors and executes `#print axioms` for all eight exports. Command: capped `systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 env LEAN_NUM_THREADS=1 python3 .lake/abi-scratch/lock-audit-1/axioms.py`, forwarding to `nice -n 5 lean -R . "$scratch/Axioms.lean"` with the same overlay. Exit 0:

```text
'KAM.SpinOrbit.IsSyncOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarSyncOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.libAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarSyncOrbit_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarSyncOrbit_unique' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarSyncOrbit_bound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_sync_lock' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Definitions have only standard foundation axioms. Each draft theorem has the expected `sorryAx`; **axiom/proof closure is not passed**. Empty providers have no theorem export whose axioms could be checked.

Kernel replay, provider=frozen-type probes, seal-body probes, and recompilation of renamed existing modules: not run in this identity-only, twelve-new-module compile scope. No claim that any empty provider is seal-ready.

## Findings, notes and closeout

No surviving declaration/manifest/rename identity defect. Adversarial checks included: wrong approval number (D48 versus D49), hidden theorem hypotheses, changed strict/weak inequalities or rational carriers, copied declaration but altered definition body, unregistered draft body, meaning-changing rename edits, use of landed `soVq` in place of approved `soField`, stale baseline manifest entries, and sparse-overlay cache confusion. Raw §1 comparison, D49 retrieval, guard and ABI checks refuted these identity concerns or resolved the environmental setup issue.

Notes: the generated root remains stale; four theorems are intentionally unproved; empty providers provide no seal evidence; choice/fallback semantics and all mathematical source/certificate/consumer closure are outside scope. No suspected pinned-source defect is reported from this identity audit. The approved fallback is explicitly preserved, not silently repaired or semantically certified. No implementation deviations were introduced. The documented `open Real` wrapper and helper rename are accounted for.

Only this report is a persistent repository change. No repair, seal, manifest update, commit or generated-file regeneration was authorized or performed.

## Snapshot digests

Full-file SHA-256 values at frozen-v1 (theorem full hashes supplement the manifest's prefix/suffix hashes):

| File | SHA-256 |
|---|---|
| `KAM/Frozen/SpinOrbit/Defs/IsSyncOrbit.lean` | `82c951487ed884ea70a56c2fa5d3166315ca41739666b708fd770cf0d373dcde` |
| `KAM/Frozen/SpinOrbit/Defs/LibAction.lean` | `fbc6fd4b4626cda9c9c9deb48db8f3de9e6baeec025c85fde70f75750c4d82d6` |
| `KAM/Frozen/SpinOrbit/Defs/LunarOmega.lean` | `7bf8d650c858d91bda6748094ef8f52ec58367ac551359e676a8c645fa767aa5` |
| `KAM/Frozen/SpinOrbit/Defs/LunarSyncOrbit.lean` | `ae11f7e2b080fbedd4c61a889460bfeae4f18cd5c185d4bf8c935288a349be74` |
| `KAM/Frozen/SpinOrbit/Theorems/LunarSyncLock.lean` | `f70a75efb37bb77b59cf8850decb64a98b6cf88b9c3442f717d16f85207d52da` |
| `KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitBound.lean` | `e712fafd9c736a5ec9719c7a72a0ba3b48a93dcc2f30d428e8c983d3f55181ec` |
| `KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitSpec.lean` | `5ad96a03ecb4c51a960337a6eb5b3ee6b982f8bb2b0dde8ebd283a9538ccb766` |
| `KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitUnique.lean` | `95049836a394ee2dc270026aa7613e20cd5a7fa718ced3adb1164ba0030894ad` |
| `KAM/Provider/SpinOrbit/LunarSyncLock.lean` | `f9dc8f075249f408503b0c9274957cbeb52c996a3a803064d2236ba563878cc0` |
| `KAM/Provider/SpinOrbit/LunarSyncOrbitBound.lean` | `bd62717644bccc537657c78377834dde64151be4d5aece48963d38b57710fe4e` |
| `KAM/Provider/SpinOrbit/LunarSyncOrbitSpec.lean` | `d62d09b5be3a7402bab32677b875c0437c07eda5034e963a6563a654b7578dd2` |
| `KAM/Provider/SpinOrbit/LunarSyncOrbitUnique.lean` | `c56f894831668bdec3da9023be5bf5ff5da1c368b84839548126f4ec401f4646` |
| `KAM/SpinOrbit/Lock/Assembly.lean` | `a8fcc7828291ed88112e94e42c22f37210e3e44d9a7c8e778a9e340615a1f9f8` |
| `KAM/SpinOrbit/Lock/PO/Orbit.lean` | `aa661feee79c5e6e4f4c5da6be24963add8ab6ff74283ef46e9f51ccc825fcc4` |
| `docs/tracks/SO/audits/LOCK-FREEZE-handoff.md` | `444d74a01201073486f9afe2e9583f9d86270a492654b98dfc17c0711f867d5d` |
| `manifest/frozen-anchors.json` | `8859fe7f8bae7ca904585d0b72a6c23601d848c66febefdc7e5c74adb2300555` |
| `docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md` | `a6df58747ebc11eb2aaa3a3f6217f791a282b62f31c761ce6f579fdad73368d8` |

New manifest ABI values (all independently reproduced):

| Export in KAM.SpinOrbit | ABI SHA-256 |
|---|---|
| `IsSyncOrbit` | `4875c0ccc6b901683b276df2736eaf559cc23b5d23fc7ea826491a526c62198e` |
| `lunarSyncOrbit` | `c8fa111bf32ac4e8c602ab55db5f42dcb51a49341d007e904265e28331bbc0a7` |
| `libAction` | `8e19531b34df70d3b455309b9c1925ab9489d4a64f874cff35bea94024bbc748` |
| `lunarOmega` | `d03e97ff1f603076a5e777f1847e379b84e49d0e8a1a8d3063587ce34149504a` |
| `lunarSyncOrbit_spec` | `3da1e71aa0ff41f1bb7ea4aa392df5889b3194f634061cac6bceeb9bf62a3c88` |
| `lunarSyncOrbit_unique` | `009cd93863ea628dbbec41f73c10e9677de4a59ec8f8228aacbabf29dfe1c882` |
| `lunarSyncOrbit_bound` | `66204b3b1d9f70de2381676d82a181bd3f34a68f3d1f8ac186212cd27d750e0d` |
| `lunar_sync_lock` | `5ccf9ade60178773223d4deb74440bf1f7a23ba89225c542137cf525109aa4dc` |
