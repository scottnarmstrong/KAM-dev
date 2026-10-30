# W freeze: independent identity audit (round 2)

**Verdict: PASS WITH NOTES.**

* Audited commit: `a526d662` on branch `inp-wfreeze` (parent `d7aae35d`, base `inp` `3860bc48`).
* Approved text: the twelve declarations of `docs/tracks/W/W-STATEMENTS.md` rev 1 at `ffcbdb93` (owner decision
  D41, `/root/code/KAM/docs/DECISIONS.md` line 337).
* Round 1 targeted `d7aae35d`. The coordinator moved the target to `a526d662` (D-WF2) during the audit. Every
  byte check below was rerun on `git archive a526d662`, never on the working tree. At audit time the working tree
  was clean at `a526d662`.
* Auditor scratch: `/tmp/claude-0/-root-code-KAM/63b27f23-b168-4cda-b9ba-19d89d35756b/scratchpad/audit/`. It
  holds `extract.py`, `chars.py`, `mkprobe2.py`, the `probes/` files and their outputs, `wave-manifest.json` and
  `abi.json`. All `.lake/abi-scratch/` probe files were deleted after use. Nothing was built, and no Lean,
  frozen, manifest or root file was edited.

## Per-declaration table

The "declaration vs approved" column compares the bytes from `namespace KAM.Wave` through `end KAM.Wave`. For
each declaration, the approved fence in W-STATEMENTS.md and the `.lean.txt` draft at ffcbdb93 are byte-identical
to each other. All 12 were checked.

| Declaration | Declaration vs approved (exact edits) | Header vs draft | ABI (pp.all) vs draft | Manifest |
|---|---|---|---|---|
| `lam` | identical | OK | identical | OK |
| `sineMode` | identical | OK | identical | OK |
| `ellWeight` | identical | OK | identical | OK |
| `WaveSpace` | identical | OK | identical | OK |
| `coeff` | identical | OK (import renamed to frozen path) | identical | OK |
| `reconU` | D-WF1: offset 106, `' '` to `'\n'` (in docstring) | OK (imports renamed) | identical | OK |
| `reconV` | D-WF1: offset 100, `' '` to `'\n'`; D-WF2: offset 102, `'q'` to `'p'` (both in docstring) | OK (imports renamed) | identical | OK |
| `cubicGrad` | identical | OK (import renamed) | identical | OK |
| `linearTorus` | D-WF1: offset 108, `' '` to `'\n'` (in docstring) | OK (imports renamed) | token-identical* | OK |
| `IsAnalyticTorusEmbedding` | identical | OK | identical | OK |
| `IsClassicalSolution` | identical | OK | identical | OK |
| `nlw2` | D-WF2: offset 32, `' (proposed)'` deleted (in docstring); statement up to `:=` identical; body exactly `  by sorry\n` between markers | OK (imports renamed, plus private provider import and markers) | identical (`#check @`) | OK (DRAFT_SORRY) |

\* `linearTorus` differs only in the line-wrapping of the pretty-printer output. This comes from the probe's
longer `KAM.Wave.AuditDraft.` names; after renaming, the whitespace-split token sequences are equal.

The coordinator asked for three confirmations:

* **(a) Only D-WF1 and D-WF2: confirmed.** The character-level diff of approved against frozen finds exactly five
  edits. Three are D-WF1, one space replaced by a newline in `linearTorus`, `reconU` and `reconV`. Two are D-WF2:
  `q` to `p` in `reconV`, and ` (proposed)` deleted in `nlw2`. There are no other differences in any of the 12.
* **(b) Docstring-only, and the ABI is unchanged: confirmed.**
  * All five edit offsets fall strictly inside the declaration docstring span (`/--` to `-/`), and no character
    outside a docstring changed.
  * The `pp.all` `#print`/`#check` output contains no docstring text (grep for `velocity`, `W-NLW2`,
    `period-one`, `displacement`: 0 hits), so the ABI hash cannot see these edits.
  * The frozen terms equal the terms of the approved drafts, elaborated independently (Lean probe below).
  * The manifest `abi_sha256` values (unchanged between d7aae35d and a526d662) recompute equal on oleans that
    carry the a526d662 docstrings.
* **(c) Manifest hashes match the a526d662 files: confirmed.** I recomputed every full-file, prefix, suffix and
  closure hash myself. The guard reports OK.

## A. Byte-for-byte declaration identity

`extract.py` / `chars.py` work as follows:

* They read the frozen files from `git archive a526d662`.
* They read the drafts and W-STATEMENTS.md from `git show ffcbdb93:...`.
* They match each fence with `^### \`Name\` (\`Module\`)\n\n```lean\n(.*?)\n```` (12 fences found, 12 lean fences
  in total).
* They cut each text from `namespace KAM.Wave\n` to the last `end KAM.Wave`.
* For `nlw2` they require the frozen block to end with
  `:=\n  -- FROZEN_ANCHOR_PROOF_BEGIN\n  by sorry\n  -- FROZEN_ANCHOR_PROOF_END\n-- FROZEN_ANCHOR_SUFFIX_BEGIN\n\nend KAM.Wave`
  and replace that ending with the approved `:= by\n  sorry\n\nend KAM.Wave` before comparing.

Output (round 2, a526d662):

```
Defs/Lam: draft==fence True; frozen==approved True; edits []
Defs/SineMode: draft==fence True; frozen==approved True; edits []
Defs/EllWeight: draft==fence True; frozen==approved True; edits []
Defs/WaveSpace: draft==fence True; frozen==approved True; edits []
Defs/Coeff: draft==fence True; frozen==approved True; edits []
Defs/ReconU: draft==fence True; frozen==approved False; edits [('replace', "' '", "'\\n'", 106)]
Defs/ReconV: draft==fence True; frozen==approved False; edits [('replace', "' '", "'\\n'", 100), ('replace', "'q'", "'p'", 102)]
Defs/CubicGrad: draft==fence True; frozen==approved True; edits []
Defs/LinearTorus: draft==fence True; frozen==approved False; edits [('replace', "' '", "'\\n'", 108)]
Defs/IsAnalyticTorusEmbedding: draft==fence True; frozen==approved True; edits []
Defs/IsClassicalSolution: draft==fence True; frozen==approved True; edits []
Theorems/Nlw2: draft==fence True; frozen==approved False; edits [('delete', "' (proposed)'", "''", 32)]
```

Docstring-span check (offsets relative to the `namespace KAM.Wave` line):

```
ReconU docstring span 20 137 edits inside: True
ReconV docstring span 20 131 edits inside: True
LinearTorus docstring span 20 277 edits inside: True
Nlw2 docstring span 20 317 edits inside: True
```

Proof region of `nlw2` (the bytes between the markers, as the guard defines them): `'  by sorry\n'`.

## B. Headers

I diffed each header (everything outside the declaration block) against its draft. The only changes are these:

1. The draft line `-- DRAFT (W-STMT rev1), not frozen. Proposed final path: ...` is dropped. It is a comment.
2. The module docstring (`/-! ... -/`) has a new title and an appended approval paragraph. In `nlw2`, "The proof
   body is `sorry` in this draft only." is replaced by the sealing rule. This is documentation only.
3. Every `public import KAM.Wave.Defs.X` becomes `public import KAM.Frozen.Wave.Defs.X`. Each target is the frozen
   counterpart, whose declaration block is approved-identical by A. No `KAM/Wave/` modules exist in the tree.
   Mathlib and `KAM.Frozen.Defs.IsDiophantine` imports are unchanged, with the same order and the same set. The
   probe generator asserts that the frozen import list equals the draft import list with this renaming, for all 12.
4. `Nlw2.lean` only:
   * It gets `-- FROZEN_ANCHOR_PREFIX_BEGIN`, the proof markers and `-- FROZEN_ANCHOR_SUFFIX_END`. These are
     comments.
   * It gets the private `import KAM.Provider.Wave.Nlw2`. The provider is a `module` with no imports and no
     declarations, so it brings in no instances, notation or definitions. It is also non-public, so nothing is
     re-exported. It cannot affect elaboration.

Nothing else changed:

* `@[expose] public noncomputable section` / `@[expose] public section` are as in the drafts.
* `open MeasureTheory Filter Topology` is as in the draft, `nlw2` only.
* `namespace KAM.Wave` / `end` are unchanged, and no attributes were added or removed.

## C. ABI (Lean probes)

**Method.** I wrote one scratch file per declaration, `.lake/abi-scratch/WAudit_<Name>.lean`, generated by
`mkprobe2.py` and deleted after the run. Each file does the following:

* It imports exactly the frozen file's public imports plus the frozen module itself.
* It pastes the draft text from ffcbdb93, from the `@[expose]` line to the end, in
  `namespace KAM.Wave.AuditDraft`. Name resolution sends its references to the frozen dependencies, and
  `@[expose] public` is dropped because the scratch file is not a module.
* It prints the frozen and draft declarations with `set_option pp.all true`, `pp.oneline false`: `#print` for
  definitions, `#check @` for `nlw2`.

Each file was run with `cd /root/code/KAM-inp-wfreeze && ELAN_NO_OVERRIDE_NOTICE=1 nice -n 5 lake env lean
.lake/abi-scratch/WAudit_<Name>.lean`. All 12 exited with rc=0. The only message was `declaration uses 'sorry'`
for the draft `nlw2`.

**Comparison.** I removed `AuditDraft.` and then compared the outputs:

```
Lam exact 694 | SineMode exact 604 | EllWeight exact 460 | WaveSpace exact 4041 | Coeff exact 6915
ReconU exact 5366 | ReconV exact 5326 | CubicGrad exact 5833 | LinearTorus token-identical (whitespace only) 16268
IsAnalyticTorusEmbedding exact 16177 | IsClassicalSolution exact 9221 | Nlw2 exact 165356
```

The terms refer to compiler-generated auxiliary lemmas (`X._proof_N`). I compared their types the same way, and
all are token-identical: `sineMode._proof_1`, `coeff._proof_1`, `reconU._proof_1`, `reconV._proof_1`,
`cubicGrad._proof_1`, `linearTorus._proof_1`, `linearTorus._proof_2`, `IsClassicalSolution._proof_1` and
`WaveSpace._proof_1`.

**Methodological note.** A first probe put all 12 drafts in one file that imported every frozen module. It showed
a different `NormedSpace ℝ` instance path in `IsAnalyticTorusEmbedding`: `InnerProductSpace.toNormedSpace` via
`RCLike` instead of `NormedField.toNormedSpace`. That is an artefact of the larger import set, because the same
text elaborated under its own imports gives a different path. The per-file probe uses the draft's own imports,
and there the output is identical. This confirms that the frozen import set must stay exactly the draft's, which
it does (B.3).

**The oleans are a526d662's.** `findDocString?` on the oleans returns the a526d662 docstrings. For example,
`reconV`: "…, where\n`p = coeff y` (P96-W p. 277). " and `nlw2`: "**W-NLW2.** For every …".

**ABI hash script on a restricted manifest.** I ran it on the 12 `wave.*` entries only (`wave-manifest.json` in
scratch):

```
$ python3 scripts/abi_hashes.py . <scratch>/wave-manifest.json --check
ABI HASHES OK (12 frozen declarations)
```

**Axioms.** `#print axioms` output from the round-1 probe; the axioms are the same for the frozen and draft
copies:

* The eleven definitions: `[propext, Classical.choice, Quot.sound]`.
* `KAM.Wave.nlw2`: `[propext, sorryAx, Classical.choice, Quot.sound]`. `sorryAx` is expected for DRAFT_SORRY.

## D. Manifest

Independent recomputation from the `a526d662` archive:

* id `wave.<name>.v1`, path, export `KAM.Wave.<name>`, kind, contract `{id: wave.<name>, version: 1}`, state.
* `full_file_sha256` for the definitions.
* `prefix_sha256`, `suffix_sha256` and the proof region for `nlw2`, using the guard's boundary rule.
* Every `definition_closure` hash.
* Closure completeness: the transitive `KAM.Frozen.*` import closure computed from the files equals the
  manifest's closure list, as ordered sets.
* Implementation `{module: KAM.Provider.Wave.Nlw2, export: KAM.Provider.Wave.nlw2}` and an empty
  `draft_allowlist`.

All 12 rows are `True`, followed by `ALL OK`. Closures:

* `coeff`: EllWeight.
* `reconU` and `reconV`: Coeff, EllWeight, Lam, SineMode.
* `cubicGrad`: those four plus ReconU.
* `linearTorus`: EllWeight, WaveSpace.
* `nlw2`: IsDiophantine plus all 11 Wave Defs.
* All others: empty.

Approval fields: `approved_by` Scott Armstrong, `approved_at` 2026-10-30, `approval_version` 1. `approval_ref`
quotes the owner reply "I approve the KAM for a PDE statements" and cites W-STATEMENTS rev 1 / ffcbdb93 / D41,
matching D41. The split policy is NOT_SPLIT, with ruling D41.

Pre-existing entries: the 146 non-wave anchors at a526d662 are equal (as parsed JSON) to the 146 anchors at
3860bc48. The top-level keys are unchanged.

Between d7aae35d and a526d662, the manifest diff changes only three hashes: `wave.reconV.v1.full_file_sha256`,
the matching ReconV closure entry inside `wave.nlw2.v1`, and `wave.nlw2.v1.prefix_sha256`.

```
$ python3 scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json
FROZEN-ANCHOR GUARD OK
```

## E. Provider stub and quarantine

* `KAM/Provider/Wave/Nlw2.lean` (12 lines): copyright, `module`, module docstring, nothing else.
* `grep` for `import KAM.Provider.Wave` in `*.lean` outside `.lake`: only `KAM/Frozen/Wave/Theorems/Nlw2.lean:16`.
* `git diff 3860bc48 a526d662 -- KAM.lean`: exactly the 11 `KAM.Frozen.Wave.Defs.*` lines. Neither the anchor nor
  the provider is added.
* `python3 scripts/gen_root_imports.py --check`: rc=0.
* `python3 scripts/check_lean_modules.py --root . --files <12 frozen files> KAM/Provider/Wave/Nlw2.lean`:
  `check_lean_modules: PASS (13 Lean files, 0 comparator configurations)`.

## F. Anything else under KAM/

`git diff --name-status 3860bc48 a526d662 -- KAM/` lists only the 12 frozen files (A) and
`KAM/Provider/Wave/Nlw2.lean` (A). Other checks:

* Line counts: 499 lines in total across the 13 files; the largest is 90 lines.
* No `set_option`, `axiom`, `admit`, `unsafe` or `opaque`.
* The only `sorry` is `Nlw2.lean:83` (`by sorry`, inside the markers).

Outside `KAM/`, the commits touch only:

* `docs/errata/ledger.json`: two deviation entries; the trailing newline is added.
* `docs/errata/working-record.md`.
* `docs/tracks/W/FREEZE.md` and `docs/tracks/W/freeze/*`.
* `manifest/frozen-anchors.json`.

## Findings

| # | Severity | Finding |
|---|---|---|
| F1 | NOTE | D-WF1: three whitespace-only edits to approved docstring bytes (space to newline), required by the 100-column lint. Inside docstrings only; ABI identical. Recorded as `D-W-FREEZE-1`. |
| F2 | NOTE | D-WF2: two docstring-only edits to approved bytes (`reconV` `q` to `p`; `nlw2` ` (proposed)` deleted). Inside docstrings only; ABI identical. The ruling is the main orchestrator's, not an owner re-approval. The text the owner approved in D41 is therefore not byte-identical to what is frozen. This is acceptable as a recorded deviation (`D-W-FREEZE-2`); the owner may want to acknowledge it. |
| F3 | NOTE | Round-1 process observation: while round 1 was auditing `d7aae35d`, the worktree was being edited (uncommitted D-WF2 edits to two frozen files) and the oleans were rebuilt. Resolved by commit `a526d662`; round 2 audited the committed bytes only. |
| F4 | NOTE | The provider stub has no `public section`. It is an empty module, and `check_lean_modules` passes, so AGENTS rule 3 is not violated in substance. |
| F5 | NOTE | The ABI equality depends on the frozen import sets staying exactly the drafts' (see C, methodological note). They do. |
| F6 | NOTE | The cosmetic trailing-newline addition to `docs/errata/ledger.json` is harmless. |

There are no BLOCKER, MAJOR or MINOR findings.

## Suspected defects in the approved text (ffcbdb93)

* `reconV` docstring: "`V_m(p)(x) = Σ √λ_j p_j · φ_j(x)`, where `q = coeff y`" should read `p = coeff y`. The
  body is correct. Fixed in the frozen file by D-WF2.
* `nlw2` docstring: "**W-NLW2 (proposed).**" is stale once the statement is approved. Fixed by D-WF2.
* This audit found no defect in any declaration body or statement. This is an identity audit, not a statement
  audit.
