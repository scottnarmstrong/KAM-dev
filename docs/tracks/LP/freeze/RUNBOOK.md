# Track LP: freeze-and-seal runbook

Status: written 2026-11-01 (about 10:00 UTC), documentation only. Nothing here has been executed. No file under
`KAM/Frozen/`, `KAM/Provider/` or `manifest/` was created or edited, and no Lean or Lake process was run to write it.
The orchestrator commits this file.

**Purpose.** When the owner approves the exact LP text, the freeze and the seals should go through quickly and with
nothing left to decide. This file gives every step as a command, a file list and a check, each with its stop
condition. Anything not found in the repository is marked **OPEN QUESTION** (collected in §8), not invented.

**Read §0 first.** One rebase point, `KAM.Fourier.modeSize`, invalidates most of the library and both lunar
certificate applications. As currently drafted, that makes "within the hour" impossible.

Conventions in this file:

```sh
W=/root/code/KAM-inp-lp-seal          # the seal worktree (step S0)
B=inp-lp-seal                          # its branch, off current `inp`
P=inp-lp-providers                     # provider staging branch (package LP-FREEZE7R part B; LP-FREEZE8)
T=/mnt/HC_Volume_106379410/orchestrator-tools
L=/root/code/KAM-inp/.drafts/LP        # lp_build.sh, lp_lean.sh, lp_lint.sh (D53 caps)
F=docs/tracks/LP/freeze
DATE=<YYYY-MM-DD>                      # UTC date of the owner's exact-text approval
DEC=<Dnn>                              # the decision recording it (D62 unless taken; OPEN QUESTION Q2)
A7=<sha>                               # approved commit of draft 7 revision 1 (branch inp-lp-freeze7)
A8=<sha>                               # approved commit of draft 8 (branch inp-lp-freeze8)
```

Every Lean or Lake command goes through the LP wrappers: `$L/lp_build.sh` (one module per `lake build`, 4 GB scope,
nice 10, one thread, compile-gate slot, MemAvailable ≥ 8 GB; `$L/lp_build.sh:1-5`), `$L/lp_lean.sh` and
`$L/lp_lint.sh`. Run them one at a time, as AGENTS.md:21-27 (rule 8) and D53 (main:docs/DECISIONS.md:430-438)
require. A wait on the compile gate is expected.

---

## 0. Blocking risk: the `modeSize` rebase reaches the whole library and both lunar certificates

Draft 7 freezes `KAM.Fourier.modeSize` at `KAM/Frozen/Fourier/Defs/ModeSize.lean`. The rebase therefore deletes its
`def` from the shared `KAM/Fourier/Derivative.lean` (line 37) and adds a `public import` of the frozen file
(FREEZE-PROPOSAL draft 7, `inp-lp-freeze7`@309cef26 `docs/tracks/LP/FREEZE-PROPOSAL.md:1389-1393`; handoff
convention 5, `docs/tracks/LP/audits/LP-FREEZE7-handoff.md:130`). An import-graph count over the source tree on
2026-11-01 gives:

| Modules whose import closure contains `KAM.Fourier.Derivative` | Count |
|---|---|
| core modules (2,836 of 3,797 on the `inp-lp` tree, 2,820 on `inp-lp-freeze7`; 18 existing frozen anchors and 18 providers among them) | **about 2,830** |
| `KAMLunarBand` certificate data on `main` (`KAM.SpinOrbit.Data.{Upper,Lower,Cseg*,Format}`) | **1,649 of 1,649** |
| `KAMLunarLock` data on `inp-lockdata`@20562e17 (`KAM.SpinOrbit.Data.LockN65`) | all 50 sampled, of 2,249 |
| the other LP rebase targets together (no `modeSize`) | 96, all under `KAM.Planetary.{StrongAMD,Spatial}` |

Consequences, if the text stays as drafted:

- **Step (a) rebuilds most of the core.** AGENTS.md:21-23 says "never rebuild the library from scratch in a
  worktree". A rebuild of about 2,830 modules is nearly that.
- **The landing stops.** `scripts/land-branch.sh:40` runs `prebuild_heavy.py --check-all`, which exits 3 when a heavy
  data module is stale (`scripts/prebuild_heavy.py:20-29`). The band data must then be rebuilt deliberately. The
  precedent is SO-FREEZE3 Q11: a frozen-name migration forced "a one-time full kernel rebuild of the 1,645 band data
  modules (about 7.5 h of kernel time, about 4.5 h on two lanes)", which was taken as an owner cost decision
  (`docs/campaign/OVERNIGHT.md:2159-2163`).
- **The lock data goes stale.** If LOCK-DATA lands or is built before LP's rebase, it is invalidated too. D55 puts
  that build at 28–38 h on one lane (main:docs/DECISIONS.md:443-456).

Options, for root-b8 and the owner, **before the exact text is approved** (draft 7 is in revision now, LP-FREEZE7R):

- **(C) Recommended: drop `modeSize` from the freeze.** State the Diophantine premise of LP1, LP1-H and LP2, LP2-H
  (and of the draft-8 anchors, if they use it) through the already frozen `KAM.IsDiophantine`. The proposal records
  this alternative as pointwise equivalent and avoiding the shared-module edit (FREEZE-PROPOSAL.md, Appendix A,
  "Alternatives not chosen"). It needs a text change and a delta statement audit. The rebase then touches only the
  96 LP modules, no core module outside `KAM.Planetary.{StrongAMD,Spatial}`, and no certificate data.
- **(A) Keep the text and pay.** The core cascade happens in step (a). The band (and possibly lock) rebuild is a cost
  decision for the owner. Plan hours, not one hour. Schedule it against LOCK-DATA (OPEN QUESTION Q1).
- **(B) Keep the text and pre-stage.** Build steps (a)–(d) on a never-landed staging branch before the approval,
  with a reserved `$DEC` and expected `$DATE`. This literally conflicts with D59: "before anything enters
  `KAM/Frozen/` or `manifest/`" (main:docs/DECISIONS.md:494-496). It also does not avoid the band rebuild at
  landing. Not recommended without an explicit ruling (Q3).

The rest of this runbook works for any option. Steps marked **[modeSize]** apply only under (A) or (B).

---

## 1. Preconditions (all must hold before step S0)

| # | Precondition | Who | Evidence to record |
|---|---|---|---|
| P1 | **Owner's exact-text approval** of draft 7 revision 1 and draft 8, quoted verbatim. It names the two approval objects (the file sets under `$F/draft7/` and `$F/draft8/` with their manifest-entry drafts, at `$A7` and `$A8`). D59 covers only the rulings (main:docs/DECISIONS.md:482-496). | root-b8 records it as `$DEC` in `docs/DECISIONS.md` on `main`, in the format of D41/D49 (main:docs/DECISIONS.md:337-346, 396-405) | `$DEC` text; the quoted owner reply |
| P2 | **Does the approval also authorize the seals?** D26 seals ran under the orchestrator procedure (`docs/MANIFEST-CHANGES.md:10-31`, "D26 (procedure)"). SO-2 and W-NLW2 had an explicit owner go (D50 main:docs/DECISIONS.md:406-408; D61 :507-518). The owner's "get everything sealed and audited" points to yes. `$DEC` should say so explicitly (Q4). | root-b8 | wording in `$DEC` |
| P3 | **Clean statement audits.** Draft 7 round 2 (`$F/STATEMENT-AUDIT-DRAFT7-2.md`, brief `$F/AUDIT-DRAFT7R1-BRIEF.md` on `inp-lp`) and the draft-8 statement audit are PASS or PASS WITH NOTES. Every note is disposed of. Round 1 was RETURN FOR REVISION (F1, F2; `inp-lp-freeze7`@309cef26 `$F/STATEMENT-AUDIT-DRAFT7-1.md:41-46`). | LP sub-orchestrator (kam-lp) | audit file and verdict line; audited HEAD = `$A7` / `$A8` |
| P4 | **Pinned approval objects.** `sha256sum` of every `$F/draft7/**.txt`, `$F/draft8/**.txt` and both `manifest-entries.json` at `$A7`/`$A8` equals the table in the audit report (round 1 pinned them in `verification-draft-7.txt:7-133`, `STATEMENT-AUDIT-DRAFT7-1.md:22-31`). Expected counts: draft 7 rev 1 = 129 files (90 definitions + 39 theorems: 5 anchors, 34 characterizations), the round-1 F1 fix adding 2 definitions. Draft 8 = 2 anchors + d definitions (expected d = 0). | kam-lp, by `lp_identity_check.py --pin` (§7) | hash table committed in `docs/tracks/LP/FREEZE.md` |
| P5 | **Implementation on `inp`.** The closing theorems and the modules to rebase are on `inp`: `inp-lp` (LP3, W5C), the implementation commits of `inp-lp-freeze7` (`PlanarSafety/SourceThreshold.lean`, the two `SourceCorollary.lean`, rev 1's `KAM/Planetary/Spatial/SourceBarycentric.lean`) and of `inp-lp-freeze8`. Per D61's order ("everything lands on `main` … then the seal commit", main:docs/DECISIONS.md:517-518), they land first through kam-inp-63. Otherwise step S0 merges them (S0.2). | kam-lp, kam-inp-63 | `git merge-base --is-ancestor <sha> inp` for each |
| P6 | **Providers staged** on `$P`. One module per theorem anchor (41 = 39 + 2) at the manifest's `implementation.module` path, exporting `implementation.export`. Each is built, type-probed and axiom-checked on the staging branch (as W did: `/root/code/KAM-inp/.drafts/W/SEAL-NLW2-STAGED.md:6-15`). The 34 characterization proofs are moved verbatim from their implementation modules, with the two sibling inlinings (FREEZE-PROPOSAL.md:1396-1404). | LP-FREEZE7R part B; LP-FREEZE8 | `$P` tip sha; per-provider probe output |
| P7 | **Option C, A or B (§0) decided.** If A, the owner's cost ruling for the band (and lock) rebuild and its slot against LOCK-DATA. | root-b8, owner | decision reference |
| P8 | **Machine state.** No other track rebuilds a module downstream of the rebased ones meanwhile. MemAvailable ≥ 8 GB (D53). codex-2 LP lane free for the seal audit (D57 main:docs/DECISIONS.md:472-475; `docs/tracks/LP/PROGRESS.md:17-18`). | kam-lp | — |

---

## 2. Commit sequence

One dedicated branch `$B` off current `inp`, with five commits (S0 is often empty). Each commit is followed by
its check, and the next commit starts only when that check passes. Never land the intermediate states: the
precedent is track R, "Not on main: the branch lands only after sealing, kernel replay and audit"
(`git show a9f95098`). Every step can be undone by resetting `$B` to the previous step's commit (§5).

### S0. Worktree and branch

```sh
# creates /root/code/KAM-inp-lp-seal on branch inp-lp-seal off `inp`, Mathlib linked, inp's build copied
$T/inp_new_worktree.sh lp-seal            # usage: inp_new_worktree.sh:2-3
cd $W && git log -1 --format=%H inp       # record the base sha
```

D53 asks for new worktrees on the HC volume (main:docs/DECISIONS.md:436). LP's are there under
`/mnt/HC_Volume_106379410/kam-lp/` with links in `/root/code`. `inp_new_worktree.sh` writes to `/root/code`
(OPEN QUESTION Q5).

S0.2 (only if P5 does not hold): merge the approved implementation, then regenerate the roots:
```sh
git merge --no-ff inp-lp
git merge --no-ff $A7
git merge --no-ff $A8
python3 -I scripts/gen_root_imports.py          # never hand-edit KAM.lean, KAM/Root/*, lakefile block (AGENTS.md:30-32)
git add -A KAM.lean KAM/Root lakefile.lean && git commit -m "LP seal S0: merge approved implementation; regenerate roots"
```
A merge conflict in a generated file (`KAM.lean`, `KAM/Root/*.lean`, the generated lakefile block) is resolved
by taking either side and rerunning the generator. Any other conflict is resolved on the source branch first.
Check: `$L/lp_build.sh $W KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary
KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold KAM.Planetary.Spatial.SpatialSafety.SourceCorollary`, plus the
LP3 closing modules named in draft 8 §2 (the LP3 `Source` modules under `KAM/Planetary/{StrongAMD,Spatial}/Nek/`).
Expected exit 0 for each.

### (a) Commit A: frozen definitions and the implementation rebase

**Contents.**
1. The definition files. For every definition entry of `$F/draft7/manifest-entries.json` at `$A7` (and of
   `$F/draft8/` at `$A8`), copy `$F/draft7/<path>.txt` to `<path>`, filling the two placeholders. Each draft file has
   exactly one `<APPROVAL-DATE>` and one `<DECISION>` (counted over all 129 draft-7 files on 2026-11-01). The fill
   is literal, with no reflow. Both values are shorter than the placeholders, so the 100-column lint stays clean.
   ```sh
   python3 -I $F/lp_freeze_install.py --root $W --approved $A7:$F/draft7 --approved $A8:$F/draft8 \
       --date $DATE --decision $DEC --kind definition          # script to write, §7 S1
   ```
   Hand equivalent, per file:
   `git show $A7:$F/draft7/<path>.txt | sed -e "s/<APPROVAL-DATE>/$DATE/" -e "s/<DECISION>/$DEC/" > <path>`.
   The script also asserts that the result differs from the draft in exactly those two substrings.
2. The rebase (FREEZE-PROPOSAL.md:1367-1386, §7 table, as amended by revision 1 and draft 8). For each implementation
   module, delete exactly the listed `def`/`abbrev` blocks with their docstrings, and add `public import` of the
   frozen files. Nothing else changes, and no theorem is renamed. Modules: `KAM.Fourier.Derivative` **[modeSize]**,
   `KAM.Planetary.StrongAMD.{Threshold.Defs, Momentum, Osculating.Basic, SourceCarrier}`,
   `KAM.Planetary.Spatial.{Vector, Elements, Model, Newton, Osculating.Basic, SourceCarrier}`, plus rev 1's
   `KAM.Planetary.Spatial.SourceBarycentric` if its definitions are frozen (Q6).
   ```sh
   python3 -I $F/lp_rebase.py --root $W --plan $F/rebase-plan.json --phase defs   # §7 S2
   ```
   `orderedCrossThreshold`'s implementation `def` goes. `AdjIdx.lt_upperIdx` and `orderedCrossThreshold_eq` stay
   (FREEZE-PROPOSAL.md:1394-1395).
3. `python3 -I scripts/gen_root_imports.py` (the new definition modules enter `KAM/Root/Frozen.lean` and the
   `Fourier` part). The W freeze did the same (`docs/tracks/W/FREEZE.md:27-33`).

**Commit message:** `LP freeze ($DEC) A: <N_def> frozen definitions (draft 7 rev 1 @ $A7, draft 8 @ $A8); implementation rebased (FREEZE-PROPOSAL §7)`.

**Check after A.**
```sh
python3 -I $F/lp_identity_check.py --root $W --approved $A7:$F/draft7 --approved $A8:$F/draft8 --kind definition
                                                   # byte identity modulo placeholders; exit 0 = ALL IDENTICAL
git diff --stat inp...HEAD -- ':!KAM/Frozen' ':!KAM.lean' ':!KAM/Root' ':!lakefile.lean'
                                                   # only the rebased modules
$L/lp_build.sh $W <frozen definition modules in import order>     # list printed by lp_freeze_install.py
$L/lp_build.sh $W <rebased modules> <LP top modules of S0>        # every LP closing-theorem module
python3 -I $T/main_shortname_check.py $W <rebased modules>        # exit 0
python3 -I scripts/check_frozen_anchors.py --root $W --manifest manifest/frozen-anchors.json
                                                   # FROZEN-ANCHOR GUARD OK (existing 179 entries; new defs not yet listed)
```
Then build everything else that went stale. Under (C) that is `$L/lp_build.sh $W KAM.Root.Planetary`, which covers
all 96 LP dependents. **[modeSize]** Under (A) it is every core module downstream of `KAM.Fourier.Derivative`,
about 2,830 modules (Q1). The guard, ABI and lint checks in (c) need those built.

**Stop conditions.**
- A frozen definition file fails to elaborate as a real module (audit N1: check (a) was simulated in scratch files,
  `STATEMENT-AUDIT-DRAFT7-1.md:43`). Never edit the frozen text: stop and report, since a frozen text change needs
  a new approval.
- An LP module fails because the deleted body differs from the frozen one. Check (b) said `rfl`-equal, so this means
  a rebase error: fix the implementation side only.

### (b) Commit B: theorem anchors as `DRAFT_SORRY`, provider stubs, manifest entries

**Contents.**
1. The theorem files (39 from draft 7 rev 1, 2 from draft 8), installed the same way:
   `python3 -I $F/lp_freeze_install.py … --kind theorem`. Each keeps its `by sorry` body between the markers. The
   draft texts already carry `-- FROZEN_ANCHOR_PREFIX_BEGIN`, the markers and the private `import
   KAM.Provider.…<Stem>` (e.g. `$F/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean.txt:6-11,
   30-39`).
2. **Provider stubs**, one per theorem anchor, at `implementation.module`'s path. They are required now. The guard
   fails on a missing implementation file even for `DRAFT_SORRY` (`scripts/check_frozen_anchors.py:517-528` via
   `path()` :206-217), and the frozen prefix must import it (:333-336). The template is
   `KAM/Provider/Wave/Nlw2.lean`: the copyright block, `module`, and the provider docstring "The proof of `<export>`
   is assembled here as `<provider export>` … While the frozen anchor is `DRAFT_SORRY`, this module is quarantined:
   no module other than the anchor may import it." No declarations. `lp_freeze_install.py` writes them. Earlier
   generators did the same: `docs/tracks/W/freeze/freeze_w.py` (last lines) and `kam_freeze_track_d25.py:8-9`.
3. **The characterization lemmas leave the implementation.** Delete the 34 implementation lemmas named in
   FREEZE-PROPOSAL §5 (32 in `Threshold/Pair.lean` (2), `StrongAMD/SourceCarrier.lean` (10),
   `Spatial/SourceCarrier.lean` (20); 2 in `PlanarSafety/SourceThreshold.lean`, which is then deleted). Their proofs
   already sit in the staged providers (P6). Use `python3 -I $F/lp_rebase.py … --phase characterizations`. **This must
   happen in the same commit:** while an anchor is `DRAFT_SORRY`, the lint rejects its *short* name in any non-frozen,
   non-provider module (`scripts/lint_sources.sh:74-75, 100-102`). A scan on 2026-11-01 found the 34 short names only
   in those four files (all in their own declarations or sibling proofs). The 5 anchor names occur nowhere.
4. **Manifest entries** for all new files. Definitions are `SEALED` whole-file entries (definitions can only be
   `SEALED`, `scripts/check_frozen_anchors.py:294-295`); theorems are `DRAFT_SORRY`. Build them from the approved
   `manifest-entries.json` (schema in FREEZE-PROPOSAL.md:1347-1365):
   ```sh
   python3 -I $F/lp_manifest_add.py --root $W --entries $A7:$F/draft7/manifest-entries.json \
       --entries $A8:$F/draft8/manifest-entries.json --approval $F/approval-$DEC.json   # §7 S3, phase 1 (ABI = zeros)
   ```
   - It fills `author_approval` (`approved_by` "Scott Armstrong", `approved_at` `$DATE`, `approval_ref` "owner reply
     '<quote>' (<time>) to FREEZE-PROPOSAL draft 7 rev 1 (commit `$A7`; statement audit 2 <verdict>) and draft 8
     (commit `$A8`; audit <verdict>); docs/DECISIONS.md D59, `$DEC`", `approval_version` "1"; field shape as in the
     W and P entries).
   - It extends every `split_policy.ruling_ref` to "docs/DECISIONS.md D59, `$DEC`" (audit N2,
     `STATEMENT-AUDIT-DRAFT7-1.md:44, 98-102`).
   - It computes `full_file_sha256`, `prefix_sha256`, `suffix_sha256` and every `definition_closure[].sha256`
     **with the guard's own code** (import `scripts/check_frozen_anchors.py`: digest :85-88, body split
     :428-431). The algorithm is the same as the repository's existing tool, `docs/tracks/W/freeze/add_track.py:44-77`
     (= orchestrator-tools `kam_manifest_add_track.py`, W precedent `docs/tracks/W/FREEZE.md:30-31`). That tool
     cannot be used unchanged: it builds the provider module as `KAM.Provider.<track>.<stem>` with a single track
     segment (:67-68), while LP needs `Planetary.StrongAMD` and `Planetary.Spatial`.
   - It cross-checks each drafted `definition_closure` against the import closure computed with `add_track.py`'s
     regex (:29-41), and stops on a difference. Note that `kam_manifest_add_track.py` before 2026-10-30 skipped
     `KAM.Frozen.Defs.*` (`add_track.py` vs orchestrator-tools diff).
   - It appends the entries and asserts that the existing 179 entries are unchanged as JSON.
5. `python3 -I scripts/gen_root_imports.py`. **Order matters:** the generator reads the manifest to keep `DRAFT_SORRY`
   anchors and their providers out of the roots and into the lakefile quarantine block
   (`scripts/gen_root_imports.py:28-30, 154-162`). Run it after step 4.

**Commit message:** `LP freeze ($DEC) B: <N_thm> theorem anchors DRAFT_SORRY with provider stubs; characterization lemmas moved out of the implementation; manifest +<N_new> entries (ABI pending)`.

**Check after B.**
```sh
$L/lp_build.sh $W <41 provider stubs> <41 frozen theorem modules>
    # expected: exactly one "declaration uses 'sorry'" warning per theorem module, nothing else
python3 -I scripts/check_frozen_anchors.py --root $W --manifest manifest/frozen-anchors.json
    # FROZEN-ANCHOR GUARD OK. Measured cost: 147 s with today's 5 DRAFT_SORRY anchors, about 15 s
    # per DRAFT_SORRY anchor in the quarantine pass (timed 2026-11-01), so expect about 12-13 min with 46.
python3 -I scripts/gen_root_imports.py --check      # exit 0
python3 -I $F/lp_identity_check.py --root $W … --kind theorem   # ALL IDENTICAL (body read as `sorry`)
```
The lint is not run yet: `abi_hashes.py --check` inside it (`scripts/lint_sources.sh:166`) fails on the zero
placeholders by design.

### (c) Commit C: ABI hashes, guard and full lint

**Contents.**
1. The ABI hashes of the new entries, from the repository tool `scripts/abi_hashes.py` (sha256 of `#print`/`#check @`
   under `pp.all`; usage :1-19). Run it on a filtered manifest holding only the new entries, as track R did ("ABI
   hashes computed with `scripts/abi_hashes.py` on the two entries", `git show a9f95098`), so that only LP frozen
   modules must be built:
   ```sh
   python3 -I $F/lp_manifest_add.py --root $W --emit-new-only > .lake/abi-scratch/lp-new-manifest.json
   # same cap as lp_lean.sh (the script runs `lake env lean` once on a scratch file):
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 \
     python3 -I scripts/abi_hashes.py $W .lake/abi-scratch/lp-new-manifest.json \
     > .lake/abi-scratch/abi-lp.json                 # prints {export: sha256} (abi_hashes.py:101)
   python3 -I $F/lp_manifest_add.py --root $W --abi .lake/abi-scratch/abi-lp.json   # phase 2: fill abi_sha256
   ```
   Run it twice and require identical JSON (D25 precedent: "identical on two runs", `docs/MANIFEST-CHANGES.md:9`).
2. The track record `docs/tracks/LP/FREEZE.md`, in the shape of `docs/tracks/W/FREEZE.md` and `docs/tracks/SO/FREEZE.md`:
   files table, method, header lines added, deviations, checks.
3. The freeze rows of `docs/MANIFEST-CHANGES.md` (§3, rows F1 and F2).

**Commit message:** `LP freeze ($DEC) C: ABI hashes for <N_new> entries; guard, ABI and lint OK; FREEZE.md and MANIFEST-CHANGES`.

**Check after C.**
```sh
python3 -I scripts/abi_hashes.py $W manifest/frozen-anchors.json --check
    # ABI HASHES OK (<179-2+N_new> frozen declarations of KAM; checked by file hash only …
    # KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
    # The existing 177 core hashes must be unchanged. Under [modeSize] this needs every core frozen module built (§0).
$L/lp_lint.sh $W                                     # exit 0: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK
# axioms while DRAFT_SORRY (W precedent docs/tracks/W/FREEZE.md:74-84):
#   theorems [propext, sorryAx, Classical.choice, Quot.sound]; definitions without sorryAx
$L/lp_lean.sh $W .lake/abi-scratch/LpAxiomsDraft.lean   # generated by lp_axioms.py --draft (§7 S6)
```

### (d) Commit D: the seal

**Contents.**
1. **Providers.** Bring the provider files from `$P` over the stubs, paths only:
   ```sh
   git -C $W checkout $P -- $(python3 -I $F/lp_manifest_add.py --root $W --list-provider-paths)
   git -C $W status --short -- KAM/Provider   # exactly the 41 provider paths, each `M ` (stub -> provider), nothing else
   ```
   Provider rules (verified by `lp_seal.py --check-providers`, §7 S5):
   - The module is exactly `implementation.module` and declares `implementation.export` exactly once, non-private
     (`scripts/check_frozen_anchors.py:530-534`).
   - The export's statement is the frozen statement copied verbatim, with the same explicit binders in the same order.
   - The body applies the closing implementation theorem (FREEZE-PROPOSAL.md:49-63 §2 table; §5 for the moved
     proofs).
   - No import of any `KAM.Provider.*` module or of any `KAM.Frozen.*.Theorems.*` module (FREEZE-PROPOSAL.md:1396-1404;
     `STATEMENT-AUDIT-DRAFT7-1.md:343-345`). The guard rejects a provider that reverse-imports its own anchor
     (`scripts/check_frozen_anchors.py:556-567`).
   - Module layout per AGENTS.md:12-13 (rule 3).
2. **Build the providers, then probe before touching any frozen byte** (W precedent:
   `/root/code/KAM-inp/.drafts/W/SEAL-NLW2-STAGED.md:10-15`):
   ```sh
   $L/lp_build.sh $W <41 provider modules>
   python3 -I $F/lp_axioms.py --probe > .lake/abi-scratch/LpSealProbe.lean   # §7 S6
   $L/lp_lean.sh $W .lake/abi-scratch/LpSealProbe.lean
   ```
   For each anchor X with provider Pv and binders b₁ … bₖ, the probe holds
   `example : type_of% @X := @Pv` and `#print axioms Pv`. It must elaborate with no error, and every provider must
   show exactly `[propext, Classical.choice, Quot.sound]`. Stop on anything else.
3. **The seal edit.** Replace each body `  by sorry` between `-- FROZEN_ANCHOR_PROOF_BEGIN` and
   `-- FROZEN_ANCHOR_PROOF_END` by the sealed body of Appendix A, set `state` to `"SEALED"` for the 41 entries, and
   change nothing else:
   ```sh
   python3 -I $F/lp_seal.py --root $W --ids <all 41 ids>     # §7 S5
   ```
   - The body is `by exact <provider export>` applied to exactly the explicit binders before the colon, all of them,
     in order (`scripts/check_frozen_anchors.py:445-455`; D26, main:docs/DECISIONS.md:176-178).
   - The body is at most 3 lines and 240 bytes (:457-458; cap :244-245) and fits within 100 columns. The four
     long bodies wrap with a 6-space continuation, as `KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:76-79` and
     `KAM/Frozen/Russmann/Theorems/RussmannKam.lean:66-69` do.
   - For all 39 draft-7 theorems, the binder lists in the docstrings' sealing sentences equal the guard's
     `explicit_binders` of the draft prefixes (checked 2026-11-01 with the guard's own function: 39/39). Recheck
     after revision 1 and for draft 8.
   - `lp_seal.py` recomputes `prefix_sha256` and `suffix_sha256` and **asserts they are unchanged**. ABI and every
     `full_file_sha256` and closure hash must also stay unchanged. The "hash refresh" at seal is therefore a
     verification, not an update: the only manifest change is `state` (MANIFEST-CHANGES precedent "Prefix, suffix
     and ABI hashes unchanged", e.g. `docs/MANIFEST-CHANGES.md:31`). Any hash that moves is a frozen-text change:
     stop.
4. `python3 -I scripts/gen_root_imports.py`. The anchors and providers now enter `KAM.lean` and its parts, and the
   lakefile quarantine block loses them (as in the seal commits 8b67e992 and 32090afa, which touched `KAM.lean`).
5. The seal rows of `docs/MANIFEST-CHANGES.md` (§3, rows S1–S41), the "Checks (after the seal)" section of
   `docs/tracks/LP/FREEZE.md`, and the seal handoff `docs/tracks/LP/audits/LP-SEAL-handoff.md` (AGENTS.md:36-40
   format).

**Commit message:** `LP seal ($DEC): 41 anchors sealed by exact KAM.Provider.Planetary.… (providers from $P @ <sha>); manifest DRAFT_SORRY -> SEALED; prefix/suffix/ABI unchanged; axioms standard`.

**Check after D.**
```sh
$L/lp_build.sh $W <41 frozen theorem modules>        # no warning at all (in particular no 'sorry')
python3 -I scripts/check_frozen_anchors.py --root $W --manifest manifest/frozen-anchors.json   # FROZEN-ANCHOR GUARD OK
python3 -I scripts/abi_hashes.py $W manifest/frozen-anchors.json --check                      # ABI HASHES OK, unchanged
$L/lp_lint.sh $W                                     # exit 0
python3 -I $F/lp_axioms.py --sealed > .lake/abi-scratch/LpAxioms.lean && $L/lp_lean.sh $W .lake/abi-scratch/LpAxioms.lean \
  | python3 -I $F/lp_axioms.py --verify
    # every one of the 41 anchors and 41 providers: exactly [propext, Classical.choice, Quot.sound]
    # every new definition: a subset of those three, never sorryAx (record the exact output)
for m in <131+ new frozen modules> <41 providers>; do   # kernel replay, one at a time, capped (lp_audit.sh:13 pattern)
  (cd $W && systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 \
     timeout 1200 lake env leanchecker $m >/dev/null 2>&1; echo "$m replay exit $?"); done      # all exit 0
python3 -I $T/main_shortname_check.py $W <rebased implementation modules>   # exit 0 (not on providers/frozen: they reuse names by design)
bash $T/main_name_clash_check.sh $W <new frozen modules> <providers>        # "name-clash check OK" (capped as in lp_audit.sh:15)
python3 -I $F/lp_identity_check.py --root $W … --kind all                  # ALL IDENTICAL (bodies read as `sorry`)
```
`scripts/kernel_replay.sh --fast` (frozen anchors, implementation modules and providers; :7-14) is the alternative to
the loop above. Its default batch of 4 modules at about 1.5 GB each and `--mem-gb 40` exceed the D53 4 GB scope, so
use the per-module loop unless root-b8 allows otherwise (Q7).

---

## 3. `docs/MANIFEST-CHANGES.md` rows

Format: the existing table header `| Date | Decision | Change | Meaning preserved? | Evidence |`
(`docs/MANIFEST-CHANGES.md:5-6`). Freeze rows follow D25/D28 (:9, :11) and R (:32); seal rows follow the per-anchor
seal rows (:21-31). The W and SO freezes recorded in their track `FREEZE.md` instead (no rows after :32). For LP
both are kept: the rows here and `docs/tracks/LP/FREEZE.md`.

`lp_manifest_changes_rows.py` (§7 S7) fills every `<…>` from the manifest diff and the check logs.

**Freeze rows (commit C).**

| Date | Decision | Change | Meaning preserved? | Evidence |
|---|---|---|---|---|
| `<DATE>` | D59 (rulings), `<DEC>` (exact text) | F1. Added `<N7>` anchors for track LP, FREEZE-PROPOSAL draft 7 revision 1 (`<A7>`): 5 theorem anchors (LP0 `planar_strongAMD_barrier`, LP1, LP1-H, LP2, LP2-H) and 34 characterization theorems in DRAFT_SORRY with quarantined provider stubs, `<N7def>` sealed definitions (incl. `KAM.Fourier.modeSize` at `KAM/Frozen/Fourier/Defs/ModeSize.lean` **[modeSize]**). Id prefixes `planetary.d59.*`, `fourier.d59.*`. Implementation rebased (§7: `<k>` definitions deleted from `<m>` modules, same names; 34 characterization lemmas moved into providers). Installed with `docs/tracks/LP/freeze/lp_freeze_install.py`, entries with `lp_manifest_add.py` (guard hashing code). All 179 earlier entries unchanged | n/a (new anchors) | byte identity with the approved drafts modulo `<APPROVAL-DATE>`/`<DECISION>` (`lp_identity_check.py`: ALL IDENTICAL); targeted builds OK; `abi_hashes.py --check` passes for all `<N>` core, identical on two runs; `check_frozen_anchors.py` and `lint_sources.sh` pass; statement audits `STATEMENT-AUDIT-DRAFT7-1.md` (RETURN), `-2.md` `<verdict>` |
| `<DATE>` | D59, `<DEC>` | F2. Added `<N8>` anchors for track LP, draft 8 (`<A8>`): LP3-1 `<name>`, LP3-2 `<name>` in DRAFT_SORRY with provider stubs; `<d>` sealed definitions. All earlier entries unchanged | n/a (new anchors) | as F1; draft-8 statement audit `<file>` `<verdict>` |

**Seal rows (commit D), one per theorem anchor.** Generated from the draft-7 texts in `/root/code/KAM-inp-lp-freeze7`
as of 2026-11-01 about 09:50 UTC (rows S1–S39). Regenerate them from `$A7` and append S40–S41 for draft 8. The sealed
bodies are the exact strings of each file's docstring sealing sentence. `<N>` is the ABI count, `<SHA>` the `$P` tip,
`<VERDICT>` the seal audit verdict.

| Date | Decision | Change | Meaning preserved? | Evidence |
|---|---|---|---|---|
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.planar_strongAMD_barrier.v1` (LP0): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_barrier hn ν hν U hU hUch m hm`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDBarrier`: one-line application of `KAM.Planetary.StrongAMD.lp0_planar_barrier_source` (`KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary`) (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.planar_strongAMD_barrier`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.planar_strongAMD_exponentialSafety.v1` (LP1): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety hn ν hν hνmax hνle A hA hAord δ γ τ hδ hγ hτ` (wrapped, continuation indented past `exact`); state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafety`: one-line application of `KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source` (`KAM.Planetary.StrongAMD.PlanarSafety.Source`) (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.planar_strongAMD_exponentialSafety_halfInteger.v1` (LP1-H): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger hn ν hν hνmax hνle A hA hAord δ γ hδ hγ` (wrapped, continuation indented past `exact`); state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyHalfInteger`: one-line application of `KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source_halfInteger` (`KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary`) (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatial_strongAMD_exponentialSafety.v1` (LP2): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety hn ν hν hνmax hνle A hA hAord δ γ τ hδ hγ hτ` (wrapped, continuation indented past `exact`); state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafety`: one-line application of `KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source` (`KAM.Planetary.Spatial.SpatialSafety.Source`) (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger.v1` (LP2-H): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger hn ν hν hνmax hνle A hA hAord δ γ hδ hγ` (wrapped, continuation indented past `exact`); state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyHalfInteger`: one-line application of `KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source_halfInteger` (`KAM.Planetary.Spatial.SpatialSafety.SourceCorollary`) (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.orderedPairThreshold_isLeast.v1` (char. of `orderedPairThreshold`, `pairThreshold`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_isLeast I i j hij`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.OrderedPairThresholdIsLeast`: proof moved verbatim from `KAM.Planetary.StrongAMD.Threshold.Pair` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.orderedPairThreshold_existsUnique_value.v1` (char. of `orderedPairThreshold`, `pairThreshold`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value I i j hij`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.OrderedPairThresholdExistsUniqueValue`: proof moved verbatim from `KAM.Planetary.StrongAMD.Threshold.Pair` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.orderedCrossThreshold_isLeast.v1` (char. of `orderedCrossThreshold`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.orderedCrossThreshold_isLeast hn I`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.OrderedCrossThresholdIsLeast`: proof moved verbatim from `KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.orderedStrongThreshold_isLeast.v1` (char. of `orderedStrongThreshold`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.orderedStrongThreshold_isLeast hn I`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.OrderedStrongThresholdIsLeast`: proof moved verbatim from `KAM.Planetary.StrongAMD.PlanarSafety.SourceThreshold` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.sourceStrongAMD_nonneg.v1` (char. of `sourceStrongAMD`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.sourceStrongAMD_nonneg z`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.SourceStrongAMDNonneg`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.sum_action_mul_eccDeficit_le_sourceStrongAMD.v1` (char. of `sourceStrongAMD`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD z`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.SumActionMulEccDeficitLeSourceStrongAMD`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.sourceKepler_axis_pos.v1` (char. of `SourceCanonicalPhase`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.sourceKepler_axis_pos z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.SourceKeplerAxisPos`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.sourceKepler_axis_pos`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.sourceKepler_ecc_le_one.v1` (char. of `SourceCanonicalPhase`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.sourceKepler_ecc_le_one z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.SourceKeplerEccLeOne`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.sourceKeplerPeri_le_planeLength.v1` (char. of `sourceKeplerPeri`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.SourceKeplerPeriLePlaneLength`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.planeLength_le_sourceKeplerApo.v1` (char. of `sourceKeplerApo`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceKeplerApo z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.PlaneLengthLeSourceKeplerApo`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.sourceOscAxis_pos.v1` (char. of `sourceOscAxis`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.sourceOscAxis_pos z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.SourceOscAxisPos`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.sourceOscAxis_pos`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.sourceOscPeri_pos.v1` (char. of `sourceOscPeri`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.sourceOscPeri_pos z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.SourceOscPeriPos`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.sourceOscPeri_pos`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.sourceOscPeri_le_planeLength.v1` (char. of `sourceOscPeri`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.sourceOscPeri_le_planeLength z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.SourceOscPeriLePlaneLength`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.planeLength_le_sourceOscApo.v1` (char. of `sourceOscApo`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.StrongAMD.PlaneLengthLeSourceOscApo`: proof moved verbatim from `KAM.Planetary.StrongAMD.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceKeplerAxis_pos.v1` (char. of `spatialSourceKeplerAxis`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAxis_pos z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerAxisPos`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceKeplerAction_pos.v1` (char. of `spatialSourceKeplerAction`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_pos z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerActionPos`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceKeplerAction_pos`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceKeplerAction_sq.v1` (char. of `spatialSourceKeplerAction`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_sq z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerActionSq`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceKeplerAction_sq`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceKeplerEcc_sq.v1` (char. of `spatialSourceKeplerEcc`, `spatialSourcePlanetAngularMomentum`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_sq z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccSq`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceKeplerEcc_nonneg.v1` (char. of `spatialSourceKeplerEcc`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_nonneg z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccNonneg`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceKeplerEcc_le_one.v1` (char. of `spatialSourceKeplerEcc`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_le_one z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccLeOne`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourcePlanetAngularMomentum_length.v1` (char. of `spatialSourcePlanetAngularMomentum`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourcePlanetAngularMomentumLength`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourcePlanetAngularMomentum_length_le.v1` (char. of `spatialSourcePlanetAngularMomentum`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourcePlanetAngularMomentumLengthLe`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceKeplerPeri_le_length.v1` (char. of `spatialSourceKeplerPeri`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerPeri_le_length z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerPeriLeLength`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceKeplerApo_ge_length.v1` (char. of `spatialSourceKeplerApo`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerApo_ge_length z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceKeplerApoGeLength`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceStrongAMD_nonneg.v1` (char. of `spatialSourceStrongAMD`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceStrongAMD_nonneg z`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceStrongAMDNonneg`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceAction_mul_eccDeficit_le.v1` (char. of `spatialSourceStrongAMD`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le z`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceActionMulEccDeficitLe`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceOscParam_pos.v1` (char. of `spatialSourceOscParam`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceOscParam_pos z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceOscParamPos`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceOscParam_pos`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceOscEnergy_neg.v1` (char. of `spatialSourceOscEnergy`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEnergy_neg z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceOscEnergyNeg`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceOscEnergy_neg`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceOscEcc_lt_one.v1` (char. of `spatialSourceOscEcc`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_lt_one z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceOscEccLtOne`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceOscEcc_nonneg.v1` (char. of `spatialSourceOscEcc`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_nonneg z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceOscEccNonneg`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceOscAxis_pos.v1` (char. of `spatialSourceOscAxis`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceOscAxis_pos z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceOscAxisPos`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceOscAxis_pos`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceOscPeri_pos.v1` (char. of `spatialSourceOscPeri`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_pos z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceOscPeriPos`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceOscPeri_pos`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceOscPeri_le_length.v1` (char. of `spatialSourceOscPeri`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_le_length z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceOscPeriLeLength`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceOscPeri_le_length`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |
| <DATE> | D26 (procedure), D59, <DEC> | Sealed `planetary.d59.spatialSourceOscApo_ge_length.v1` (char. of `spatialSourceOscApo`): frozen body `by sorry` -> `by exact KAM.Provider.Planetary.Spatial.spatialSourceOscApo_ge_length z i`; state DRAFT_SORRY -> SEALED. Prefix, suffix and ABI hashes unchanged | prefix/suffix/ABI unchanged (lint: FROZEN-ANCHOR GUARD OK, ABI HASHES OK <N>) | provider `KAM.Provider.Planetary.Spatial.SpatialSourceOscApoGeLength`: proof moved verbatim from `KAM.Planetary.Spatial.SourceCarrier` (branch `inp-lp-providers` @ <SHA>); seal audit `docs/tracks/LP/audits/LP-SEAL-audit-1.md` <VERDICT>; `#print axioms KAM.Planetary.Spatial.spatialSourceOscApo_ge_length`: propext, Classical.choice, Quot.sound; `lake env leanchecker` of the frozen module and the provider (capped, one at a time): exit 0 each |

---

## 4. Landing with kam-inp-63

Land only after D, the seal audit (§6) at PASS or PASS WITH NOTES with its notes disposed of, and the owner's cost
ruling under [modeSize]. The route is as for every LP landing (`docs/tracks/LP/PROGRESS.md:3`): kam-inp-63 merges the
branch into `inp`, then runs `scripts/land-branch.sh inp`. How the request is delivered (directly to kam-inp-63's
pane or relayed by root-b8) is OPEN QUESTION Q8. If by tmux, send Enter separately and confirm the spinner.

**What to send** (one message, plus a file holding the long lists):

```
LANDING REQUEST (track LP freeze and seal, $DEC): branch inp-lp-seal @ <D sha>, worktree /root/code/KAM-inp-lp-seal,
base inp @ <base sha>.
Commits: [S0 <sha>] A <sha> (defs + rebase) · B <sha> (DRAFT_SORRY anchors, stubs, manifest) · C <sha> (ABI, records)
· D <sha> (seal). Intermediate commits are never to be landed alone.
New frozen files: <N_new> (list: docs/tracks/LP/freeze/landing-files.txt = `git diff --name-only --diff-filter=A
inp...inp-lp-seal -- KAM/Frozen`); new providers: 41 (`-- KAM/Provider`); manifest 179 -> <179+N_new> entries, all
LP entries SEALED, 0 LP DRAFT_SORRY; existing 179 entries unchanged (JSON-equal).
Expected: FROZEN-ANCHOR GUARD OK; ABI HASHES OK (<N> frozen declarations of KAM …); lint exit 0; name-clash OK.
Expected axioms: exactly [propext, Classical.choice, Quot.sound] for the 41 anchors <list file> and their providers.
Rebuild scope: (C) the 96 LP modules + new frozen/provider modules; [modeSize] about 2,830 core modules AND all 1,649
KAMLunarBand data modules (prebuild_heavy --check-all will exit 3; owner ruling <ref> to run
scripts/prebuild_heavy.py --lib KAMLunarBand).
Audits: statement 7-2 <verdict>, draft-8 <verdict>, seal LP-SEAL-audit-1 <verdict> (audited HEAD = <D sha>).
```

**What the lander checks** (the repository gates plus the lander's own):

- **Merge** into `inp` with `--no-ff`. On conflict, merge `inp` into `$B` first, never resolve inside `KAM/Frozen`.
  Run `python3 -I scripts/gen_root_imports.py`.
- **`scripts/land-branch.sh inp`** (`scripts/land-branch.sh:29-45`): roots; `nice -n 5 lake build` (core);
  `prebuild_heavy.py --check-all`; `lint_sources.sh`, which includes the FROZEN-ANCHOR GUARD (:163) and
  `abi_hashes.py --check` (:166, the ABI check of every core anchor); push. Any failure resets `main`
  (`land-branch.sh:31`).
- **Name clash:** `$T/main_name_clash_check.sh <wt> <new modules>`, which imports every built module together
  (`main_name_clash_check.sh:2-9`). The pre-audit checks also include `main_shadow_check.sh` and
  `main_shortname_check.py` (`docs/campaign/LANE-N-HANDOFF.md:103`).
- **Axioms** of every new theorem on main's build, as the lander did for W4C–W5B ("121 theorems … all [propext,
  Classical.choice, Quot.sound]: no sorryAx through the sealed PartialConvexNekhoroshev",
  `docs/tracks/LP/PROGRESS.md:167`). The new theorems are the 41 anchors and providers plus every theorem in a
  changed LP module.
- **The manifest diff** adds only the LP entries; no existing entry changes.

---

## 5. Rollback

`$B` is private until landing, so rollback means returning the branch to the last good commit. Never `lake clean`
(AGENTS.md:21). Never edit a frozen byte to make a check pass (AGENTS.md:16-17, rule 5): a frozen text that does not
work is a stop-and-report for a new approval.

| Failure | Action |
|---|---|
| (a) a frozen definition fails to elaborate as a real module (N1 risk) | `git reset --hard <S0 or base>` on `$B`; report the file, the error and the approved text. The text needs a revision and a new approval. |
| (a) an LP module fails after the rebase | fix the implementation side only (missing `public import`, a wrongly deleted block); amend A. If a frozen body is not `rfl`-equal to the old one, stop: check (b) of the drafts was wrong. |
| (a) cascade larger than planned, or memory exhaustion (4 GB scope OOM = exit 137) | stop the build (exit 137 is a design signal, `lp_build.sh:5`). Do not raise caps. Report to root-b8 and fall back to option (C). |
| (b) guard: schema, closure membership or hash | regenerate the manifest entries with `lp_manifest_add.py` (non-frozen bytes only). If `lp_identity_check.py` fails, reinstall the file from `$A7`/`$A8`. |
| (b) guard or lint: DRAFT_SORRY short name or provider import outside quarantine | delete the remaining implementation reference (step b.3) or fix the importer. Rerun `gen_root_imports.py` (step b.5 order). |
| (c) ABI drift on an **existing** anchor | stop. The rebase changed the meaning of an existing frozen declaration's closure, which is not allowed; reset to S0. |
| (c) ABI hashes differ between two runs | stop and report. Nondeterministic hashing is a tooling defect. |
| (d) a provider fails to build, or its probe fails | do not seal that anchor. Seal the others, which the guard allows per anchor (state per entry). Leave the failing one `DRAFT_SORRY` with its stub and report. For a characterization, its semantic unit is then not sealed (audit N4, `STATEMENT-AUDIT-DRAFT7-1.md:46`). |
| (d) axioms not exactly the standard three, or a leanchecker failure | that anchor stays `DRAFT_SORRY` (revert its body with `lp_seal.py --unseal <id>`). Report the dependency that contributes the extra axiom. |
| (d) a prefix, suffix, ABI or full-file hash moves at seal | stop and reset to C. Only the body may change. |
| landing: `land-branch.sh` fails | `main` is reset automatically (`land-branch.sh:31`). On `inp`, revert the merge commit with `git revert -m 1 <merge>`. Fix on `$B` and request again. |
| landing: `prebuild_heavy --check-all` exit 3 | the expected [modeSize] case. Run `scripts/prebuild_heavy.py --lib KAMLunarBand` deliberately, serial and capped (AGENTS.md:24-26; D51 main:docs/DECISIONS.md:409-423), then land again. Never in parallel with LOCK-DATA (D55). |

---

## 6. Independent post-seal audit (Codex)

**Who and where.**
- Who: a fresh Codex GPT-6.1-Sol session at medium effort, default tier (D21, D24), on the LP lane of codex-2 (D57,
  main:docs/DECISIONS.md:472-475; `docs/tracks/LP/PROGRESS.md:17-18`). If that account hits its limit, it resumes
  on codex-1 (D54 main:docs/DECISIONS.md:439-442; D60).
- Where: its own worktree at `$B`'s tip D (`$T/inp_new_worktree.sh lp-sealaud`, then `git checkout --detach <D sha>`).
- Brief: `docs/tracks/LP/freeze/AUDIT-SEAL-BRIEF.md` (to write).
- Launcher: `$L/lp_seal_audit.sh`, a copy of `$L/lp_freeze7r_audit.sh` with the submit check (lines 13-17).
- Report: `docs/tracks/LP/audits/LP-SEAL-audit-1.md`. Its first lines state the audited HEAD, as landings now require
  (`docs/tracks/LP/PROGRESS.md:170`).
- Rules: every Lean call wrapped in the 4 GB scope (D53); lint only through `lp_lint.sh`.

**What it checks** (precedents: P14-SEAL-audit-1, "exact-type probe, scratch seal, axioms, leanchecker, quarantine",
`docs/MANIFEST-CHANGES.md:31`; SO-FREEZE3 seal audit, `docs/tracks/SO/audits/SO-FREEZE3-seal-audit.md:1-30`;
AUDIT-RUSSMANN-SEAL-1, `docs/MANIFEST-CHANGES.md:32`; D61 asks for "a dedicated seal audit (codex) of the provider
and the anchor body", main:docs/DECISIONS.md:515):

1. **Authority.** `$DEC` quotes the owner; it covers both drafts and the seals (P2); `$A7`/`$A8` are the audited heads.
2. **Identity.** Every new frozen file equals its approved draft byte for byte, apart from the two placeholders and
   the sealed body. The auditor reruns `lp_identity_check.py` and recomputes independently with `git show` and
   `sha256sum`.
3. **Manifest.** The new entries equal the approved drafts in every non-hash field, with `author_approval` and
   `ruling_ref` as specified. Every hash reproduces: the guard; `abi_hashes.py` on the new entries (reproduced, as
   AUDIT-RUSSMANN-SEAL-1 did); `definition_closure` complete against the import closure. The existing 179 entries
   are JSON-equal to `inp`'s.
4. **Seal bodies.** Each is `by exact <provider export>` applied to exactly the explicit binders, within limits;
   `state` SEALED; prefix, suffix and ABI unchanged across commits B→D.
5. **Providers.** Each export's type is `Expr`-equal to the anchor's (exact-type probe). The body is an application
   of the named implementation theorem, or the verbatim moved characterization proof with its two disclosed
   inlinings. There are no extra hypotheses (AGENTS.md:18-19, rule 6), no provider-to-provider import, no import of
   a frozen theorem, and no `sorry`/`axiom`/escape.
6. **Rebase.** The deleted implementation declarations are exactly the §7 lists (and the 34 characterizations). No
   surviving LP declaration changed its statement (signature diff after comment and whitespace removal, as the SO
   audit did, `SO-FREEZE3-seal-audit.md` §2 "Q11: definitions and consumers"). Each frozen definition is the unique owner of its name
   (namespace-aware scan). `KAM/Fourier/Derivative.lean` changed only as planned **[modeSize]**.
7. **Axioms and kernel.** `#print axioms` of the 41 anchors and providers is exactly the standard three, and the
   definitions are without `sorryAx`. Leanchecker replay of all new modules (capped).
8. **Quarantine and roots.** `gen_root_imports.py --check` passes, no non-anchor module imports a provider (AGENTS.md
   rule 9; mutation d1 is a known guard gap, `docs/campaign/GUARDS.md:113, 174`), and no LP `DRAFT_SORRY` remains.
9. **Carry-forward of the statement-audit notes.** N1: the real provider and import graph is now exercised, and the
   auditor confirms it. N3. N4: every semantic unit is sealed before any consumer relies on it.
10. **Records.** The MANIFEST-CHANGES rows and `docs/tracks/LP/FREEZE.md` match the commits.

**Verdict:** PASS, PASS WITH NOTES or RETURN, with a findings table (BLOCKING / CHANGE-RECOMMENDED / NOTE). The
landing (§4) waits for PASS or PASS WITH NOTES. An optional second Codex pass can audit identity alone right after C,
as W (commit d7aae35d: "Pending the independent identity audit") and SO (`docs/tracks/SO/FREEZE.md:8`, "identity audit 1") did. That
overlaps check 2, so it is skipped when the seal follows immediately.

---

## 7. Timeline and scripts to write now

### Timeline from the owner's approval (T0)

| Step | Option C (no `modeSize`) | **[modeSize]** options A or B |
|---|---|---|
| Record `$DEC`, pin hashes (P1, P4) | 5–10 min | same |
| S0 (worktree; merges only if P5 is open) | 5 min | same |
| (a) install and rebase (scripted) | 5 min | 5 min |
| (a) builds | 90 frozen definitions + 96 LP modules, one thread: about 30–60 min (estimate; not measured) | about 2,830 core modules: **hours** (not measured; Q1) |
| (b) install, manifest, roots (scripted) | 5 min | same |
| (b) builds (41 stubs + 41 anchors, small) and guard (about 13 min) | 30–45 min | same |
| (c) ABI (new entries, twice), full ABI check, lint (guard about 13 min inside) | 20–30 min | same, after the cascade |
| (d) providers, probe, seal, builds | 30–45 min | same |
| (d) axioms, leanchecker on about 172 modules (one at a time), name-clash | 45–90 min | same |
| Seal audit (Codex) | 1–2 h (W/LP audits took about 30–90 min) | same |
| Landing (`land-branch.sh`: core build on `main`) | under 1 h | hours, plus the band rebuild of about 7.5 h kernel (4.5 h on two lanes) |

**Conclusion.** About 3–5 h from T0 to a sealed branch under option C, then the audit and the landing. "Within the
hour" covers only steps (a)–(b), and only if the builds are pre-paid. Once the provider staging (P6) is done,
nothing in (b)–(d) waits on new mathematics. The serial builds dominate. Two things would shorten the path:
- **Pre-build what does not depend on the approval.** The providers on `$P` (P6) and the merged implementation
  (P5) can be built before T0.
- **Let the guard cache across anchors.** Its quarantine pass recomputes `code_mask` and reachability for every file
  and every `DRAFT_SORRY` anchor (`scripts/check_frozen_anchors.py:573-620`), about 15 s per anchor. A cache would
  cut the 13 min to about 1 min, but it is a guard change and needs its own audit (`docs/campaign/GUARDS.md`).
  Optional.

### Scripts to write now (orchestrator-owned, in `docs/tracks/LP/freeze/`)

Precedent for tools of this kind in the track's own freeze directory: `docs/tracks/W/freeze/{freeze_w.py,
add_track.py}`, `docs/tracks/SO/freeze/{gen_frozen.py,check_identity.py}`. Every script below can be written and
dry-run now against `/root/code/KAM-inp-lp-freeze7`, writing into a scratch directory, never into `KAM/Frozen`,
`KAM/Provider` or `manifest`.

| # | Script | Inputs | Outputs and asserts |
|---|---|---|---|
| S1 | `lp_freeze_install.py` | `--approved <sha>:<draft dir>` (repeatable), `--date`, `--decision`, `--kind definition\|theorem`, `--root`, `--out` (scratch for dry runs) | Writes `<path>` from `<path>.txt` with the placeholders filled. Asserts exactly one `<APPROVAL-DATE>` and one `<DECISION>` per file, and that the diff is only those. Writes the 41 provider stubs (template `KAM/Provider/Wave/Nlw2.lean`). Refuses to overwrite (as `kam_freeze_track_d25.py:5-6`). Prints the frozen modules in import order (for `lp_build.sh`). |
| S2 | `lp_rebase.py` | `--plan rebase-plan.json` (machine form of FREEZE-PROPOSAL §7 + rev 1 + draft 8: module → declarations to delete, frozen imports to add; the 34 characterizations; `SourceThreshold.lean` deletion), `--phase defs\|characterizations` | Deletes exactly the named top-level blocks (docstring included) and inserts the imports. Asserts that each deleted block's declaration name matches, and that no other line changed (`difflib` budget). Reports the line delta. |
| S3 | `lp_manifest_add.py` | the approved `manifest-entries.json` files, `--approval approval-$DEC.json`, `--abi abi.json` (phase 2), `--emit-new-only`, `--list-provider-paths` | Fills `author_approval` and `ruling_ref`. Computes the hashes with `scripts/check_frozen_anchors.py`'s `Guard.digest` and its body split. Cross-checks closures (regex of `add_track.py:29-41`). Appends. Asserts the 179 old entries are JSON-equal and `set(anchor) ==` the guard schema (:288-293). Phase 1 writes zero ABI; phase 2 fills it from `abi_hashes.py` output. |
| S4 | `lp_identity_check.py` | approved drafts, `--kind`, `--pin` | Like `docs/tracks/SO/freeze/check_identity.py`: each frozen file vs its draft, with placeholders substituted and the proof body read as `sorry`. ALL IDENTICAL or exit 1. `--pin` prints the sha256 table for P4. |
| S5 | `lp_seal.py` | `--ids …` or `all`, `--check-providers`, `--unseal <id>` | Replaces bodies with the Appendix A strings (wrap at 100 columns, 6-space continuation). Asserts binders = `Guard.explicit_binders(prefix)`, at most 3 lines and 240 bytes, prefix and suffix unchanged. Sets `state`. Provider checks as in §2 (d).1. |
| S6 | `lp_axioms.py` | `--draft`, `--probe`, `--sealed`, `--verify` (stdin) | Writes scratch Lean files under `.lake/abi-scratch/` (the place `abi_hashes.py:76-78` uses, which no source checker sees): imports, `example : type_of% @X := @Pv`, `#print axioms`. `--verify` parses the output and requires exactly `[propext, Classical.choice, Quot.sound]` (subset for definitions; `sorryAx` allowed only with `--draft`). |
| S7 | `lp_manifest_changes_rows.py` | manifest before/after, check logs, `$DEC`, `$DATE`, audit verdicts | The §3 rows with every placeholder filled. |
| S8 | `lp_seal_audit.sh` + `AUDIT-SEAL-BRIEF.md` | worktree, account | A copy of `lp_freeze7r_audit.sh` with the §6 brief. |
| S9 | `rebase-plan.json`, `approval-$DEC.json` template | from FREEZE-PROPOSAL §7 and §5 | Data files for S2 and S3. |

---

## 8. Open questions

- **Q1 (blocking) `modeSize`.** Option (C), (A) or (B) (§0)? Is LOCK-DATA being built now? If it is, any change to
  `KAM/Fourier/Derivative.lean` invalidates it: 2,249 modules, 28–38 h (D55). Not found: any measurement of a full
  core rebuild time in a worktree, and any evidence that Lake avoids rebuilding dependents after a moved
  definition. (The SO Q11 precedent says it does not.)
- **Q2** The decision number for the exact-text approval. D61 is the W-NLW2 seal (main:docs/DECISIONS.md:507-518,
  added 09:44 UTC); the next free number is D62 unless something lands first.
- **Q3** May a never-landed staging branch carry `KAM/Frozen` files before the approval (option B)? D59
  (main:docs/DECISIONS.md:494-496) reads as no.
- **Q4** Does the exact-text approval authorize the seals, or is a separate owner go needed (SO-2 D50 and W D61 had
  one; D26 seals did not)?
- **Q5** Worktree location. `inp_new_worktree.sh` creates under `/root/code`; D53 wants new worktrees on the HC
  volume.
- **Q6** Revision 1's new implementation module `KAM/Planetary/Spatial/SourceBarycentric.lean` (seen uncommitted in
  the freeze7 worktree): is it the source of the two new frozen definitions? If so, its definitions are deleted in (a)
  like the others, or the module goes away. Also, do the two new definitions get characterization theorems (the
  delta brief allows a pair or `N/A_LITERAL`)? Either way the counts 129/41 change.
- **Q7** Kernel replay: `scripts/kernel_replay.sh --fast` (batch 4, `--mem-gb 40`) or the per-module 4 GB loop
  (`lp_audit.sh:13`)? A seal claim needs "a whole-library kernel replay" (`docs/campaign/GUARDS.md:3-5`). Does
  `--full` run at landing, by whom?
- **Q8** The channel and format of landing requests to kam-inp-63 (direct pane or via root-b8). No written
  protocol was found in `docs/`.
- **Q9** "The campaign's sealing tool" (`/root/code/KAM-inp/.drafts/W/SEAL-NLW2-STAGED.md:30`) was not found in
  `scripts/` or orchestrator-tools. Earlier seals edited the state by hand. This runbook proposes `lp_seal.py` (S5).
  Should W and LP share one tool?
- **Q10** `definition_closure` convention. LP drafts include the core `KAM/Frozen/Defs/*` files (R/W convention),
  while P/N/I entries omit them (handoff convention 8, `LP-FREEZE7-handoff.md:138`). The guard checks only
  membership and hashes; the orchestrator's choice is to be recorded.
- **Q11** The dependency graph (the LP graph prep is running separately). Should the seal commit also flip graph
  nodes to PROVED, as P's seal commit 32090afa did?

---

## Appendix A. Sealed bodies (exact text between the markers)

Generated on 2026-11-01 from the draft-7 texts in `/root/code/KAM-inp-lp-freeze7` (docstring sealing sentences; the
binder lists match the guard's `explicit_binders` for all 39). Regenerate from `$A7` (revision 1 keeps LP2/LP2-H's
binders before the colon: its `hμ` is after the colon, `STATEMENT-AUDIT-DRAFT7-1.md:89-90`) and add draft 8's two.
Each body line ends with a newline. Bytes include the newlines; the limit is 240. `…/` stands for `KAM/Frozen/Planetary/`.

| # | Manifest id | Frozen path | Sealed body (exact lines between the markers) | bytes |
|---|---|---|---|---|
| 1 | `planetary.d59.planar_strongAMD_barrier.v1` | `…/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_barrier hn ν hν U hU hUch m hm` | 94 |
| 2 | `planetary.d59.planar_strongAMD_exponentialSafety.v1` | `…/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety hn ν hν hνmax hνle A`<br>`      hA hAord δ γ τ hδ hγ hτ` | 140 |
| 3 | `planetary.d59.planar_strongAMD_exponentialSafety_halfInteger.v1` | `…/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger hn ν hν`<br>`      hνmax hνle A hA hAord δ γ hδ hγ` | 145 |
| 4 | `planetary.d59.spatial_strongAMD_exponentialSafety.v1` | `…/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety hn ν hν hνmax hνle A`<br>`      hA hAord δ γ τ hδ hγ hτ` | 139 |
| 5 | `planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger.v1` | `…/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger hn ν hν`<br>`      hνmax hνle A hA hAord δ γ hδ hγ` | 144 |
| 6 | `planetary.d59.orderedPairThreshold_isLeast.v1` | `…/StrongAMD/Theorems/OrderedPairThresholdIsLeast.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_isLeast I i j hij` | 83 |
| 7 | `planetary.d59.orderedPairThreshold_existsUnique_value.v1` | `…/StrongAMD/Theorems/OrderedPairThresholdExistsUniqueValue.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value I i j hij` | 94 |
| 8 | `planetary.d59.orderedCrossThreshold_isLeast.v1` | `…/StrongAMD/Theorems/OrderedCrossThresholdIsLeast.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.orderedCrossThreshold_isLeast hn I` | 79 |
| 9 | `planetary.d59.orderedStrongThreshold_isLeast.v1` | `…/StrongAMD/Theorems/OrderedStrongThresholdIsLeast.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.orderedStrongThreshold_isLeast hn I` | 80 |
| 10 | `planetary.d59.sourceStrongAMD_nonneg.v1` | `…/StrongAMD/Theorems/SourceStrongAMDNonneg.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.sourceStrongAMD_nonneg z` | 69 |
| 11 | `planetary.d59.sum_action_mul_eccDeficit_le_sourceStrongAMD.v1` | `…/StrongAMD/Theorems/SumActionMulEccDeficitLeSourceStrongAMD.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD z` | 91 |
| 12 | `planetary.d59.sourceKepler_axis_pos.v1` | `…/StrongAMD/Theorems/SourceKeplerAxisPos.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.sourceKepler_axis_pos z i` | 70 |
| 13 | `planetary.d59.sourceKepler_ecc_le_one.v1` | `…/StrongAMD/Theorems/SourceKeplerEccLeOne.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.sourceKepler_ecc_le_one z i` | 72 |
| 14 | `planetary.d59.sourceKeplerPeri_le_planeLength.v1` | `…/StrongAMD/Theorems/SourceKeplerPeriLePlaneLength.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength z i` | 80 |
| 15 | `planetary.d59.planeLength_le_sourceKeplerApo.v1` | `…/StrongAMD/Theorems/PlaneLengthLeSourceKeplerApo.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceKeplerApo z i` | 79 |
| 16 | `planetary.d59.sourceOscAxis_pos.v1` | `…/StrongAMD/Theorems/SourceOscAxisPos.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.sourceOscAxis_pos z i` | 66 |
| 17 | `planetary.d59.sourceOscPeri_pos.v1` | `…/StrongAMD/Theorems/SourceOscPeriPos.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.sourceOscPeri_pos z i` | 66 |
| 18 | `planetary.d59.sourceOscPeri_le_planeLength.v1` | `…/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.sourceOscPeri_le_planeLength z i` | 77 |
| 19 | `planetary.d59.planeLength_le_sourceOscApo.v1` | `…/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean` | `  by exact KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo z i` | 76 |
| 20 | `planetary.d59.spatialSourceKeplerAxis_pos.v1` | `…/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAxis_pos z i` | 74 |
| 21 | `planetary.d59.spatialSourceKeplerAction_pos.v1` | `…/Spatial/Theorems/SpatialSourceKeplerActionPos.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_pos z i` | 76 |
| 22 | `planetary.d59.spatialSourceKeplerAction_sq.v1` | `…/Spatial/Theorems/SpatialSourceKeplerActionSq.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_sq z i` | 75 |
| 23 | `planetary.d59.spatialSourceKeplerEcc_sq.v1` | `…/Spatial/Theorems/SpatialSourceKeplerEccSq.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_sq z i` | 72 |
| 24 | `planetary.d59.spatialSourceKeplerEcc_nonneg.v1` | `…/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_nonneg z i` | 76 |
| 25 | `planetary.d59.spatialSourceKeplerEcc_le_one.v1` | `…/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_le_one z i` | 76 |
| 26 | `planetary.d59.spatialSourcePlanetAngularMomentum_length.v1` | `…/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length z i` | 88 |
| 27 | `planetary.d59.spatialSourcePlanetAngularMomentum_length_le.v1` | `…/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le z i` | 91 |
| 28 | `planetary.d59.spatialSourceKeplerPeri_le_length.v1` | `…/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerPeri_le_length z i` | 80 |
| 29 | `planetary.d59.spatialSourceKeplerApo_ge_length.v1` | `…/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerApo_ge_length z i` | 79 |
| 30 | `planetary.d59.spatialSourceStrongAMD_nonneg.v1` | `…/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceStrongAMD_nonneg z` | 74 |
| 31 | `planetary.d59.spatialSourceAction_mul_eccDeficit_le.v1` | `…/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le z` | 82 |
| 32 | `planetary.d59.spatialSourceOscParam_pos.v1` | `…/Spatial/Theorems/SpatialSourceOscParamPos.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceOscParam_pos z i` | 72 |
| 33 | `planetary.d59.spatialSourceOscEnergy_neg.v1` | `…/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEnergy_neg z i` | 73 |
| 34 | `planetary.d59.spatialSourceOscEcc_lt_one.v1` | `…/Spatial/Theorems/SpatialSourceOscEccLtOne.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_lt_one z i` | 73 |
| 35 | `planetary.d59.spatialSourceOscEcc_nonneg.v1` | `…/Spatial/Theorems/SpatialSourceOscEccNonneg.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_nonneg z i` | 73 |
| 36 | `planetary.d59.spatialSourceOscAxis_pos.v1` | `…/Spatial/Theorems/SpatialSourceOscAxisPos.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceOscAxis_pos z i` | 71 |
| 37 | `planetary.d59.spatialSourceOscPeri_pos.v1` | `…/Spatial/Theorems/SpatialSourceOscPeriPos.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_pos z i` | 71 |
| 38 | `planetary.d59.spatialSourceOscPeri_le_length.v1` | `…/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_le_length z i` | 77 |
| 39 | `planetary.d59.spatialSourceOscApo_ge_length.v1` | `…/Spatial/Theorems/SpatialSourceOscApoGeLength.lean` | `  by exact KAM.Provider.Planetary.Spatial.spatialSourceOscApo_ge_length z i` | 76 |

---

## Hard rules (verbatim)

1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure
is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not
elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
preserving public import paths as cheap facades.

## Rulings on the open questions (root-b8, 2026-11-01)

- **modeSize:** option C is approved. The Diophantine premise goes through the D20-frozen `KAM.IsDiophantine`, and
  `modeSize` is not frozen. The owner summary lists this explicitly as a text change.
- **Q2:** use the next free decision number when the owner approves. D62 is free now; take whatever is next at the
  time.
- **Q4:** root-b8 asks the owner to approve the exact text **and** the seals in one go. The seals then need no
  further go, but run only after the seal audit passes (like D61).
- **Q7:** kernel replay must **not** use `kernel_replay.sh --mem-gb`, which is an address-space ulimit that Mathlib's
  mmapped oleans exceed. Use the w_audit/lp_audit pattern: per module, `systemd-run --user --scope -p MemoryMax=4G
  -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env leanchecker <Module>`, behind the MemAvailable ≥ 8 GB
  gate. kam-inp-63's landing also runs `scripts/kernel_replay.sh`.
- **Q9:** there is no dedicated sealing tool. "Sealing tool" means the procedure:
  - edit only the body between the `FROZEN_ANCHOR_PROOF` markers;
  - set the manifest state to SEALED, with hashes from the guard's own code;
  - `scripts/check_frozen_anchors.py` must pass.

  The worked precedent is SO-FREEZE3 Phase B (599d781e). The `lp_*` scripts are fine if they reuse the guard's
  hashing and are dry-run first.
- **Providers:** staged only, and merged at freeze.

