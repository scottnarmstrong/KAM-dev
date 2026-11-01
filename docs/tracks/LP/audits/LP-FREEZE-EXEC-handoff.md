# Handoff LP-FREEZE-EXEC: freeze and seal of track LP's draft 7 r1 (D62), one pass

Branch `inp-lp-freeze` (worktree `/root/code/KAM-inp-lp-freeze`, off `inp` 6798a3c5). One pass, one landing
(orchestrator plan change, root-b8): the 39 theorem anchors are installed directly with their sealed bodies, the
providers are in the same branch, and all 128 manifest entries are SEALED (precedent: track R). Draft 8 (LP3) is
**not** included (orchestrator clarification: D62 approves draft 7 r1 only).

## Commits

| Commit | Content |
|---|---|
| ad2c28fe, 8e6f75d0 | S0: merge `inp-lp`, then the approved `de343000` (`--no-ff`); approval object identical to de343000; roots unchanged |
| 172f4234 | A: 89 frozen definitions; implementation rebased (89 `def`/`abbrev` blocks deleted from 11 modules, frozen imports added); `KAM/Root/Frozen.lean`; the scripts |
| 9a23d75c | B: 39 theorem anchors sealed; 39 providers; 34 characterization lemmas moved into the providers (`PlanarSafety/SourceThreshold.lean` deleted); manifest +128 SEALED (ABI zero placeholders); roots; `replay-modules.txt`; `identity-check.txt`. `.drafts/READY-LP-FREEZE-EDITS` was touched at this point (before a message-only amend of B; same tree) |
| a4eecfc1 | C: ABI hashes; `docs/tracks/LP/FREEZE.md`; 128 MANIFEST-CHANGES rows (D62); probe, axioms and ABI outputs |

## Scripts (`docs/tracks/LP/freeze/`; the guard's own code for every hash, split and binder list)

`lp_freeze_lib.py` (it loads `scripts/check_frozen_anchors.py` and uses `Guard.digest`,
`Guard.check_theorem_region`, `Guard.explicit_binders`), `mk_rebase_plan.py` → `rebase-plan.json` (from the
approved §7/§5 tables), `lp_rebase.py`, `lp_freeze_install.py` (`--sealed`), `lp_providers.py`,
`lp_manifest_add.py`, `approval-D62.json`, `lp_identity_check.py`, `lp_axioms.py` and
`lp_manifest_changes_rows.py`. The whole edit sequence was first dry-run into a scratch tree, where the identity
check gave ALL IDENTICAL and the guard passed on an exported copy of the tree. The real run is byte-identical to
the dry run.

## Checks (exact outputs in the committed files)

- **Identity** (`identity-check.txt`): 128 files checked, ALL IDENTICAL. Against de343000's draft, only the two
  placeholders (`2026-11-01`, `D62`) and, for theorems, the body between the markers differ.
- **Guard**: `python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json` →
  FROZEN-ANCHOR GUARD OK. 307 entries: the 179 earlier ones JSON-equal, plus 128 new, all SEALED.
- **Build**: `lp_build_fast.sh /root/code/KAM-inp-lp-freeze KAM.Root.Planetary KAM.Root.Provider KAM.Root.Frozen` →
  "Build completed successfully (11090 jobs)", rc 0, 11:04 UTC. 287 modules were built (the 284 replay modules
  and 3 roots); no warning and no `sorry` in any new or changed file. Rebuild estimate given beforehand: about 284.
- **ABI**: two runs on the 128 new entries were identical. `abi_hashes.py --check` gives "ABI HASHES OK (305 frozen
  declarations of KAM …)"; the 177 earlier core hashes are unchanged.
- **Lint**: `lp_lint.sh` exit 0 (check_lean_modules PASS 4225 files, FROZEN-ANCHOR GUARD OK, ABI HASHES OK 305).
- **Expr-equality and axioms** (`seal-probe-verify.txt`; probe `LpSealProbe.lean.txt`, run with `lp_lean.sh`):
  ALL OK. For 39/39, `example : type_of% @X := @Pv` elaborates and the types are `Expr.eqv`. All 39 anchors and 39
  providers give exactly `[propext, Classical.choice, Quot.sound]`; the 89 definitions give a subset of these.
- **Kernel replay**: per module, capped (`systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10
  env LEAN_NUM_THREADS=1 lake env leanchecker <Module>`), behind the 8 GB gate, never `kernel_replay.sh --mem-gb`,
  over `docs/tracks/LP/freeze/replay-modules.txt` (284 modules: 128 frozen, 39 providers, 117 rebuilt LP modules).
  **Pre-landing replay stopped by orchestrator at 128/284 (all exit 0); full replay at landing.** The 128
  replayed modules are the 128 frozen modules, all exit 0 (`docs/tracks/LP/freeze/replay-prelanding.txt`). The
  authoritative full replay of `replay-modules.txt` is the lander's 3-worker landing replay; the seal auditor
  replays the 39 anchors and 39 providers.

## Deviations and notes for the seal audit

1. **Characterization providers.** f2fa9f88's 34 characterization providers apply the implementation lemmas.
   Those lemmas have the frozen theorems' fully qualified names and are deleted at the freeze (FREEZE-PROPOSAL §7
   point 3), so those providers cannot be used as they are. The installed providers keep f2fa9f88's statement text
   and header, and carry the implementation proofs moved verbatim. The two sibling uses are inlined as `private
   theorem`s with the sibling's exact statement and proof. The 5 anchor providers are f2fa9f88's, byte for byte.
2. **Approved text untouched.** Every installed frozen file is the approved draft plus the two placeholders and the
   sealed body; nothing was reflowed.
3. **Provider docstrings.** The 5 copied anchor providers keep f2fa9f88's sentence "While the frozen anchor is
   `DRAFT_SORRY` (or not yet created), this module is quarantined …", which is now historical (they are sealed).
4. **Implementation docstrings.** `StrongAMD/SourceCarrier.lean`'s module docstring still lists the characterization
   names. They now name the frozen theorems with the same names, so the text stays accurate.
5. **Draft 8.** Not touched. `inp-lp-freeze8` stays at its WIP commit 3a8e8b67.

Hard rules: no heartbeat override; no file over 1500 lines (largest new provider 69 lines); no axiom, admit, unsafe
or sorry.
