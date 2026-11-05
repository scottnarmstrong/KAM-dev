# Package LP-FREEZE8-EXEC: install draft 8 (LP3) frozen and sealed in one pass (D64)

**D64** (main `14fe69d6`, 2026-11-01, 14:20 UTC). The owner approved draft 8 with the words "approve draft 8". The
approval object is **`inp-lp-freeze8r` at `6c168945`**: `docs/tracks/LP/FREEZE-PROPOSAL-DRAFT8.md`, plus the two
anchor texts and `manifest-entries.json` under `docs/tracks/LP/freeze/draft8/`, byte for byte. D64 installs them **in
one pass, already sealed, as D62 did.** Read D64 in full with `git show main:docs/DECISIONS.md`.

**Worktree:** `/root/code/KAM-inp-lp-freeze8x`, branch `inp-lp-freeze8x`, cut at `6c168945`. That commit sits on the
current `inp` (`2bbacd66`) with the staged providers. Its build already includes the landed D62 freeze.

## Procedure: FREEZE-PROPOSAL-DRAFT8 §6 exactly, with D62's scripts in `docs/tracks/LP/freeze/`

1. Run `lp_freeze_install.py --sealed` from `$A8 = 6c168945`, filling **only** `<APPROVAL-DATE>` with `2026-11-01`
   and `<DECISION>` with `D64`. The 2 anchors are installed with their sealed one-line `by exact KAM.Provider.… …`
   bodies, and the 2 staged providers are installed.
2. Run `lp_identity_check.py`. It must show that only the two placeholders and the proof body between the
   `FROZEN_ANCHOR_PROOF` markers differ from `6c168945`. Record the output.
3. Run `lp_manifest_add.py` to add 2 entries, directly SEALED, hashed by the guard's own code, with
   `author_approval`/`ruling_ref` citing D64. Every existing entry must stay JSON-equal. Then run `abi_hashes.py` on
   the 2 new entries twice (identical results), then `lp_manifest_add.py --abi`.
4. Regenerate the roots (`scripts/gen_root_imports.py`), and add 2 MANIFEST-CHANGES rows citing D64 and the
   `docs/tracks/LP/FREEZE.md` update.
5. **N3 (from the draft-8 audit):** in `KAM/Planetary/StrongAMD/Nek/PlanarSafety/Source.lean`, lines 15 and 36,
   change the docstrings from `LP:MAIN L15 (502–506)` to `LP:MAIN T15 (502–506)`. This is implementation docstring
   only.
6. **Commit the content.** Then `touch .drafts/READY-LP-FREEZE8-EDITS` **before** the build. The orchestrator starts
   the seal audit in parallel at that point.
7. **Build and check.**
   - Build the 2 frozen anchor modules, the 2 providers, the edited `Source` module and the LP3 modules, with
     `/root/code/KAM-inp/.drafts/LP/lp_build_fast.sh <worktree> <targets…>`: one 12 GB scope, about 4 jobs,
     `MemAvailable ≥ 14 GB`.
   - Then `scripts/check_frozen_anchors.py`, `lp_lint.sh` (exit 0), the ABI check, the Expr-equality probe of each
     provider against its anchor, and `#print axioms` of both anchors and both providers. They must be exactly
     `[propext, Classical.choice, Quot.sound]`.
   - Write the replay module list to `docs/tracks/LP/freeze/replay-modules-d64.txt`: the changed and rebuilt modules
     only.
8. Commit, write the handoff, and `touch .drafts/READY-LP-FREEZE8-P1`. The orchestrator lands it after the seal audit
   passes.

## Rules

- **Approved text is immutable.** If any installed file needs a change beyond the two placeholders and the sealed
  body, STOP and report it.
- **Hard rules (verbatim):**
  1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration
     failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
     proof will not elaborate at default heartbeats, report it as a design signal.
  2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
     preserving public import paths as cheap facades.
- Builds only through the LP wrappers. Never `lake clean`. Never build the certificate libraries.
- No sorry, axiom or unsafe. Never kill processes by name. Never search the whole filesystem.
- **Do not push to `inp` or `main`.**

## Handoff

`docs/tracks/LP/audits/LP-FREEZE8-EXEC-handoff.md` (committed).
