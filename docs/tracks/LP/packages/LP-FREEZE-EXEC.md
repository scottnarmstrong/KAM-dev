# Package LP-FREEZE-EXEC: freeze, then seal, the owner-approved LP statements (D62)

**D62** (main 7394d94e, 2026-11-01): the owner approved draft 7 r1, "approve draft 7". The approval object is
**`inp-lp-freeze7` at `de343000`**: `docs/tracks/LP/FREEZE-PROPOSAL.md` and the 128 files under
`docs/tracks/LP/freeze/draft7/`, byte for byte. That is 5 anchors (both corollaries included), 34 characterization
theorems and 89 definitions. D62 covers the freeze **and** the seals. The seals land only after a dedicated seal
audit passes, with no further owner go. Read D62 in full: `git show main:docs/DECISIONS.md`.

**Procedure:** `docs/tracks/LP/freeze/RUNBOOK.md` on `inp-lp`. Read all of it, including the "Rulings on the open
questions" section at its end. Follow its order exactly. The worked precedent is SO-FREEZE3 Phase B (`599d781e`) and
the earlier freeze commits it cites.

## Phase 1: the freeze (top priority)

1. **Worktree and branch.**
   - Create a dedicated worktree on a new branch `inp-lp-freeze` from the current `inp` (or `main` if the runbook says
     so), with the repository's worktree tool. RUNBOOK S0: `inp_new_worktree.sh`; check its path under
     `/mnt/HC_Volume_106379410/orchestrator-tools/`.
   - It must get the copy-on-write build snapshot. **Never rebuild the library from scratch.**
2. **Install** (RUNBOOK step (a)/(b)).
   - Take the frozen files from de343000's `draft7/**.txt`. Fill **only** `<APPROVAL-DATE>` with `2026-11-01` and
     `<DECISION>` with `D62`.
   - Write `lp_identity_check.py`. It must prove that the diff of every installed file against its draft text is
     exactly those placeholder substitutions; record its output.
   - Install the 89 definitions and the 34 characterizations, then the 5 DRAFT_SORRY anchors.
   - Rebase the implementation per proposal §7: delete the implementation `def`s, import the frozen files. Names stay
     unchanged; no LP theorem statement changes.
   - The implementation files that must already be on the branch are LP-FREEZE7R's new modules
     (`SourceBarycentric`, `DiophantineBridge`, `PlanarSafety/{SourceThreshold,SourceDiophantine,SourceCorollary}`,
     `SpatialSafety/SourceCorollary`). They are on `inp-lp-freeze7`; bring them in as the runbook says.
   - Provider stubs follow the runbook's guard requirement; the real providers come in phase 2.
3. **Manifest.** Add the entries with hashes computed by the guard's own code (`scripts/check_frozen_anchors.py` and
   its helpers), state DRAFT_SORRY, `author_approval` per D62, `ruling_ref` including D62. The existing entries must
   stay untouched. Then compute the ABI hashes (`scripts/abi_hashes.py`), regenerate the roots, and fill in
   `FREEZE.md` and the MANIFEST-CHANGES rows (one per entry, citing D62).
4. **Checks, all of which must pass:**
   - `scripts/check_frozen_anchors.py`;
   - `lp_lint.sh` exit 0;
   - the ABI check;
   - `lp_build.sh` of every LP module;
   - a kernel replay of every new frozen module and every rebased LP module, per module with
     `systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env leanchecker <Module>`
     behind the MemAvailable ≥ 8 GB gate. **Never** use `kernel_replay.sh --mem-gb`.
5. **Commit and report.** Commit in the runbook's order: separate commits for definitions plus rebase, then anchors
   plus manifest, then hashes and records. Write `.drafts/READY-LP-FREEZE-P1` and tell the orchestrator. The
   orchestrator lands the freeze through the lander. Do not push to `inp` or `main` yourself.

## Phase 2: the seals (after phase 1 is committed)

On a branch `inp-lp-seal` from `inp-lp-freeze`:
- Copy the providers from `inp-lp-providers` (f2fa9f88) over the stubs.
- Write the one-line `by exact KAM.Provider.… …` body between the `FROZEN_ANCHOR_PROOF` markers of each of the 39
  theorem anchors. Edit nothing else.
- Set the state to SEALED, with hashes from the guard's code.
- Run `check_frozen_anchors.py`, lint, ABI, the Expr-equality of each provider against its anchor, and
  `#print axioms` of all 39 anchors (exactly `[propext, Classical.choice, Quot.sound]`). Do a kernel replay of the
  anchor and provider modules.
- Fill the MANIFEST-CHANGES seal rows citing D62.
- Commit, then `touch .drafts/READY-LP-FREEZE-P2`. The orchestrator runs the dedicated seal audit (codex-2) before
  anything lands.

## Rules

- **Approval object.** Touch no draft7/ file and no proposal text; de343000 is the approved object. If an installed
  file needs any change beyond the two placeholders, STOP and report. Never "fix" approved text.
- **Hard rules (verbatim):**
  1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration
     failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
     proof will not elaborate at default heartbeats, report it as a design signal.
  2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
     preserving public import paths as cheap facades.
- **Builds.** One targeted build at a time, through the LP wrappers (`lp_build.sh`, `lp_lean.sh`, `lp_lint.sh`),
  capped at 4 GB. Never `lake clean`. Never build the certificate libraries.
- No axiom, admit or unsafe. The only `sorry` allowed is the manifest-bound DRAFT_SORRY body of a frozen anchor
  between its markers, in phase 1 only.
- Never kill processes by name. Never search the whole filesystem.

## Handoff

Write `docs/tracks/LP/audits/LP-FREEZE-EXEC-handoff.md` (committed) with each phase's commits, check outputs, the
identity-check output and the axioms.
