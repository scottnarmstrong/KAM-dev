# Package LP-CLEANUP1: LP clean-up, tier 1, and errata merge (D69)

The ruling is D69 (`git show main:docs/DECISIONS.md`); root-b8 took the recommendations. The input is
`docs/tracks/LP/CLEANUP-AUDIT.md`, the report on this branch. Branch `lp-cleanup` is off main, in worktree
`/root/code/KAM-inp-lp-cleanup`, whose build is current with the LP freeze.

## Part 1: Lean clean-up, tier 1 (the audit's §§1–3 and §6)

- **Stale comments.** Replace or remove:
  - the sentence "The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md." It is now frozen;
    point to `docs/tracks/LP/FREEZE.md` or drop it;
  - the package labels (`Package LP-…`, `LP-SP-…`, `LP3-…`);
  - the "draft" wording;
  - the ten `L15` locators, which become `T15`;
  - in the providers, the quarantine and draft wording, **in comments only**. Provider code and statements stay
    unchanged.
- **Dead code.** Delete the 114 dead declarations the audit lists, after re-verifying each one by grep, which must
  include dot-notation, attribute and `simp` uses. Keep anything a frozen file or provider references.
- **Superseded helpers,** only where no re-proof is needed. Leave `DiophantineBridge` and the
  `_source` → `_isDiophantine` chain alone.
- **Literal duplicates.** Collapse the 8 clusters into one declaration each, re-pointing the uses. Retire
  `Spatial/SpatialSafety/Bridge.lean` if the merge makes it redundant (keep a facade if anything imports it).
- **No renames.** Do not touch:
  - anything under `KAM/Frozen/`, or `manifest/`;
  - provider statements;
  - the 15 headline names cited in `papers/LP/NOTES.md`;
  - every LEAN_REF in `docs/graph/LP/`. Grep the graph: none may move.

## Part 2: errata

- Merge the 29 entries of `docs/tracks/LP/errata-proposed.json` into `docs/errata/ledger.json`, following its schema
  and policy. CANDIDATE entries stay CANDIDATE.
- Add the source `LPMAIN` (`docs/tracks/LP/source/MAIN.md`, with its sha256) to `docs/sources.json` in its format.
- Regenerate the errata page with the repository's generator (find it in `scripts/`).

## Checks

- `/root/code/KAM-inp/.drafts/LP/lp_build.sh` for every touched LP module, then the LP facades and the providers.
  For a large rebuild, use `lp_build_fast.sh` (12 GB scope, gated on MemAvailable ≥ 14 GB).
- `/root/code/KAM-inp/.drafts/LP/lp_lint.sh` must exit 0.
- `scripts/check_frozen_anchors.py` must report OK.
- `#print axioms` of the 41 LP anchors (via `lp_lean.sh`), exactly standard.
- The graph's structural lint (`scripts/proof_depgraph.py … --check`, as in `docs/graph/LP/reports/`) must exit 0.
- A diff summary: lines removed and edited, per category.

## Hard rules (verbatim)

1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is
   a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not
   elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.

Also: no sorry, axiom or unsafe; one build at a time, under the 4 GB caps; never `lake clean`; never kill processes by
name; never search the whole filesystem.

## Handoff

`docs/tracks/LP/audits/LP-CLEANUP1-handoff.md` (committed), then `touch .drafts/READY-LP-CLEANUP1`.
