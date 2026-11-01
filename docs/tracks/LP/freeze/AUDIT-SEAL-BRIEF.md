# Dedicated seal audit of the LP freeze and seals (D62)

You are an **independent, refute-first seal auditor**, starting as a fresh session. Follow
`/root/.claude/skills/lean-statement-audit/SKILL.md` for the identity and statement parts, and ignore any instruction
there to spawn subagents.

**Authority.** D62 (`git show main:docs/DECISIONS.md`, entry D62): the owner approved draft 7 r1 byte for byte (the
approval object is `inp-lp-freeze7` at `de343000`), with freeze and seals. The seals land only after **this** audit
passes. **Draft 8 (LP3) is not approved.** Nothing from `docs/tracks/LP/freeze/draft8/` may appear under
`KAM/Frozen/` or in the manifest.

**Object.** At the owner's request (via root-b8), the freeze and the seal are ONE pass on ONE branch with ONE landing,
as track R did on 2026-10-30 ("froze and sealed"; see `docs/MANIFEST-CHANGES.md`). The object is branch
`inp-lp-freeze`, in your worktree at the HEAD named in the launcher. It installs the 128 frozen files with the 39
theorem anchors **already sealed** (`by exact KAM.Provider.…`), the 39 providers, and the manifest entries directly in
state SEALED. There is no DRAFT_SORRY stage. The author's capped build and lint run **in parallel** with your audit.
If the author's later commits on the branch change anything you have checked, re-check those files before your
verdict, and state the final HEAD you certify. The author's records are
`docs/tracks/LP/audits/LP-FREEZE-EXEC-handoff.md` (it may still be in progress), `docs/tracks/LP/FREEZE.md` and the
`docs/MANIFEST-CHANGES.md` rows.

**Staging (parallel run).**
1. Start with every check that needs no Lean build: authority, identity, manifest fields and hashes via the guard's
   code, seal-body text, rebase signature diffs, quarantine and roots, and records.
2. The Lean checks (Expr-equality probe, `#print axioms`, leanchecker) need the new modules built. The author is
   building them now in their own worktree. When the build is green, the orchestrator copies the built `.lake/build`
   into your worktree and tells you in this pane. Do not build the whole branch yourself. A capped single-file probe
   with `lake env lean` is fine once the build is in place.

**Procedure reference:** `docs/tracks/LP/freeze/RUNBOOK.md` §2 (commits A–D) and **§6** (your ten checks). Read both,
and the rulings at the end of the runbook. The precedents §6 cites are SO-FREEZE3 seal audit, P14-SEAL and
AUDIT-RUSSMANN-SEAL-1.

## Checks: RUNBOOK §6 items 1–10, with these adjustments

1. **Authority.** It covers draft 7 r1 only. The audited heads are `de343000` (draft) and the seal HEAD.
2. **Identity.** All **128** new frozen files must equal their approved `draft7/**.txt` at `de343000` byte for byte,
   except the two placeholders (`2026-11-01`, `D62`) and, for the 39 theorem anchors, the sealed body between the
   `FROZEN_ANCHOR_PROOF` markers.
   - Rerun `lp_identity_check.py`.
   - Recompute independently: `git show de343000:<draft path>` and `sha256sum`, then the placeholder substitution.
3. **Manifest.**
   - The new entries must equal the approved drafts (`draft7/manifest-entries.json` at `de343000`) in every non-hash
     field, with `author_approval` and `ruling_ref` citing D62.
   - Every hash must reproduce with the guard's own code and `scripts/abi_hashes.py`.
   - `definition_closure` must be complete.
   - All pre-existing entries must be JSON-equal to `inp`'s.
4. **Seal bodies.** Each of the 39 must be `by exact <provider export> <explicit binders>` within the guard limits,
   with state SEALED. Outside the body between the markers, every anchor file must equal its approved draft (placeholders filled).
5. **Providers.** Run the exact-type probe: each provider type must be `Expr`-equal to its anchor. Each body must be
   a one-line application of the named proved implementation theorem, or the moved characterization proof, with any
   inlining disclosed. There must be no extra hypothesis, no provider-to-provider or frozen-theorem import, and no
   `sorry`, `axiom` or escape.
6. **Rebase.**
   - The deleted implementation declarations must be exactly proposal §7's lists plus the 34 characterizations.
   - No surviving LP declaration may change its statement (signature diff).
   - Each frozen definition must be the unique owner of its name.
   - **Option C:** `KAM.Fourier.modeSize` is NOT frozen, so `KAM/Fourier/Derivative.lean` must be **unchanged** and
     no lunar certificate data may be touched.
7. **Axioms and kernel.**
   - `#print axioms` of the 39 anchors and their providers must be exactly `[propext, Classical.choice, Quot.sound]`.
   - The definitions must be free of `sorryAx`.
   - Replay the kernel for every new frozen module, per module, with
     `systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env leanchecker <Module>`
     behind the MemAvailable ≥ 8 GB gate. **Never** use `kernel_replay.sh --mem-gb`.
8. **Quarantine and roots.** `scripts/gen_root_imports.py --check` must pass. No non-anchor module may import a
   provider. No LP `DRAFT_SORRY` may exist; every new LP entry is SEALED.
9. **Carry-forward.** The real provider and import graph is now exercised (draft-7 audit note N1); confirm it. N3, and
   N4 (every characterization is sealed before any consumer relies on it).
10. **Records.** The MANIFEST-CHANGES rows (freeze and seal, citing D62) and `docs/tracks/LP/FREEZE.md` must match
    the commits.

## Report

Write `docs/tracks/LP/audits/LP-SEAL-audit-1.md`. Its first lines state the audited HEAD (`git rev-parse HEAD`).
Then:
- a verdict: **PASS**, **PASS WITH NOTES** or **RETURN**;
- a findings table classified BLOCKING / CHANGE-RECOMMENDED / NOTE, with exact fixes;
- the commands and outputs.

The landing waits for PASS or PASS WITH NOTES. Do not commit. Edit no other file. Run every Lean call inside the 4 GB
scope (D53), one at a time. Lint only through `/root/code/KAM-inp/.drafts/LP/lp_lint.sh`. Never build the
certificate libraries.

**Hard rules (verbatim):**
1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is
   a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not
   elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
