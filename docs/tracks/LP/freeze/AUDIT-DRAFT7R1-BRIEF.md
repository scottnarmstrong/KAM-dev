# Delta statement audit of FREEZE-PROPOSAL draft 7 revision 1 (track LP; D59 approval object)

You are an **independent, refute-first statement auditor**, starting as a fresh session. Follow
`/root/.claude/skills/lean-statement-audit/SKILL.md`, and ignore any instruction there to spawn subagents.

**Round 1 audit**, of draft 7 at the audited HEAD `809aa0dd`, returned RETURN FOR REVISION:
`docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT7-1.md`. Its findings were:
- **F1, BLOCKING:** the spatial barycentric reconstruction maps were used as physical maps on their whole carrier.
- **F2:** the role paragraphs of `actionAxis`, `eccDeficit` and the two raw spatial maps.
- **N2:** the sentence on what changes at freeze.
- N1, N3 and N4: notes.

Revision 1 (package LP-FREEZE7R) applies F1, F2 and N2. It is in your worktree, `$W`, on the branch named in the
launcher prompt. The author's record is `docs/tracks/LP/freeze/verification-draft-7r1.txt`, with the handoff
`docs/tracks/LP/audits/LP-FREEZE7R-handoff.md`.

## Scope (root-b8)

1. **F1.** The two new source definitions `spatialSourceBarycentricPositions` and `spatialSourceBarycentricVelocities`
   must have exactly the auditor's text, be definitionally the raw maps, and carry correct role paragraphs. In LP2 and
   LP2-H:
   - the binder must be `∀ μ : ℝ, ∀ hμ : 0 < μ, μ ≤ μ₀ →`;
   - the reconstruction must go through the source maps with `hν hμ`;
   - the binder must be **typing data, not a new premise**: the mathematical content of the anchors must be
     unchanged, and their closing theorems must still close, by `exact` or, where option C (item 4) applies, by a
     one-line term over the proved bridge lemma.

   Check the treatment of characterizations under OD-11 (b) for the two new definitions: either a characterization
   pair, or `N/A_LITERAL` with a valid reason. Check consistency with the frozen planar barycentric maps.
2. **F2.** The four role paragraphs must be the auditor's exact text. §4.2 must say `internal`, and §4.4 must list the
   four.
3. **N2.** The sentence must be exact.
4. **Option C (orchestrator addition, from the freeze runbook, docs/tracks/LP/freeze/RUNBOOK.md).**
   - Freezing `KAM.Fourier.modeSize` would rebase the shared `KAM/Fourier/Derivative.lean`. So revision 1 states the
     Diophantine premise of LP1, LP1-H, LP2 and LP2-H through the already-frozen
     `KAM.IsDiophantine γ τ (fun i => ν i ^ 3 / Λ_i ^ 3)` (`KAM/Frozen/Defs/IsDiophantine.lean`, D20).
   - `modeSize` is removed from the frozen set.
   - **Check that this is a literal equivalence and not a change of meaning** (root-b8: on the exact frequency vector
     `ν_i³/Λ_i³`, with the same ℓ¹ size and the same `γ`, `τ`): the same ℓ¹ mode size, `γ s^{−τ} =
     γ/s^τ` for `k ≠ 0`, the same `ω_i = ν_i³/Λ_i³`, and the `τ = n − 1/2` forms. Check that the bridge lemma is
     proved, that the closure, manifest and rebase plan no longer contain `modeSize`, and that Appendix A records the
     change.
5. **Nothing else changed.**
   - Recompute the sha256 of every draft file under `docs/tracks/LP/freeze/draft7/` (127 or more) and diff them
     against the audited state at `809aa0dd` (`git show 809aa0dd:<path> | sha256sum`).
   - Every changed or new file must be explained by F1, F2, N2 or option C.
   - Diff the proposal and the manifest drafts the same way.
6. **Re-verification.** Re-run the author's check (c) for LP2 and LP2-H and for any new characterization, check (a)
   for every changed or new file, and check (b) for the two new definitions. Confirm `#print axioms` (standard).
   - Use `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
     lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>` from your worktree, one at a time.
   - Scratch files go in `.drafts/` of your worktree.
7. **Carry-forward.** Restate whether N1, N3 and N4 are carried correctly.

## Report

Write `docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT7-2.md` in your worktree. Its first lines must state the audited
HEAD (`git rev-parse HEAD`). Then:
- a verdict: **PASS**, **PASS WITH NOTES** or **RETURN FOR REVISION**;
- a findings table classified BLOCKING / CHANGE-RECOMMENDED / NOTE, with exact replacement text;
- the hash-diff table;
- the commands you ran and their outputs.

Do not commit. Edit no other file. Never create anything under `KAM/Frozen/` or `manifest/`.

**Hard rules (verbatim):**
1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is
   a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not
   elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
