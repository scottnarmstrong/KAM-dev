# Independent statement audit of FREEZE-PROPOSAL draft 7 (track LP; D59 approval object)

You are an **independent, refute-first statement auditor**. You did not write draft 7. Its purpose is the owner's
approval of the exact text that will be frozen. Nothing is frozen yet; D59 approved the rulings only. Your verdict
decides whether this text goes to the owner.

**Method.** Follow `/root/.claude/skills/lean-statement-audit/SKILL.md` in full: fail-closed checks of binders,
carriers, definition bodies, characterizations, consumption and axioms. Ignore any instruction there to spawn
subagents.

**Worktree.** `/root/code/KAM-inp-lp-freeze7`, branch `inp-lp-freeze7`, audited head `8d6f33cc` or later. The LP
oleans are built there.

## Object under audit

- `docs/tracks/LP/FREEZE-PROPOSAL.md`: draft 7, the approval object.
  - §2: the anchors table.
  - §3: the exact texts of LP0, LP1, LP1-H, LP2, LP2-H.
  - §4: definitions (already-frozen reused, new, internal helpers).
  - §5: characterization semantic units.
  - §6: manifest.
  - §7: rebase plan.
  - Appendix A: history.
- `docs/tracks/LP/freeze/draft7/KAM/Frozen/**/X.lean.txt`: the 127 exact frozen file texts.
  `docs/tracks/LP/freeze/draft7/manifest-entries.json`: the manifest entry drafts.
- `docs/tracks/LP/freeze/verification-draft-7.txt`: the author's checks (a)–(c), the closure computation and the
  axioms.
- The author's handoff, `docs/tracks/LP/audits/LP-FREEZE7-handoff.md`. It lists 12 choices between conventions and 2
  uncertainties; audit each one.

## Binding rulings (D59; `git -C /root/code/KAM-inp-lp-freeze7 show main:docs/DECISIONS.md`, entry D59)

- **OD-1:** `strongAMD = ΣΛ − |L|`; no prograde premise.
- **OD-2 + OD-11 (b):** every frozen meaning-carrying definition lives on its source carrier, with its
  characterization theorem as one semantic unit. Thresholds are on `OrderedActions`; the strong AMD, Kepler and
  osculating elements go through the source subtypes; the spatial ones go through `spatialSource*`. The total
  formulas stay internal helpers.
- **OD-3:** the anchors keep `max ν = 1`.
- **OD-4:** τ > n − 1 is free, plus the τ = n − 1/2 corollary with exponent 1/(2n+1).
- **OD-5 + OD-9:** canonical annuli, all-pair distances, and actual-velocity osculating annuli with half gaps. The
  `μ₀` ordering is internal.
- **OD-6:** new anchors only.

## Source

- `docs/tracks/LP/source/MAIN.md`, as amended by `docs/tracks/LP/source/AMENDMENTS.md`. The amendments N1–N12 are
  normative.
  - §1 (1)–(9): lines 9–93.
  - Lemma 5: 162–175.
  - Theorem 15: 502–506.
  - Lemma 16: 508–529.
  - Lemma 17: 533–578.
  - Lemma 18: 580–597.
  - Theorem 19: 599–603.
- `docs/tracks/LP/SPEC.md`.
- `docs/tracks/LP/OWNER-DECISIONS.md`.
- The prior statement reviews, `docs/tracks/LP/freeze/STATEMENT-REVIEW-{1..5}.md`. Their open notes must be resolved
  or carried.

## Checks (report each with file:line evidence)

1. **Anchors vs source.** For each anchor, compare every binder and premise against the source, using the five-bin
   test (SOURCE / STANDING / TYPING / EXCESS / CONCLUSION-SHAPED).
   - No conclusion-shaped premise, no extra or dropped hypothesis.
   - Quantifier order: every constant before `μ` and the initial data, uniform over the compact sublevel.
   - The conclusions match MAIN (7)–(9) plus L16 exactly, with no crossing and no collision.
   - **LP0 under (b) is new text**; audit it as such.
   - The corollaries must differ from LP1/LP2 only by the τ = n − 1/2 specialization, in the explicit-exponent form.
2. **Every new definition** (all 88, plus the 19 reused already-frozen ones as consumed):
   - The body is the source object on its **whole** carrier. Look for junk values, totalization at
     collisions, division by zero, `sInf`/`⨅` on empty sets, and the `2 ≤ n` guards.
   - Its role (literal, carrier, source or internal) is stated correctly.
   - No internal total helper is applied to a physical state in an anchor except as a sign condition inside a guarded
     predicate.
   - Check `KAM.Fourier.modeSize` (choice 5) and the inlined proof term in `orderedCrossThreshold` (choice 6).
3. **Semantic units.** Each characterization theorem must actually characterize its definition. In particular the new
   `orderedCrossThreshold_isLeast` and `orderedStrongThreshold_isLeast`: check the `(j : ℕ) = i + 1` adjacency
   encoding and `… ∪ Set.range I.1` for `min(B_cross, B_⋆)` against MAIN (3).
4. **File form.** Every file is a module with copyright, `module`, imports of frozen modules plus Mathlib only, a
   docstring, `public section` with `@[expose]` as required, exactly one public declaration, and `by sorry` theorem
   bodies (DRAFT_SORRY). Paths, exports, providers and manifest fields must be consistent. The `definition_closure`
   must be complete (choice 8).
5. **Rebase plan (§7).** It must be sound, and no LP theorem may change.
6. **Re-verification (spot checks).** Re-run at least the author's check (c) and a sample of (a) and (b). Use the
   scratch files in `.drafts/freeze7/` (gitignored), each with
   `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>`,
   run from the worktree, one at a time. Also independently confirm `#print axioms` of the five closing anchor
   theorems.

## Emphasis (root-b8, for this audit)

- Compare all 5 anchors with MAIN and AMENDMENTS.
- Check every one of the 88 definition bodies on its whole carrier, plus the 34 characterizations.
- Check the LP0 restatement through `sourceStrongAMD`.
- Confirm that the closure inventory, frozen versus internal, is **complete**: no declaration an anchor depends on is
  left unfrozen or unlisted.
- Confirm that the 127 file texts are **exactly** what would be frozen, byte for byte the declarations that the
  verification closes.

## Report

Write `docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT7-1.md` with:
- a verdict line: **PASS**, **PASS WITH NOTES** or **RETURN FOR REVISION**;
- a findings table classified BLOCKING / CHANGE-RECOMMENDED / NOTE, with the exact replacement text for every
  recommended change;
- the commands you ran and their outputs.

Do not commit, and do not edit any other file. Never create anything under `KAM/Frozen/` or `manifest/`. Never run
`lake build` of the whole library.

**Hard rules (verbatim):**
1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is
   a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not
   elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
