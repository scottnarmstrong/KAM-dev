3fabe89f2f819dd39e0c740bec8e24cb7b237df9

Verdict: **RETURN**

Independent, refute-first CHEAP diff audit of `git diff main...HEAD`, branch `lp-cleanup`.
Merge base: `2dad481b844c48a3cbdf43af7bcef996b04eec2e`. Read AGENTS.md, PLAN.md,
DECISIONS.md (including D69), LP-CLEANUP1.md and LP-CLEANUP1-handoff.md.
The diff contains 191 files, including 183 Lean files; KAM totals are +544/-1237 lines.
No build, Lean elaboration, lint suite, axiom probe, or state-changing git command was run.
Only this report was written. Consumer reads outside the diff serve solely to test the deleted-name claims.

| ID | Result | Finding and evidence | Required disposition |
|---|---|---|---|
| F1 | RETURN | Deleted `KAM.Planetary.StrongAMD.lpChart_isOpen_dom` is still used in tracked `applications/hd11964/HD11964/HoloG2.lean:120`: `(lpChart_isOpen_dom 2).mem_nhds hz`. That file opens `KAM.Planetary.StrongAMD` at line 29. The declaration was removed from `KAM/Planetary/StrongAMD/PlanarDictionary.lean`. | Restore this used declaration under the package's keep-used rule. Application opt-in build scope does not make a branch consumer unused. |
| F2 | RETURN | The edited source comment at `KAM/Planetary/StrongAMD/PlanarSafety/Constants.lean:17` still reads ``Source: (planar theorem LP1, `LP:MAIN L14 (468–500)`, `L15`), track LP, non-frozen.`` MAIN:502 is **Theorem 15**; MAIN:502–506 is the correct locator. | Replace this remaining `L15` with `T15 (502–506)`. The handoff's claim that all L15 locators were corrected is incomplete. |
| F3 | NOTE / literal scope exception | `docs/graph/LP/DEPGRAPH.md:10` changes only the FROZEN_MANIFEST hash, correctly. However, `docs/graph/LP/SPEC.md:447–451` also adds a five-line changelog entry. Thus “nothing else in the graph changed” is literally false, although no graph node, edge, status, or LEAN_REF changed. | If the requested graph-only-hash condition is literal, remove the extra SPEC change or obtain an explicit allowance. This documentation addition is not a semantic graph mutation. |
| F4 | NOTE | Unchanged graph report `docs/graph/LP/reports/lean-ref-map.txt:57–58,133` still names deleted `lpChart_eccentricity_sq` and `isSpatialMovingSolutionOn_rotate_iff`. These are historical matching suggestions, not LEAN_REF records or Lean consumers. | Record this documentation consequence; do not silently treat these historical rows as live LEAN_REF failures or modify the graph during this audit. |
| C1 | PASS | No diff path is under `KAM/Frozen/` or `manifest/`. All 41 changed provider files have exactly equal code after removal of nested block comments and line comments, with strings preserved and blank lines ignored. | Provider statements and proofs are unchanged. |
| C2 | FAIL via F1 | Extracted 97 deleted Lean declarations: 96 cleanup deletions plus `exists_spatialBudget_radius`. An exact-identifier search across all 4,483 tracked Lean files, allowing preceding dots, finds exactly the F1 use. No deleted name is referenced in frozen files, providers, `papers/LP/NOTES.md`, or graph LEAN_REF records. | Keep the F1 declaration. Remaining 96 deleted names have no surviving Lean textual occurrence. |
| C3 | PASS | All 1,190 surviving named declaration signatures in changed Lean files compare equal after comment and whitespace normalization; no declarations were added and no renames were found. The only added noncomment lines are the new planar Constants import and the call to `exists_budget_radius`. | No statement drift found. |
| C4 | PASS | The deleted `exists_spatialBudget_radius` and surviving `exists_budget_radius` have literally identical normalized binders and conclusions after substituting only the declaration name. The new public import makes the existing StrongAMD theorem available to Aligned, which already opens StrongAMD. | Faithful duplicate re-pointing; no re-proof or premise change. |
| C5 | PASS WITH NOTE | Ledger JSON parses; its old entry prefix, policy and status vocabulary are unchanged. Exactly 29 entries are appended, byte-content-equivalent as parsed objects to the proposal: 8 errata and 21 deviations, no ID collisions; all required entry fields are nonempty strings and statuses obey the type-specific vocabulary. Six CANDIDATE entries remain CANDIDATE, two errata remain CONFIRMED, and 21 deviations remain ADOPTED. | This is a merge/schema/policy audit, not independent mathematical verification of all 29 allegations. CONFIRMED entries explicitly retain their existing verification caveats. Proof supplements remain deviations. |
| C6 | PASS | Existing LPMAIN registration equals the source file's actual SHA-256; sources.json is absent from the diff. `python3 scripts/render_errata.py --check` exits 0 with no output. | No registration or generated-page discrepancy. |
| C7 | PASS, except F3 | Actual frozen manifest SHA-256 equals the new pin. DEPGRAPH's entire diff is that one header line; all other graph content is unchanged except the SPEC changelog described in F3. | Correct re-pin. |

Verification evidence and limits:

- Read-only git checks: `git status --short` initially empty; `git rev-parse HEAD` gives the first line above;
  `git merge-base main HEAD` gives the recorded base; `git diff --name-only main...HEAD` gives 191 paths;
  `git diff --check main...HEAD` exits 0, no output.
- Inline Python compared merge-base blobs from `git show` against HEAD files using a nested-comment scanner
  that preserves string literals. Output: `PROVIDER_CODE_EQUAL 41`, `SURVIVING_SIGNATURES 1190`,
  `DIFFERENCES []`, `DELETED_NAMES 97`. Normalized code diff has precisely two added lines:
  `public import KAM.Planetary.StrongAMD.PlanarSafety.Constants` and the re-pointed budget call.
  This also checks for surviving code edits beyond signatures; none were found beyond that call/import.
- Deleted-name searches used identifier boundaries rather than requiring whitespace, so qualified names,
  dot notation, attributes and simp references are included. Initial `rg -n --glob '*.lean'` search found F1;
  a second scan over **all `git ls-files` Lean paths**, including applications and regardless of ignore rules,
  confirmed exactly that one occurrence. Searched graph LEAN_REF lines separately from historical reports.
- Comment review sampled the large mechanical package/freeze/quarantine rewording and source labels;
  MAIN:502–506 was read directly. A full residual `L15` grep across the changed implementation/provider
  areas found the single F2 locator. Corrected T15 locators agree with the source. This does not certify
  every unchanged source locator. PlanarDictionary's retained module summary still advertises deleted
  one-line chart corollaries (lines 28–33); that pre-existing summary becomes stale after the deletions.
- JSON checks compared the complete old ledger prefix and the complete 29-object proposal, checked required
  fields and allowed statuses for every added entry, and checked uniqueness of all ledger IDs.
  No candidate was upgraded. LP-E-01 transparently records a historical typo already fixed in MAIN; its
  CONFIRMED status is not a claim that the current pinned text still contains that typo.
- Actual source digest (`hashlib.sha256` over file bytes):
  `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b`
  for `docs/tracks/LP/source/MAIN.md`, equal to `docs/sources.json` LPMAIN.sha256.
- Actual manifest digest:
  `80b8a24ab90efec860ab85772d5292636c653407534da59b09a6d8302c4308f6`
  for `manifest/frozen-anchors.json`, equal to DEPGRAPH.md:10.
- No changed Lean file approaches the 1,500-code-line cap: the largest comment-stripped, nonblank file
  has 414 lines (`KAM/Planetary/StrongAMD/Geometry.lean`). No new heartbeat override or prohibited Lean
  construct is introduced: the complete added noncomment code is the import and call recorded above.
- No build or `#print axioms` result is claimed from this audit. The handoff's build/axiom receipts were read
  but not reproduced; F1 is a direct textual consumer failure independent of those receipts. No new pinned
  source defect was discovered. The reported failures concern cleanup and documentation.

Lean hard rules (verbatim):

1. Never use set_option maxHeartbeats (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules, preserving public import paths as cheap facades.
