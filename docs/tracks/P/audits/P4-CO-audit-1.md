# Independent P4-CO package audit 1

Audited HEAD: `85e9096c9ba45505a55f7804cb84c6fa35d8129d`.

**Overall verdict: FAIL (hygiene only).** The mathematics, four required signatures, definition and proof dependencies pass. `KAM/Planetary/PGMeasure/Collar.lean:113` has 101 Unicode characters and fails the required source lint. The brief permits the stale generated-root failure only. Copying a design signature does not exempt a line from the length check. Wrap this statement line without changing its tokens, then rerun lint. No production fix was made during this read-only audit.

**Anchor status:** P4-CO is a helper package, with no provider export or frozen theorem seal. P-G (`KAM.Planetary.properlyDegenerateKAM`) remains `DRAFT_SORRY` in the manifest; this audit gives no seal-ready verdict for that anchor. Provider/frozen-type equality and a frozen seal-body probe are therefore inapplicable here. The four package interfaces were independently elaborated against the design instead.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the exact `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, local P4-CO-handoff.md, the P45 design including row P4-CO and its proof plans, design audits 1–3 in `docs/tracks/P/design/`, the shared `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, blueprint-P Part 4 and relevant Part 5 consumers, track P statement.md, the frozen P-G telescope and relevant frozen definitions. The explicit user destination overrides the generic brief's MAIN-worktree destination. Only `KAM/Planetary/PGMeasure/Collar*.lean` is audited as production scope; Setting is inspected as an imported interface.

`git diff inp...HEAD` reports two additions: Collar.lean (249 lines) and inherited PGMeasure/Setting.lean (111 lines). Git warns of multiple merge bases and selects `f11c90357967f666b1673409df890dbcec823dff`. The observed `inp` ref was `aa359d8fcbe90f6489dc2c4a3ccaf7b5a8e7f8ec`. The focus comparison `git diff inp-p4s...HEAD -- 'KAM/Planetary/PGMeasure/Collar*.lean'` shows only the 249-line Collar addition; observed inp-p4s was `262629ac064c7af227b2306f465a5799cf6339e7`. Unrelated differences against that branch, including Tonelli, are outside this audit.

## Declaration and node verdicts

Names below are in `KAM.Planetary`; line numbers refer to Collar.lean.

| Node / role | Declaration | Verdict | Evidence |
|---|---|---|---|
| bpP:p4:ext-conn | `ext_conn` (29) | PASS | Exact design signature; preconnectedness suffices without nonemptiness/closedness assumptions on V. Separation by interior V and complement of closure V proves frontier crossing. Exported before collar. |
| bpP:p4:domain-collar, product step | `realNbhd_joinedActions` (57) | PASS | Exact identity for the Pi max metric, arbitrary sets and every real s. Witness construction and Fin.append cover empty sets, zero dimensions and nonpositive radii without infDist fallbacks. |
| Product coordinate adapter | `blockSplitEquiv` (85) | PASS | Genuine measurable equivalence on the whole carrier; classification below. |
| Adapter identification | `blockSplitEquiv_apply` (90) | PASS | Both coordinate blocks agree exactly with the frozen-compatible projections. |
| Volume adapter | `measurePreserving_blockSplitEquiv` (96) | PASS | Composition of Mathlib coordinate-permutation and sum/product volume equivalences. No determinant/normalization factor omitted. |
| Product volume | `volume_joinedActions` (102) | PASS | Lebesgue outer measure equality for arbitrary factors; uses measurable equivalence preimage and product rectangle volume, without hidden measurability premises. |
| bpP:p4:domain-collar, difference step | `domain_collar_helper` (110) | PASS mathematically; FAIL hygiene | Exact design signature, unnormalized estimate and shell exponent. Extra hypotheses hX, hl, hsl, hXfinite are prescribed, not newly introduced. Line 113 exceeds 100 characters. |
| bpP:p4:collar, co-compact/co-meas/co-nbhd | `collar` (166) | PASS | All four design clauses are present. Compactness and exact difference hold for every t>0, independently of t<d; loss bounds retain t<d. No connectedness, positivity of A/d or positive-volume core assumption is added. |

All four named design signatures are identical after whitespace normalization to both the design appendix and the shared fixture. The scratch probe copies each telescope and conclusion, changes it to `example`, and applies the implementation to every explicit argument in order: `ext_conn hC hCV hCc`, `collar hV hVb hc`, `realNbhd_joinedActions X Y s`, and `domain_collar_helper hX hl hlu hs hsl hXfinite hE`. Final probe elaboration exits 0. The first probe attempt incorrectly used unapplied theorem names inside already-introduced telescopes and exited 1; those errors were in the auditor's probe, repaired before the successful rerun.

The earlier design F1/N2 repairs remain implemented. Collar compactness follows from the closed intersection of closure V with all closed distance constraints, and boundedness. The neighbourhood proof crosses the frontier along a segment and bounds its distance from the core point by the endpoint distance. Monotonicity against hc supplies both loss bounds; the lower-volume result uses ENNReal truncated subtraction and union subadditivity, without an invalid subtraction identity for nonmeasurable sets.

For the domain estimate, the slow neighbourhood lies in the box (l-s,u+s)^b. The product difference lies in the union of the fast collar times that box and X times the slow box difference. Product volume and measurable finite shell subtraction yield exactly the displayed bound. The proof handles E<0 explicitly; no nonnegative-E premise or division by core volume is smuggled in. The normalized estimate and full shell-neighbourhood equality in the larger blueprint lemma are not claimed exports of this helper package; the approved P4-CO row requests this unnormalized helper.

## Definitions, hypotheses and imports

The only new definition is `blockSplitEquiv`: a coordinate permutation from Fin(a+b) to Fin a ⊕ Fin b followed by splitting a function on a sum into a product. It is the intended bijection for all a,b and all input vectors, including empty blocks. There are no junk values, total inverse fallbacks, new structures, instances or bundled proof assumptions. It is exposed by the section annotation.

Imported `realNbhd` is witness based; `innerCore` universally bounds distance to frontier points; `actionShell` is the open coordinate box; `joinedActions` uses the literal fast/slow projections. No carrier or norm replacement occurs. Imported PGData is unused by these proofs; hc is exactly the fixed-A,d instance of the frozen hboundary, not a new conclusion-shaped premise. The standard compactness and topology facts are proved or supplied by Mathlib.

Direct imports are Mathlib and KAM.Planetary.PG.Setting. A recursive scan of all KAM imports finds definition anchors only, no frozen theorem module and no provider module. Thus no DRAFT_SORRY theorem enters the package import closure. The frozen P-G theorem was read as audit evidence, not imported into the proof probe.

## Independent validation

All Lean/Lake commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource override, clean/update/cache action or source rebuild was requested.

1. Targeted gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4co KAM.Planetary.PGMeasure.Collar
   [inp-gate] slot 1 acquired 08:49:33 for KAM.Planetary.PGMeasure.Collar
   ⚠ [9062/9062] Replayed KAM.Planetary.PGMeasure.Collar
   Build completed successfully (9062 jobs).
   ```

   Exit 0. Only unused-variable warnings: hX at 110:52, hl at 111:19, hsl at 111:59, hXfinite at 112:5. This was a cached replay of the targeted module, not 9062 newly compiled jobs.

2. Interface and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4COAudit.lean
   'KAM.Planetary.ext_conn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.realNbhd_joinedActions' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.blockSplitEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.measurePreserving_blockSplitEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.volume_joinedActions' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.domain_collar_helper' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.collar' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Final exit 0; every new public theorem is covered.

3. Kernel replay (one invocation; this package has a single module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.Collar
   replaying KAM.Planetary.PGMeasure.Collar
   ```

   Exit 0.

4. Source lint, including its serialized ABI elaboration:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   Lean lines over 100 characters:
   /root/code/KAM-inp-p4co/KAM/Planetary/PGMeasure/Collar.lean:113:101
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (494 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Exit 1. The generated-root line is the explicitly permitted exception; the 101-character line is an additional failure. No other lint failures were emitted. The handoff's wording “PASS except” does not satisfy the specified gate for this extra failure.

Static hygiene: 249 lines, valid copyright/module/public-import/docstring/public exposed section; no forbidden proof escape, resource option or EuclideanSpace token. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (apart from Git's multiple-merge-base diagnostic). `git diff --check inp...HEAD` exits 0. The branch comparison against inp-p4s has inherited generated-root changes, outside Collar scope; the required inp protected-path comparison is clean.

## Defects, limitations and handoff

The sole new requested correction is to wrap Collar.lean:113. Its verbatim text is:

```lean
    volume (realNbhd (joinedActions X (actionShell b l u)) s \ joinedActions X (actionShell b l u)) ≤
```

A safe report-only replacement is:

```lean
    volume (realNbhd (joinedActions X (actionShell b l u)) s \
      joinedActions X (actionShell b l u)) ≤
```

No suspected new pinned-paper defect, false blueprint assertion used by the proof, frozen-statement defect or mathematical deviation was found within scope. Existing CP10 collar allegations are not independently re-adjudicated here. Dropping connectedness/positive A,d in the helper yields a stronger valid statement, already approved in the design. The four unused assumptions preserve that exact interface. No claim is made that later assembly consumers or the P-G anchor are proved.

The pre-existing untracked P4-CO-handoff.md is preserved. The only persistent audit edit is this report in the user-specified worktree; no Git mutation or production edit was made. The scratch probe was deleted. Final status lists only this report and that pre-existing handoff as untracked; no tracked modification. Final report checks confirm balanced fences, terminal newline and no trailing whitespace; `git diff --check` exits 0.

## Orchestrator addendum (hygiene fix, 2026-10-28)
The single blocking finding (Collar.lean:113, 101 characters) is fixed in the commit after this audit by wrapping the
line before `\ joinedActions`. Verified by the orchestrator (whitespace-only fix, no Codex delta round): whitespace-stripped
contents identical before and after; the module rebuilds through the compile gate; `lake env leanchecker
KAM.Planetary.PGMeasure.Collar` exits 0; no line exceeds 100 characters; `git diff --check` clean. The audit's
mathematical verdict (signatures, definitions and proofs pass) stands: **PASS WITH NOTES** after this fix.
