# S10 independent package audit 1

Audit date: 2026-10-28. Auditor marker: `maud-p14-s10-1`.

**Overall verdict: PASS WITH NOTES for S10 (`KAM.Planetary.sb_unique`).**
The signed contract and all three assigned proof nodes are established; the independent
Lean probe, kernel replay, targeted build, frozen guard and ABI checks passed. The sole
validation note is the brief-permitted stale generated `KAM.lean` warning.
There is no S10 provider/anchor to seal; no verdict of seal-readiness is issued for the
larger frozen `KAM.Planetary.secularBoxSafety` anchor, whose assembly is outside scope.

Scope is only `KAM/Planetary/SecularBox/Uniqueness.lean`, HEAD
`cd7f46c12a65c7814bef0456e60bf9f25f935c72`. The comparison ref `inp` resolved to
`4a5b757e944936d0ae6e9269a1170dc7098e4240` when inspected.
The complete `git diff inp...HEAD` includes inherited Field (287 lines), SlowFlow (204),
GlobalFlow (171), S7 audit/handoff, and the target Uniqueness module (94).
Inherited files were inspected for context; this report does not re-audit S7–S9.
The initially untracked `S10-handoff.md` is user-supplied input and was preserved.
The user's explicit absolute report destination overrides the generic brief's MAIN-worktree destination.

Read governing AGENTS/PLAN/DECISIONS, the package brief, S10 handoff, P14 design row S10 and
node table, design audits 1–2, authoritative P14Signatures, track-P statement, blueprint
p14b lines 268–275 and its graph packet, the frozen secular-box target and meaning-carrying
solution/Hamiltonian definitions, and the actual ODE uniqueness/S7 interfaces.

## Declaration and node ledger

| Node / declaration | Implementation locator | Verdict | Evidence |
|---|---|---|---|
| `bpP:p14:sb-unique` / `KAM.Planetary.sb_unique` | Uniqueness:61–90 | PASS | Exactly the signed telescope, including implicit binders, premise order, all real mu, and full pointwise equality on U. |
| `stepP:p14:sb-un-1` | Uniqueness:71,77–87,89 | PASS | A is the agreement set; zero belongs by h0/hv0. Continuity excludes unequal values at closure points in U. `key` gives A = interior A, so the closure argument establishes relative closedness of A. |
| `stepP:p14:sb-un-2` | `sbUnique_local`:32–58; `key`:72–76 | PASS | Continuity puts v in open S on a positive-radius ball contained in U. Both curves satisfy IsSolutionIn there; sb_regular.2 supplies C1 and gen_uniqueness gives equality throughout the ball. |
| `stepP:p14:sb-un-3` | Uniqueness:88–90 | PASS | Convex U is preconnected; nonempty intersection with interior A and the closure condition imply U is contained in A. Since A is defined inside U, A = U. |
| Private `sbUnique_local` | Uniqueness:32–58 | PASS | Genuine local consequence of source premises, with a positive-radius neighbourhood; no equality conclusion assumed beyond the initial agreement point. |

All nodes assigned to SecularBox/Uniqueness at design lines 257–260 are implemented.
There are no unsigned public graph-node exports. The handoff informally groups un-1/un-2
under the local helper; the actual closedness obligation un-1 is in the public proof at
77–87, and is accounted for above. This is a locator clarification, not a missing node.

## Definitions, premises, and consumers

No new def, abbrev, structure, instance, or public helper is introduced. Proof-local
`A := {t | t ∈ U ∧ v t = w t}` is exactly the intended agreement set on the whole real
carrier. `interior A` and metric balls have their standard meanings. No junk branch,
fallback, carrier change, hidden estimate, time rescaling, or conclusion-shaped input occurs.

The frozen Iso predicate supplies two-sided HasDerivAt and hence continuity. S7's
sb_pred preserves that predicate; its sb_regular at Field:243–250 proves C2 for H and C1
for X_H on open S. This is the fix-round export actually consumed at Uniqueness:57.
The old S7 audit-1 FAIL is historical; it is not a substitute for inspecting the present code.

The absence of a GlobalFlow import is sound: sb_unique takes the global solution and S
membership as inputs, exactly as signed. S9 constructs these inputs for S11. No S9
existence claim is assumed without its explicit source data. The deliberate stronger
contract drops competitor SecularRegular (design departure D5, lines 330–331); the
frozen secularBoxSafety uniqueness clause can supply its extra premise and ignore it.
No narrower domain or stronger initial condition is imposed.

A recursive scan of 67 local KAM imports found no provider and no frozen theorem module;
there is therefore no DRAFT_SORRY/SEALED theorem-state dependency to waive. Imported frozen
**definitions** are permitted. The single public name is sb_unique, with no reused short
helper or harmful root shadow. A scratch probe also checks resolution of topological closure.

## Independent validation

All Lean/Lake/leanchecker invocations in this audit use `LEAN_NUM_THREADS=1` and
`nice -n 5`, with no overlap. The initial gate request remained waiting without
acquiring a slot; it was stopped (exit 143) to run the independent checks first,
after verifying that its only child was sleep and no Lean build had begun.
The required targeted gate build is resubmitted separately below.

1. Signed statement: Python extracted the telescope before the proof body from the
   authoritative signature file and the target. Whitespace-normalized equality was `True`.
   Target SHA-256: `281efc94c137ca1cbcb73e283e3ef1d0d8d2e42ccc2ad25783d88e40e6b421fe`.
   Signature-file SHA-256: `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.
2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10Audit.lean`
   exited **0**, no warnings/errors. The copied signed theorem under fresh name
   `s10SignedCheck` is proved by applying sb_unique to all explicit binders, in order.
   A second example elaborates the exact frozen uniqueness telescope, using the
   initial equality w(0)=w0 and ignoring only its extra SecularRegular premise.
   Output:

   ```text
   'KAM.Planetary.sb_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.s10SignedCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
   fun S => closure S : Set ℝ → Set ℝ
   ```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Uniqueness`
   exited **0**. Complete output:

   ```text
   replaying KAM.Planetary.SecularBox.Uniqueness
   ```

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` exited **1** solely
   for the explicitly permitted generated-root mismatch. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (952 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint failure occurred. KAM.lean was not regenerated or edited.
5. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s10 KAM.Planetary.SecularBox.Uniqueness`
   (the wrapper invokes `nice -n 5 lake build`), exited **0**, no warnings/errors:

   ```text
   [inp-gate] slot 2 acquired 21:48:23 for KAM.Planetary.SecularBox.Uniqueness
   Build completed successfully (9113 jobs).
   ```
6. Static checks: target is 94 lines, maximum line width 99; required module/header/import/docstring/
   public-section conventions hold. No forbidden token, resource override, EuclideanSpace,
   new definition/instance or reused public helper found. `git diff --check` exited 0.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited 0 with no output.
   Scratch `S10Audit.lean` was deleted after validation. Final `git status --short`
   contains only the new report and the pre-existing untracked S10-handoff.md; no tracked
   file changed. `git diff --check` and protected-path diff were rerun successfully.

## Errata, deviations, and scope limits

No new suspected pinned-source or blueprint defect found in this slice. The design's
explicit D5 strengthening is preserved; no new deviation introduced by this audit.
Blueprint p14b:269 says “No regularity of v(t) is used beyond the predicate”; the proof
establishes precisely this by entering S only near agreement points, without global
confinement of the competing curve. Design audits 1:225 and 2:87 agree on this contract.

S10 is an ordinary library lemma package, not a provider or frozen theorem seal. A
provider=frozen-type probe and copied frozen seal body are consequently not applicable
here; the signed helper telescope and frozen uniqueness-clause application are probed
instead. This audit cannot seal secularBoxSafety, secularBoxAtCitedMasses, or S11/S12.
