# Independent package audit 1: N89-G5

**Overall verdict: PASS WITH NOTES.** All four G5 declarations pass statement, definition,
premise, build, axiom and kernel checks. Notes concern retained unused source premises and
the inherited generated-root history/staleness. No frozen theorem anchor is assigned to G5;
this is an infrastructure-package verdict, not a frozen seal or N-HEAD-C closure.

## Scope and authority

Worktree: `/root/code/KAM-inp-n89g5`; HEAD `6a010892a561b5299abb09348bceeecc3f5ad4e3`.
Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the supplied G5 handoff.
The user's exact report path overrides the generic brief's main-worktree destination.

The AUDIT FOCUS restricts production review to `ResonanceGeometry/Blocks*.lean`:
only `KAM/Nekhoroshev/ResonanceGeometry/Blocks.lean` matches. Read the current design
`docs/tracks/N/design/N89-LEAN-DESIGN.md`, especially row G5 (L309), proof plan (L355–356),
Appendix A (L752–767), blueprint `blueprint-N/parts/p8-resonance-geometry.tex:120–136`,
the track-N statement, and the actual checked-in design audits under `docs/tracks/N/design/`.
The handoff's `audits/DESIGN-N89-...` paths do not exist. Original signatures are absent from
this checkout's `.drafts/design/`; read `/root/code/KAM-inp/.drafts/design/N89Signatures.lean:249–261`.
Also read the four focused records in `docs/graph/N/packets/N-p8.nodes.md:834–949`.
Audits 1 and 2 agree on these four contracts; audit 2's projection and ownership fixes are outside G5.

Executed `git diff inp...HEAD`; `inp` resolved to `f11c90357967f666b1673409df890dbcec823dff`.
Git reports multiple merge bases, selecting `7e0feebf1e74e666dbb9c9d3ae26e13971f3470c`;
the other merge base is `4dad814dc58f7f254a380a342178c120e2d69be9`.
The broad comparison has 30 changed files, including unrelated merged packages. It is not a
one-file package diff. The requested comparison with `inp-n89g4` (at `7e0feebf...`) was also
run; restricted to G5 it adds exactly the 58-line Blocks file. `git show --stat HEAD` and
`git diff HEAD^ HEAD --name-only` independently establish that the G5 commit changes only that file.
Inherited G1–G4 code was read as dependency context, not re-certified.

## Statements, definitions, and proof

All declarations below are in `KAM.Nekhoroshev`. The three complete definition bodies and
the complete `blocks_cover` header through `:=` match the original design signatures literally.
There is no additional premise, constant, carrier change, altered binder order, or weakened conclusion.

| Node | Declaration / location | Verdict | Reason |
|---|---|---|---|
| `bpN:p8:blocks` | `zone`, Blocks L25–26 | PASS | Strict Euclidean resonance-distance tube; bottom zone is the whole space. |
| `bpN:p8:blocks` | `zoneStratum`, L28–29 | PASS | Union over maximal K-lattices of exactly rank d, guarded by 1≤d≤n. |
| `bpN:p8:blocks` | `blocks`, L31–32 | PASS | Exact set difference of own zone and next dimension's stratum. |
| `bpN:p8:blocks-cover` | `blocks_cover`, L34–56 | PASS | Both finite maximal family and every-frequency block witness; literal design type. |
| `stepN:p8:bc-finite` | first conjunct of `blocks_cover`, L38 | PASS | Subset of the proved finite set of all K-lattices via `hΛ.1`. |
| `stepN:p8:bc-top` | second conjunct of `blocks_cover`, L39–56 | PASS | Bounded nonempty natural dimension set has an attained maximum; empty set gives bottom. |

Definition classification on the whole carrier:

- `zone`: intended total extension to every integer lattice and every real sequence lam.
  The bottom branch is the blueprint's explicitly prescribed zone, not a junk fallback.
  For nonbottom lattices `resonanceDistance = euclid (proj (lattice Λ) w)` (Projection L121–122),
  and G2's `projection_distance` identifies this with distance to the resonance subspace.
  Covolume is the existing `volume_def`. No ambient Pi max norm replaces Euclidean distance.
- `zoneStratum`: exact set-theoretic union over the indexed family; d=0 and d>n give the empty set.
  In particular the prescribed top sentinel `zoneStratum K lam (n+1)` is empty without a new premise.
- `blocks`: correct for every lattice; at bottom `latticeDim_bot=0` gives the complement of stratum 1.
  No disjointness, nesting of zones, or maximality of arbitrary input lattices is falsely asserted.

No new abbrev, structure, instance, or extra public helper theorem occurs.
`@[expose] public noncomputable section` exposes the three definitions.

For the covering proof let D be the dimensions of occupied strata. Every member is ≤n by
construction, so the natural-number supremum is a member when D is nonempty. Its stratum witness
supplies an actual maximal lattice Λ and own-zone membership. Membership of the next stratum
would give d+1≤d, contradicted by `omega`. If D is empty, `maximalK_bot K` supplies maximality;
`zone lam ⊥=univ` and the absence of every stratum supply block membership. This is exactly
blueprint step `bc-top`, including the full-rank case. The n=0 extension is valid: all positive
strata are empty and bottom covers the singleton frequency space. The proof needs neither hK nor
hlam; retaining these source/design premises is faithful and explains the expected warnings.
There is no conclusion-shaped hypothesis or unpaid hard step hidden in data.

## Frozen surface and imports

No frozen theorem anchor or provider export is assigned to G5. Provider/frozen type-equality
and frozen seal-body probes are therefore not applicable; a fresh theorem using the exact
original design signature is the appropriate interface check.
The only direct import is `KAM.Nekhoroshev.ResonanceGeometry.Maximal`.
A recursive source-import walk visits 59 project modules, no provider modules and no frozen
theorem modules. The 19 frozen modules reached are all manifest-kind `definition`, state `SEALED`.
The relevant frozen real-part/solution definitions were inspected; G5's objects and statements
are purely geometric and impose no Hamiltonian or solution premise.

The generic protected comparison `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
is **not empty**: it includes 15 added imports in `KAM.lean`, inherited from the earlier root
regeneration commit `4dad814`. There is no frozen/manifest/README diff. The same inherited
root difference is present in the unrestricted comparison against `inp-n89g4`.
`git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
This broad-history exception is recorded explicitly; the G5 commit and this audit do not edit
any protected file. The generated root was not regenerated during the audit.

## Independent checks

All Lean/Lake commands are serialized, with `LEAN_NUM_THREADS=1`, `nice -n 5`, and default
resource budgets. No library rebuild from scratch, cache operation, or package mutation was used.

1. **Targeted compile gate**, command:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89g5 KAM.Nekhoroshev.ResonanceGeometry.Blocks
   ```

   Exit **0** after the expected slot wait. Gate acquired slot 2 at 08:35:31 UTC and internally
   ran `nice -n 5 lake build`. Output ended `Build completed successfully (3214 jobs).`
   Replayed warnings: `Gradient.lean:168:5` unused `hgr`; `Maximal.lean:249:25` unused `hK`;
   `Blocks.lean:34:30` unused `hK`; `Blocks.lean:35:5` unused `hlam`. Only the last two belong to G5.
   These are source/design premises deliberately retained, not new premises or missing proof steps.

2. **Original-signature, definition, edge-case and axiom probe**, command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89G5AuditProbe.lean
   ```

   Final exit **0**, no warnings or errors. The probe copied the original `blocks_cover` header
   under fresh name `audit_blocks_cover`, with body `by exact blocks_cover hK lam hlam`.
   It also elaborated all three literal defining equations by `rfl`, the top stratum empty-set
   identity, and the bottom-zone whole-space identity. This verifies exact source-signature
   applicability and definition unfolding, rather than merely checking a pretty-printed type.
   Exact axiom output:

   ```text
   'KAM.Nekhoroshev.blocks_cover' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.zone' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.zoneStratum' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.blocks' depends on axioms: [propext, choice, Quot.sound]
   ```

   Here `choice` is `Classical.choice`, shortened because the probe opens `Classical`.
   No `sorryAx` or other axiom occurs. The initial audit probe exited 1 because the auditor omitted
   classical decidability in a literal `if` type and the explicit `(n := n)` on the top-stratum
   equation; it also used a deprecated set-membership simp name. Correcting these probe-only
   issues gave the clean exit above. Production code was never changed.

3. **Kernel replay**, command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.ResonanceGeometry.Blocks > .lake/abi-scratch/N89G5-leanchecker.log 2>&1
   ```

   Exit **0**. Complete output (one line):

   ```text
   replaying KAM.Nekhoroshev.ResonanceGeometry.Blocks
   ```

   This is one invocation for the single package module; there is no provider or additional G5 lemma module.

4. **Repository lint**, command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely for the explicitly permitted stale generated root. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (480 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden-token, line-length, module-format, frozen-source, or ABI error was reported.
   This passes the brief's stated lint criterion with the generated-root exception.
   `nice` and `LEAN_NUM_THREADS=1` also apply to lint's internal ABI Lean invocation.
   This command was started only after kernel replay terminated.

5. **Source hygiene and comparisons:** literal-definition/header comparison against the original
   signatures returns `True` for all four declarations. Focused file: **58 lines**, maximum
   **97 Unicode characters per line**; forbidden-token scan returns `[]`. Copyright, `module`,
   public import, module docstring and exposed public section are present. The protected-file
   comparisons and inherited root exception are recorded above. Final whitespace/cleanup checks
   are recorded below.

## Errata, deviations, and limits

No suspected new pinned-source or blueprint defect was found in the G5 definitions or argument.
Blueprint p8 L122–135 explicitly prescribes the bottom zone and the top-dimension argument;
Lean follows them. No new source deviation is introduced. Existing design-wide source notes
and G1–G4 obligations are outside the focused verdict; no claim of a fresh PDF audit is made.
The design-signature file and design-audit path discrepancies above are documentation locator
notes, not mathematical defects. No design-signal resource failure has occurred.

Only this report is authored in the repository. The temporary probe under `.lake/abi-scratch/`
has been deleted after validation; the temporary kernel log has also been removed. No state-changing Git command or production edit is authorized or used.

Final checks: `git diff --check`, `git diff --no-index --check /dev/null
/root/code/KAM-inp-n89g5/docs/tracks/N/audits/N89-G5-audit-1.md`, and
`git diff --exit-code` all exit **0**. Final `git status --short` lists only the new audit
report and the pre-existing untracked `docs/tracks/N/audits/N89-G5-handoff.md`.
The proof, source signatures, blueprint, frozen files, manifest, root and README remain unchanged.
No unresolved G5 mathematical issue or resource-design signal remains.
