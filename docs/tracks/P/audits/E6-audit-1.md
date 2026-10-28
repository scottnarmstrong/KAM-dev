# E6 independent package audit 1

Audit date: 2026-10-28. Scope: only `KAM/Planetary/Exponential/ComplexTube.lean`.

## Verdict and scope

**Overall: PASS WITH NOTES.** E6 is complete and its two theorem contracts (`real_trace_identity`, `tube`) pass. All four required declarations exactly match the signature file; no blocking fidelity, soundness, completeness, import or hygiene finding remains. Notes: the explicitly permitted stale generated root makes whole-repository lint exit 1, and the module has one nonblocking deprecation warning. E6 is ordinary library infrastructure with no frozen anchor/provider of its own; no frozen seal is certified by this verdict.

Inspected HEAD `35aed5fdfcefa06d6d334f5b9ca174339e587c5c`, including the orchestrator's removal of the duplicate `fastShift_add`; comparison ref `inp` was `700477228205080ba6e81c21cb4f1d05acafe970`. `git diff inp...HEAD` adds exactly one 271-line Lean module. Its SHA-256 is `23561eeec17103b1a6a127ef576004886781fcf202f068adf0197c31689d4b2d`. The handoff's 281-line count refers to the earlier version, not the audited HEAD.

Read the local AGENTS.md, PLAN, DECISIONS, audit brief, E6 handoff/AUDIT FOCUS, P14 design including E6 row and proof plan, both P14 design audits, track P statement, relevant blueprint/packet entries and frozen `complexifyPhase`/`fastShift` definitions. The audit is scoped library infrastructure: E6 exports no provider and seals no frozen anchor. The relevant eventual `planetaryExponentialSafety` anchor was inspected for context; its closure is outside this package. Provider/frozen-type equality and anchor seal-body probes are therefore inapplicable; exact E6 contract probes are used instead.

The user explicitly overrides the brief's default MAIN-worktree report destination. This report is written only at `/root/code/KAM-inp-p14-e6/docs/tracks/P/audits/E6-audit-1.md`. No production, frozen, manifest, generated-root or git-state changes are made. Initial status contained the untracked supplied `E6-handoff.md`.

## Declaration and node ledger

All names below are in `KAM.Planetary`. Line numbers refer to the audited module.

| Node / obligation | Declaration / proof location | Verdict | Reason |
|---|---|---|---|
| E6 transport | `e5Pack_unpack`, L36 | PASS | Reverse inverse to E5's packing; both Fin blocks checked, all dimensions and RCLike scalars. |
| x-id real trace | `norm_realInclusion_sub_le`, L44 | PASS | Real projection contracts distance to a real centre; supplies nonempty real trace. |
| `bpP:p14:x-id` E6 instance | `real_trace_identity`, L52–104 | PASS | Exact contract, restricted to real-centred ball intersections; empty intersections require no witness. |
| Translation algebra | `complexifyPhase_add`, L106 | PASS | Coordinatewise real-to-complex inclusion preserves addition on the entire carrier. |
| Translation algebra | `complexifyPhase_sub`, L111 | PASS | Same for subtraction. |
| Max-norm transport | `norm_complexifyPhase`, L116 | PASS | Actual product/Pi max-norm isometry, no Euclidean replacement. |
| `stepP:p14:tb-glue` and translated consistency | `exists_glue`, L120–138 | PASS | Real agreement on overlaps is promoted to full complex agreement by the proved identity theorem. No complex-agreement conclusion is assumed. |
| `stepP:p14:tb-leb` finite-radius selection | `exists_pos_le_half`, L140–150 | PASS | Positive common lower radius for any finite family; empty finset starts at 1. |
| Periodic real carrier | `periodicOrbitSet`, L152 | PASS | Literal signature definition, union of all lattice translates of K. |
| Complex carrier | `complexTube`, L154 | PASS | Literal signature definition, open union of complex max-balls. |
| Translated ball transport | `mem_ball_shift`, L158 | PASS | Exact equivalence for any real radius; pure addition/subtraction. |
| `bpP:p14:tube` | `tube`, L165–267 | PASS | Exact telescope and conclusion; no new premises, constants chosen after precisely the fixed source data. |
| `stepP:p14:tb-local` | `tube.hloc`, L177–187 | PASS | E5 extension shrunk by openness of W; real agreement and real-ball containment retained. |
| `stepP:p14:tb-leb` | L188–190, `hcov` L219–235 | PASS | Finite half-ball cover, common positive radius, explicit triangle inequality giving full complex-ball coverage. |
| `stepP:p14:tb-glue` | `hGd`, `hGval`, `hF`, L195–218 | PASS | Simultaneous gluing includes untranslated branches and all translated overlaps; local branches are holomorphic and have real value f on W. |
| `stepP:p14:tb-per` | L237–267 | PASS | Local branch equality gives holomorphy, real membership/agreement, shift invariance and exact periodicity by reindexing `(x,k')` to `(x,k'+k)`. |

## Fidelity and completeness

The two theorem signatures and two definition bodies match `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` literally (not merely up to equivalent propositions). Signature file SHA-256: `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`. Fresh declarations copied from those contracts apply `real_trace_identity x y r s hf hg heq` and `tube hW hK hKW hWp hf hfp` in explicit-binder order; `type_of%` checks additionally compare the full elaborated telescopes. Definition equality probes use `rfl`.

Compared design L149–153, L348, E6 row L379 and identity discussion L445–447 with blueprint `p14a-amd-expsafe.tex` L210–218 and packet nodes `tube`, `tb-local`, `tb-leb`, `tb-glue`, `tb-per`. Every assigned obligation is implemented. The general identity theorem is legitimately reused from ordinary `PGAssembly.RealSlice`; E6 proves its required product-phase intersection instance rather than assuming it. The `e5Pack`/`e5Unpack` inverse and norm identities preserve balls and their real traces, and the componentwise real projection of an overlap point supplies the nonempty open real set. No positivity premise is silently needed for empty/negative-radius intersections.

The implementation fuses the blueprint's finite first gluing and subsequent periodisation into one gluing over all `K × (Fin n → ℤ)` branches. Restricting to the finite cover and zero lattice index recovers the first-stage extension; `hGval` proves equality with f on every real overlap using W-invariance and f-periodicity before `exists_glue` is invoked. This is a sound proof organisation change, not an omitted obligation. The finite cover is used exactly where uniform radius is needed; gluing an arbitrary family needs no finite-family premise. The chosen radius can be smaller than the blueprint's displayed finite minimum, which preserves the existential contract.

For empty K, the subtype-indexed branch family is empty, the subcover is empty, `exists_pos_le_half` returns 1 and `exists_glue` can return zero everywhere. The tube is empty and all requested properties are vacuous. No nonemptiness premise is added. A fresh probe checks tube openness as a union of balls and checks `complexTube ∅ r = ∅`; openness is implicit in the exact signature but fully recoverable without an extra premise.

## Definition classification and imports

There are exactly two new definitions and no new abbreviations, structures or instances. Both `periodicOrbitSet` and `complexTube` are intended literal set constructions on their whole carriers, including empty K, n=0 and nonpositive r. For r≤0 the latter is empty, as the strict norm inequality requires. No alternate norm, distance, carrier or fallback is used. The only fallback value is the locally constructed glued function's zero outside its union of balls (L133–134); all uses on the tube first obtain a valid branch via `hcov`, so no theorem relies on that exterior value.

The additional ordinary import `KAM.Planetary.PGAssembly.ExtensionTubeP` supplies the existing general `fastShift_add`, with `a=b=n`. Its source theorem uses the literal frozen radian shift `2*pi*k`, preserving the period convention. Recursive source inspection found 49 KAM modules in the import closure and no `KAM.Provider.*` or frozen theorem-anchor module at all; hence no DRAFT_SORRY or provider quarantine violation and no theorem-anchor manifest state to waive. Frozen definition imports are allowed. No conclusion-shaped hypothesis occurs: gluing assumes local holomorphy and equality on real points, then proves complex compatibility.

A whole-KAM declaration-name scan found no other declaration with any of the 12 new short names, including `exists_glue`, `exists_pos_le_half` and `mem_ball_shift`. `fastShift_add` is reused, not redeclared. No project-root shadow module was added; generated `KAM.lean` is unchanged.

## Validation receipts

All Lean/Lake invocations were serial with `LEAN_NUM_THREADS=1` and `nice -n 5`; no budgets were overridden. No clean, cache download, package update, or `.lake/packages` modification was performed.

Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e6 KAM.Planetary.Exponential.ComplexTube
```

Exit 0. Output (terminal styling omitted):

```text
[inp-gate] slot 2 acquired 16:29:51 for KAM.Planetary.Exponential.ComplexTube
⚠ [9095/9095] Replayed KAM.Planetary.Exponential.ComplexTube
warning: KAM/Planetary/Exponential/ComplexTube.lean:135:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead
Build completed successfully (9095 jobs).
```

This is the targeted incremental gate, not an independent forced recompilation of all dependencies. The module was then independently kernel-replayed below.

Fresh contract/definition/axiom/edge-case probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E6Audit.lean
```

Final exit 0; signature, binder-order application, definition-rfl, openness and empty-tube examples elaborate without diagnostics. Exact output:

```text
'KAM.Planetary.e5Pack_unpack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_realInclusion_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_trace_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexifyPhase_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexifyPhase_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_complexifyPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_pos_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_ball_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tube' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The initial probe exited 1 only because its additional audit-authored openness example used a `simp only` list missing the existential-proposition normalization; all contract and axiom commands already succeeded. Replacing that scratch proof step with `simp [complexTube, Metric.mem_ball, dist_eq_norm]` closed the same openness proposition on the next run. No package code was altered.

Kernel replay (E6 contains no provider or second new lemma module):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.ComplexTube
```

Exit 0; exact output:

```text
replaying KAM.Planetary.Exponential.ComplexTube
```

Lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (784 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The root was not regenerated. Module hygiene, frozen-anchor guard and elaborated ABI checks pass independently of that expected root mismatch.

Additional read-only checks:

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
wc -l KAM/Planetary/Exponential/ComplexTube.lean
```

The first two commands exit 0 with empty output. Line count: `271 KAM/Planetary/Exponential/ComplexTube.lean`. A code-mask scan using `scripts/check_lean_modules.py` finds no forbidden proof escapes, `EuclideanSpace`, or `set_option`; copyright, `module`, public imports, module docstring and public section are present. Both definitions are exposed by the enclosing `@[expose] public noncomputable section`.

Temporary audit probes and receipt files under `.lake/abi-scratch/` are removed before handoff. Final `git status --short` contains only the pre-existing untracked `docs/tracks/P/audits/E6-handoff.md` and the new untracked `docs/tracks/P/audits/E6-audit-1.md`; tracked worktree diff is empty. The report passes `git diff --no-index --check /dev/null <report>` and contains no pending validation placeholders.

## Notes, errata and limits

No suspected pinned-source or blueprint mathematical defect was found in this E6 slice. No frozen statement, premise, constant dependency or carrier was repaired or substituted. The only proof-plan variations are simultaneous translated gluing and a possibly smaller positive uniform radius, justified above. The handoff's line count predates the orchestrator commit. This report establishes only the E6 package result; it does not certify downstream E7/E11, the N root, or a physical confinement theorem. No new Lean brief or delegated task was created.
