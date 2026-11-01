# W-GRAPH-CLOSE independent audit 2 — W-SOLVE-FIX

Auditor: `maud-wpj-2`. Date: 2026-11-01. **Verdict: PROVED-OK for `bpW:w5:solve`; round-1 F1 is closed.** This is a one-node, tight-delta acceptance, not a re-audit of the other nine nodes or a frozen-anchor seal.

Audited HEAD: `b0e251babb23c0d5a1c2b4edc9dfc941e2c7d7f3`. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, round-1 F1, and the handoff's W-SOLVE-FIX/AUDIT FOCUS. Compared `git diff inp...HEAD` (`inp = 2264fd4e52a3650eccf47b5551762737aa1712e6`) and reviewed only `git diff a82197a3..HEAD`. Both comparisons show the same two-file repair: `ExportSolve.lean` (55 additions, one deletion) and the handoff (79 additions). Unchanged supporting definitions were read only to assess the new conjuncts. The user's explicit scope, destination, D53 wrapper, lint route and replay instructions control over the generic brief. Local DECISIONS ends at D51; D53 authority is the current owner prompt.

## Exact graph record

| Node | Verdict | Exact LEAN_REF list |
|---|---|---|
| `bpW:w5:solve` | **PROVED-OK** | `KAM.Wave.stepSolveLemma, KAM.Wave.stepSolveLemmaMod` |

References are in `KAM/Wave/KamStep/ExportSolve.lean:239,286`. The three new helpers support the second export; they need not be added to the node's LEAN_REF list.

## Why F1 is closed

The controlling blueprint says `N̂ ∈ S_(p_+)(𝒫) (indeed p′)` (`blueprint-W/parts/w5-kamstep.tex:355–356`), and sets `p′=p+1` in the modified case (`:335–336`). The new conjunct at `ExportSolve.lean:295–297` is exactly `IsSmoothing (p := p) (pb := p + 1) ... univ` for

```lean
waveStepFun H.ha (homPP H.hp H.hpb)
  (homNhatTaylor_gen (H.hyp.core.R ξ))
```

This is literally the Hamiltonian in the old `S_(p_+)` clause, reality clause, equation and normal-correction bound. It is not a separately chosen correction. `IsSmoothing` (`Class.lean:33–38`) supplies holomorphic Hamiltonian, holomorphic field in the indicated weighted representation, and the derivative/symplectic identity for every point and direction. `univ` covers all of `𝒫`, with no strip or radius restriction.

The `p+1` field is `stepField ... (homNhatTaylor_gen (H.hyp.R1 ξ))`. This representation is justified as follows:

| Declaration (namespace `KAM.Wave`) | Result of delta review |
|---|---|
| `StepHypMod.nhat_fun_eq_R1` (`:201`) | PASS. Global equality of the two Hamiltonian functions. Rewrites `H.core.R ξ` and `H.R1 ξ` using `stepTaylorFam_of_mem`, then applies existing `stepFun_nhat_taylorRho` (`StepReweightTaylor.lean:209`). The equality holds at every `w`, not only on the step domain. |
| `StepHypMod.nhat_isSmoothing_p1_univ` (`:215`) | PASS. Rewrites the same Hamiltonian by that equality and applies existing `stepNhat_isSmoothing_univ` at `pb := p+1` to `H.R1 ξ`. This proves the missing class membership rather than assuming it. |
| `StepHypMod.nhat_field_eq_rhoK` (`:223`) | PASS. Uses `IsSmoothing.rhoK` and `isSmoothing_unique_apply` to identify the old `p_+` field with `D_ρ` of the `p+1` field at every point. Both smoothing facts concern the same Hamiltonian on `univ`. |
| `stepSolveLemmaMod` (`:286`) | PASS. Inserts both conclusions immediately after the old global smoothing clause and instantiates the helpers with `H.hyp`. Source-facing type retains only the original `StepHypModSrc` argument. |

`H.R1` is the existing Taylor family of the original `(P,X)` at `p+1` (`StepHypMod.lean:114`), not a new definition or fallback. The source already assumes `P ∈ S_(p+1)` in the modified case. The helper's `hξ : ξ ∈ Par` is discharged by the existing export quantifier. `Fact (0<r)` is constructed locally from `H.hr`. `H.hc : pb ≤ p+1` is derived from `H.hβ0` and `H.h2β` (`StepHypMod.lean:104`); `stepRho_nn2 H.hp` is typing data. The source-facing hypothesis conversion preserves these input premises (`StepTheoremSrc.lean:505–528`). No conclusion-shaped hypothesis, instance or new premise is introduced.

A read-only Python comparison extracted the old and new declarations/proofs and checked exact text equality after deleting precisely the two inserted conjuncts and their proof terms. Output:

```text
PASS: stepSolveLemma declaration/proof byte-identical; stepSolveLemmaMod declaration/proof identical after removing exactly the two new conjuncts and their proof terms.
```

Thus every previous conjunct, constant, family bound, frequency estimate, quantifier and proof term is retained. The non-modified export is unchanged; its existing global `S_(p_+)` clause already supplies `p′=p_+`. Round-1 acceptance of the unchanged parts is retained within this tight scope.

## Definitions and hygiene

No new `def`, `abbrev`, `structure`, instance, import or provider appears in the delta. The three helpers prove propositions about the existing objects. Provider/frozen type matching and seal-body probes are inapplicable. No frozen anchor is introduced or sealed.

`ExportSolve.lean` has 332 lines, below 1500, and retains copyright, `module`, interface `public import`, module docstring and `@[expose] public noncomputable section`. A literal search for `sorry`, `admit`, `axiom`, `unsafe`, `opaque` and `set_option` in this file returned no matches (rg exit 1). No heartbeat, synthesis or recursion override was used. `git diff --check a82197a3..HEAD` exited 0 with no output. `git diff a82197a3..HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md` is empty. This auditor edited only this report in repository sources; the scratch axiom probe was removed afterwards. No state-changing git command or root regeneration was run.

## Fresh verification

All Lean/Lake activity was serial. Every invocation, including lint children, was enclosed in:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Targeted build command:

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpj KAM.Wave.KamStep.ExportSolve
```

The inspected driver acquires the compile gate and wraps its single `lake build KAM.Wave.KamStep.ExportSolve` in exactly the D53 scope above. Exit **0**; output includes:

```text
[w_build] slot 2: KAM.Wave.KamStep.ExportSolve (12:13:03)
Build completed successfully (3441 jobs).
```

Cached dependency warnings were replayed (including deprecated conditionals and unused variables/tactics); no failure or default-heartbeat design signal occurred. This was one targeted module build, not a core/application rebuild.

Prescribed lint command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpj
```

Exit **0**, complete output:

```text
check_lean_modules: PASS (4059 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The wrapper spent several minutes preparing its symlink overlay before running the checks; it completed successfully. No alternative lint route was used.

A scratch probe imported `KAM.Wave.KamStep.ExportSolve` and issued `#print axioms` for the two node exports and all three new public helpers. Exact command, from the worktree:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/WGraphCloseAudit2.lean'
```

Exit **0**, complete output:

```text
'KAM.Wave.stepSolveLemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolveLemmaMod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.nhat_fun_eq_R1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.nhat_isSmoothing_p1_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.nhat_field_eq_rhoK' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All axiom sets are permitted. The temporary probe was deleted after this successful check.

The launcher replay and name checks are reported by the owner as already completed, but their outputs are unavailable to this auditor. No replay or name check was rerun, and no fresh leanchecker exit code is claimed. This tight repair did not require replaying the other nine nodes.

## Uncertainties, errata and deviations

No remaining uncertainty or suspected pinned-source defect was found in this delta. Round-1's packet omission remains an editorial issue: `W-w5a.nodes.md:909` omits the blueprint's “(indeed p′)”; it is not evidence against the now-complete Lean export. No packet was edited here. Extending the conjunction shifts projections inside its parameter block by two positions; it does not change the prior mathematical clauses. No implementation deviation was introduced by the auditor.
