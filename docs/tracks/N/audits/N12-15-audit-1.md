# N12-15 independent package audit 1

Verdict: **PASS WITH NOTES** for the N12-15 helper package. No blocking mathematical or statement-fidelity finding. This package exports no provider and seals no frozen anchor; neither averaging root is certified seal-ready by this audit.

## Scope and authority

Audited HEAD `fdd44199ddea0cb6007c938ddf930ee3e6eefc24` in `/root/code/KAM-inp-n1215`. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the worktree's `docs/tracks/N/audits/N12-15-handoff.md`. The user's exact report destination overrides the generic brief's main-worktree destination.

Ran `git diff inp...HEAD` (and its `--stat`/protected-path variants). Git warns of multiple merge bases and selects `8eb17a1ba2bce8c218d81a65f77f4c97ed9534a6`; the wider diff has 9 files, including earlier N12 packages. Per AUDIT FOCUS, isolated `git diff inp-n1214...HEAD`: exactly one addition, `KAM/Nekhoroshev/Averaging/GoodSet.lean`, 181 lines (SHA-256 `4708fcf5041fddb9f25a267cfbd51d41bb04dab17afc1363363f4fae6840f0ce`). Comparison ref `inp-n1214` was `3cb29ebe508532e808fc9f235d3a225239712e92`; `inp` was `872a014af58890f96058190624e431a0ed0228a5`. Earlier packages are dependencies, not independently re-audited here.

Read Part 12 blueprint lines 232–288, design row N12-15 (line 290), node mappings and Appendix signatures (lines 885–919), both design audits at `/root/code/KAM-inp/docs/tracks/N/design/DESIGN-N12-design-audit-{1,2}.md`, and the delivered `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`. The latter and design-audit files are not present at the handoff's suggested worktree locations; the actual main-worktree files were read. Audit 2 resolves audit 1's unrelated derivative-series omission.

Read track N's averaging statement section, both frozen averaging theorem anchors, and frozen definitions `ActionBall`, `IsAnalyticIntegrable`, `IsAnalyticPerturbation`, `HasAveragingFrequencyRank`, `AveragingError`, and `IsSolutionOn`. Inspected the consumed `Setting`, `FlowDefs`, `CompactMaximum`, `Exit`, and `Stopped` interfaces. The historical “unapproved v0.5 candidates” wording in `statement.md:341` is superseded by D28 and the owner-approved frozen anchors; it is not an authority to change their types.

## Declaration and node ledger

Names below are in `KAM.Nekhoroshev`; locators are in `KAM/Nekhoroshev/Averaging/GoodSet.lean`.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| `bpN:p12:good`, good-set object | `avgGood` (:33) | PASS | Literal delivered-design definition, including full-time domain guard, original real `sSup`, and strict `< η`. |
| Auxiliary flow-domain inclusion | `mem_flowDomain_of_omega` (:43) | PASS | From endpoint membership and `t ∈ [0,T]`, uses zero membership and order-connectedness of the maximal interval. No existence or continuity is assumed. |
| Auxiliary joint continuity | `continuousOn_disp` (:49) | PASS | Restricts actual joint flow continuity to `[0,T] × avgOmega T`, then projects, subtracts initial action and takes the max norm. No sign assumption on T is needed for this possibly empty domain. |
| `good` / compact-maximum continuity | `continuousOn_sSup_disp` (:57) | PASS | N12-02 `compact_max_on`; explicit `0 ≤ T` guards nonempty compact time interval. |
| Auxiliary maximum attainment | `exists_max_disp` (:63) | PASS | Compact continuous image is bounded and nonempty; proves both inequalities identifying real `sSup` with an attained displacement. |
| `bpN:p12:good` | `good` (:82) | PASS | Exact design telescope and conclusion; relative openness and measurable bad set. General η and no inner-action premise are valid strengthenings of the blueprint's standing context. |
| `bpN:p12:bad` | `bad` (:107) | PASS | Exact design telescope, constants before ε and η, integral bound, nonstrict bad-data threshold and full-window good-data pointwise bound. Witnesses are derived from `stopped`, never supplied as premises. |
| `stepN:p12:bd-exit` | `bad`, :121–144 | PASS | Finite exit before T gives displacement exactly R/8; stopped bound includes the endpoint τ. EReal conversion excludes both infinities before `toReal`. |
| `stepN:p12:bd-stay` | `bad`, :145–159 | PASS | `T ≤ τ` gives genuine flow membership through T. Failure of strict good membership forces `η ≤ sSup`; attained maximum is bounded by the stopped majorant. |
| `stepN:p12:bd-concl` | `bad`, :142–159 | PASS | Monotonicity of `ENNReal.ofReal` combines η≤R/8 or η≤maximum with the stopped bound. Specializing η=R/8 supplies the blueprint's second assertion. |
| `stepN:p12:me-good`, designed extra output | `bad`, :160–175 | PASS | An exit before T would force R/8≤maximum<R/8. Thus T≤τ and the endpoint-inclusive stopped estimate controls every t∈[0,T]. |

Mechanical comparison against delivered signatures found exact textual equality of the `avgGood`, `good`, and `bad` signatures, and exact equality of the entire `avgGood` definition. Fresh scratch copies of the two design theorem statements, with bodies `by exact good d K hK hε η` and `by exact bad d K hK hKI`, check consumer applicability without changing premises or binder order.

No provider/frozen-type equality or seal-body probe applies: this change contains only implementation helpers, not a provider theorem. Frozen `averaging_mean` and `averaging_most` retain their existing draft bodies; this audit does not attempt to seal them.

## Definition classification and proof review

The only new definition/abbreviation/structure is **`avgGood`: intended set on its whole carrier**. It is exactly K intersected with the full-time flow domain and the strict real-supremum sublevel set. It introduces no fallback, hidden field, replacement Hamiltonian, norm instance, or parallel error quantity. Outside the analytic/positive-ε hypotheses the expression remains the specified total set definition; the theorem claims do not depend on invalid flow extensions or junk supremum values.

`AveragingData` is pre-existing and contains only `1 ≤ n`, positive R,s, frozen analytic inputs and frequency rank. The new helpers introduce no conclusion-shaped premise or instance. The local `Classical.propDecidable` instance concerns decidability only.

`good` realizes the set as `K ∩ O`, with O open by compact maximum continuity on open `avgOmega T`; relative openness follows by subtype preimage, and `K \ avgGood = K \ O` is measurable because compact K is closed. The blueprint's measurable good set follows as K minus the measurable bad set.

`bad` specializes the genuinely proved perturbation-uniform stopped witness to `f` using `d.hf`. M₂ and A₁ are chosen before ε and η. The implementation splits `τ < T` / `T ≤ τ`, whereas the blueprint splits `τ ≤ T` / `T < τ`. This is a sound redistribution of the equality case: `exit` guarantees T<T₊ even at T=τ, and `stopped` accepts T≤τ. At equality the attained-maximum branch proves the same nonstrict bad bound. The good-data output only needs T≤τ, which is sufficient. No blueprint contradiction or missing endpoint argument results.

The maximum is always evaluated on a nonempty compact time interval with continuous genuine flow under the relevant hypotheses. `exists_max_disp` supplies attainment explicitly; the final contradiction also supplies `BddAbove` explicitly. Infinite exit times are handled in EReal without an unguarded conversion.

## Import and protected-path hygiene

A source traversal of the 89 local KAM modules in GoodSet's import closure found **no provider modules and no frozen theorem modules**. All 26 imported frozen definition modules have manifest state `SEALED`. The only direct imports are `Stopped` and `CompactMaximum`; N12-11 Exit/Flow come through Stopped as designed.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: no diff (only Git's multiple-merge-base warning). `git diff --check inp-n1214...HEAD`: exit 0, no output. GoodSet is 181 lines; required copyright, module header, public imports, module docstring and exposed public section are present. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, resource override, or new global instance occurs in the audited module. No production, frozen, manifest, generated, or git-history edits were made.

## Independent verification receipts

All audit-owned Lean/Lake invocations used `LEAN_NUM_THREADS=1` and ran sequentially at nice level 5. The build used the prescribed gate; lint is also run at nice level 5 because its ABI check launches Lean. An initial lint attempt was terminated during the source-only frozen guard, before its ABI Lean invocation, so it could not overlap the targeted build; only the completed rerun below is used as evidence.

### Targeted build

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1215 KAM.Nekhoroshev.Averaging.GoodSet
```

Exit 0. Gate output: `[inp-gate] slot 1 acquired 11:48:58 for KAM.Nekhoroshev.Averaging.GoodSet`. Final output: `Build completed successfully (3247 jobs).` No GoodSet warning. Replayed dependency warnings concern unused variables/section variables, deprecated tsum/if lemmas, and a haveI style suggestion in Shells, EnvelopeIntegrals, PicardFamilies, LocalDependence, CompactMaximum, ODE.Exit, CorrectorRegular and Transport. They are outside this delta and do not affect successful elaboration.

### Design statement probes and every new theorem's axioms

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1215Audit.lean
```

Exit 0. The probe imports only GoodSet, copies the literal delivered `good` and `bad` telescopes/conclusions under fresh names, and applies the existing exports using every explicit binder in order. No added hypothesis, cast or replacement definition is used. Complete output:

```text
'KAM.Nekhoroshev.mem_flowDomain_of_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuousOn_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuousOn_sSup_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.exists_max_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.bad' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.GoodSet
```

Exit 0. Complete output:

```text
replaying KAM.Nekhoroshev.Averaging.GoodSet
```

One invocation replays the single new lemma module. There is no provider module in this package.

### Lint

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the permitted stale generated-root check. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (559 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Accepted under the audit brief's explicit exception. No root regeneration was performed.

### Closeout

The temporary `.lake/abi-scratch/N1215Audit.lean` was deleted after successful elaboration. `git diff --no-index --check /dev/null docs/tracks/N/audits/N12-15-audit-1.md`: exit 0, no output. `git diff --exit-code -- KAM manifest KAM.lean README.md`: exit 0, no output. Final status contains only the new audit report and the pre-existing untracked handoff. The report is the only persistent audit-owned repository change.

## Findings, errata, deviations, and limits

No new suspected source/blueprint defect or introduced mathematical deviation was found. The equality-case redistribution above preserves the source argument. No fresh pinned-PDF audit or independent proof audit of N12-01 through N12-14 is claimed. The known Nei76 maximum-error issue documented by the design/source audits is inherited context, not a new finding here.

Package-level acceptance does not establish either frozen averaging root. The acceptance notes are the expressly permitted stale generated-root lint result and existing replayed dependency warnings. No code change is requested for N12-15.
