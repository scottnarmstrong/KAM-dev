# W5-AA independent audit 2 — tight delta

**Verdict: PASS for the F1/N1 repair delta.** F1 is closed for all four exported series definitions: their public carriers now require sufficient weight guards, exclude the round-1 counterexamples, and support convergence for every input on those carriers. N1 is addressed by the warning cleanup. This is round-2 acceptance of the named repairs, carrying forward unchanged round-1 PASS material; it is not a new full-package audit, frozen `nlw2` seal audit, or W6/W8 consumer audit.

## Scope and snapshot

Audit date: 2026-11-01 UTC. Worktree/report destination: `/root/code/KAM-inp-wps` (physical checkout `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wps`). Audited HEAD: `5831b8222749050b586cdc02d178653a660fb6fc`. Repair base: `3f5734fce1925efc99f8e06c0e8cd86ee859ade9`; comparison ref `inp`: `698fd38075bb3d814749ecfeae94a919cac3743e`. `git merge-base inp HEAD` equals the repair base, so `git diff inp...HEAD` and `git diff 3f5734fc..HEAD` describe the same repair: seven Lean files and the handoff, 226 insertions / 68 deletions. Initial repository status was clean.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the W5-AA-FIX audit focus, round-1 findings F1/N1, and the affected source clauses. The prompt's tight-delta scope, report destination, D53 cap and lint command govern over the generic brief. No provider/frozen declaration is introduced by this delta; provider/type and seal-copy checks are N/A. No agents were delegated.

Source: `blueprint-W/parts/w5-kamstep.tex`, SHA256 `d8daf4af9d63da34ae860d2ce9aeefec0a5fe8e7d603cdddb26af6f463e5153c`. Standing weights at lines 33–39 are `a=p=1`; action-angle (i)–(vi) is at lines 622–659 and initial at lines 696–710. The source is unchanged by the repair. Unchanged round-1 PASS proofs were not re-audited.

## Findings and definition classification

All declarations below are in `KAM.Wave`; file paths are relative to `KAM/Wave/KamStep/`.

| Finding / node | Declaration / location | Verdict | Reason |
|---|---|---|---|
| F1 / AA (iv) | `aaNfun`, ActionAngleNormal.lean:69 | PASS | Public carrier binds `ha : 0 ≤ a`, `hp : 1/2 ≤ p`; literal finite tangential sum plus the original normal series. |
| F1 / AA (iv)–(v) | `aaQt`, ActionAngleNormal.lean:75 | PASS | Public carrier binds `ha : 0 ≤ a`, `hp : 0 ≤ p`; literal quadratic expression and original normal series. |
| F1 / AA (v) support | `aaGbarR`, ActionAngleGbar.lean:39 | PASS | Public carrier binds `ha : 0 ≤ a`, `hp : 1/2 ≤ p`; original `J≥3` series, matching W3's `birkHamBar` carrier. |
| F1 / AA (iii) | `birkOmegaMix`, ActionAngleSymp.lean:40 | PASS | Public carrier binds `ha : 0 ≤ a`, `hqq' : 0 ≤ q+q'`; original mixed-coordinate symplectic pairing. |
| AA (iv) convergence | `norm_aaOmegaN0_le`, ActionAngleNormal.lean:202 | PASS | Proves `‖Ω⁰_J(ξ)‖ ≤ (1+‖⟨b,ξ⟩‖) λ_J` for arbitrary complex ξ and positive m. |
| AA (iv) convergence | `summable_aaNfun`, ActionAngleNormal.lean:214 | PASS | Convergence on exactly the guarded definition carrier, with no smallness, reality or domain premise. |
| AA (iv)–(v) convergence | `summable_aaCoefC_aaZZ`, ActionAngleQt.lean:143 | PASS | Bounds the diagonal quadratic terms by ℓ² products for `0≤a`, `0≤p`. |
| AA (iv)–(v) convergence | `summable_aaQt`, ActionAngleQt.lean:160 | PASS | Multiplies that convergent series by the finite scalar `aaBdot y`; no extra premise. |
| AA (v) convergence | `hasSum_aaGbarR`, ActionAngleGbar.lean:82 | PASS | Proves the original `J≥3` series sums to the guarded definition for every BirkSpace input and tangential index. |
| AA (iii) convergence | `hasSum_birkOmegaMix`, ActionAngleSymp.lean:83 | PASS | Proves the original series including the factor `I` sums to the guarded pairing. |
| N1 / all affected nodes | Seven changed ActionAngle modules | PASS | Deprecated aliases, unused simp arguments and unused binders removed without linter suppression or budget overrides. |

For each of the four repaired definitions: **BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=OK; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS**. Proof guards are binders of the definitions themselves, not merely downstream theorem premises. Their bodies do not depend on the proof witnesses; proof irrelevance also prevents a choice of guard proof from changing the object. There are no new definitions, structures, auxiliary totalizations or fallback branches. `aaPfun` retains its old signature and formula, supplying its existing guards to `aaQt`.

### Counterexamples and convergence on the whole carrier

Round 1 used `m=1,a=0,p=−1` and normal representatives `u_j=1/(j+2),v_j=0` to make `aaNfun` summands fail to tend to zero and `aaQt` diverge harmonically. These weights now require the false guards `1/2≤−1` and `0≤−1`, respectively. The `aaGbarR` example with both signs equal to `1/J` likewise cannot satisfy `1/2≤−1`. The `birkOmegaMix` example at `a=0,q=q'=−1` cannot satisfy `0≤−2`. The exclusion is in the exported types, not a convention about how callers should use them.

The guards also suffice for **all** inputs that remain:

- For `aaNfun`, at `J=j+2`, `λ_J/(J^(2p) exp(2aJ))` is bounded when `a≥0,p≥1/2`, including the boundary `a=0,p=1/2`. `summable_norm_lam_aaZZ` supplies the corresponding absolute bound by an ℓ² pairing; the new Ω bound lets `summable_coef_aaZZ` prove `summable_aaNfun`. No restriction on complex ξ or w is hidden here.
- For `aaQt`, `c_j=3/(2πλ_J)` has norm ≤1 and the squared weight is ≥1 for `a,p≥0`. `summable_aaCoefC_aaZZ` expands `zz̄` as `(u_j²+v_j²)/(2 weight²)`, bounds each series by the corresponding sum of squared representative norms, then `summable_aaQt` multiplies by `⟨b,y⟩`. The boundary `a=p=0` is included.
- For `aaGbarR`, `‖B_{Ji}‖≤1`, each actual action is bounded by `‖w'_(+,J)‖ ‖w'_(-,J)‖` since the weights are ≥1, and `birkHalf_summable` supplies the ℓ² product bound. Restricting to `J≥3` preserves summability. The chosen `p≥1/2` is sufficient; the repair need not expose every possible convergent weight.
- For `birkOmegaMix`, the weight product is `J^(q+q') exp(2aJ)≥1`. `norm_birkOmegaMix_term_le` bounds each term by `‖y_l‖ ‖y'_{-l}‖`; `birkPair_summable` proves convergence. Individual q or q' may still be negative when their sum is nonnegative, exactly as the source mixed pairing permits. In particular `a=0,q+q'=0` is covered.

These are absolute-convergence bounds for scalar complex series; no conditional-sum ordering or divergent-`tsum` fallback is used. Fresh typed witnesses check each convergence export using only its advertised carrier guards.

## Meaning and premise preservation

| Source clause / affected helper | Verdict | Delta assessment |
|---|---|---|
| AA (i), (ii), (vi) | PASS carried forward | ActionAngle.lean and ActionAngleDomain.lean are byte-unchanged from the repair base. No source theorem or norm/weight convention changes. |
| AA (iii): `aaDer_symp`, equal-weight and plus-weight bridges | PASS | Only calls to `birkOmegaMix` gain proofs of guards already in the statements. Existing `0≤a` and `q+q'≥0` suffice. Derivative/inverse theorem signatures are unchanged; ActionAngleDeriv edits are documentation and deprecated alias replacements. |
| AA (iv): `aaMap_normalForm` | PASS | Already had `ha : 0≤a`, `hp : 1/2≤p`. These now feed `aaNfun`; `aaPfun` feeds the derived `0≤p` to `aaQt`. The literal Hamiltonians, constants, ξ-dependence, normal products and identity are unchanged. |
| AA (v): `aaQt_hasFDerivAt`, `aaQt_eq` | PASS | Already had exactly `ha : 0≤a`, `hp : 0≤p`; these now feed the guarded scalar definition. Derivative and symplectic conclusion unchanged. |
| AA (v): `aaP_isSmoothing`, `aaConjugacy`, reality and periodicity | PASS | Source-facing declaration types unchanged. No new theorem premise, field bound, regularity input or conclusion-shaped hypothesis. |
| AA (v) helper: `aaGbarR_aaMap` | PASS at revised helper scope | `hp : 0≤p` becomes `hp : 1/2≤p` to use the newly guarded W3-carrier object. This is a real helper restriction, not an unchanged generalization. Its source-facing caller `aaConjugacy` already assumes `p≥1/2`; at source `a=p=1` it adds nothing. |
| AA (v) helper: `aaQt_congr` | PASS at revised helper scope | Now takes `ha` and `hp0 : 0≤p`; its periodicity caller derives these from existing guards. This is an API change, not an extra source premise. |
| AA (v) helper: `aaP_isSmoothing_of` | PASS, stronger | Unused `hV : IsOpen V` removed; the domain conditions are retained and the conclusion unchanged. |
| AA (v) helper: `summable_aaGbarR` | PASS | Unused tangential index binder removed; coefficient bound and convergence conclusion unchanged. |
| initial: all `Initial*` exports | PASS carried forward | Both files byte-unchanged. `initialPerturbation`, its family bounds, constants, frequencies and source premises retain their round-1 meaning after the dependency repair. |

Comparing declaration headers throughout all eleven files confirms no other signature changes than the guarded-definition call substitutions and helper changes enumerated above. The blueprint's standing `a=p=1` discharges every new definition guard numerically. The mixed-form sum-of-exponents guard was already explicit in clause (iii). **Additional premises beyond the blueprint on source-facing theorems: zero.** Existing round-1 stronger statements omitting unused `0<s` / `r≤1` are unchanged, not new round-2 deviations. W6/W8 call-site adaptation is outside this delta approval.

## Validation

All Lean/Lake processes launched by this audit, including lint's ABI subprocess, ran serially inside the binding D53 wrapper:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

No heartbeat, recursion-depth, synthesis-budget or linter overrides were introduced. The owner's rules remain in force: **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override); **No Lean file may exceed 1500 lines of code.** All eleven package files remain under the cap (maximum 430 lines). No Lean source was edited by the audit.

Targeted build command (the driver acquires the compile gate and applies the exact D53 wrapper to each individual `lake build`):

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wps KAM.Wave.KamStep.ActionAngleConj KAM.Wave.KamStep.Initial
```

Exit 0. Output: `Build completed successfully (3671 jobs).` and `Build completed successfully (3674 jobs).` No `warning:` line names any `ActionAngle*` or `Initial*` file. Replayed warnings from unchanged dependencies, including Homological/PPlusOne, are outside N1 and are not claimed closed. Full output: `.lake/abi-scratch/w5-aa-r2-build.log`.

Lint was invoked **only** through the prescribed wrapper:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wps
```

Exit 0, exact output:

```text
check_lean_modules: PASS (3964 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

Full output: `.lake/abi-scratch/w5-aa-r2-lint.log`. The opt-in lunar declarations were only checked by file hash, exactly as stated in that output; no application build was requested.

N1 was independently checked by fresh elaboration of every changed Lean file, after lint completed. Sequential commands (each individual call wrapped with D53):

```sh
for m in ActionAngleDeriv ActionAngleSymp ActionAngleNormal ActionAngleQt ActionAngleGbar ActionAngleField ActionAngleConj; do
  systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean "KAM/Wave/KamStep/$m.lean"
done
```

Every call exited 0 and emitted **no warnings or errors**. This freshly covers every file that had an N1 warning in round 1. The remaining four package files are byte-unchanged and had no N1 warning sites; their targeted dependency builds passed as recorded above. Thus N1's 33 warning sites are closed, without expanding the audit to dependency warning cleanup.

A scratch file imported ActionAngleConj and Initial, ran `#print axioms` for the six new theorems, the affected theorem interfaces/helpers, and the three main dependent exports listed below. Four anonymous typed witnesses applied the convergence exports with only `m>0` where relevant, the advertised weight guards, and arbitrary representatives/parameters; each elaborated. Command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/W5AAR2.lean
```

Exit 0, no warnings/errors. Exact axiom output:

```text
'KAM.Wave.norm_aaOmegaN0_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_aaNfun' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_aaCoefC_aaZZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_aaQt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasSum_aaGbarR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasSum_birkOmegaMix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaMap_normalForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaQt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaQt_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaDer_symp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.birkOmega_eq_birkOmegaMix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.birkOmegaPlus_eq_birkOmegaMix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaGbarR_aaMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaQt_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaP_isSmoothing_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_aaGbarR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.birkHamBar_eq_aa' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fderiv_birkHamBar_tan' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.birkCoord_birkHamBarX_tan' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaConjugacy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaP_isSmoothing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.initialPerturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full fresh-elaboration/axiom output: `.lake/abi-scratch/w5-aa-r2-checks.log`. Scratch Lean probe deleted after verification.

Kernel replay and short-name checks: supplied as already completed by the launcher in the user prompt; their pane output is unavailable here. No local `leanchecker` invocation or newly observed replay/name-check exit code is claimed. The narrow fix did not require another replay. This provenance is separate from the local axiom and elaboration checks above.

Read-only static checks: `git diff --check 3f5734fc..HEAD` exited 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md` was empty. Four literal-body comparisons returned true; ActionAngle, ActionAngleDomain, Initial and InitialBound byte comparisons against the repair base returned true. Declaration-header comparison across all eleven files found only the signature changes enumerated above. Changed-source inspection found no forbidden proof placeholders, axioms, unsafe/opaque declarations or budget overrides. Module lint passes. No source erratum or unresolved semantic limitation remains for F1/N1; consumer adaptation beyond this delta remains unreviewed.

## Errata, deviations and limits

No new suspected blueprint/source defect was found in this delta. F1 was an implementation carrier defect and is repaired in the implementation; the pinned source is unchanged. No audit-introduced mathematical deviation. The helper restrictions/API changes are explicitly recorded above. No implementation, frozen file, manifest, generated root, README or git history was edited by this audit. Only this report is a repository deliverable; probe files are confined to `.lake/abi-scratch/` and removed after use.
