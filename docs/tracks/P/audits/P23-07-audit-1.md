# P23-07 independent package audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.lip_sup`. The proof delivers the exact revision-2 design signature, with no added premises or weakened conclusion. The notes concern a valid alternative Cauchy dependency and the permitted stale generated root. This infrastructure package contains no provider and seals no frozen anchor; provider/frozen-type and frozen seal-body checks are therefore not applicable.

Audited HEAD: `42ff00054e666a6eae8dff1057b4177bc76dc137`; comparison ref `inp`: `cba16d0704fe352828a08b2eff9cb691184b8208`. `git diff inp...HEAD` adds only `KAM/Planetary/TwoScale/Lipschitz.lean` (106 lines). Its SHA256 is `2610065db55eacb66a814ec7741d5e3932823d11a7665239e31daed215653022`. The pre-existing untracked handoff was preserved.

Read the package brief, AGENTS.md, PLAN, DECISIONS, track-P statement, handoff, revision-2 design and both design audits, the scoped blueprint statement/proof, frozen `actionNbhd`, and the actual Cauchy/inclusion dependencies. Design audits are under `docs/tracks/P/design/`, rather than the handoff's abbreviated audits-directory reference. The shared signatures are at `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`; this worktree has no copy at that relative path. The explicit user instruction determines this report's location in the package worktree, overriding the generic brief's main-worktree destination. Only this report was edited; temporary probes were confined to `.lake/abi-scratch/` and removed.

## Declaration and node verdicts

| Node / obligation | Lean declaration / locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p3:lip-sup` | `KAM.Planetary.lip_sup`, Lipschitz.lean:37–104 | PASS | Exact signature: arbitrary `S`, positive `r`, nonnegative `A`, holomorphy and pointwise bound on the frozen complex tube; all `N,m : ℕ`; Pi max norms; constant exactly `4*N*A/r`. |
| `stepP:p3:ls-close` | `lip_sup`, local `hder`, `hdiff`, `hmv`, lines 61–96 | PASS | Strict closed-ball inclusion, derivative operator bound `2*A/r`, convex mean value and isometric real inclusion give the stronger near-pair bound before weakening to the required constant. |
| `stepP:p3:ls-far` | `lip_sup`, lines 97–104 | PASS | Endpoint bounds give `2*A`; `r/2 ≤ ‖x-y‖` and `1 ≤ N` give the requested global constant. Equality at the threshold is included here. |
| Zero-dimensional case | `lip_sup`, lines 52–56 | PASS | `Fin 0 → ℝ` is subsingleton, so the difference vanishes; no positive-dimension premise is added. |
| Auxiliary openness | private `isOpen_actionNbhd_aux`, lines 28–35 | PASS | Identifies the frozen tube as a union of open complex balls. No premise beyond the literal definition. |

The public statement is whitespace-insensitively identical to both design Appendix A (lines 1018–1023) and the shared signature (lines 635–639). Binder order, constant dependence, carriers and conclusion agree. A probe copied the shared statement under the fresh name `KAM.Planetary.audited_lip_sup`, proved it with `exact lip_sup hr hA hΔ hbound`, and checked:

```lean
example : type_of% @audited_lip_sup := @lip_sup
```

This independently elaborated both the statement application and the fully quantified type comparison. No signature file containing draft proofs was imported. All hypotheses are source or typing/positivity data; no derivative estimate, Lipschitz conclusion or construction result is assumed. Explicit `hA` is exactly the approved design positivity guard, including when `S` is empty. Empty `S`, zero codomain dimension and `A=0` introduce no exceptional branch or fallback.

## Definitions and proof review

There are **no new definitions, abbreviations or structures**. The private auxiliary is a theorem, not a replacement domain definition. Reused frozen `KAM.actionNbhd` is literally the existential open max-norm tube around real `S`. `KAM.realInclusion` is the componentwise real-to-complex continuous linear inclusion, and `norm_realInclusion` preserves the Pi max norm on the whole carrier. No alternate norms, default values, extensions of `Δ`, or selected witnesses enter the proof.

For a near pair, the complex ball `B(ιx,r/2)` contains both endpoints. If `z` is in this ball and `w` is in `closedBall z (r/2)`, then `‖w-ιx‖ ≤ r/2 + ‖z-ιx‖ < r`, establishing the actual closed-ball hypothesis of `KAM.norm_fderiv_le_of_closedBall`. Holomorphy on the open tube supplies genuine derivatives throughout the convex ball. Its mean-value estimate therefore applies without assuming that `S` is convex or even connected. The far branch uses bounds only at the two endpoints. Both branches are sound under default elaboration resources.

**Dependency note:** design row P23-07 (line 271) lists `P23-01; Weighted.general_cauchy`, and the handoff's AUDIT FOCUS says “Weighted.general_cauchy consumed”. It is **not consumed**. The actual proof imports `KAM.Strip.Cauchy` and uses `KAM.norm_fderiv_le_of_closedBall` (line 75), whose operator-norm estimate is proved by restriction to unit complex lines. This proves the stronger local `2*A/r` estimate directly, replacing the blueprint's coordinatewise `2*N*A/r` argument. It is a valid proof-route deviation, not a missing analytic hypothesis or an unpaid proof step. Any dependency inventory should record the actual Cauchy theorem rather than claim consumption of `Weighted.general_cauchy`. No change to the theorem is required.

The KAM import closure has eight modules. Its only frozen imports are `KAM.Frozen.Defs.ActionNbhd` and `KAM.Frozen.Defs.ComplexStrip`, both `SEALED` in the current manifest. There is no provider or DRAFT_SORRY frozen theorem in that closure.

## Independent checks

Checks were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5` on every Lean/Lake invocation. No clean, update, dependency-cache mutation, generated-root regeneration, resource override or state-changing git command was used.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2307 KAM.Planetary.TwoScale.Lipschitz
```

Exit **0**; output:

```text
[inp-gate] slot 2 acquired 07:36:16 for KAM.Planetary.TwoScale.Lipschitz
Build completed successfully (9054 jobs).
```

This is the targeted overlay build's reported job total, not a command to rebuild the entire library. No warnings or elaboration failures appeared.

2. Signature and axioms probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2307Audit.lean
```

Exit **0**; only output:

```text
'KAM.Planetary.lip_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is every new public theorem (one); there is no provider export. No `sorryAx` or nonstandard axiom appears.

3. Kernel replay, one invocation for the sole new module:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.Lipschitz
```

Exit **0**; output:

```text
replaying KAM.Planetary.TwoScale.Lipschitz
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted generated-root exception; combined output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (454 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The root was left untouched as instructed. No line-length, forbidden-token, file-size, module-format, frozen-byte or ABI error was reported.

5. Static and repository integrity checks: module has 106 physical lines, maximum line length 97 Unicode characters; copyright, `module`, public imports, module docstring and `public section` are present. No new `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, `set_option`, recursion-depth or synthesis-heartbeat override occurs. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `git diff --check` exits **0**, with no output. Final report/scratch integrity was checked before handoff.

## Blueprint, source and handoff qualifications

No suspected pinned-source defect or false frozen statement was found in this scoped audit; no fresh external-PDF verification is claimed. The blueprint statement at `blueprint-P/parts/p3a-two-scale-iteration.tex:138–145` agrees with the theorem. Its proof's phrase “Since N ≥ 1” leaves the degenerate case implicit; the Lean proof handles it explicitly, so the statement needs no dimension repair. The blueprint's “up to the open/closed boundary; use radius r/2−epsilon” qualification is unnecessary here: the strict distance from `z` to `ιx` already supplies a strict margin for the closed radius `r/2` ball.

The handoff line 12 says “Constant 2NA/r in fact”. The submitted export proves `4NA/r`; its displayed near/far argument does not itself establish that stronger global claim. This audit certifies the exported constant only and does not allege that a stronger theorem is false. The actual dependency deviation is recorded above; no production correction was made by the auditor.

Files changed by this audit: only `/root/code/KAM-inp-p2307/docs/tracks/P/audits/P23-07-audit-1.md`. Remaining uncertainty: none about the scoped theorem after the checks recorded here. This result does not close P-G, other P23 packages, or the planetary campaign.
