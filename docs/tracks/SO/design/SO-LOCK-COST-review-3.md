# SO-LOCK-COST delta review 3

**Overall verdict: FAIL.** The revised G1b comparison now observes the actual landed expression and all five jet fields; baseline accounting and the explicit deferral of unmeasured work are materially repaired. Remaining blockers are the incomplete G1c program-tail contract and the stale claim that the one-sqrt rewrite changes only unlanded declarations. The cited runner also points to a removed worktree, and G2 still does not check claim passing. These findings concern the reviewed plan and probe sources; no probe was run, and no resource result is asserted.

Auditor: maud-lockcost-3, 2026-10-30 UTC. Scope: **only review-2 findings and changed text**, including the cited probe sources. No re-audit of SO-LOCK-DESIGN or of the landed mathematical proofs. Read the repository rules, PLAN and DECISIONS, the requested diff, response table, prior report and directly relevant landed declarations. Refute-first source inspection only. This report is the sole new edit; the pre-existing untracked review-2 report was preserved.

## Snapshot and sources

Audited HEAD: **`424d7108dd469ec8292eaef265a4284d253ad9a9`** (`git log -1`: “SO-LOCK-COST rev 3: punctuation”). Compared against `21d8c1653ed9a50ae4f0b0a948183a0a31d98069`. All note locators below refer to this HEAD. `SO-LOCK-COST.md` SHA256: `9e249a0fe2893fc6c4b43eeaab8989b7543820733772a6eec4b1307a24097576`.

The four files actually present under `/mnt/HC_Volume_106379410/kam-data/so-lock/gate/` were inspected without execution:

| File | SHA256 |
|---|---|
| `GateLib.lean.inc` | `c457259a7f2a4573e0e74096d0becbd82aac0c69c8d46ee7f8ac9d87e67ef5e1` |
| `G0_emit.lean` | `1532e3ee3cdff6267e59d1d932b1d58a3f113cb8e98ae62d45ae801406190629` |
| `G1a_force.lean` | `c7dfb569b6c5fa7c9b2e83da1ad1b7b1b82c2306312da329f11acaa23094dfc5` |
| `run_gate.sh` | `6469102a9ce69656ba3589211ca0b627038089b8e62fa49cd406289c24d41961` |

Generated G1b/G1c/G1lit/G2 files and measurement logs were not present. Their intended contents were reviewed through the generator; they are not reported as emitted, elaborated or passing.

Current `inp` HEAD observed: `e78c95b46ab1321ef5896600b7ee7fc9babfa351`. Its `KAM/SpinOrbit/Lock/Coords/HamExpr.lean` is landed, has a built `.olean`, and has SHA256 `3cb6ac0a98d41776e8db30e696e9d4adafb3d0aa84d59fbf6c9af604889ae6a7`. Its last source commit is `59d5371548f87c4aa870c202f81f8e7caf57179a`. This live landing changes the status of the note's older “unlanded” claims; no frozen-source change was inferred from it.

## 1. HIGH — The no-landed-statement-change claim must account for the now-landed Hamiltonian and eval theorem

**Anchors:** note:133–147,214–217; current `inp` `HamExpr.lean:104–107,249–259`. The note still says “`lockHamExpr` is unlanded” and lists adding hΩ/hI to `lockHamExpr_eval` among changed **unlanded** design contracts. Both declarations now exist on `inp`. The landed expression is the two-root form, and the actual landed theorem is:

```lean
theorem lockHamExpr_eval (Ω : ℚ) (cs : List ℚ)
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockHamExpr Ω cs).eval z = soRotHC (lockToRotC Ω cs z)
```

Therefore the proposed one-sqrt body cannot replace the landed `lockHamExpr` while preserving that theorem's statement. The Ω/I branch premises are mathematically correct for the rewrite, but adding them to this existing theorem is now a landed statement change, outside the note's advertised additive contract and unrelated to the existing Q8 exception.

**Adversarial check:** at Ω=1, empty centre, α=φ=0, I=−1 and J̃=0, the totalized Y root vanishes. Replacing Y²/2 by `(Ω/(2π)) I cos²(2πα)` changes the value by −1/(2π). Thus retaining the all-z eval statement with the changed body is not an alternative repair. Giving the new statement a stronger premise does repair the new identity, but changes the landed statement if the old name is reused.

**Required correction:** introduce the one-sqrt expression under a genuinely new name, for example `lockHamExprLean`, with a separately named positive-domain eval theorem. Preserve the existing expression and all-z theorem, and route only the new certificate instance/glue through the new expression. Update the jet data and its bridge for whichever expression is actually selected. Lever 0 itself remains additive; this finding concerns the now-stale classification of lever 5 and the whole-plan additivity claim. No broader proof re-audit was performed.

## 2. HIGH — G1c includes program segments but still cannot assemble full program equality without a tail/length proof

**Anchors:** note:182; `G0_emit.lean:34–49`. The fallback now checks four program slices and the four remaining jet fields. This fixes review 2's omission of `prog`, but the program equations all use **bounded** slices:

```text
opsBeq ((lockJ.prog.ops.drop a).take (b-a))
       ((lockOpsLit.drop a).take (b-a)) = true
```

Their coverage stops at 3158. There is no checked `lockJ.prog.ops.length = 3158`, no equality of the full remaining tails, and no final empty-tail equation. `G1lit` checks **only the literal** list's length. G0 printing the computed program length is untrusted generation output, not a kernel theorem about the original program.

**Counterexample to the advertised structural implication:** let the literal program have 3158 operations, let the original program be that list followed by one extra operation, and leave v0/d1/d2/d3 unchanged. All four bounded slice comparisons, the four table comparisons and the literal length check pass, but the complete `HamJet` values differ. `List.take_append_drop` leaves the original `.drop 3158` tail unpaid; it does not establish that the tail is empty.

**Adversarial check:** G0 obtains literals from the actual compiler, so the emitted data may indeed have the correct full length. That is not a proof premise available to the advertised eight-theorem assembly. The purpose of the bridge is precisely to verify untrusted literal output. Nor do equal derivative tables rule out unused trailing operations.

**Required correction:** add and measure an actual-program length/equal-length theorem, or make the last program comparison use the **entire remaining tail** on both sides without `.take`. Assemble the full op-list equality, then all jet fields, by generic soundness/structural lemmas. The added theorem/assembly cost must be included in the bridge bill. G1b's full comparison does not have this tail defect; it is specific to the fallback.

## 3. MEDIUM — Probe syntax is substantially repaired, but the cited runner is not runnable in its specified environment

**Anchors:** note:166–170,204,209; `run_gate.sh:6–15`. The runner fixes `wt=/root/code/KAM-inp-lockcc`, but that worktree no longer exists. The landed Hamiltonian and its built object are available in `/root/code/KAM-inp`. Because the script uses `set -u` rather than fail-on-error, a failed `cd $wt` can continue in the caller's directory, accidentally selecting a different build/snapshot. “Now runnable” is not established by these files as currently configured.

**Required correction:** select an existing built checkout explicitly, record its revision, and make changing into it fail closed. Do not recreate the old worktree merely to preserve a stale path. The review did not execute the script or change its configuration.

The Lean-source changes themselves are appropriate at source-inspection depth:

- `GateLib.lean.inc:9` uses the real landed `lockHamExpr (8/65) lockCs`, with no invalid `.inv` expression proxy.
- Its `SlpOp` pattern matches cover all eight currently landed constructors, including `.sqrt`.
- `opBeq` compares every constructor field; `opsBeq` compares lengths before zipped entries; `jetBeq` compares the program plus v0/d1/d2/d3. `ballsBeq` similarly compares full rational ball lists.
- The G0 serializer emits constructor-qualified op literals and rational numerators/denominators. The chunking API `List.toChunks` exists in the imported library dependency sources. G2's counter and reverse-state argument order matches landed `ballsRev`.

These are **static checks**, not an elaboration receipt. G0, its `#eval`, G1 and G2 were not run. No assertion is made that the historical 3158 count matches the current compiled program until its actual checked count/bridge is available.

The runner now records USER/SYS, wall time, RSS, a saved process rc, `memory.peak` and OOM events, with `LEAN_NUM_THREADS=1` in the probe branch. Its shell syntax passes `sh -n`. Two operational notes remain: it logs the saved rc but does not exit with it after the final `tee`, so callers must not treat the runner's own exit status as Lean success; and a cgroup not found before termination yields a zero/missing peak, which must be classified as **unmeasured**, not a successful zero-memory receipt. The `emit` branch itself is not under the probe branch's lock/cap/logging. These observations do not require running any probe.

## 4. MEDIUM — G2 computes and compares balls, but does not check the claims used to select precision

**Anchors:** note:183,187–189; `G0_emit.lean:51–75`. The eight P/L/early/late combinations are now explicit, and checkpoints and segment output are computed with the same real evaluator and P. Successful generated theorems compare the **whole** returned list against the output literal. This repairs the missing interval/state specification and invalid-proxy issue at the level of intended G2 measurements.

However, the generator never calls `hamBoundsOk`, `hamClaimOk`, or any equivalent final inequality check. It does not even carry the M/refined-claim data needed for those checks. A `some` ball result can be far too loose to pass the intended Hamiltonian bounds. Conversely, `none` indicates failure of an evaluator safety/domain/reduction check; it does not prove that P is “too low for the claims.” Failure can be due to the domain/enclosure geometry, and may persist at P=320.

**Required correction:** call these outputs evaluator-success/segment-equality evidence only. Distinguish evaluator failure from failure of final bounds. Require the actual whole-pass claim/margin check at the candidate P before accepting it for the route, and do not presume that switching to 320 resolves failure. Middle segments, full tiling/chain and the final Ham consumers remain unmeasured. The revised deferral rule appropriately prevents a total-cost claim while those are open; it does not supply the missing precision-acceptance evidence.

## 5. CLOSED IN SUBSTANCE — G1b now measures the full bridge observation; production proof remains pending

**Anchors:** note:179–181; `GateLib.lean.inc:19–35`; `G0_emit.lean:30–40`. G1a is explicitly a scout that authorizes nothing. G1b tests `jetBeq lockJ lockJetLit = true`, comparing **all five fields**, including complete program lengths and every op payload. Successful evaluation of this conjunction cannot stop after checking only the program spine or indices: all comparisons must be true. This resolves the review-2 observation mismatch for the monolithic bridge.

A generic new lemma proving `jetBeq J K = true → J = K` is a sound intended bridge: the primitive/list equalities are lawful, and the observer checks all constructor/structure data with length checks before zip. The corresponding `ballsBeq` lemma can turn G2's Bool observation into an exact `some` equality. These lemmas are not supplied or proved by the inspected files, so G1b/G2 remain proposed measured observations until run and connected to those generic soundness lemmas. The production equality application and its assembly also remain proof/resource work; a sub-9-GB receipt would apply only to the tested workload.

The specialization to concrete Ω and centre coefficients removes review 2's generic-literal quantification concern. The generator is untrusted tooling; it does not introduce an analytic assumption. No landed theorem statement must change to add the literal jet, Bool-equality soundness, full bridge and J-variant checkers. The bridge must match the selected two-root or newly named one-root expression exactly; current G1/G2 target the landed **two-root** form.

## 6. CLOSED AS ACCOUNTING POLICY — Baseline is no longer added twice; total decisions explicitly defer

**Anchors:** note:172–175,191–205. The revised rule sums **whole-module USER+SYS totals**, counts each module once and does not add its data-only baseline again. G1lit/G4 are diagnostic splits, not extra charges on top of measured totals. This closes the review-2 ambiguity in `t_s + t_l/k`.

The updated bill explicitly includes the bridge/assembly, both Ham passes, emitted packed-module inventory, full consumers and bites/advice/graph/SOS. G3/G4 are now correctly blocked on LOCK-DATA emission, rather than described as ready without data. Consumer re-probing after subdivision precedes the final report outcome. Most importantly, **any unmeasured bill row means defer**; no current ≤20-hour decision is authorized.

The current evidence therefore leaves all of the following open:

| Item | Status after this source-only review |
|---|---|
| G0 generation and G1a scout | Source files only; not executed. |
| G1b complete bridge observation | Generator template only; no equality/axiom/resource receipt. |
| G1c fallback and structural assembly | Templates only; tail/length correction still required. |
| G1lit literal cost | Template only; no measured count/cost receipt. |
| G2 early/late P/L trials | Templates only; no generated ball data or measurements. |
| Middle segments, exact full chain and final claim checks | Unmeasured; not generated by the current eight-trial loop. |
| G3 full compose/Gram/torsion/frame and assembly consumers | Blocked on emission; no workload resource bound. |
| G4 actual grouped shard-module baselines/totals | Blocked; emitted class/count inventory unmeasured. |
| Lock-specific bites or verified reuse, advice-generation CPU, graph/SOS | No new receipt in this delta. |
| One-sqrt cost benefit and box-pass benefit | Earlier conditional estimates; current real probes target two roots. |

Per-class shard extrapolation and two-position segment extrapolation must remain labeled as such; they are not measurements of every final theorem. The note now says this explicitly for middle segments. The complete total must not be declared measured merely because a representative class was measured once. G0 emission cost also needs a place in the final generation/proof bill if the target includes total preparation CPU. No existing measurement establishes either resource target here.

## 7. Other review-2 dispositions and residual wording

The previous pass judgments on exact-equality checkpoint soundness, generic-P containment/320 compatibility, the repaired Ω/positive-domain identity and the abstract additive J-checker route remain scoped design judgments; this review did not re-audit those proofs. The now-landed two-root evaluator changes only the additivity classification discussed in finding 1, not the validity of the proposed positive-domain one-root identity under a new name.

Memory and packed-bill ranges are unchanged conditional models. The earlier caveat remains: differences of separately measured peaks are not independent additive allocations or a proof that every current lock consumer exceeds the cap. The older lever-0 summary at note:59 still mentions just the four table fields; the detailed §7 now includes program segments but needs finding 2's complete-tail condition. The older “G3/G4 decide it” wording at line 110 is superseded by the explicit all-rows-measured rule. These should be reconciled editorially once the blocking changes are made.

## Verification and closeout

**No probes were run.** In particular, neither `run_gate.sh emit`, its `probe` branch, G0's `#eval`, nor any generated Lean file was executed or elaborated. No benchmark, numerical generator, build or kernel replay was run. Validation consisted of source reads, the requested git diff/log, source/path existence checks, hashes, `sh -n run_gate.sh` (exit 0) and `git diff --check 21d8c165 HEAD` (exit 0). The shell syntax check does not execute the runner.

Source lint was not re-run: `scripts/lint_sources.sh` invokes a Lean ABI probe, and this turn explicitly restricts verification to inspection without running probes. No new Lean source was edited. Accordingly no fresh lint/ABI, build, theorem proof or `#print axioms` receipt is claimed; prior lint limitations are not silently upgraded.

The initial worktree already contained untracked `SO-LOCK-COST-review-2.md` with SHA256 `3400a54c183cd359c14134cf78edcfef6cb1ce9e5c4311c9396a94e3c045c8fe`. It was read and preserved byte-for-byte. No files under the gate directory, `inp`, frozen paths, manifest or generated roots were edited. Input hashes and final worktree status were checked at closeout. The only new file is this report.

Findings 1–4 survived separate adversarial checks against the actual landed header/body, a trailing-program counterexample, the runner's real path/error handling, and the distinction between evaluator success and final bound checks. No pinned mathematical-source erratum is alleged. This is a completed **FAIL delta report**, not a claim that any unrun probe or future resource target has failed experimentally.
