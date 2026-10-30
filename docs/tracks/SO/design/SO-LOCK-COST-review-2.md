# SO-LOCK-COST delta review 2

**Overall verdict: FAIL.** Revision 2 repairs the principal memory attribution, the B1 sharing discount and the one-sqrt Ω contract. The literal-jet bridge is sound and can be additive. However, the new G1–G4 gate is not yet sufficiently defined or measured to make its stated route decisions: the proxy expression is not valid landed syntax, G1 does not measure the bridge it purports to authorize, its component fallback omits the program, and the post-gate bill still depends on unmeasured work and ambiguous baseline accounting. The remaining failure is in the proposed calibration/decision protocol, not in the landed checker or the mathematical possibility of the levers.

Auditor: maud-lockcost-2, 2026-10-30 UTC. Scope: **only review-1 findings and changed text**, including new lever 0 and G1–G4. No re-audit of SO-LOCK-DESIGN. Reviewed `git diff 9226069d 21d8c165`, the pinned revised note, its §9 response, the prior report and the directly relevant landed definitions/receipts. Used the focused refute-first audit protocol: fixed inputs, source comparison, separate adversarial checks, then validation. No implementation, numerical generation, resource benchmark, approval, commit or push was performed. This report is the sole retained edit.

## Snapshot

All revised-note locators below refer to **`21d8c1653ed9a50ae4f0b0a948183a0a31d98069`**, 269 lines, SHA256 `a3d43771ce06ee22aef2c1c1bb9126aa671777bf90877dc37f1bbc846b9f5aa2`. Comparison base is `9226069dfdc279e007296667ce4b10e7a520569d`. The requested delta changes the cost note and adds review 1; it changes no `KAM/` or `manifest/` source.

Worktree HEAD observed: `4b15819cb03903836986c433cac09e1d65ada8bf`. Its later compacted note has SHA256 `09fa17468d4758b6bc33134cab965c118ad39ca778ab3024f8278438bcd8bb8f`. The later compaction was inspected to distinguish versions; the review is anchored to the requested commit, and its substantive gate claims persist in the compacted file. Neither version was edited.

Read repository rules, PLAN and DECISIONS. Additional exact evidence includes:

- `SO-BALLDY-handoff.md` §§5–7, SHA256 `ae0e3f825988998b120904e2a0103676ebe9f31dfa326710a01724f29df84f15`.
- `inp-soballdy:.drafts/bd/J0.lean`, SHA256 `4f92cb29e6ead41827aa065adf96f9d5e2fce07e75101bd812424647eb169799`, and `.drafts/bd/run.sh`, SHA256 `c18048b8d14d582bf6927708d3d873d301e448a0d00b652f2f68587adf5d6bb9`, read through `git show` without creating a checkout.
- Landed `Certificate/Expr/{Basic,Slp,Diff,Ball,BallRound}.lean`, `Certificate/Defs.lean`, V2 interfaces and the OVERNIGHT 11:19 receipt. The review-1 report in the worktree has SHA256 `765df7e917c5f0efcdc5776f40fefcf46a19a52269f94eeea7882dab7ea1dfb8`.

## 1. HIGH — G1 cannot authorize the actual jet bridge; its proxy and fallback are incomplete

**Anchors:** revised note:63–73,220–226,242–243. The stated proxy replaces each `HamExpr.sqrt e` with `.inv e` and claims approximately the same compiled operation count. Landed `HamExpr` (`Expr/Basic.lean:35–47`) has **no `inv` constructor**: reciprocal expressions use `.div (.const 1) e`. `SlpOp.inv` is a different, internal language constructor. `lock_ham.py` emits `HamExpr` text, not an SLP, so the advertised replacement does not produce a valid expression for the landed compiler.

**Adversarial check:** interpreting “inv” as shorthand for `.div (.const 1) e` can produce a valid exploratory proxy. It does not justify the ±4 operation assertion or its use as a pass gate. Reciprocal and sqrt jet builders have different derivative formulas and emitted products/inverses, and no structural or measured comparison is supplied. A proxy can scout compiler costs, but cannot certify the actual sqrt bridge or actual ball/compose workloads. The note itself says it measures size rather than values; that limitation must constrain the decision rule too.

The G1 observation is also weaker than the bridge target. The actual referenced BALLDY `opOk` checks:

```text
const re im _ : positivity of re.den and im.den; degree is ignored
char k       : length of k only
other ops    : operand/index bounds
```

It does not compare rational numerators, the constant degree, individual Fourier-key integers, or the `v0/d1/d2/d3` tables to literals. The expression `ops.all opOk = true` is useful traversal evidence; it is not the same forced observation as equality of a complete `HamJet` with literal data. Even at the same imports and even for the real program, a peak below 8 GB for this observation would not establish that the full bridge equality fits below 10 GB. The 2 GB nominal reserve is not a measured bound on the missing work.

**Fallback defect:** `HamJet` (`Expr/Slp.lean:73–78`) has **five** fields: `prog`, `v0`, `d1`, `d2`, `d3`. G1′ names only the latter four. Proving those table equalities does not establish the `prog` equality, which contains the very operation list responsible for the program-forcing concern. Splitting table proofs also does not automatically split the compiler: each projection of `HamExpr.jet` can still demand substantial shared compilation. `Expr/Diff.lean:332–339` defines all five fields from the same `slpCompile` result.

**Required correction:** define a valid proxy transformation and label its result exploratory only. After the actual sqrt compiler is available, gate the **actual complete jet equality**, or a complete decomposition including `prog.ops`, under the cap with the intended literal data/imports. If the program equality needs segments, state and measure those program-segment bridges and the final structural assembly; table-only G1′ is insufficient. No proxy-only “≤8 GB ⇒ one bridge theorem” authorization should remain.

Status: survived attempts to rescue the rule using inverse shorthand, the nominal margin and table decomposition. This is a specification/measurement failure; no expensive probe was executed in this review.

## 2. HIGH — G2–G4 leave the route decision underdetermined and can double-count the literal baseline

**Anchors:** revised note:224–238 and the B1–B6 table:127–145. The improved gate addresses important missing observations, but its current bill and coverage cannot decide the stated route.

**G2:** exact early/late ball-result equalities are appropriate. However, the table fixes intervals 0–800 and 2400–3158, then selects the “largest segment” and has a stop test for a **late 400-operation** segment that it never specifies. Define the tested candidate lengths, exact late endpoints, actual checkpoint state/order and trial-selection procedure. The ellipses must be instantiated with the selected Hamiltonian form, rational parameters, Taylor order and genuine prefix literals. Because the actual program contains sqrt, G2 needs the new sqrt opcode and ball rule; it cannot run on the landed evaluator as written. An inverse proxy's ball values are not a valid substitute for actual sqrt ball values. Thus the assertion that all gates need “no checker change” requires a staged prerequisite: proxy exploration now, actual ball gates after the sqrt extension is available. The chosen precision must also pass the intended final Ham inequalities/claims; equality to a loose computed list alone does not show that P=128 is usable.

**G3:** forcing a full composition-step result and cached norms fixes review 1's `isSome` concern. One selected U-model × exp-witness step still does not bound the **other consumer theorems**: complete composition, Gram, torsion, frame and assembly remain B5. Those can fail the cap even when the isolated step is below 8 GB. This is already acknowledged at note:104–110, but the gate measures only the step. Establish representative stage/consumer targets, including the largest remaining stage and the final equality/assembly consumers, or explicitly defer these as blocking follow-up gates. Do not infer that stage subdivision is unnecessary from a passing single-step G3.

**G3/G4 accounting:** the command at lines 216–218 measures the whole Lean invocation. Unless otherwise defined, G3's measured shard time `t_s` already includes the literal/import work measured again by G4. The formula

```text
N_shards × (t_s + t_l/k)
```

therefore risks the same type of duplicate charge that the revision correctly removed from B1/B2. The note now quotes the useful matched example 235 s total, 190 s data-only. For k=1, using those measured values literally gives 425 s per shard, whereas the observed total is 235 s. To use this formula, define `t_s` as the **increment over a matched data-only module**, 45 s in that example, or use whole-module totals without adding the baseline again. For k>1, measure the actual grouped module and its memory peak; literal costs are not known to amortize as `1/k` independently of the import/data layout.

**Missing bill entries:** G1 bridge proof production/checking and its literal data are not separately included in the post-gate bill. B5 is explicitly unknown, yet the bill adds B5 without a measurement or upper budget. B6 (advice generation, graph/SOS and any non-reused bites) is absent from that formula. `N_shards` is also still unknown; the note does not require the emitted inventory which would determine it or distinguish width/shape classes. Multiplying a single selected shard time by an unknown count does not settle either the upper bound or the total.

**Measurement units:** the command records wall time (`%e`), RSS and exit status, not user/system **CPU** seconds. Either collect `%U` and `%S` and sum them, or label the budget as a wall-time model under explicit serialization assumptions. Set `LEAN_NUM_THREADS=1` for consistent probes. Preserve the Lean process exit/OOM result. The cited runner's 1-second sampled anon peak is a receipt for sampled anonymous memory, not an exact total cgroup peak; collect `memory.peak`/OOM events when deciding a hard cap. One cgroup-limited successful run is useful evidence for that exact workload, not an upper bound for unmeasured consumer workloads.

**Required decision rule:** unknown count/time/consumer peak means **defer/report**, not “≤20 hours.” Use a disjoint bill including bridge, all packed/module groups, both full Ham passes, all consumers, graph/advice/bites and assembly. Define precedence between G3's “subdivide” outcome and the global “any probe failing ⇒ report” rule. Route selection can be provisional, but must say which implementation/resource validations remain blocking. These repairs need no landed theorem-statement changes.

Status: survived the interpretation that the table is only a preliminary scout. As a scout it is useful, but the text calls it the authorization step and says G3/G4 decide the total; those stronger claims are not supported.

## 3. CLOSED WITH NOTE — Review-1 finding 1: memory attribution now matches BALLDY, conditionally

**Anchors:** revised note:23–61. The receipts now correctly distinguish 3.9 GB spine/import, 6.9 GB forced program, 7.46 GB with lookups and 8.98 GB full rounded Ham check. The assertion that all 6.4 GB above a 2.6 GB baseline scales with P has been withdrawn. Precision and ball segmentation are no longer represented as a certain remedy for compiler evaluation. The explicit full-state length of about 3158 and the withdrawn 0.15 MB claim also match the previous review.

The arithmetic differences are 3.0, 0.56 and **1.52** GB, as displayed approximately. These are differences of separate workload peaks, not measured additive allocations or proof of a causal decomposition. The new lock ranges explicitly state scaling assumptions; retain that qualification when saying the low-end sum exceeds 10 GB. No lock OOM or necessary scaling law has been measured. The defensible conclusion is **risk requiring calibration**, not that every consumer must fail. Lever 0 is a reasonable option, not a theorem that all successful routes must use it.

This closes the original attribution error at the level of the note's risk analysis. Findings 1–2 above explain why the replacement calibration does not yet close the resource decision.

## 4. CLOSED FOR B1/B2 — Review-1 finding 2: the revised CPU bill counts packed work once

**Anchors:** revised note:121–145. The initial packed bill is no longer discounted for avoiding duplicate frame work. B2 alone receives the sharing credit, conditional on actual reuse of B1 equations, with remaining model/norm work charged to B5. This resolves the review-1 double-discount finding.

Read-only arithmetic re-evaluation of the stated exponent model gives:

```text
per-product factor              19.1213 … 56.25
× 300/129 × R2 0.3 … 0.9 h     13.3405 … 117.7326 h
× 0.93 ÷ (2…3) × (96/112)^(1…2)
                                3.0384 … 46.9248 h
```

The revised 13–118 and 3–47 ranges are consistent. They remain conditional model ranges; the latter is B1, **not the total**. The box/width improvements are now explicitly unverified, the radius/sample mismatch is retained, and an exact box mirror precedes its Lean implementation. B4–B6 are admitted unknown or potentially dominant. That is a materially more honest bill.

The fresh baseline ambiguity and unpriced entries in the **post-gate** formula are separate, surviving problems (finding 2), so this closure does not approve a numerical total.

## 5. PASS AT DESIGN LEVEL — Lever 0 is sound and additive; its resource feasibility remains open

**Anchors:** revised note:63–73,201–208,252–257. A fully proved equality

```text
hJ : c.ham.jet = J
```

supports new checkers with explicit `J : HamJet` arguments and soundness theorems for the same actual Hamiltonian `c.H`. Such proofs can replace original jet references by J and reuse the original value/derivative bridges through hJ. The equality must cover **the entire jet**: program operations, v0 and all derivative-slot tables. Equal operations alone or equal tables alone do not suffice.

The new evaluator bodies must use J consistently for the op list, requested slot lists and all projections; leaving `c.ham.jet.d2` or a helper that recompiles `c.ham.jet` in a supposedly literal computation can reintroduce the original cost. Prove the generic J-variant soundness over variables, then instantiate it by theorem application with the bridge; avoid broad concrete reduction during final assembly. These are proof-structure obligations, not added analytic assumptions.

The emitted literal also must match the theorem's quantification: either specialize Ω and cs to the actual certificate data, or parameterize `lockJetLit` by them. An arbitrary-Ω/centre jet cannot equal one fixed unparameterized literal. The note's schematic N65 bridge can be made precise either way.

No landed declaration needs a changed statement for this route: keep `HamJet`, `HamExpr.jet`, old checkers, `TorusCertificate`, V2 interfaces and frozen analytic statements intact; add the literal data, full equality, J-checkers and new soundness/glue under new names. The pre-existing Q8 exception is neither used to change another helper nor enlarged. The additional evidence hJ is a checked computation identity in explicitly named helper theorems, not a replacement for the physical/analytic conclusion.

**Soundness/additivity verdict: PASS as an intended contract.** The actual bridge is not implemented or proved here. Its own complete proof and consumers must pass the resource gates; G1 as written cannot certify that (finding 1). A correct equality can still be expensive to establish or consume.

## 6. CLOSED — Review-1 finding 3: one-sqrt eval now has the correct Ω/domain conditions

**Anchors:** revised note:171–190 and253–254. The advertised eval helper now requires **both** Ω>0 and Re I>0. Therefore `IΩ/π` has positive real part and lies in the analytic sqrt branch, making the kinetic rewrite valid. The previous Ω=−1,I=1 example cannot satisfy the new premises.

Consumer checks remain scoped to this replacement contract:

- The clock consumer uses equality on the open positive-real-action set, so the full Fréchet derivatives agree locally. Its positive Ω premise is already available.
- Real transport supplies Ω>0 and I>0; its map-complexification statement need not use this Hamiltonian eval helper.
- Generic barrier glue now explicitly needs `actionPosOk`, with soundness, or an explicit derivation from the checked X radicand. `radius[0] < centre[0]` plus membership in the corresponding open action disc implies Re I>0 by the real-part/norm bound. Static shape checks and n=2 make that list coordinate legitimate. The note correctly does not claim `checkStatic` itself enforces this inequality.
- For the stated N65 literals, 0.01480−0.00261 = **0.01219>0** exactly. This supplies the data instance only after checking the actual rationals; it is not silently substituted for the generic premise.
- Generic Hamiltonian soundness/reality/safety results remain about the evaluator itself. The remaining X sqrt and emitted inverses still require their original checked safety obligations.

This closes the Ω finding without any landed theorem-statement change. Implementation, exact new check/signatures and their proofs remain future work; no physical theorem is sealed by this audit.

## 7. CLOSED AT SPECIFICATION LEVEL — Review-1 findings 4–7 and changed glue

The revised note explicitly withdraws “packed shards bound compose memory,” keeps model-stage subdivision as a contingency, and corrects missing-advice behavior (`none` leads to the coarse enclosure, explicit `.direct` selects direct multiplication). This addresses the earlier source-description defects. The remaining consumer-resource coverage is the gate problem in finding 2, not an allegation that the correction itself is false.

Exact checkpoint chaining now explicitly requires empty initial state, absolute slots, matching state lengths and exact tiling. It concludes deterministic pass equality. Widening is correctly separated as a different semantic/safety checker and is not proposed. Generic-P soundness is to be newly proved, rather than applying the landed fixed-320 `ballsSpec_sound` at 128. The plan is a new-base parameter or equality-bridge input, not implicitly an engine witness visible to `BaseChecker.check`. These are sound contract choices.

P=320 compatibility by unfolding the new `ballsP` body against existing `ballsAux` and `slpBallPrec=320` remains viable. Original functions/data paths can stay bit-identical. The note now qualifies precision accuracy and mixed exp/inv/sqrt workload costs. The new Gram projection and adapted torsion proof are properly named as additional glue instead of changing old Bool-premise theorems. No further landed-statement exception is required by the changed text.

## Gate disposition

| Gate | Useful observation | Current disposition |
|---|---|---|
| G1 / G1′ | Program traversal and potential full jet bridge cost | **FAIL:** invalid proxy syntax; traversal does not measure full equality; fallback omits `prog`; actual sqrt bridge still required. |
| G2 | Exact early/late segment result, precision comparison | **INCOMPLETE:** specify all inputs/trial intervals, genuine sqrt prerequisite, precision claim-passing check and full chain/consumer validation. |
| G3 | Packed shard equation and forced model/norm output | **INCOMPLETE:** one step is not the full consumer census; actual widths/layouts/counts and stage targets needed. |
| G4 and final bill | Matched literal/import baseline | **INCOMPLETE:** define incremental versus total shard time, actual module grouping/CPU units; price remaining entries or defer decision. |

The command's shared lock, `nice -n 5`, no-swap cap and reference to the existing runner are useful and source-identifiable. They do not fill these missing propositions, data dependencies or decision inputs. A route may be selected for further experimentation now, but the note cannot yet use G1–G4 as a sufficient authorization that the full route meets the requested resource limits.

## Verification and closeout

This was a read-only source/design review plus small Python arithmetic evaluations. The pinned note, requested diff, actual J0 observer/runner and relevant landed type/definition bodies were inspected. No G1–G4 probe, compiler proxy, dynamics computation or code generator was run. Existing BALLDY measurements are source receipts, not independent reruns. No Lean signatures/proof implementation were supplied for lever 0 or the revised gates, so none were elaborated or kernel-verified; no new theorem/axiom claim is made. There is no new production module to target with a build.

`git diff --quiet 9226069d 21d8c165 -- KAM manifest`: exit 0. Source lint was run separately with `LEAN_NUM_THREADS=1 nice -n 5 scripts/lint_sources.sh` and exited **1**:

```text
check_lean_modules: PASS (1650 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
.../.lake/abi-scratch/tmp8x0193sl.lean:1:0: error: unknown module prefix 'KAM'
No directory 'KAM' or file 'KAM.olean' in the search path entries:
.../KAM-inp-lockdesign/.lake/build/lib/lean
```

No other diagnostic appeared. The worktree still lacks its local build snapshot, so **full lint/ABI validation did not pass**. No build was created to mask that limitation. No audit Lean process overlapped lint, and no resource override, build clean, frozen/generated-source edit, dependency update or state-changing git operation was used.

Final `git diff --check`: exit 0. Both pinned and current cost-note hashes were rechecked unchanged. `git status --short` contains only `?? docs/tracks/SO/design/SO-LOCK-COST-review-2.md`. No auditor scratch files were created or retained.

No pinned mathematical-source erratum is alleged. Findings concern the internal calibration plan. The pass judgments above are design judgments with explicit proof/resource limits. This delta review is complete as a **FAIL report** with findings 1–2 unpaid; no repairs were silently applied.
