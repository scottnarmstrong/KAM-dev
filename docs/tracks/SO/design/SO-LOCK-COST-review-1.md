# SO-LOCK-COST review 1

**Overall verdict: FAIL as a priced recommendation.** The proposed additive checker architecture is viable, generic outward-rounded precision is sound, and exact checkpoint equations can be chained soundly. The note does not establish its claimed per-theorem memory guarantee or its approximately 20 CPU-hour total. Its memory premise contradicts the cited BALLDY breakdown, and its totals apply an unsupported sharing discount to a baseline that already counts the expensive work once. The one-sqrt eval signature also omits an essential Ω condition. These are defects in this cost note, not findings that the landed checker is unsound.

Auditor: maud-lockcost-1, 2026-10-30 UTC. Refute-first, focused source/contract/cost review. Scope is the four questions in the request. **SO-LOCK-DESIGN was not re-audited.** Its existing decisions, including the already documented helper exception, are treated only as interfaces referenced by this note. No source repair, implementation, data generation, kernel benchmark, commit or push was authorized or performed. This report is the only retained edit.

## Snapshot and evidence

The requested note is pinned to `9226069dfdc279e007296667ce4b10e7a520569d`, 331 lines, SHA256 `3ad82917aa7c15c43c6f9cb960969f04eeb63a1bf221f28c9fc0b16412128bc8`. **All cost-note line numbers below refer to that commit.** Worktree HEAD during review was `81aa699a53f4da80d4eb59e76d6e0709af53d469`; its note has subsequently been compacted to 249 lines, SHA256 `a43a111b6de6ce77eb874389a9249fff44e528f6e7f3732aa9ac94f21f80daeb`. The later compaction retains the material claims reviewed here. The pinned version was read through `git show`; neither version was modified.

Additional inputs read:

| Source | Revision / SHA256 |
|---|---|
| `inp-lockgen2` handoff | branch HEAD `fa835749ffef0b0ea346b01419ce95f21a5f3b6b`; file SHA256 `426f59b520bd4ac28baa20c4271363927474363e63f4978587a2f0c006167875` |
| `inp-lockgen2` `LOCK-GEN-NUMERICS.md`, Part 2 | same branch HEAD; SHA256 `12ff854d0e94c46af90c29db0ba3575b9012368fc9c8c6e8cbd6aeb6650306d3` |
| `inp-socsplit` study and audit 1 | branch tip `ad3f10f0d52d9d83894d0a6e484a6ca614052f88`, read through `git show`; the audit itself identifies its audited snapshot as `77dd30a7a141456dd6b763062aeb2930a7029c0c` |
| `SO-BALLDY-handoff.md` | worktree HEAD; SHA256 `ae0e3f825988998b120904e2a0103676ebe9f31dfa326710a01724f29df84f15` |
| `SO-V2PKG.md`, §4 | worktree HEAD; SHA256 `f3ccfe71bc6138b1e23502bacebbf03955de51cfad2558a28ff80cbddb25b6d1` |
| `KAM/Certificate/Expr/Ball.lean` | worktree HEAD; SHA256 `7adf31cb14a18c948b3849295f61e489e57a74ae0834179c102c3d24cf0cb521` |
| `KAM/Certificate/Expr/BallRound.lean` | worktree HEAD; SHA256 `b5b5edbaa7a397d16e5e891fb964c0b9167c4c1072a529d3d099c27e9ca09576` |

Also inspected the KDEPTH handoff, SO-DATA3 interim note 2, the landed pruning/shared-composition definitions, V2 `BaseChecker`/`EngineV2` interfaces, refined-engine wiring, Ham claims, torsion producer/soundness, frame majorants, product advice and packing layout. Rules, PLAN and DECISIONS were read. The `inp-socsplit` worktree is absent; branch-object inspection supplied its sources without creating a checkout.

## 1. HIGH — Ham memory attribution contradicts the cited measurement; segmentation plus P does not guarantee the cap

**Anchors:** cost note:25–26,33,60–63,105–121,208–210,300–302,325–326. In particular, “close the 10 GB risk on the Ham pass for certain” and “Ham-pass memory is the retained slot-ball list” are not supported by the cited source.

The BALLDY handoff explicitly reports a decomposition (`SO-BALLDY-handoff.md:148–160,212–221`):

| Observed workload | Reported peak / wall |
|---|---|
| Program spine alone, 887 operations | 3.9 GB / 54 s |
| All compiled program operations forced, **no balls** | **6.9 GB / 59 s** |
| Program plus reverse-list lookups | 7.46 GB / 65 s |
| Full rounded Ham check | 8.98 GB / 91 s |

Its explicit conclusion is **“The jet program dominates the memory, not the balls.”** This is not a single undifferentiated point, contrary to cost-note:325. The note's model assigns all 8.98−2.6 = 6.38 GB to `ops × P`; that includes program-generation cost which does not depend on the ball precision P. It also transfers a 2.6 GB literal baseline from a different workload without a matched-import measurement.

**Adversarial check:** smaller ball precision really can reduce ball arithmetic. Exact checkpoints really can stop cross-segment ball evaluation. Neither fact removes the cost of reducing `c.ham.jet.prog.ops` to obtain a segment. The proposed equations still use `(ops.drop start).take length` on the compiled program; late segments may force substantial compiler prefixes. Every boundary also carries **all prior balls**, so the maximum input-state length remains about 3158, not 400. A literal ball prefix alone does not make the original generated op list literal or prove its equality cheaply.

The source does not prove that the lock necessarily exceeds 10 GB either. It proves that the proposed guarantee and calibration model are unjustified. Possible repairs include checked literal op segments, a separate bounded compiler-to-literal bridge, or segmentation of compiler evaluation as well as ball evaluation. Those remain new-declaration approaches, but their bridge/assembly theorems must themselves be measured under the cap.

The arithmetic of the stated model is mostly close, **conditional on its invalidly calibrated premise**. Direct evaluation gives peaks 25.315, 11.686, 9.414, 8.354, 4.902 and 3.751 GB for the six unmeasured rows in the note. Scaling only the variable term by 1.5–2 gives 4.326–4.902 GB for an eight-segment box pass, rather than a justified 4.5 GB guarantee. These arithmetic checks do not validate the model.

**Required correction:** withdraw the categorical cap claims; separate compiler generation, op-data imports, checkpoint imports, lookup/state cost, ball arithmetic, export equality and final assembly. Measure an early **and late** fully forced segment with matched imports at P=128 and P=320, plus the program-identity bridge and final consumers. One 400-op segment cannot settle all these contributions or establish linear scaling.

## 2. HIGH — The 2–20 CPU-hour total discounts sharing twice and omits unbounded components

**Anchors:** cost note:48–54,96–99,217–220,285–293,327–328; LOCK-GEN-2 Part 2 §§P2.6; SO-V2PKG §4.4:219–235.

The initial 12–100 CPU-hour estimate is obtained from about **300 products = 106 torsion-model + 17 Gram + 157 compose + 20 witness products**, relative to R2's **base packed part** of 0.3–0.9 CPU-hour. The note correctly says pruning is already included in that estimate. SO-V2PKG then lists duplicate frame-majorant work as a **separate additional** 0.3–0.8 CPU-hour on R2, not as part of that base packed number.

The cost note nevertheless reduces 12–100 to 7–55 by sharing the extra frame work. Sharing prevents adding the duplicate bill; it cannot also discount the already single-counted base bill. There is no expanded product census in the note establishing that 12–100 secretly included another frame/torsion run. Its explicit 300-product census says otherwise.

**Adversarial check:** if an unshared implementation costs about 1.9 times the single-counted work, sharing can recover that factor **from the enlarged unshared total**. It returns to the single-counted 12–100 baseline, not below it. Reusing individual packed-shard theorems twice also saves proof production/checking of those shard equations; it does not automatically eliminate every downstream norm, matrix and model traversal. The separate base/frame projection proofs still need accounting.

Retaining the note's optimistic factors but removing that unsupported discount gives:

```text
single-counted packed baseline                         12–100 CPU-h
one-sqrt saving                                       × about 0.93
sharper pass                                          ÷ 2–3
width 112 -> 96                                        × (96/112)^(1…2)
result, best and worst endpoint combinations           about 2.7–39.9 CPU-h
even best sharper/width discounts on the 100 h endpoint about 22.8 CPU-h
```

This is **packed computation only**. The note itself excludes advice generation and per-declaration literal elaboration; it does not quantify their eventual total, model/radius/norm checks, shared-result assembly or graph/SOS work. SO-V2PKG explicitly excludes the literal baseline as well. Thus even a justified packed bound of 20 hours would not establish a total of 20 hours.

Further arithmetic caveats: factor sizes about 0.7 times the old sizes give `0.7^(1.5…2) ≈ 0.49–0.586`, not the note's substituted `0.6^(1.5…2) ≈ 0.35–0.5`. Using exactly size 6.5 and width ratio 240/208 in the stated exponent model gives about **19.1–56.25** per product, rather than 17–48. These are approximate input estimates, but do not support optimistic endpoint guarantees.

The sharper pass's threshold/support improvement is a plausible research lever. It is **not** a certified box-pass result: the note acknowledges no mirror; LOCK-GEN-2's “true sup” is sampled at ρ=1/140, whereas the recommendation uses ρ=1/100. Neither a sampled lower estimate of the true supremum nor a heuristic 1% inflation is a uniform bound. A sound box rule does not imply its final claims achieve those samples. The two compared radii and all frame/graph bounds must be recomputed with the actual checker. SO-DATA3's interim note separately records that some earlier sampled frame claims had been too small.

**Required correction:** publish a single non-overlapping bill of materials: base products, additional frame work, shared equations/projections, shard counts, literal costs and other checks. Retain the ≤20-hour goal as a conditional calibration target; the current evidence supports plausibility at favorable costs, not the claimed worst-endpoint total.

## 3. HIGH — One-sqrt eval identity needs an Ω/radicand condition, not positive action alone

**Anchor:** cost note §5:233–254, especially the proposed `lockHamExpr_eval (hI : 0 < (z.2 0).re)` at lines 239–241 and the “safe” verdict at 253. This review concerns that proposed replacement contract, not a re-audit of the earlier coordinate design.

Replacing `Y²/2` by `(Ω/(2π)) I cos²(2πα)` is valid when the radicand `IΩ/π` obeys `sqrtE(w)²=w`. `Re I>0` alone does not ensure that when Ω is unrestricted. Take Ω=−1, empty centre coefficients, α=φ=0, I=1 and J̃=0. Then the original totalized Y root is `sqrtE(-1/π)=0`. The lean kinetic term is instead **−1/(2π)**. The other terms agree at this point, so the proposed eval equality is false despite `Re I=1>0`.

**Adversarial check:** all intended physical callers already have Ω>0. That rescues their intended applications; it does not prove the displayed arbitrary-Ω helper from hI alone. Totalizing sqrt on the cut also does not rescue the algebraic rewrite. A sufficient corrected new contract has **both** `hΩ : 0 < Ω` and `hI : 0 < (z.2 0).re`. A more general algebraic contract can directly require the radicand in the slit plane (and optionally handle zero separately). Do not describe hI alone as the complete repair.

Consumer disposition for this lever:

| Consumer / use | Review result |
|---|---|
| Clock derivative | Safe with Ω>0 and Re I>0 **on a neighborhood**: equality on that open set justifies equality of full Fréchet derivatives. Pointwise equality alone would not. |
| Real physical transport | Safe with Ω>0 and I>0; positive-action recovery supplies the branch. The real map's own complexification theorem need not use the Hamiltonian eval identity. |
| Generic certificate-to-barrier transport | Needs an actual proof of the domain/local branch condition, not merely the numerical N65 example. `checkStatic` does **not** check `centre[0] > radius[0]`; see `Certificate/Defs.lean:220–234`. Add a new decidable positivity premise/check and its soundness, or explicitly derive the needed branch condition from the checked remaining sqrt operand. |
| Analytic bounds / structural reality | Their generic `HamExpr.eval` theorems do not depend on the physical eval identity. They retain their statements after proving the relevant new expression cases. |
| Program safety | The checked jet must still certify every remaining sqrt/inverse. Removing Y's root does not remove the obligation for X's root. This is independent of physical transport. |

For the proposed N65 disc, 0.01480−0.00261 = **0.01219 > 0**; 0.0122 is a rounded display, not an exact lower bound. Exact rational data can establish positivity. That particular calculation does not supply a premise to a universally quantified certificate helper. Since the physical Ω and positive domain are available or checkable, the one-sqrt lever is repairable without changing landed theorem statements or the headline; its advertised helper signature and “one hypothesis” accounting are incomplete as written.

## 4. MEDIUM — A cap on packed shards does not bound composition/matrix assembly; missing advice behavior is misstated

**Anchors:** cost note:258–278,309–310. Choosing smaller blockRows can bound an individual packed integer multiplication theorem and is a reasonable lever. It does not establish the stronger claim “the shard layout already bounds the compose memory.”

The landed composition still builds slot models/cached norms and performs polynomial merges, truncation and error-radius arithmetic outside the integer-product shard equations. Gram/torsion perform additional matrix/model work (`Torsion/Models.lean:152–177`, `Frame/Majorants.lean:130–175`). Their consumer theorem can retain or re-normalize inputs/results even if all integer multiplications have named proofs. This is exactly the distinction in SO-COMPOSE-SPLIT audit 1, findings 4–5. Reusing shard proofs is valuable; it is not evidence that the remaining whole composition, Gram check, torsion construction or final assembly fits.

The claim that missing advice falls back to direct multiplication is also wrong for the inspected landed source. In `Model/Ops.lean:83–94`, nonconstant factors with missing advice return `none`. `CertModel.mul:114–116` then returns a zero polynomial with a coarse sound radius. An **explicit `.direct` advice entry**, or a constant factor, selects the direct route. `Expr/Compose.lean`'s cached-norm multiplication has the analogous fallback. LOCK-GEN-2's handoff repeats the same inaccurate missing-advice description. Advice is still practically necessary for the desired tight certified margins, but the reason is not automatic unbounded direct multiplication on every absent key.

The 6.5-times-larger term count does not itself determine the number of block pairs per shard. The emitter derives rectangular dimensions, strides and block length from the key geometry (`scripts/spin_orbit/sofx_packed.py:424–453`). Bound the actual encoded integer bit lengths, pairs and literal/import overhead. Smaller blockRows also changes shard counts and packing/decoding overhead; “same total” is not exact cost invariance.

**Required correction:** retain composition/stage subdivision as a contingency until representative **consumer** checks fit. The calibration must force full outputs/norms and prove the intended shard equations, not just observe `Option.isSome`. Include assembly in the under-10-GB measurements. Reused Diophantine bites are conditional on exact box/site parameters, as the note correctly acknowledges; other near-cap work is not covered by that reuse.

## 5. NOTE — Segmented Ham soundness passes for exact equations; containment is a different contract

**Anchors:** cost note:139–162; landed `Expr/Ball.lean:214–247,264–288,456–460`. Unlike the request's informal containment description, the pinned note actually proposes **exact equality** between segment outputs and checkpoint lists. This distinction matters.

For fixed P, n, weight, domain and Taylor order, let F(k,A,ops) denote `ballsRev P … k A ops`. Its defining recursion admits:

```text
F(k,A,u ++ v) = (F(k,A,u)).bind (fun B => F(k + u.length,B,v)).
```

If the checked plan tiles exactly `[0,p.ops.length]`, starts with **empty acc₀**, has `acc_j.length=s_j`, uses reverse-order state consistently, and proves each exact segment equation from that same original op list, induction gives `Slp.ballsP … = some acc_m`. Absolute slot numbers must not reset at a boundary. Every checkpoint is untrusted literal witness data until its producing equation is proved. Endpoint/length checks must be explicit, not defaulted unchecked indices. With these conditions, no assumed `Encloses` or analytic conclusion is smuggled into the chain.

The append lemma alone provides computation equality, not memory reduction or semantic safety. A generic-P ball soundness theorem plus inverse/sqrt safety extraction then gives the analytic facts. Existing `ballsSpec_sound` permits arbitrary initial `BallRel`, but its actual statement uses **fixed-320** `ballsSpec`; applying that landed theorem directly at P=128 is invalid. Add a new `ballsSpecP`/generic soundness induction, or prove the invariant directly for `ballsRev P`, using existing generic `ballStepG_sound`. This requires new lemmas, not a change to the old theorem.

If checkpoint transitions instead permit **containment/widening**, require a checked componentwise condition in the outward direction:

```text
computed ball B_i ⊆ next checkpoint ball A_i
e.g. an outward bound on |centre(B_i)-centre(A_i)| + radius(B_i) <= radius(A_i).
```

Together with matching lengths/order and an initial semantic `BallRel` established from the empty state, this propagates enclosures soundly. Preserve each segment's successful inverse-exclusion and sqrt-positive-real checks as well: final slot enclosure alone does not imply those safety predicates. A widening chain generally **does not** imply equality with the deterministic monolithic `Slp.ballsP` result. For example, widening a computed zero-radius ball to radius 1 preserves enclosure but changes the list value. Such a route needs a new segmented checker/semantic soundness theorem, not the advertised `ballsP_eq_of_segments` equality conclusion.

Thus the exact-equality route is a sound intended contract and preserves old APIs. A containment variant is also possible with a different conclusion and full safety bookkeeping. Neither route has typed implementation/proof evidence in this note. Its 0.15 MB checkpoint calculation is raw mantissa arithmetic (3158×3×128/8 = 151584 bytes), not Lean expression/import/equality-checking memory. Unrounded constants/actions/characters/sums, rational denominators and exponent spreads also defeat a blanket “each rational ≤128 bits” claim.

## 6. NOTE — Per-certificate precision is sound and can preserve the 320-bit path; accuracy and linear performance are unproved

**Anchors:** cost note:123–137,164–166; `BallRound.lean:41–106`; `Ball.lean:167–247,353–454`.

`ballRound_mem P` is proved for **every natural P**, using positive dyadic scale, flooring both centre coordinates and rounding the radius upward after adding the centre displacement. This is a containment theorem, not a nearest-rounding heuristic. `ballStepG_sound` is already generic in P. The inverse test still excludes zero before inversion, and exponential rounding is outward throughout range reduction/squaring. New sqrt rules must have the corresponding proved branch/ball checks. P=128 can be sound even if it produces looser bounds or returns failure; a lower bound on P is not needed for basic containment.

A new definition

```text
Slp.ballsP P … p := (ballsRev P … 0 [] p.ops).map List.reverse
```

at P=320 has the same computation as the existing `Slp.balls` by unfolding `Slp.balls`, `ballsAux`, and `slpBallPrec=320`. An exact compatibility lemma should record this. Leaving the old functions, route and certificate data untouched preserves SO-DATA3's original path bit-for-bit. Adding P to a **new base-checker parameter** or a new engine witness does not require changing `TorusCertificate`. However, `BaseChecker.check` itself receives only c, not an engine witness; a checkpoint plan stored solely in that witness must be used by an equality bridge, supplied as a parameter to the new base instance, or handled in a new checker. It is not implicitly available to `B.check c`.

The numerical claim “rounding inflation per op ≈2⁻¹²⁸ relative” needs qualification. The rounding grid is relative to each **ball's magnitude**, not the exact result of a cancellation or a global final bound. Repeated operations, interval overestimation, inverse margins, root margins, exact sums and exponential growth must be checked by the actual mirror/checker. Soundness does not guarantee the chosen claims pass. BALLDY's measured 887-op benchmark contains **zero exp and zero inv**, whereas the lock program includes both and sqrt, so scaling 91 seconds linearly by ops×P is not a measured workload comparison. This numerical/performance limitation reinforces finding 1; it is not an unsoundness of outward rounding.

## 7. PASS AT ARCHITECTURE LEVEL — The cost levers need no additional landed theorem-statement change

The no-new-landed-statement-change route is available for each lever, **relative to the separately authorized sqrt extension and its existing Q8 helper exception**, which the note explicitly excludes from its new changes. “Every lever adds new declarations” is shorthand: lever 5 changes an unlanded expression/design contract and lever 6 changes emitted data/layout, not necessarily checker declarations.

| Lever | Additive route checked against landed consumers |
|---|---|
| Pruned V2 base/frame | New `torsionModelsPruned` uses `Slp.composePruned_sound` to enclose original wanted slots. New torsion/frame soundness theorems establish the same analytic facts; they need not prove equality with old unpruned Bool tests. `BaseFacts` and `checkV2With_sound` permit selecting a new `BaseChecker`. |
| Precision P | New evaluator/checkers and generic-P proofs; fixed-320 functions/contract remain untouched. |
| Segments | New exact computation bridges, or a separately named containment-based checker with semantic/safety proofs; no old theorem strengthened. |
| Box pass | New sound pass and Ham facts feed unchanged `refinedCore_sound`. Positive-real sqrt imaginary bound is valid: writing √w=u+iv, u≥√ℓ and 2uv=Im w gives |v|≤b/(2√ℓ). Rational upper bounds must use a certified positive **lower** approximation for the denominator. Box/disc selection must preserve actual slot containment. |
| One-sqrt form | Unlanded body/eval/consumer contracts may change, with finding 3's corrected branch conditions. Generic landed expression/soundness results remain about the actual evaluator. |
| Product layout | Valid emitted packed advice uses the existing layout/decoding/shard soundness contracts. Measured resource bounds are separate from mathematical validity. |

Do not use `checkGram_of_checkTorsion` literally on a new `checkTorsionPruned` premise: add its new projection analogue, or expose the new checker's internal successful `gramCheck`. Similarly adapt the proof behind `checkTorsion_sound_of` to the new producer rather than assuming its old Bool premise. This is new proof glue and does not require editing those landed statements. `checkInvEnShared_sound` already consumes analytic Hamiltonian/embedding facts, and the refined core consumes abstract `HamFacts`/`FrameFacts`, so the proposed additive integration has the needed semantic interfaces.

This is a **design feasibility** result. No implementation diff exists here to verify literal declaration preservation. The actual dispatch needs exact new signatures and per-consumer wiring, and subsequent implementation/ABI checks must enforce the no-extra-change contract. Nothing in this report reopens or silently expands the existing SO-LOCK-DESIGN exception.

## Verification and closeout

Evidence collection was read-only: pinned `git show`, source reads/searches, branch/worktree identification, hashes, and small Python arithmetic evaluations. No generator, numerical dynamics computation or kernel resource probe was rerun. Timings, memory peaks and previous audit outcomes quoted above are **source receipts**, not fresh benchmark results. No draft Lean signatures were supplied by this cost note; no new declaration was elaborated or proved in this review, and no new main-result axiom claim is made. No production module exists to target with a build. All source/consumer assessments above have their explicit design-level limits.

`LEAN_NUM_THREADS=1 nice -n 5 scripts/lint_sources.sh` exited **1**:

```text
check_lean_modules: PASS (1650 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
.../.lake/abi-scratch/tmp1f5l23s7.lean:1:0: error: unknown module prefix 'KAM'
No directory 'KAM' or file 'KAM.olean' in the search path entries:
.../KAM-inp-lockdesign/.lake/build/lib/lean
```

No other diagnostic appeared. The worktree lacks its local build snapshot, so **the full lint/ABI gate did not pass**. No build was created to conceal the limitation. No audit Lean process ran concurrently with lint. No heartbeat/depth override, build clean, frozen/manifest/generated-root edit, dependency update, state-changing git action or message to another person was performed.

Final `git diff --check`: exit 0. Both the pinned and current cost-note hashes remained unchanged. `git status --short` contains only `?? docs/tracks/SO/design/SO-LOCK-COST-review-1.md`. No auditor scratch files were created or retained.

Findings 1–4 survived a separate adversarial check: precision/checkpoint benefits do not remove compiler cost; sharing saves only a duplicate bill actually incurred; positive action does not imply a positive radicand for arbitrary Ω; shard equations do not bound the rest of model/checker normalization. Findings 5–7 identify sound options and the exact contracts their implementation must prove. The appropriate recommendation is **calibrate and repair the note before treating it as a ≤20-hour, under-10-GB implementation authorization**. No pinned mathematical source erratum is alleged; the errors concern our internal estimates and interface descriptions.
