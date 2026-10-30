# SO-LOCK-COST: pricing the kernel levers for the N = 65 lock certificate (design note)

**Status:** 30 October 2026, branch `inp-lockdesign`. Design note only: no Lean, no proofs, no data. The numbers
come from:
- LOCK-GEN-2 (`inp-lockgen2`: `.drafts/handoff-LOCK-GEN-2.md` and `LOCK-GEN-NUMERICS.md` §Part 2);
- SO-V2PKG §4;
- the SO-BALLDY and SO-KDEPTH handoffs;
- SO-DATA3 interim 2;
- SO-COMPOSE-SPLIT and its audit 1 (`inp-socsplit`).

I made no Python reruns: every figure below is either quoted, with its source, or derived by plain arithmetic
that is shown. This note includes the orchestrator's addendum (Ham-pass precision and segmenting). A codex-1
review follows.

**Targets:**
- every single kernel theorem stays under the 10 GB cap;
- the total stays at about 20 CPU-h or less;
- landed statements are unchanged, and anything new carries a new name.

## 0. Summary

| # | lever | what it buys | landed-statement impact | size | audit |
|---|---|---|---|---|---|
| 1 | pruned composition in a v2 base checker | **already assumed** by LOCK-GEN-2's 12–100 CPU-h. Without it, 1026 instead of 157 compose products, about 3–5× the compose cost | none: new names `sharedBaseV2`, `torsionModelsPruned`, `checkFrameMajorantsP`, `routeAV2P` | 250–400 lines | small (it reuses `composePruned_sound`) |
| 2 | Ham-pass precision P (default 320) | Ham-pass memory and time ∝ P (addendum). At P = 128, ≈ 0.4× | none: new names `Slp.ballsP`, `checkHamBoundsP`, `checkHamClaimP`. `ballStepG` is already generic in P | 80–150 lines | small, like BALLDY |
| 3 | segmented Ham pass with ball checkpoints | per-theorem memory ∝ segment length. Hard cap safety | none: new names only. Checkpoints are certificate-side witness data | 300–450 lines | medium (chaining lemma) |
| 4 | sharper Ham pass (strip/box shapes through exp and sqrt) | threshold −18.0 → about −15.6, support 90×18 → about 75×15, cost ÷ 2–3 | none: new pass and new route names | 600–900 lines | medium–high (like C3) |
| 5 | one-sqrt "lean" `lockHamExpr` | −1 sqrt, −1 inv, −20 of 128 torsion-compose products (≈ −7 % of all products) | none landed (`lockHamExpr` is not landed). A design statement changes; owner item | ≈ 0 extra | small |
| 6 | product shards (blockRows) | keeps each packed-product theorem ≲ 4 GB | none: an emitter parameter (SO-PACKFIX layout) | 0 | none |

**Recommendation, in order:**
1. 1 + 6, which are mandatory;
2. 2 + 3, which are cheap and close the 10 GB risk on the Ham pass for certain;
3. 5, a free 7 %, pending the owner's ruling;
4. **a calibration probe**, before 4 is commissioned (§6);
5. then 4, unless the probe already puts the total under 20 CPU-h without it.

The ≤ 20 CPU-h target is reachable with 1 + 4 (+5) at the lower two thirds of LOCK-GEN-2's exponent range. It
is not reachable without 4 unless the probe lands at the bottom of the range (§5).

## 1. The starting point (quoted)

LOCK-GEN-2 at ρ = 1/100, μ = 1/1000, κ = 1, refined route A, configuration d01b:
- **Threshold:** 10^−18.03. err is 9e-20 and disp is 3.4e-14.
- **Support:** diamond 90 × 18, with 1636 / 1576 / 1509 half-terms. CertFixed 112, data scale 101 bits.
- **Program:** 3158 operations (4 sqrt, 8 inv, 4 exp), against 887 for R2.
- **Products:**
  - ≈ 300 heavy products, against R2's 129: 106 torsion models + 17 Gram + 157 compose + ≈ 20 witnesses;
  - factors ≈ 6.5× R2's;
  - per product ≈ 17–48× R2.
  - **The 157 compose products are counted after pruning**: 5 energy + 24 invariance + 128 torsion
    (`lock_jet.heavy_products`).
- **Projection:** ≈ 12–100 CPU-h for the packed part. That excludes the Ham passes, the advice generation and the
  literal baseline.
- **Ham claims:** the disc pass overestimates 70–300× (d2x 3.5e4 certified against 102 true, dx 140 against 1.7).
- **Memory:** R2's Ham pass peaked at 8.98 GB on 887 operations at `slpBallPrec` = 320 (SO-BALLDY: 91 s,
  8.98 GB). That pass is one declaration and runs twice: `checkHamBounds` in the base and `Slp.balls` again in
  `checkHamClaim` (SO-V2PKG §4.4).

SO-KDEPTH does **not** help the Ham pass. It made the following traversals log-depth or strict:
`weightedNormUp`, `directItems` and `composeOps`. The Ham-pass memory is the retained slot-ball list of
`Slp.balls` (SO-BALLDY's reverse-cons, rounded to 320 bits). SO-KDEPTH's strict `composeOps` loop is still what
lets a 3158-operation composition reduce at all.

## 2. Lever 1: pruned composition

**Status of the landed engine.**
- `KAM/CertificateSharp/Kernel/Prune.lean` gives `Slp.composePruned` and `Slp.composePruned_sound`. The latter is
  `Slp.compose_sound` for the original program at the wanted slots.
- `Kernel/Shared.lean` uses it in `checkInvEnShared`, but only inside v1's `checkTorusCertificateShared`.
- **The V2 engine does not use it.** `landedBase` (V2/Engine.lean:100), `trigBase` and `cornerBase` all call the
  landed `checkInvariance`, `checkEnergy`, `checkGram` and `checkTorsion`. Those run the plain `Slp.compose` over
  the whole program.
- `checkTorsion` reaches `Slp.compose` through `torsionModels` (Certificate/Torsion/Models.lean:155, wanted =
  `torsionSlots`).
- `checkFrameMajorants` (CertificateSharp/Frame/Majorants.lean:160) calls `torsionModels` again.

For R2 this cost little: 887 operations, and most slots are wanted. For the lock it is decisive. The whole
program has 1026 model × model products; the wanted closures have 157.

**Change.** New names only; no landed statement moves:

| new declaration | body | soundness |
|---|---|---|
| `torsionModelsPruned` | `torsionModels` with `Slp.composePruned … (torsionSlots n e.jet)` | `torsionModels_sound`'s proof, with `composePruned_sound` in place of `compose_sound` (Models.lean:575) |
| `checkTorsionPruned` | `checkTorsion` over `torsionModelsPruned` | the conclusion of `checkTorsion_sound` (and `_of`) |
| `sharedBaseV2 : BaseChecker` | `checkStatic && checkHamBounds(P/seg, §3) && checkEmbedding && checkInvEnShared && checkTorsionPruned` (Gram from `checkGram_of_checkTorsion`-style reuse) | assembled like `landedBase.sound` from `checkInvEnShared_sound` |
| `checkFrameMajorantsP` | `checkFrameMajorants` with `torsionModelsPruned` | as landed, with the pruned torsion lemma |
| `routeARefinedP`, `routeAV2P` | `routeARefined` with `checkHamClaimP`/segmented (§3–4) and `checkFrameMajorantsP` | `refinedCore_sound` is unchanged: it takes `HamFacts` and `FrameFacts` abstractly |

**Consequences for the design.**
- `lockBarrier_of_certV2` (SO-LOCK-DESIGN §6) names `checkTorusCertificateV2 routeAV2` / `landedBase`. It would
  name `checkV2With sharedBaseV2 routeAV2P` instead.
- That is a statement change of an **unlanded** design theorem only: it is listed for the owner.

**Further saving.** SO-V2PKG §4.4 notes that the frame majorants re-run Gram and torsion: about 90 % of the
packed shards again. Sharing those product proofs as one `torsionModelsPruned` result is an
emitter/theorem-structure choice: the same packed-shard theorems are cited twice, at no checker change. It is
worth up to about 1.9× on the packed part; include it.

**Price:** 250–400 lines. One audit, mechanical, because every soundness proof is a re-use.

## 3. Ham-pass memory: levers 2 and 3

**The memory model.** This is my assumption, to be calibrated (§6):
- memory = base + ops × P × m₁;
- base ≈ 2.6 GB (SO-DATA-2: literal data alone, 2.6 GB);
- R1 then gives m₁ = (8.98 − 2.6)/(887 × 320) ≈ 22 kB per op-bit.

| configuration | ops in one theorem | P | projected peak |
|---|---:|---:|---:|
| R2 (measured) | 887 | 320 | 8.98 GB |
| lock, monolithic | 3158 | 320 | **≈ 25 GB** (fails) |
| lock, monolithic | 3158 | 128 | ≈ 11.5 GB (fails) |
| lock, monolithic | 3158 | 96 | ≈ 9.3 GB (no margin) |
| lock, 4 segments | ≤ 800 | 320 | ≈ 8.2 GB (thin) |
| **lock, 4 segments** | ≤ 800 | **128** | **≈ 4.9 GB** |
| lock, 8 segments | ≤ 400 | 128 | ≈ 3.7 GB |

So **precision alone does not suffice**, unless the scaling is far better than linear. Segmentation at 320 bits
is borderline. Together they give a margin of 2× or more.

**Lever 2: precision.**
- `ballStepG (P n …)` and `ballStepG_sound {P n …}` (Expr/Ball.lean:167, 353) are already generic in P. Only
  `ballsAux`/`Slp.balls` fix `slpBallPrec`.
- **Change** (new names):
  - `Slp.ballsP P := (ballsRev P … ).map List.reverse`;
  - `ballsP_sound`, by the `ballsSpec_sound` route, re-run with P;
  - `checkHamBoundsP`, `checkHamClaimP` with their `_sound`;
  - `HamExpr.nonvanishingOn_of_ballsP`, the analogue of `nonvanishingOn_of_balls` (now with sqrt, per
    SO-LOCK-DESIGN §4.2).
- **Where P lives.** Put P in the base checker or the route witness, **not** in `TorusCertificate`. That avoids a
  format change, and SO-DATA3's landed data and mirror are untouched (default 320). One example is the base
  checker `sharedBaseV2 P`.
- **Accuracy.** The claims need only a relative accuracy of about 1 %, and the data are 101-bit. At 128 bits the
  rounding inflation per op is ≈ 2^−128 relative, which is negligible over 3158 ops.
- **Size and audit.** 80–150 lines. A BALLDY-like audit, small.

**Lever 3: segmentation with ball checkpoints.** This is route E of SO-COMPOSE-SPLIT, applied to balls instead of
models.
- **The witness.** The certificate side (route witness) carries a plan [0 = s₀ < s₁ < … < s_m = 3158] and, at each
  boundary s_j, the literal list `acc_j` of all slot balls so far, already rounded.
- **One theorem per segment:**
  `ballsRev P … s_j acc_j.reverse (ops.drop s_j |>.take (s_{j+1} − s_j)) = some acc_{j+1}.reverse`, by
  `decide +kernel`. This is **equality**, exactly as in route E.
- **Chaining.** The segment results are combined by a new lemma `ballsRev_append`, which splits `ballsRev` over
  `ops₁ ++ ops₂` by `Option.bind`. The result is `Slp.ballsP … = some acc_m`. That is pure computation, with no
  `Encloses`. The soundness of the whole pass is then the landed one: `ballsSpec_sound` is stated for an arbitrary
  starting `acc` with `BallRel V acc`.
- **Why route E's objection does not apply.** The SO-COMPOSE-SPLIT audit judged route E's chaining sound. It
  failed the study on evidence: the probe P11 did not force the heavy product, and the memory calibration was
  invalid. Here the ledger is tiny: 3158 balls × 3 rationals × ≤ 128 bits ≈ 0.15 MB per checkpoint, against
  110–250 MB of models for compose. So no "ledger cost" question arises.
- **What still needs measuring.** The per-segment peak. My projection assumes the BALLDY memory is mostly
  retained slot balls, which grow with ops × P. One probe answers this (§6).
- **Consumers.**
  - `checkHamBounds`, `checkHamClaim`, `nonvanishingOn_of_balls` and every landed statement are unchanged.
  - New: `checkHamBoundsSeg`/`checkHamClaimSeg`, or simply the `_P` versions applied to a value that a
    `ballsP_eq_of_segments` theorem rewrites. The second way is cleaner: one new chaining theorem; the consumers
    see `Slp.ballsP`.
- **Size and audit.** 300–450 lines (plan type, segment check, `ballsRev_append`, `ballsP_eq_of_segments`, tests
  on T2/T3). Medium audit; the risk is concentrated in one lemma.

**Time.** R1's pass took 91 s. The lock pass is ≈ 3.6 × 91 s × (P/320) ≈ 2.2 min at P = 128, twice (base and
claim), so it is negligible in CPU-h. If lever 4 lands, the base pass may also use the sharp pass; `M` only feeds
`checkHamBounds`.

## 4. Lever 4: a sharper Ham pass

**The overestimate's mechanism** (LOCK-GEN-2 P2.2):
- sin 2πα becomes a disc of radius ≈ cosh around 0;
- X = √(I/(πΩ)) sin 2πα becomes a disc of radius ≈ 0.21;
- A = 4π(c + X) becomes a disc of radius ≈ 2.6;
- exp(±iA) becomes a ball of radius e^{2.6} ≈ 13.

On the actual domain, A is nearly real, so |exp(±iA)| ≤ e^{|Im A|}.

**My cross-check.**
- Inputs: |Im sin 2πα| ≤ sinh(2π ρ_H) = sinh(0.0957) ≈ 0.096. On I ∈ 0.0148 ± 0.0026, |Im √I| /|√I| ≤ 0.0026/(2 ×
  0.0122) ≈ 0.11.
- So |Im X| ≲ 0.21 × (0.096 + 0.11) ≈ 0.043, |Im A| ≲ 4π × 0.043 ≈ 0.55, and |exp(±iA)| ≲ 1.7 instead of 13.
- d2x carries the exp factor and up to three chain-rule factors in the root's I-derivatives. That is consistent
  with LOCK-GEN-2's 70–300× and its estimate of ≈ 2.5 decades (−18.40 → −15.94 at ρ = 1/140).

**Option 4a (recommended): strip/box shapes.** This is a new pass `ballsBox`, modelled on `ballsTrig`
(CertificateSharp/Ham/BallsTrig.lean, 408 lines, cosh shapes for χ_k + χ_{−k}).
- **The shape.** Each slot also carries rational bounds |Re v| ≤ a and |Im v| ≤ b on the domain.
- **Rules:**
  - real constants and `pi`: b = 0;
  - trig pairs (from the `ballsTrig` shape): |Re| ≤ c·cosh, |Im| ≤ c·sinh(2πρ_H|k|₁);
  - actions: from centre ± radius;
  - add: componentwise;
  - mul: |Re uv| ≤ a_u a_v + b_u b_v and |Im uv| ≤ a_u b_v + b_u a_v;
  - inv: via the ball (unchanged);
  - **sqrt** with Re w ≥ ℓ > 0 (the operand's ball): |Im √w| ≤ b_w/(2√ℓ);
  - **exp**: |exp w| ≤ e^{a_w}, where a_w bounds Re w. That is the whole gain, since exp(±iA) has Re = ∓Im A.
- **The ball.** Each slot's ball is replaced by the box's circumscribed disc whenever that is smaller, so the
  output type is still that of `Slp.balls`.
- **Statements.** New names only:
  - `ballsBox`, `val_mem_ballsBox`, `invGood_of_ballsBox`, `sqrtGood_of_ballsBox`;
  - `checkHamBoundsBox(Split)` and its `_sound`;
  - `hamFacts_of_box`, the analogue of `hamFacts_of_trigSplit` (V2/HamTrig.lean:28);
  - a route `routeARefinedBox`, which is `routeARefined` with `checkHamClaim` replaced, through
    `refinedCore_sound` unchanged.
- **Module.** It needs its own module, for the same reason `HamTrig.lean` does (the `expLoQ` name clash noted in
  V2/HamClaim.lean).
- **No landed statement changes.**
- **Composition with levers 2 and 3.** `ballsBox` is given the P parameter and the `_append` lemma from the start,
  so one pass covers all three levers. Its kernel memory is ≈ 1.5–2× the disc pass's, because each slot carries
  4 more rationals. That is affordable with segmentation (8 segments at P = 128: ≈ 4.5 GB by the §3 model).
- **Size.** 600–900 lines over 2–3 files, plus tests: toy agreement as in `toyCert2_trig_eq`, and a
  `cos(sin …)`-type test where the box is strictly better.
- **Audit cost.** One codex audit, comparable to C3's cosh pass. Plan 1–2 rounds.
- **Gain** (LOCK-GEN-2):
  - the threshold rises ≈ 2.5 decades, to about 10^−15.6 at ρ = 1/100;
  - the support falls to about 75 × 15 (≈ 1.15k half-terms against 1.6k);
  - factors are ≈ 0.7×, and per product ≈ 0.6^{1.5…2} ≈ 0.35–0.5×;
  - cost ÷ 2–3.
  - A smaller CertFixed width becomes possible too (err 10^−16.6, rather than 9e-20 at 112 bits). That is worth
    another (96/112)^{1…2} ≈ 0.75–0.86.

**Option 4b (fallback): angle cells.**
- Cover the α-strip by cells, run one ball pass per cell, and take the max.
- The difficulty is that `certDomain` is a product of full strips, and `Slp.balls` bounds `char k` by
  w^{|k|₁}, which is cell-blind. A cell needs a new domain type and a new char-ball rule (centre
  e^{2πik·θ_c}, radius from the cell width), and `HamFacts` must be assembled as a max over a cover.
- It is still new names only, but larger (≈ 1000+ lines). The number of passes is multiplied by the cell count.
- It gains more than 4a only near the cut, which is not the binding effect here. Not recommended unless 4a falls
  short of 2 decades.

## 5. Lever 5: the one-sqrt lean `lockHamExpr`

**The form** (LOCK-GEN-2 owner item 1): ½Y² = (Ω/2π) I cos² 2πα, which removes Y's root.
- **Savings:** 1 sqrt, 1 inv, 20 of the 128 torsion-compose products. That is ≈ 7 % of the ≈ 300 products, and
  the Ham claims change by 2 %.
- **Status:** `lockHamExpr` is **not landed** (no `.lean` in KAM/ mentions it). So this changes a design statement
  only; it is an owner-review item.

**Eval identity.** The lean expression agrees with soRotHC ∘ lockToRotC exactly where sqrtE(w)² = w, that is off
the nonpositive real axis of IΩ/π. The statement becomes `lockHamExpr_eval (hI : 0 < (z.2 0).re)`, or the weaker
"not a nonpositive real".

**Every consumer of `lockHamExpr_eval`** (from SO-LOCK-DESIGN §3, §4.2, §6; nothing in landed code):

| consumer | where eval is used | still valid? |
|---|---|---|
| `lockHamExpr_clock` (hΩ, Re I > 0) | fderiv at z with Re I > 0. That is a local statement, and the identity holds on the open set {Re I > 0} | yes |
| `lockBarrier_of_certV2` (`hham` tie) | `CertifiedTorus` gives the torus of `c.ham.eval` inside `certDomain`. Its I-disc is 0.01480 ± 0.00261, so Re I ≥ 0.0122 > 0 on all of it | yes, given `certDomain ⊆ {Re I > 0}`, which follows from the certificate's centre and radius (a new decidable premise, or read off `checkStatic`) |
| real transport (`lockToRotC_ofReal`, I > 0) | real points of the torus with I > 0 | yes |
| safety (`nonvanishingOn_of_program_good`, `SlpSqrtGood`) | does not use eval | unaffected; one sqrt fewer to check |
| `checkHamBounds_sound` / `ham_structural` | holomorphy of `HamExpr.eval` on the domain, not the identity | unaffected |

**Verdict:** safe. Every consumer evaluates on Re I > 0. The cost is one hypothesis on one unlanded theorem, plus
the domain-positivity side condition in the barrier glue, which the design already needs for `SlpSqrtGood`.

## 6. Lever 6, the per-theorem cap, and the calibration probe

**Packed products (lever 6).**
- After SO-PACKFIX, a blockRows-32 shard of 12 block pairs at w ≈ 659 bits took 4.6 GB. R2 at ≤ 4 pairs and 208
  bits took ≲ 1.5 GB (SO-V2PKG §4.4).
- Lock factors are ≈ 6.5× the terms at ≈ 240 bits, so a shard has 6.5× more block pairs at the same blockRows.
- The emitter chooses blockRows so that each shard keeps ≤ 8 pairs. That gives ≈ 2.5–3.5 GB per shard by the
  SO-V2PKG model, with more shard theorems and the same total.
- No checker change. This is the SO-DATA3 practice: one theorem per shard, each alone under `MemoryMax=10G`.

**Other near-cap theorems.**
- SO-DATA3's δ₁ bite (l = 12) passed at 8.36 GB. The lock uses the upper torus's box, Diophantine data and sites
  (LOCK-GEN-2 P2.3), so the **same bite theorems can be reused verbatim** if the box literal is identical (κ = 1).
  Otherwise use d0b.
- The compose chain must stay out of any single theorem. Per-product shard theorems plus the advice books (not yet
  emitted: LOCK-GEN-2) give this. Without advice, the products fall back to the direct route inside one
  declaration, which will not fit. **Advice emission is therefore a prerequisite**, not an optimisation.

**Calibration probe** (before lever 4 is commissioned):
1. one heavy lock compose product (U-model × exp witness) as a single shard at the chosen blockRows, alone under
   the cap: time and peak;
2. a 400-op segment of the lock Ham program through `ballStepG` at P = 128 and P = 320 (`decide +kernel` on a
   `#eval`-generated literal prefix), to check memory ∝ ops × P.

These fix the exponents in "per product ∝ size^{1.5…2} × width^{1…2}". The uncertainty in that exponent is most
of the spread in 12–100 CPU-h.

## 7. Totals and the recommended combination

**Projection** (LOCK-GEN-2's packed part × the factors above; the Ham passes and bites are minutes):

| combination | packed CPU-h | max theorem (projected) | landed statements |
|---|---:|---:|---|
| as is (no pruning, monolithic Ham pass) | ≈ 40–400 | Ham pass ≈ 25 GB: **fails** | — |
| 1 + 6 + shared frame proofs | 12–100 → **7–55** | Ham pass ≈ 25 GB: fails | none |
| + 2 + 3 (P 128, 4–8 segments) | 7–55 | ≈ 5 GB (Ham), ≈ 3.5 GB (shards), 8.4 GB (reused bite) | none |
| + 5 (lean form) | 6.5–51 | same | none (design statement) |
| **+ 4a (box pass, 75 × 15, CertFixed 96)** | **≈ 2–20** | ≈ 4.5 GB (Ham box, 8 segments) | none |

**Recommendation.**
1. **Now, cheap and mandatory:**
   - lever 1 (`sharedBaseV2`, `routeAV2P`, pruned torsion and frame) with shared frame-majorant proofs;
   - lever 6 (blockRows chosen at emission);
   - advice-book emission.
2. **Now, cheap; closes the cap risk:**
   - levers 2 + 3 as **one** package (`Slp.ballsP`, `ballsRev_append`, `ballsP_eq_of_segments`) at P = 128 with
     8 segments.
   - It is also the right base for 4a, which should be written generic in P and segmentable from the start.
3. **Owner ruling:** lever 5. It is safe by §5 and adopted unless the owner prefers to keep the all-z eval.
4. **Calibration probe** (§6).
   - If it puts 1 + 2 + 3 + 5 at ≤ 20 CPU-h, i.e. at the bottom of the range, stop there.
   - Otherwise commission **4a**. It is the only lever that moves the total by a factor and not by percentages, and
     it is the only way to the ≤ 20 CPU-h target across most of the projected range.
5. **Do not** pursue angle cells (4b) or route-E model checkpoints for compose: the shard layout already bounds the
   compose memory.

**Landed-statement impact of the whole recommendation: none.**
- Every checker change adds new declarations (`*P`, `*Seg`, `*Box`, `sharedBaseV2`, `routeAV2P`,
  `routeARefinedBox`).
- `TorusCertificate`, `Slp.balls`, `checkHamBounds`, `landedBase`, `routeAV2` and SO-DATA3's R2 path are
  untouched.
- The only statements that change are unlanded design ones:
  - `lockBarrier_of_certV2` names the new base and route;
  - `lockHamExpr_eval` gains `0 < Re I` under lever 5.
- **Existing exception, not a new one:** the SO-LOCK-DESIGN Q8 exception (`nonvanishingOn_of_program_good`)
  stands as before. The new passes add their own `nonvanishingOn_of_ballsP`/`_ballsBox`.

## 8. Uncertainties

- The memory model in §3 (linear in ops × P above a 2.6 GB base) is an assumption. BALLDY measured a single point.
  Probe 2 settles it.
- The cost exponents (§6, probe 1). With the worst exponents the recommended total is ≈ 20 CPU-h, at the target;
  with the best it is ≈ 2.
- The gain of the box pass rests on LOCK-GEN-2's sampled true sup (ρ = 1/140) and my arithmetic in §4, not on a box
  mirror. A Python mirror of `ballsBox`, about 150 lines extending `lock_balls.py`, should precede the Lean work.
- Reusing the bites needs the lock box literal to equal SO-DATA3's upper box exactly.
