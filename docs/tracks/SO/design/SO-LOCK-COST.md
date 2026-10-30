# SO-LOCK-COST: pricing the kernel levers for the N = 65 lock certificate (design note, rev 3)

**Status:** 30 October 2026, branch `inp-lockdesign`. Design note: no Lean, no proofs, no data, no reruns. Rev 2
answers review 1 (§9); rev 3 answers review 2 (§10). Sources: LOCK-GEN-2 (`inp-lockgen2` handoff,
`LOCK-GEN-NUMERICS.md` §Part 2); SO-V2PKG §4.4; SO-BALLDY handoff §5–7; SO-KDEPTH handoff; SO-DATA3 interim 2;
SO-COMPOSE-SPLIT and its audit 1. Every figure is a **measured receipt** (cited), a **range** with its stated
assumption, or unknown.

## 0. Verdict

**The existing measurements do not support either target** ("every theorem < 10 GB", "total ≤ 20 CPU-h") for
the lock certificate.
- **Memory.** BALLDY's breakdown (§1) shows that the jet program, not the balls, dominates Ham-pass memory: forcing the compiled 887-operation program alone costs 6.9 GB, and the lock program has 3158 operations. Ball-side levers (precision, segments, box pass) cannot fix a cost that sits in `HamExpr.jet`.
- **Time.** The single-counted packed bill is 13–118 CPU-h (§3). The best lever stack gives about 3–47 CPU-h, and several components are unquantified.

So **a calibration gate (§7)** decides. Its probe files are written; the total is decided only once every bill row is measured. The levers
(§2–§6) are priced as options, and the gate chooses among them. The architecture claim of rev 1 stands (review 1
§7): every lever is additive under **new names**, with no landed statement change.

## 1. Measured receipts

| receipt | value | source |
|---|---|---|
| R1/R2 Ham program | 887 ops: 204 const, 3 action, 14 char, 180 add, 486 mul, **0 exp, 0 inv, 0 sqrt** | BALLDY §5 (`P0`) |
| program spine only (`K0`) | 54 s, 3.9 GB | BALLDY §5 |
| every op forced, no balls (`J0`) | 59 s, **6.9 GB** | BALLDY §5 |
| `J0` + `revGet` lookups (`Lk`) | 65 s, 7.46 GB | BALLDY §5 |
| full rounded `checkHamBounds` (P = 320) | 91 s, **8.98 GB** | BALLDY §5 |
| lock Ham program | 3158 ops: 4 sqrt, 8 inv (4 `inv π`), 4 exp | LOCK-GEN-2 P2.1 |
| R2 packed part, landed sub-checks | 0.3–0.9 CPU-h per torus (model, not measurement) | SO-V2PKG §4.4 |
| R2 frame-majorant duplicate | **+**0.3–0.8 CPU-h per torus (model) | SO-V2PKG §4.4 |
| packed shard (SO-PACKFIX, blockRows 32, 12 pairs, w ≈ 659) | 235 s, 4.6 GB; literal data alone 190 s, 1.0 GB | OVERNIGHT 11:19 |
| δ₁ bite (l = 12) | 2:03, 8.36 GB | SO-DATA3 interim 2 |
| lock products after pruning | ≈ 300 (106 torsion + 17 Gram + 157 compose + ≈ 20 witnesses) against R2's 129; factors ≈ 6.5× | LOCK-GEN-2 P2.6 |

**BALLDY breakdown, by subtraction:** spine 3.9 GB (with the certificate import); program forcing +3.0 GB; lookups +0.56 GB; ball arithmetic and rounding at P = 320 about +1.5 GB.

Only the last part depends on P. **Rev 1's model (all of 6.4 GB ∝ ops × P) is withdrawn.**

## 2. Per-theorem memory

**The lock Ham pass.** Each lock range follows from the assumption in its row:
| part | R2 (measured) | lock, assumption | lock range |
|---|---:|---|---:|
| spine + import | 3.9 GB | between constant and ∝ ops (×3.56) | 3.9–13.9 GB |
| program forcing | 3.0 GB | ∝ ops (×3.56); exp/inv/sqrt compilers unmeasured | ≈ 10.7 GB or more |
| lookups | 0.56 GB | ∝ ops × depth (O(slot) list) | 2–7 GB |
| balls at P | 1.5 GB at 320 | ∝ ops × P | 5.3 GB (320), 2.1 GB (128) |

**Program forcing plus the spine already exceeds 10 GB at the low end of these ranges.** So:
- no ball-side lever can guarantee the cap while a theorem forces `c.ham.jet`;
- the same holds for **every** consumer that reduces `c.ham.jet`: both Ham passes, invariance/energy and torsion composition, and the frame majorants.

**Lever 0 (new, necessary): a literal jet bridge.**
- **The bridge.** Emit the compiled program as a literal `lockJetLit : HamJet`. Prove **one** bridge theorem `lockHamExpr_jet : (lockHamExpr Ω cs).jet = lockJetLit`.
- **New checker names** that take the jet as an argument: `checkHamBoundsJ c J`, `checkInvEnSharedJ`, `torsionModelsJ`, and so on. Their soundness holds under `hJ : c.ham.jet = J`, so the sub-check theorems reduce over literal ops only.
- **Statements:** new names only; the landed checkers are untouched.
- **Risk:** the bridge theorem itself forces the compiler (the lock analogue of `J0`, projected over 10 GB).
- **Contingency, gated by G1:** segment it by jet component (`v0`, `d1`, `d2`, `d3` are separate lists in `HamJet`, Expr/Slp.lean:66) or by top-level summand. This is plausible but **unproven**.
- **Price:** 150–300 lines plus the bridge data; a medium audit (one `hJ`-rewrite per consumer).

**Lever 2: Ham-pass precision P.**
- **Soundness.** `ballStepG`/`ballStepG_sound` (Ball.lean:167, 353) and `ballRound_mem` are generic in P. New `Slp.ballsP P` with a **new generic soundness induction** `ballsSpecP_sound`. The landed `ballsSpec_sound` is fixed at 320 and is *not* reused at P ≠ 320. Compatibility lemma `ballsP_320 : Slp.ballsP 320 = Slp.balls`, by unfolding.
- **Where P lives:** as a parameter of a new base instance (`sharedBaseV2 P …`), not as a `TorusCertificate` field.
- **Gain:** the ball line only, about 1.5 → 0.6 GB at R2 scale and 128 bits.
- **Caveat:** soundness holds at every P, but claim passing does not. Cancellation and the exp/inv/sqrt margins must be checked by the mirror at the chosen P.
- **Price:** 100–200 lines; a small audit.

**Lever 3: segmented ball pass with exact checkpoints.**
- **Chaining.** Equality checkpoints, `F(k, A, u ++ v) = F(k, A, u).bind (F(k + |u|, ·, v))` (review 1 §5), with: acc₀ = [] and |acc_j| = s_j; absolute slot numbers; an exact tiling, with explicit length and endpoint checks.
- **Conclusion and safety.** The chain concludes `Slp.ballsP … = some acc_m`. Safety (inverse exclusion, sqrt positivity) is read off the final balls by the generic-P safety lemmas.
- **Where the plan lives.** `BaseChecker.check` sees only `c`, so the plan and checkpoints are a **parameter of the new base instance**, or are consumed by a separate equality bridge.
- **Limits.** Every boundary carries all earlier balls, so the state stays about 3158 long. The memory gain is in the forced-op and arithmetic part only, and only on top of lever 0 (literal ops). Rev 1's 0.15 MB checkpoint figure was raw mantissas, not Lean term memory; it is withdrawn.
- **Widening variant.** A containment variant would be a different checker, with its own semantic and safety soundness. It does not give `ballsP_eq_of_segments`. Not proposed.
- **Price:** 300–450 lines; a medium audit.

**Packed shards (lever 6).**
- blockRows bounds one integer-product shard theorem: SO-PACKFIX measured 4.6 GB at 12 pairs.
- It does **not** bound the consumer theorems (compose, Gram, torsion, frame), which build slot models, norms, truncations and radii (Torsion/Models.lean:152–177, Frame/Majorants.lean:130–175). Rev 1's "shards bound compose memory" is withdrawn.
- Model-level stage subdivision (SO-COMPOSE-SPLIT route E; its chaining was audited sound) stays **a contingency**, gated by G3.

**Advice (correction).**
- Missing advice for nonconstant factors returns `none` (Model/Ops.lean:83–94). `CertModel.mul` then gives a zero polynomial with a coarse sound radius (:114–116); there is no direct fallback unless `.direct` is explicit.
- Advice is needed for tight margins.
- LOCK-GEN-2's handoff repeats rev 1's wrong description; this is reported as an in-repo inaccuracy.

**Bites.** SO-DATA3's site theorems (8.36 GB) can be reused only if the lock's box, Diophantine and site literals
equal SO-DATA3's upper ones exactly. Otherwise they are re-run near the cap, or the route falls back to d0b.

## 3. CPU bill of materials (each pass counted once)

**Per-product factor.** In the LOCK-GEN-2 model (cost ∝ size^{1.5…2} × width^{1…2}, with size 6.5× and width
240/208), the review's arithmetic gives **19.1–56.3× R2**. With 300/129 = 2.33× the products, the packed part is
44–131× R2's.
| item | basis | range |
|---|---|---:|
| B1 packed products (pruned; torsion, Gram, compose, witnesses) | (0.3–0.9 CPU-h) × 44–131 | **13–118 CPU-h** |
| B2 frame-majorant duplicate | unshared: (0.3–0.8) × 44–131; **0** if the frame theorem cites B1's shard equations (the remaining model and norm work goes to B5) | 0 or 13–105 |
| B3 Ham passes | 2 passes; lock time unknown (R2: 91 s each, no exp/inv/sqrt) | unknown; likely < 1 CPU-h |
| B4 literal baseline | R1: 190 s per shard declaration (OVERNIGHT 11:19) × shard count (R2: 667–718 per torus; lock unknown, larger) | **possibly dominant**: 1000 shards × 190 s = 53 CPU-h; amortised if several shards share a module |
| B5 consumer theorems (compose, Gram, torsion, frame, assembly) | not measured | unknown |
| B6 bites, advice generation, graph/SOS | bites ≈ 140 s if re-run; the rest unmeasured | unknown |

**Sharing.** B2 = 0 is the *only* sharing credit. B1 is not discounted, so rev 1's step from 12–100 to 7–55 is
withdrawn.

**Levers on B1** (all **unverified** multiplicative estimates): one-sqrt form × 0.93 (product census); box pass (§4) ÷ 2–3 (LOCK-GEN-2 estimate at ρ = 1/140; no mirror); CertFixed 112 → 96 × (96/112)^{1…2} = 0.73–0.86, conditional on the box pass's threshold.

**Total.** With all levers, B1 ∈ **3.0–47 CPU-h**. ≤ 20 CPU-h therefore holds only in the lower part of that range,
before B4–B6. **≤ 20 CPU-h is a conditional goal, not a projection**, and gate probes G3/G4 decide it.

## 4. Lever 4: a sharper Ham pass with box shapes (research lever)

**Rules.**
- Each slot also carries |Re v| ≤ a and |Im v| ≤ b; exp: |exp w| ≤ e^{a_w}.
- sqrt with Re w ≥ ℓ > 0: |Im √w| ≤ b_w/(2√ℓ). This is sound (review 1 §7); the rational bound needs a certified *lower* approximation of √ℓ.
- mul and add: interval rules. The ball is kept, or replaced by the box's circumscribed disc when that is smaller, so containment is preserved.

**Names and size.**
- New names only: `ballsBox`, `val_mem_ballsBox`, the safety lemmas, `checkHamClaimBox`, `hamFacts_of_box` and `routeARefinedBox`. `refinedCore_sound` is unchanged.
- 600–900 lines and a C3-sized audit. Written generic in P and on literal jets (lever 0).

**The gain is not established.**
- My |exp(±iA)| ≲ 1.7 (rev 1) and LOCK-GEN-2's 2.5 decades both use sampled suprema at ρ = 1/140; the package uses ρ = 1/100.
- Certified box claims can be looser than samples.
- The frame claims must be recomputed: SO-DATA3 found sampled frame claims too small.

**Prerequisite.** A Python `ballsBox` mirror (extending `lock_balls.py`; exact rationals; the same rules) reporting
the certified dh, dx, d2x and d2h, and from them the threshold, support and B1 factor. No Lean before that.

## 5. Lever 5: the one-sqrt lean `lockHamExpr` (corrected contract)

½Y² = (Ω/2π) I cos² 2πα saves 1 sqrt, 1 inv and 20 of the 128 torsion-compose products. `lockHamExpr` is unlanded,
so this changes a design contract only (an owner item).

**The eval contract needs both conditions.**
- The identity needs sqrtE(IΩ/π)² = IΩ/π. `hI` alone is false: at Ω = −1, I = 1, sqrtE(−1/π) = 0, but the lean term is −1/(2π) (review 1 §3).
- New contract: `lockHamExpr_eval (hΩ : 0 < Ω) (hI : 0 < (z.2 0).re) : (lockHamExpr Ω cs).eval z = soRotHC (lockToRotC Ω cs z)`. A more general version would assume "IΩ/π in the slit plane".
| consumer | requirement | disposition |
|---|---|---|
| `lockHamExpr_clock` (hΩ) | equality on the **open** set {Re I > 0}, a neighbourhood of z, so that the fderivs agree | safe; it has hΩ and needs Re I > 0 |
| `lockToRotC_ofReal`, real transport | Ω > 0, I > 0 | safe; it does not use the eval identity |
| `lockBarrier_of_certV2` (`hham`) | eval on all of `certDomain` | needs a **new decidable check** `actionPosOk c := radius[0] < centre[0]` with its soundness, since `checkStatic` lacks it (Defs.lean:220–234); or a derivation from X's checked sqrt operand. The N = 65 data give exactly 0.01480 − 0.00261 = 0.01219 > 0, but that is data, not a premise |
| `checkHamBounds_sound`, `ham_structural`, safety | generic in `HamExpr.eval` | unaffected; X's sqrt and the inv still need certifying |

Repairable with no landed statement change. The cost is two premises on one unlanded theorem plus one new
decidable check.

## 6. Lever 1: pruned composition in V2

**Current state.**
- V2's `landedBase`/`trigBase`/`cornerBase` call the unpruned `checkInvariance`, `checkEnergy` and `checkTorsion` (`torsionModels` → `Slp.compose`, Models.lean:155).
- `checkFrameMajorants` calls `torsionModels` again (Majorants.lean:160).
- `Slp.composePruned_sound` (Kernel/Prune) is used only by v1's `checkInvEnShared`.
- B1 assumes pruning, so this lever is **mandatory**, not a saving.

**New names:** `torsionModelsPruned`, `checkTorsionPruned`, `checkFrameMajorantsP`, `sharedBaseV2`, `routeAV2P`,
each with the J-variant of lever 0.

**Glue:** a new Gram projection from the pruned torsion check (`checkGram_of_checkTorsion` takes the old Bool), and an adapted proof of the content of `checkTorsion_sound_of` for the new producer.

No landed statement changes. 250–400 lines; a mechanical audit.

## 7. Calibration gate (rev 3: concrete probe files, not yet run)

**Files** (scratch, cited by path; `G = /mnt/HC_Volume_106379410/kam-data/so-lock/gate/`):
- `GateLib.lean.inc`: shared prelude. It defines `lockJ := (lockHamExpr (8/65) cs).jet`, the **exact landed** LOCK-COORDS-C expression (`inp-lockcc` 8eafd7ec, `KAM/SpinOrbit/Lock/Coords/HamExpr.lean`; no proxy), with the ball domain and Bool observers `opBeq`/`opsBeq`/`jetBeq`/`ballsBeq` (no `DecidableEq SlpOp` is landed);
- `G0_emit.lean`: an elaborator-only generator. It writes the probe files below with chunked literals;
- `G1a_force.lean`: a BALLDY `J0` scout;
- `run_gate.sh`: `emit`, then `probe FILE [CAP]`. It runs in the built `inp-lockcc` worktree, with `LEAN_NUM_THREADS=1`, under the shared kernel lock and `MemoryMax=10G`, no swap, `nice -n 5`. It records **USER + SYS CPU** (`/usr/bin/time %U %S`), wall time, max RSS, exit code, cgroup `memory.peak` and `oom_kill` in `G/gate.log`.

**Measurement conventions.**
- Every figure is a **whole-module total** (imports, literals and the kernel check).
- The baseline is never added again: `G1lit` measures literals alone, only to split a total into data and check, never to add.
- One successful capped run is a receipt for that exact workload, not an upper bound for other workloads.

| probe | proposition (file) | measures | rule |
|---|---|---|---|
| G1a (scout) | `lockJ.prog.ops.all opOk = true` (`G1a`) | forcing the real program | informative only; authorises nothing |
| G1lit | `lockOpsLit.length == 3158` on the literal jet (`G1lit`) | literal elaboration of the jet data | input to the bill |
| **G1b bridge** | `jetBeq lockJ lockJetLit = true`: **all five** `HamJet` fields (`G1b_bridge`) | the bridge itself, compiler plus full comparison | peak < 9 GB: the bridge is one theorem (production: `= ` via a proved `jetBeq` soundness lemma, new name) |
| G1c fallback | `opsBeq` on **program** segments [0,800), [800,1600), [1600,2400), [2400,3158), and `v0`, `d1`, `d2`, `d3` separately (`G1c_*`) | per-component cost; each recompiles the shared `slpCompile` result | all < 9 GB: 8 component theorems plus a structural assembly (`List.take_append_drop`, `HamJet` fields; no reduction). **Any one ≥ 9 GB, or OOM: stop and report** (compiler segmentation is a redesign) |
| **G2 balls** | `ballsRev P 2 lockWH lockCentre lockRadius 30 s accIn segLit = some accOut` with literal checkpoints (`G2_P{P}_s{s}_L{L}`), for P ∈ {128, 320}, L ∈ {400, 800}, s = 0 (early) and s = 3158 − L (late): 8 files | per-segment peak versus P, L and position. **This includes sqrt** (`ballStep` sqrt arm on `inp-lockcc`) | L* = the largest L with **both** positions < 9 GB at the chosen P; if late L = 400 at P = 128 is ≥ 9 GB, stop and report. If G0 prints "balls fail", P is too low for the claims: record it and use 320 |
| G3 shard + consumer | **blocked**: needs LOCK-DATA's emitted models and advice (not yet emitted) | a shard equation; the composition, Gram, torsion and frame consumers forced to full output | each consumer < 9 GB; otherwise route-E stage subdivision, then re-probe; a failure of that re-probe ⇒ report |
| G4 literal shard module | **blocked** as G3 | per-module totals for the actual grouping k | input to the bill |

**G2 domain literals.** Rounded outward from LOCK-GEN-2 P2.2: ρ_H 1523/100000, w 1101/1000, centre (37/2500,
49986/100000), radius (2615/1000000, 109/100000), taylorN 30. The checkpoints are computed by `ballsRev` at the
same P, so the segment theorem checks exactly the computation the chain would.

**Post-gate bill.** Sum of whole-module CPU totals; every item counted once:

| item | source | status after G1–G2 |
|---|---|---|
| bridge (G1b, or Σ G1c + assembly) | measured | measured |
| Ham passes: base + claim, each Σ over ⌈3158/L*⌉ segment modules | G2 per-segment × count | extrapolated from 2 positions: middle segments unmeasured |
| packed shard modules | Σ over the emitted inventory (counts by width/shape class), each class measured once | **unmeasured** (needs LOCK-DATA) |
| consumers (compose, Gram, torsion, frame, assembly) | G3 | **unmeasured** |
| bites (reuse or re-run), advice generation (Python CPU), graph/SOS | SO-DATA3 receipts if reused | **unmeasured** for the lock |

**Decision rule.**
- **Per-theorem cap:** apply the listed remedy first; a remedy whose own probe fails ⇒ report to the owner.
- **Total:** decided **only when every bill row is measured**. Any unmeasured row ⇒ defer; there is no ≤ 20 claim. Once every row is measured: ≤ 20 CPU-h: levers 0, 1, 2, 3, 5; 20–60 CPU-h: build the `ballsBox` mirror, and commission lever 4 if it projects ≤ 20; > 60 CPU-h: owner ruling (budget, d0b, ρ).
- **Now runnable:** G1a, G1lit, G1b, G1c and G2. They only require `run_gate.sh emit`.
- **Blocking follow-ups:** G3 and G4, after LOCK-DATA emits.

## 8. Recommendation

1. **Run G1–G2 now** (files ready; no checker change). G3–G4 follow LOCK-DATA's emission and are blocking.
2. **Mandatory regardless:** lever 1 (pruned V2 base and frame; B2 = 0 by shard reuse); lever 0 (literal jet bridge and the J-variants); advice emission; blockRows from G3.
3. **Then** levers 2 + 3 as one package, with parameters from G2, and lever 5 (owner ruling; corrected contract).
4. **Lever 4 only through the §7 rule**, after its mirror.

**Landed-statement impact: none.** Every checker change is a new declaration. Changed unlanded design contracts:
- `lockBarrier_of_certV2` names the new base and route, and gains `actionPosOk` under lever 5;
- `lockHamExpr_eval` gains hΩ and hI under lever 5;
- new `lockHamExpr_jet` (lever 0).

The SO-LOCK-DESIGN Q8 exception is unchanged and not extended.

## 9. Response to review 1

| finding | response |
|---|---|
| 1 HIGH: memory premise contradicts BALLDY's breakdown; segments + P are no guarantee | §1 now uses the breakdown; the rev 1 model is withdrawn. §2 shows program forcing dominates and projects over 10 GB. New **lever 0** (literal jet bridge, its own risk gated by G1). Segments are scoped to literal ops, with a state length of about 3158. The cap claim is withdrawn in favour of G1/G2 (early **and** late segments, P = 128 and 320, full forcing) |
| 2 HIGH: sharing discounted twice; omissions | §3 is a non-overlapping bill. B1 = 13–118 (corrected to 19.1–56.3× per product). The only sharing credit is B2 = 0. B4–B6 are unknown or possibly dominant. ≤ 20 h is a conditional goal, decided by §7 |
| 3 HIGH: one-sqrt eval needs Ω | §5: hΩ ∧ hI (counterexample cited); the clock uses the open-set argument; new decidable `actionPosOk`, since `checkStatic` lacks it; the exact rational 0.01219 |
| 4 MEDIUM: shards don't bound consumers; advice misstated | §2: shards do not bound consumer memory; route E is a contingency (G3 forces full outputs). Advice behaviour corrected (`none` → zero polynomial and coarse radius; `.direct` only when explicit); LOCK-GEN-2's handoff inaccuracy reported |
| 5 NOTE: exact-chain contract; `ballsSpec_sound` is 320-only; widening differs | §2 lever 3: exact-equality conditions listed; new `ballsSpecP_sound`; plan as a base-instance parameter; widening named and not proposed; the 0.15 MB claim withdrawn |
| 6 NOTE: precision sound; accuracy and linearity unproven | §2 lever 2: `ballsP_320` compatibility lemma; P not in `TorusCertificate`; accuracy caveat; BALLDY's 887 ops have no exp/inv/sqrt, so linearity is not assumed (G2 measures it) |
| 7 PASS: additive architecture | Kept; the Gram-projection and `checkTorsion_sound_of` glue is noted in §6 |

## 10. Response to review 2

| finding | response |
|---|---|
| 1 HIGH: invalid proxy; G1 does not measure the bridge; fallback omits `prog` | No proxy: the probes use the **landed** `lockHamExpr` (`inp-lockcc`, with the sqrt arm). G1a (the `opOk` observer) is a scout only. **G1b** forces the full five-field comparison against the literal jet. G1c **includes the program** in four segments, plus v0/d1/d2/d3 and a structural assembly; any component ≥ 9 GB ⇒ stop. Files: `G/G0_emit.lean`, `G/GateLib.lean.inc` |
| 2 HIGH: G2–G4 underdetermined; baseline double count; units; unmeasured items | G2: 8 concrete files (P, L, early and late endpoints), real checkpoints, sqrt included; explicit L* rule. Accounting: whole-module totals only, `G1lit` never added. Units: USER + SYS CPU, `memory.peak`, `oom_kill`, `LEAN_NUM_THREADS=1`. Bill rows flagged measured/unmeasured; unmeasured ⇒ defer. Precedence: remedy first, then report. G3/G4 are explicit blocking follow-ups on LOCK-DATA |
| 3–7 (closed or passed) | Unchanged. The bridge's production form is `=` from `jetBeq` via a new soundness lemma, specialised to the N = 65 Ω and cs (review 2 §5) |
