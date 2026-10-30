# SO-LOCK-COST: pricing the kernel levers for the N = 65 lock certificate (design note, rev 4)

**Status:** 30 October 2026, branch `inp-lockdesign`. Design note: no Lean in KAM/, no proofs, and no probe has been run.
- **Review responses:** rev 2 answers review 1 (§9), rev 3 review 2 (§10), rev 4 review 3 (§11).
- **Coordination.** Rev 4 also applies the orchestrator's coordination note: **segmenting is SO-CSPLIT's
  deliverable** (`inp-socsplit2:docs/tracks/SO/design/SO-CSPLIT.md`, read-only), and its lock projection is the
  baseline bill.
- **Sources:**
  - LOCK-GEN-2 (`inp-lockgen2`: its handoff and `LOCK-GEN-NUMERICS.md` §Part 2);
  - SO-CSPLIT §0, §4.1, §5–7;
  - SO-V2PKG §4.4;
  - SO-BALLDY handoff §5–7;
  - SO-DATA3's receipts, as quoted by SO-CSPLIT §4.1.
- **Evidence classes.** Every figure is one of: a **measured receipt** (cited), a **range** with its assumption, or
  unknown.

## 0. Verdict

- **Baseline bill.** SO-CSPLIT's projection for the lock is **25–60 CPU-h** (unmeasured, wide error), with a
  **ledger of about 100–200 MB**. That is over the owner's 50 MB volume flag (SO-CSPLIT O2).
- **Targets.** Neither "≤ 20 CPU-h" nor "every theorem < 10 GB" is supported by measurement for the lock.
  - Below 20 CPU-h needs the levers of §4–§5, each unverified.
  - The per-theorem cap rests on SO-CSPLIT's mechanisms M0–M3 and on the probes of §7.
- **What this note now owns:**
  - the lock-specific levers: the sharper Ham pass, the one-sqrt variant and Ham-pass precision;
  - the lock's **bridge and Ham-pass calibration probes**, G1–G2, whose files are written but not run;
  - the list of what the gate must still measure.
- **What it does not own:** composition, Gram, torsion and frame segmentation are SO-CSPLIT's. Rev 3's
  `sharedBaseV2` (lever 1) is withdrawn in favour of SO-CSPLIT §3.1, which proves the landed Bools with no new
  `BaseChecker`.
- **Landed statements: none change.** Every new piece has a new name (§8). Since review 3, `lockHamExpr` and its
  all-z `lockHamExpr_eval` are **landed** (`KAM/SpinOrbit/Lock/Coords/HamExpr.lean`, two-root form). They stay
  untouched.

## 1. Measured receipts

| receipt | value | source |
|---|---|---|
| R1/R2 Ham program | 887 ops: 204 const, 3 action, 14 char, 180 add, 486 mul, 0 exp/inv/sqrt | BALLDY §5 |
| spine only (`K0`) / all ops forced (`J0`) / + lookups (`Lk`) | 3.9 GB, 54 s / **6.9 GB**, 59 s / 7.46 GB, 65 s | BALLDY §5 |
| full rounded `checkHamBounds` (P = 320) | 91 s, **8.98 GB** | BALLDY §5 |
| kernel memory law (forced results only) | peak ≈ 1.5 GB + (0.04–0.13 GB per kernel-second) × time | SO-CSPLIT §4.1 |
| one `mulN … [0,10]` product, forced | +62 s, +6.39 GB over its base | SO-DATA3 P1 (SO-CSPLIT §4.1) |
| one packed shard `= true` / all 7 shards | +3.5 s, +0.68 GB / +29 s, +3.28 GB | SO-DATA3 SH/RR |
| packed shard, production rate | 0.47 GB and 4.1 s per shard | SO-CSPLIT §4.1 |
| pruned energy (86 slots, 26 products) | OOM-killed at 10 GB within 1.5 min (859 k calls plus J0) | SO-DATA3, SO-CSPLIT §4.1 |
| δ₁ bite (l = 12) | 2:03, 8.36 GB | SO-DATA3 interim 2 |
| lock Ham program | 3158 ops (4 sqrt, 8 inv, 4 exp); ≈ 300 heavy products; factors ≈ 6.5× | LOCK-GEN-2 P2.1, P2.6 |
| lunar R2 under SO-CSPLIT | 3.0–4.3 CPU-h per torus; ledger 10–11 MB per torus (projection) | SO-CSPLIT §5–6 |

These are differences of separate workload peaks, not additive allocations.
- **Per product, not per op.** SO-DATA3's finding is that kernel cost goes by model × model product: a single
  forced product reached +6.39 GB. So the lock's 6.5× larger factors make **single-product splitting** (SO-CSPLIT M3,
  L1c/L1d) the expected case, not the exception.

## 2. Per-theorem memory: what is SO-CSPLIT's and what is the lock's

| component | owner | mechanism | lock status |
|---|---|---|---|
| jet bridge `lockJ = lockJetLit` | SO-CSPLIT M0 (shared `HamJet.beq`); calibrated here by G1 | monolithic, or split by program slices plus tables | J0 at 3158 ops projects above 10 GB, unmeasured (G1) |
| compose chains (invariance, energy, torsion), Gram, frames | SO-CSPLIT M1–M2 | route E ledger segments | projection only (SO-CSPLIT §7) |
| single products over the cap | SO-CSPLIT M3 (L1c shards, L1d staged linear ops) | memoised subterms | expected for most heavy products |
| Ham ball pass (`checkHamBounds`, `checkHamClaim`) | this note (G2), on literal ops | monolithic on `lockJetLit`, or segmented with SO-CSPLIT's tooling | ball state ≈ 3158 entries; unmeasured (G2) |
| bites | SO-DATA3 reuse if the literals are identical | — | otherwise re-run near the cap (8.36 GB) |

**Rev 2–3's Ham-pass segmentation (old lever 3).** This is now **SO-CSPLIT's tool**. The ball-pass analogue (exact
`ballsRev` checkpoints chained by `bind`; review 1 §5 contract) is an input request to SO-CSPLIT: the same plan,
checkpoint and assembly machinery, with balls in place of models. G2 supplies its calibration.

**Ham-pass precision P (lever 2).** This stays here: it is a parameter, not segmentation.
- `ballStepG`/`ballStepG_sound` and `ballRound_mem` are generic in P.
- New pieces: `Slp.ballsP`, a new `ballsSpecP_sound` (the landed `ballsSpec_sound` is 320-only), and the
  compatibility lemma `ballsP_320`.
- P lives as a parameter of the new consumer, not in `TorusCertificate`.
- **Acceptance needs claim passing at the chosen P** (G2claim), not just evaluator success.
- 100–200 lines; a small audit.

## 3. CPU bill (baseline: SO-CSPLIT §7, each item counted once)

| item | basis | range | status |
|---|---|---:|---|
| C1 compose, Gram, torsion, frames, single-product splits | SO-CSPLIT §7: ≈ 170 M kernel calls (≈ 2,300 theorems at B = 75 k), about 300 packed products | **25–60 CPU-h** (includes the packed shards and the fixed per-theorem cost) | projection |
| C2 jet bridge | SO-CSPLIT: ≈ 2 min for R2 | minutes to < 1 CPU-h | G1 |
| C3 Ham passes (base and claim) | R2: 2 × 91 s | likely < 1 CPU-h | G2 |
| C4 ledger and data modules | 100–200 MB literals; R2: < 0.1 h for 10 MB | ≈ 1–2 CPU-h, linear in volume (assumption) | unmeasured |
| C5 bites | SO-DATA3 reuse: 0; re-run: ≈ 140 s plus the cap risk | 0–0.1 CPU-h | conditional on literal identity |
| C6 generation (G0 emission, ledger generation, advice books) | Python and elaborator CPU | unknown | unmeasured |
| C7 graph/SOS, final assembly | — | unknown | unmeasured |

**Total.** About 26–64 CPU-h plus C6–C7 for the two-root form at the LOCK-GEN-2 package. **The ≤ 20 CPU-h target
is not met by the baseline**; it needs §4–§5:

| lever | factor on C1 | status |
|---|---|---|
| one-sqrt variant (§5) | × 0.93 (product census) | unverified |
| box Ham pass (§4): threshold to about 10^−15.6, support 90 × 18 → about 75 × 15, so ≈ 0.7× the terms | ÷ 2–3 on the products; also a smaller ledger (∝ terms) | LOCK-GEN-2 estimate at ρ = 1/140; no mirror |
| CertFixed 112 → 96 (after the box pass) | × (96/112)^{1…2} = 0.73–0.86 | conditional |

C1 with all levers: 25–60 × 0.93 ÷ (2–3) × 0.73–0.86 ≈ **5.7–24 CPU-h**. The ledger falls to about 70–140 MB, still
over the flag; SO-CSPLIT §5 options (i)–(iii) apply. So ≤ 20 CPU-h is **conditional**, on the box-pass mirror and
on SO-CSPLIT's calibration (its κ at lock factor sizes).

## 4. Lever 4: the sharper Ham pass with box shapes (research lever)

**Rules.**
- Each slot also carries |Re v| ≤ a and |Im v| ≤ b.
- exp: |exp w| ≤ e^{a_w}.
- sqrt with Re w ≥ ℓ > 0: |Im √w| ≤ b_w/(2√ℓ). This is sound (review 1 §7) and needs a certified *lower* bound
  for √ℓ.
- mul and add: interval rules. The ball is kept, or replaced by the box's circumscribed disc when that is smaller.

**Names and size.**
- New names only: `ballsBox`, `val_mem_ballsBox`, its safety lemmas, `checkHamClaimBox`, `hamFacts_of_box`,
  `routeARefinedBox`. `refinedCore_sound` is unchanged.
- 600–900 lines and a C3-sized audit. Written generic in P and on literal jets.

**The gain is not established.**
- My |exp(±iA)| ≲ 1.7 and LOCK-GEN-2's 2.5 decades use sampled suprema at ρ = 1/140, while the package uses
  ρ = 1/100.
- Certified claims can be looser than samples.
- The frame claims must be recomputed (SO-DATA3 found sampled frame claims too small).

**Prerequisite.** A Python `ballsBox` mirror (extending `lock_balls.py`, exact rationals) that reports the
certified claims, threshold, support and C1 factor. No Lean before that.

## 5. Lever 5: the one-sqrt variant, under NEW names (landed two-root form untouched)

- **Saving.** ½Y² = (Ω/2π) I cos² 2πα saves 1 sqrt, 1 inv and 20 of the 128 torsion-compose products.
- **Why new names.** The landed `lockHamExpr` (two roots) and its all-z
  `lockHamExpr_eval (Ω cs z) : (lockHamExpr Ω cs).eval z = soRotHC (lockToRotC Ω cs z)` cannot take the new body:
  at Ω = 1, I = −1 the values differ by −1/(2π) (review 3 §1). Adding premises would change a landed statement.
- **New declarations:**
  - `lockHamExprLean (Ω : ℚ) (cs : List ℚ) : HamExpr 2`;
  - `lockHamExprLean_eval (hΩ : 0 < Ω) (hI : 0 < (z.2 0).re) : (lockHamExprLean Ω cs).eval z = soRotHC (lockToRotC Ω cs z)`.
    Both premises are needed: at Ω = −1, I = 1 the identity fails (review 1 §3);
  - `lockHamExprLean_clock`.
  - The landed `lockHamExpr`, `lockHamExpr_eval` and `lockHamExpr_clock` stay as they are.
- **Consumers.**
  - Only the lean variant's certificate instance and glue use the new names.
  - The barrier glue needs a new decidable `actionPosOk c := radius[0] < centre[0]` with its soundness, because
    `checkStatic` does not check it. For N = 65, 0.01480 − 0.00261 = 0.01219 > 0 exactly, but that is data, not a
    premise.
  - `lockHamExprLean_clock` uses equality on the open set {Re I > 0}.
  - Safety still certifies X's sqrt and the inverses.
- **Owner item.** Selecting the lean variant means the jet literal, the bridge (G1) and every probe are re-emitted
  for `lockHamExprLean`. The current gate files target the **landed two-root** form.

## 6. Withdrawn or transferred

- **Rev 3 lever 1** (`sharedBaseV2`, pruned torsion and frame): withdrawn. SO-CSPLIT proves the landed Bools
  segment-wise with its own liveness planning (§3.1 there).
- **Rev 3 lever 3** (Ham-pass segments): transferred to SO-CSPLIT (§2).
- **Rev 1–2 shard-only memory bounds:** withdrawn. Consumers need SO-CSPLIT M1–M3.

## 7. Calibration gate for the lock's bridge and Ham pass (files written, not run)

**Files** (`G = /mnt/HC_Volume_106379410/kam-data/so-lock/gate/`, scratch):
- `GateLib.lean.inc`, the prelude:
  - `lockJ := (lockHamExpr (8/65) cs).jet`, the **landed** two-root form;
  - the domain literals: ρ_H 1523/100000, w 1101/1000, centre (37/2500, 49986/100000), radius (2615/1000000,
    109/100000), taylorN 30;
  - the Bool observers `opBeq`/`opsBeq`/`jetBeq`/`ballsBeq`.
- `G0_emit.lean`: the generator, elaborator only. It writes every probe file below and prints the elaborator's
  triage verdicts. Those verdicts are untrusted.
- `G1a_force.lean`: the J0 scout.
- `run_gate.sh`: the runner.
  - Adapted from SO-BALLDY's `run.sh`, whose original is kept as `G/balldy_run.sh.orig`, since `inp-soballdy`'s
    worktree is gone.
  - It runs in `/root/code/KAM-inp`, the built `inp` with `HamExpr.olean`. It **fails closed**: `set -eu`,
    `cd || exit 2`, an olean check, and it records `git rev-parse HEAD`.
  - It exits with the Lean rc.
  - `emit` also runs under the lock and the cap.
  - It records USER/SYS CPU, wall, max RSS, rc, cgroup `memory.peak` and `oom_kill` in `G/gate.log`. A missing
    peak is logged as **UNMEASURED**, never as 0.

**Conventions.**
- Whole-module CPU totals; literal baselines are never added again.
- One capped success is a receipt for that workload only, not a bound for any other.

| probe | proposition (generated file) | rule |
|---|---|---|
| G1a | `lockJ.prog.ops.all opOk = true` (`G1a`) | scout; authorises nothing |
| G1lit | `lockOpsLit.length == 3158` (`G1lit`) | diagnostic split of C2 |
| **G1b** | `jetBeq lockJ lockJetLit = true`: all five `HamJet` fields, with lengths (`G1b_bridge`) | peak < 9 GB: M0 is one theorem (production `=` via SO-CSPLIT's `HamJet.eq_of_beq`) |
| **G1c** | program slices [0,800), [800,1600), [1600,2400) bounded, and **the full tails** `opsBeq (lockJ.prog.ops.drop 2400) (lockOpsLit.drop 2400)` (lengths compared, so no unpaid tail; review 3 §2); plus `v0`, `d1`, `d2`, `d3` (`G1c_*`) | all < 9 GB: 8 theorems plus an assembly by `List.take_append_drop` and the field structure, and the assembly theorem is itself measured. Any one ≥ 9 GB: **stop and report** |
| **G2** | `ballsRev P 2 … s accIn segLit = some accOut`, literal checkpoints, P ∈ {128, 320}, L ∈ {400, 800}, s = 0 and s = 3158 − L (`G2_P*_s*_L*`, 8 files) | evaluator-success and segment-equality evidence **only**. L* = the largest L with both positions < 9 GB. "balls fail" from G0 is an **evaluator failure** (domain, enclosure or safety), not a precision verdict |
| **G2claim** | the **whole** pass at P on `lockJetLit`, then `hamClaimOk 4 lockJetLit r.reverse lockClaim` with LOCK-GEN-2's claim (dh 1.925, dx 140.4, d2x 35150, d2h 166) (`G2claim_P128`, `_P320`) | P is acceptable **only if** G0 prints `claims-pass` **and** the kernel probe proves it. `evaluator-fail` is distinct from `claims-fail`, and neither is presumed fixed at 320. Monolithic: if it is over the cap, run the claim check as SO-CSPLIT's final stage on a chained pass |

**Still unmeasured after G1–G2:**
- the middle ball segments and the full ball chain;
- every SO-CSPLIT item at lock sizes: its own CAL gate (G0–G7 there) re-run on lock data, giving κ at 6.5× factors,
  L1d splits and shard decode at lock widths;
- the ledger volume;
- the bites;
- generation CPU;
- graph/SOS and assembly.

These need LOCK-DATA's emission: models, advice books, `gramInv`/`torsInv`.

**Decision rule.**
- **Per theorem:** apply the listed remedy first; if the remedy's probe fails, report.
- **Total:** decided only when every row of §3 is measured; any unmeasured row means defer. Then:
  - ≤ 20 CPU-h: proceed;
  - 20–60 CPU-h: box mirror, then lever 4 if it projects ≤ 20;
  - > 60 CPU-h: owner ruling.
- **Ledger over 50 MB:** owner item O2 (SO-CSPLIT §5 options).

## 8. Recommendation

1. **Run G1 and G2 now** (`run_gate.sh emit`, then `probe`). They need no checker change and decide the bridge
   shape and the precision P.
2. **SO-CSPLIT** delivers M0–M3 and its CAL gate. This note asks it to:
   - re-run CAL on the lock's emitted data once LOCK-DATA emits;
   - carry the ball-pass checkpoint variant.
3. **Box-pass mirror** (Python) before any Lean for lever 4. It is the main lever toward ≤ 20 CPU-h and also
   shrinks the ledger.
4. **Owner rulings:**
   - lever 5 (new-name lean variant; it re-targets every emitted file);
   - O2 (ledger volume).

**Landed-statement impact: none.**
- New names: `lockJetLit` and its bridge, `Slp.ballsP` and its lemmas, the `ballsBox` family,
  `lockHamExprLean` and its eval and clock, and `actionPosOk`.
- `lockHamExpr`, `lockHamExpr_eval`, `lockHamExpr_clock`, `TorusCertificate`, the landed checkers and the V2
  interfaces are unchanged.
- The unlanded `lockBarrier_of_certV2` design names the selected expression.
- The SO-LOCK-DESIGN Q8 exception is unchanged.

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

## 11. Response to review 3 (and the coordination note)

| item | response |
|---|---|
| 1 HIGH: `lockHamExpr` and `lockHamExpr_eval` are landed; one-sqrt is not additive | §5: the one-sqrt form is `lockHamExprLean` with `lockHamExprLean_eval (hΩ) (hI)` and `_clock`, all **new names**; the landed two-root declarations are untouched. Selecting it re-emits the jet, the bridge and the probes. §0 and §8 reconciled |
| 2 HIGH: G1c has no tail or length | `G0_emit.lean`: the last program comparison is `opsBeq (lockJ.prog.ops.drop 2400) (lockOpsLit.drop 2400)` over the **entire** tails, with lengths compared. The assembly theorem is measured too |
| 3 MEDIUM: the runner points to a removed worktree | `G/run_gate.sh` is rewritten: `wt=/root/code/KAM-inp` (built `inp`), fail-closed `cd`, olean check, HEAD recorded, exit with the Lean rc, missing peak logged as UNMEASURED, `emit` under the lock and cap. The BALLDY original is kept as `G/balldy_run.sh.orig` |
| 4 MEDIUM: G2 does not check claims | New **G2claim** (whole pass, then `hamClaimOk` against LOCK-GEN-2's claim, at P = 128 and 320). G2 is relabelled evaluator and segment evidence only. `evaluator-fail` and `claims-fail` are distinguished, with no "use 320" presumption |
| 5–7 closed / accounting | Kept. The production bridge is `HamJet.eq_of_beq` (shared with SO-CSPLIT M0). Stale lines (lever 0's four fields; "G3/G4 decide it") removed |
| coordination: segmenting is SO-CSPLIT's | §2, §6: compose/Gram/torsion/frame and Ham-pass segmentation are transferred to SO-CSPLIT. `sharedBaseV2` is withdrawn. §3's baseline is SO-CSPLIT's lock projection: 25–60 CPU-h, 100–200 MB ledger over the 50 MB flag (O2). §1 adds SO-DATA3's per-product receipts (P1 +6.39 GB, SH/RR, the energy OOM). §7 lists what remains unmeasured |

## 12. Gate results (measured, 30 October 2026, 20:09–20:14 UTC)

**Setup.**
- Runner `G/run_gate.sh` in `/root/code/KAM-inp` at `7e8f8c02`, against the **landed** two-root `lockHamExpr`.
- One Lean process at a time, under the shared lock, `MemoryMax=10G`, `MemorySwapMax=0`, `LEAN_NUM_THREADS=1`.
- Raw logs: `G/gate.log`, `G/*.lean.out`, `G/run_all.log`, `G/run2.log`.
- CPU is USER + SYS. MEMPEAK is the cgroup's `memory.peak`; MAXRSS (from `time`) also counts shared, mmapped
  `.olean` pages that are charged elsewhere, which is why it can exceed the cap.

| probe | rc | CPU s | wall s | MEMPEAK | MAXRSS | outcome |
|---|---:|---:|---:|---:|---:|---|
| G0 emit (elaborator) | 0 | 7.6 | 8.6 | 495 MB | 3.4 GB | files written. **Landed program: 3116 ops** (not LOCK-GEN-2's 3158), v0 = 3115, \|d1\| = 4. Triage: G2claim P=320 `claims-pass`, P=128 `claims-pass` |
| G1asm (assembly: `split4` + `jet_ext` ⇒ `lockJ = lockJetLit` from the 8 component equalities) | 0 | 8.1 | 6.7 | 460 MB | 3.5 GB | **passes**. The first version failed on an elaborator recursion-depth limit (`show` unfolded the literal); it was fixed by the generic `jet_ext`, with no limit raised |
| G1a scout (`lockJ.prog.ops.all opOk`) | 1 | 27.4 | 27.6 | 2.9 GB | 6.0 GB | **kernel: deep recursion detected** |
| G1lit (`lockOpsLit.length == 3116`) | 0 | 9.4 | 8.0 | 660 MB | 3.7 GB | passes; the literal jet costs little |
| G1b bridge (`jetBeq lockJ lockJetLit`) | 1 | 30.6 | 29.2 | 3.0 GB | 6.1 GB | **kernel: deep recursion detected** |
| G1c_prog_0 (first 800 ops) | 1 | 32.5 | 31.2 | 3.0 GB | 6.1 GB | **kernel: deep recursion detected** |
| G1c_v0 / G1c_d1 | 1 | — | — | 3.0 / 2.9 GB | — | `decide` stuck reducing `lockJ.v0` / `lockJ.d1` (compiled result not reducible) |
| G1c_prog_800/1600/2400, G1c_d2/d3 | — | — | — | — | — | **not run**: each forces the same compiled `lockJ`, which fails above for even an 800-op prefix and the scalar `v0` |
| **G2claim P=320** (whole ball pass on `lockJetLit.prog.ops`, then `hamClaimOk 4 … lockClaim`) | 0 | 76.2 | 75.5 | **7.8 GB** | 11.0 GB | **kernel: claims pass**, one theorem |
| G2claim P=128 | — | — | — | — | — | not run: 7.8 GB of 10 GB is not "comfortably" under the cap (task rule) |
| G2 segments (8 files) | — | — | — | — | — | not run (not in this task's scope) |

**Decisions implied by §7.**
1. **G1 fails on kernel depth, not memory.** The landed jet compiler (`HamExpr.jet` via `slpCompile`) cannot be
   reduced by the kernel on the lock's expression: deep recursion after about 30 s at about 3 GB. R2's 887-op
   program reduced (BALLDY J0), so the depth limit lies between 887 and 3116 ops or comes from the sqrt/exp/inv
   compilers.
   - By §7's rule ("any one fails: stop and report"), the bridge M0, monolithic or split, **is not available** with
     the landed compiler.
   - The literal-jet route needs either a **KDEPTH-style depth fix of the jet compiler** (a body change with the
     statements kept, like SO-KDEPTH's `composeOps`), or a bridge assembled from per-subtree compilations. Both
     are a redesign, reported to the orchestrator and SO-CSPLIT, whose M0 shares this bridge.
   - No limit was raised (AGENTS rules 1 and 4).
2. **The Ham claim pass fits as one theorem at P = 320**, on the literal ops: 7.8 GB, 76 CPU-s, claims pass. So the
   ball-pass segments (G2) and precision lever 2 are **not needed** for memory.
   - **Caveat (cold page cache):** MAXRSS is 11 GB. If the `.olean` pages are not already cached and charged to
     another cgroup, this run's charge could approach the cap; repeat it once on a cold cache before relying on it.
   - It proves claims about `lockJetLit`, which become claims about `lockHamExpr` only through the bridge (item 1).
3. **Bill (§3):**
   - C2 (bridge) is **blocked**; C3 (Ham passes) is measured at about 2 × 76 CPU-s on literal ops.
   - Every other row remains unmeasured.
   - The total is deferred.

**Follow-up runs (20:17–20:20 UTC).** The runner now also logs the 1 s-sampled maxima of `memory.stat` anon, file
and file_mapped. The G1 work is on hold until SO-KDEPTH2 lands; G1a/b/c are its acceptance tests.

| probe | rc | CPU s | wall s | MEMPEAK | anon | file / file_mapped | MAXRSS | outcome |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| G2claim P=320 (repeat) | 0 | 72.5 | 71.4 | 7.8 GB | 7.6 GB | 5 / 5 MB | 11.0 GB | claims pass; identical to the first run |
| G2claim P=128 | 0 | 68.4 | 68.5 | 6.8 GB | 6.6 GB | 67 / 32 MB | 9.9 GB | **claims pass** |

**The 11 GB MAXRSS question.**
- The cgroup's charge is almost all **anon**, about 7.6 GB. The roughly 3.3 GB gap to MAXRSS is mmapped `.olean`
  pages already resident in the page cache and charged to the cgroups that first read them. Process RSS counts
  them; this cgroup's charge does not.
- I did not drop system caches (per the instruction), so a truly cold run was **not** produced. "Cold" here means
  the first run in this scope.
- On a fully cold cache those clean, file-backed pages would be charged to the probe. They are reclaimable under
  `memory.max`, though: the expected effect is re-reads, not an OOM, because only anon (7.6 GB) is unreclaimable
  with swap off. That is an inference, not a measurement.

**Decision.**
- The Ham claim pass is **one theorem**, at either precision. P = 128 saves about 1 GB (6.8 against 7.8 GB) and
  about 6 % CPU, and both pass the claims.
- Lever 2 (precision) is optional: it is worth about 1 GB of headroom, not a necessity.
- Bill row C3 (two Ham passes) is measured at about 2 × 70 CPU-s.
