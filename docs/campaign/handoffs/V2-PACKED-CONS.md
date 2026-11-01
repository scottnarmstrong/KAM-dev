# V2-PACKED-CONS handoff: the consumers of the packed jet and the packed base checker `jetBase`

Task: brief V2-PACKED-CONS (kamx-pk-cons, branch `v2-packed-cons`), design `V2-PACKED.md` §12.2 "The consumers".
Rules: additive only (new files under `KAM/CertificateSharp/Packed/`, `scripts/packed/cons_*`, this handoff, a new
§14 of the design); one Lean process at a time under a 4 GB cap; standard axioms.

## Result

- **The Lean is complete and sound, on the standard axioms.** `jetBase : BaseChecker` (the landed `checkStatic`,
  `checkHamBounds`, `checkEmbedding`, B2's packed Gram, and the three consumers of the packed jet) yields the landed
  `BaseFacts`, so `checkV2With_jetBase_sound` gives the landed `CertifiedTorus` for any engine. Each consumer's
  soundness has the conclusion of its landed counterpart under the landed hypotheses:
  - `checkTorsionJ_sound` ⇔ `checkTorsion_sound_of`;
  - `checkInvarianceJ_sound` ⇔ `checkInvariance_sound_of`;
  - `checkEnergyJ_sound` ⇔ `checkEnergy_sound_of`;
  - `checkFrameMajorantsRJ_sound` ⇔ `checkFrameMajorants_sound` (`FrameMajorants`), and `routeARefinedPackedJ`
    is route A refined on these frames.
- **No landed `Slp.compose` anywhere.** A reachability check over definition bodies (`nocompose.lean.txt` in the receipts; Checks)
  finds no `Slp.compose`, `torsionModels` or `gramCheck` below `checkTorsionJ`, `checkInvarianceJ`, `checkEnergyJ`,
  `checkFrameMajorantsRJ` or `refinedTestPackedJ`, and does find `Slp.compose` below B3b's `checkTorsionR`, §13's
  `checkFrameMajorantsR` and the landed `checkInvariance` (positive controls).
- **Modular interface (as briefed).** Each consumer's core lemma assumes the per-slot packed models (`JSlotsEnc`,
  verbatim the conclusion of kamx-packed's `jetPacked_sound`); the consumer's Boolean holds its jet check
  (`jetLowOk`, `jetFullOk` = `jetCheck` plus the checked box agreement), so its soundness discharges them with
  `jetPacked_sound`.
- **The gate passes on LG00 T′'s data** (lg00-app `8210d92e`), **on the mirror's nodes**: every consumer-side
  conjunct decides `true` in its own process, every control decides `false`, and every process stays under the 4 GB
  cap (largest 2.75 GB). The jet nodes are kamx-packed's untrusted Python mirror output, and the jet chain conjunct
  inside `jetLowOk`/`jetFullOk` (`jetCheck`) was not decided: that is kamx-packed's chain theorem. Only the box and
  scale guards of those two conjuncts are in the gate. Figures below (corrected by AUDIT-V2-PACKED-CONS-1 C2).

## What was built (Lean, `KAM/CertificateSharp/Packed/`, all new)

| module | lines | content |
|---|---:|---|
| `JetConsTors.lean` | 220 | `JSlots` (value, radius, norm bound of every program slot), `JSlotsEnc` (every slot of a list has a `PEnc` of its slot function: the conclusion of `jetPacked_sound`), `dxhSlot`, **`trAJ`** (`DX_H ∘ K` from the jet: entry `(a, b)` is `± ∂_{a'} ∂_b H ∘ K`, the slot `dxhModels` reads), **`trD1J`** (`DH ∘ K`), the two stages that read them (`trMXNJ`/`trStXNJ`, `trYJ`/`trYCheckJ`), `ptD2All`, **`torsRCoreJ`**, `trTChainOkJ`; `trAJ_encloses`, `trD1J_encloses`, `trXNmJ_encloses`, `trYJ_encloses`. |
| `JetConsTorsSound.lean` | 283 | **`torsRJ_sound`** (B3b's chain with the jet's boundary), `jetSlots`, **`jetLowOk`** (kamx-packed's `jetCheck` at `cfgLow` for `torsionSlots`, with `layoutEq jd.jb.Lb rb.Lb` and `jd.jb.P == rb.P`), `jetLowOk_sound`, **`checkTorsionJ`**, **`checkTorsionJ_sound`** (the conclusion of the landed `checkTorsion_sound_of`, under its hypotheses), `checkTorsionJ_of`, `torsRCoreJ_of`. |
| `JetConsInv.lean` | 331 | `PIBook`, the invariance array `ivX` (`(X_H ∘ K)_a · 2^P − Σ_l DK_{al} (s ω)_l`, exact, on `win Lb LU0` at `2^(2P)`), its radius `ivR`, **`ivRowOk`** (one packed norm plus the radii ≤ `err`), `ivGuard`, **`jetFullOk`** (`jetCheck` at `cfgFull` for `v0 :: d1Slots`), **`checkInvarianceJ`**, `ivX_encloses`, **`checkInvarianceJ_sound`** (the conclusion of the landed `checkInvariance_sound_of`), `checkInvarianceJ_of`. |
| `JetConsEnergy.lean` | 137 | `enGuard`, **`enOk`** (`|Re z − E₀| + |Im z| + r ≤ err`, `z` the zero-key slot of the `v0` node), **`checkEnergyJ`**, **`checkEnergyJ_sound`** (the conclusion of the landed `checkEnergy_sound_of`), `checkEnergyJ_of`. |
| `JetConsFrames.lean` | 239 | **`checkFrameTRJ`** (`sup |T|` from the jet's torsion), **`checkFrameMajorantsRJ`** (`|Lᵀ|`, `|N|`, `|Nᵀ|`, `|ω*|` are the landed packed tests verbatim), `trT_chainJ`, `checkFrameTRJ_sound`, **`checkFrameMajorantsRJ_sound`** (`FrameMajorants`), `checkFrameMajorantsRJ_of`, **`routeARefinedPackedJ : EngineV2`**, `checkV2With_packedJ_sound` (any base). |
| `JetConsLoad.lean` | 58 | **`jetCheck_mono`** (a passing jet check passes at every larger load bound), **`jetLowOk_of`**, **`jetFullOk_of`** (the consumers' jet conjuncts from kamx-packed's chain theorem at its generated bound; V2-PACKED-CONS-FIX L1). |
| `JetBase.lean` | 94 | **`jetBase : BaseChecker`**, **`checkV2With_jetBase_sound`** (any engine → landed `CertifiedTorus`), **`checkV2With_jetBasePackedJ_sound`** (`jetBase` + `routeARefinedPackedJ`), **`jetBase_check_of`**. |
| `JetConsTests.lean` | 67 | Default-build kernel tests on B3b's toy integrable case (below). |

Also merged (unchanged): kamx-packed's API commit `e4bb0b16` (`JetKeyed.lean`, `JetCheck.lean`, `JetKeyedTests.lean`,
`V2-PACKED-PROD-API.md`), because `jetLowOk`/`jetFullOk` call its `jetCheck` and the soundness uses its
`jetPacked_sound`. **Landing order: `v2-packed-prod` (at least `e4bb0b16`) before or with this branch.**

## Design (the new §14 of `V2-PACKED.md`; section number to be confirmed)

- **Torsion.** B3b's chain verbatim except the two stages that read the jet: `trStXNJ` (`X_N = A N − DN`, `A` from
  the jet) and `trYCheckJ` (`Y = DH N`, `DH` from the jet). The box agreement `layoutEq jd.jb.Lb rb.Lb` and
  `jd.jb.P == rb.P` is checked, and `rb.bA` is the load bound passed to `jetCheck` (the API doc's agreement: "the
  Low box is the torsion box"). The `D²K` boundary (`ptD2All`) stays; `ptAOk`/`ptD1Ok` and the `cfgLow`
  composition are gone. `ptPackOk` is reused as is, with the memo's `ax`/`d1` empty, so that §13's
  `checkFrameLR`/`checkFrameNR` share it verbatim.
- **Invariance.** One exact packed array per coordinate `a < 2n` on `win Lb LU0` at `2^(2P)`:
  `(X_H ∘ K)_a · 2^P − Σ_l DK_{al} (s ω)_l` (`ivX`). `X_H` from the jet's `d1` nodes (sign by `hamSign`), `DK` from
  B2's Gram memo (validated by `pgEntries` inside the packed Gram check; packed on the jet's `cfgFull` box; its keys
  must fit, `ivGuard`), `(s ω)_l` B3's packed frequency. Then one packed weighted norm plus the radii `≤ err`.
- **Energy.** The zero-key slot `z` of the `v0` node, `PEnc.average`: `|Re z − E₀| + |Im z| + r ≤ err`.
- **Frames.** `|Lᵀ|`, `|N|`, `|Nᵀ|`, `|ω*|` are §13's packed tests verbatim; `sup |T|` reads the jet's torsion.
- **Sharing.** Each consumer carries its jet check and the frames repeat the torsion's conjuncts, as identical Boolean
  terms; the `_of` lemmas (`checkTorsionJ_of`, `torsRCoreJ_of`, `checkInvarianceJ_of`, `checkEnergyJ_of`,
  `checkFrameMajorantsRJ_of`, `jetBase_check_of`) assemble a production proof in which each is established once.

## Gate on LG00 T′ (`docs/campaign/studies/V2-PACKED-CONS-GATE/`)

**Method.** A scratch Lake package (`.lake/v2-packed-cons/pkg`, requiring this worktree's `kam`; outside the default
build) holds T′'s certificate copied by kamx-packed's `prod_cert_gen.py --prefix=LG00C`, three shared data modules
(books and memos; the rounded torsion nodes; the jet's wanted nodes as α-free `JLed`s of a `JetData` without
blocks) and one probe module per conjunct (`decide +kernel`). Each module is built alone under
`systemd-run --scope -p MemoryMax=4G`, after waiting while user anon memory is above 20 GB (`cons_run.sh`). CPU is
user + sys of the process; "kernel" is `type checking took`.

| group | processes | CPU | kernel | max charge |
|---|---:|---:|---:|---:|
| certificate copy (`LG00C.*`, as kamx-packed's) | 18 | 115.7 s | — | 0.58 GB |
| shared consumer data (`Base`, `Nodes`, `JetLow`, `JetFull`) | 4 | 141.8 s | — | 1.40 GB |
| Gram link (shared with `checkGramPacked`: 8 entries, core, `eps`) | 10 | 156.8 s | 103.7 s | 2.06 GB |
| **torsion** (`jetLowOk`'s box guard, 16 `D²K`, guards, packing, N, D L, DG, C, C G⁻¹, DN ×8, **X_N ×8 (jet)**, T, **Y (jet)**, final) | **43** | **868.3 s** | 661.5 s | **2.75 GB** |
| **frames** `sup \|T\| ≤ 118` (T′'s claim) on the jet's torsion | **1** | **30.2 s** | 28.6 s | 2.19 GB |
| **invariance** (`jetFullOk`'s box guard, `ivGuard`, 4 coordinates) | **6** | **41.4 s** | 13.2 s | **1.07 GB** |
| **energy** (`enGuard`, `enOk`) | **2** | **9.7 s** | 1.0 s | 0.63 GB |
| controls (below), with the frames test's tight-bound twin | 13 | 153.3 s | 101.9 s | 2.23 GB |
| data-only controls (import cost per probe process) | 2 | 14.0 s | — | 0.56 GB |

The jet chains themselves (`jetCheck` at `cfgLow` and `cfgFull`) are kamx-packed's and are not in these figures.

**Values (mirror, decided by the kernel).**
- **Gram:** δ = 1.29·10⁻¹², β = 1.4531 ≤ σB − μ = 1.45999; `eps` = 1.88·10⁻¹².
- **Torsion:** ‖S‖ = 0.208670, δ_T = 2.02·10⁻⁸; the final test `‖S‖ + σ δ_T ≤ σ` at σ = σT − μ = 0.20999 holds with
  **margin 1.32·10⁻³**. The jet's torsion-slot radii are 1.2·10⁻¹⁷ to 3.0·10⁻¹⁵, so the radii of T's averages are
  3.3·10⁻¹⁰ to 9.2·10⁻¹⁰ and of Y's 1.6·10⁻¹⁰ (B3b on lg00-cert, with the landed `cfgLow` slots of radius up to
  3·10⁻²: δ_T = 6.8·10⁻⁴, margin 1.18·10⁻³). The slot width is the jet's, 392 bits (the torsion needs ≤ 360).
- **Frames:** sup |T| ≤ 117.5007 (row sums 39.49, 117.50) against the claim 118.
- **Invariance** (err = 7.2·10⁻¹⁶, cfgFull box `H = 48`, width 400): packed norms 1.254·10⁻¹⁶, **7.192·10⁻¹⁶**,
  1.46·10⁻¹⁷, 8.2·10⁻¹⁸ plus radii 2.4·10⁻²² to 1.05·10⁻²¹ (the jet's `d1` radius dominates). The worst coordinate
  passes with **margin 8.3·10⁻¹⁹** (0.1 % of err: T′'s err was set at its invariance error).
- **Energy:** |Re z − E₀| = 7.8·10⁻²⁴, Im z = 0, r = 4.9·10⁻²³ against err = 7.2·10⁻¹⁶.

**Controls** (each decided in the kernel as stated):
- torsion: the X_N(0,0) memo radius **one ulp (2⁻¹²⁸) below** the computed one → `false`; the Y radius table one ulp
  below → `false`; the jet's radius of slot 7744 (DX_H(0,0)) 2²⁰ ulp above the ledger's → `false`; that slot's
  largest coefficient off by 2²⁰ (2⁻¹⁰⁸) → `false`;
- frames: `sup |T|` at the tight bound → `true`, one ulp below → `false`;
- invariance: coordinate 1 at its tight bound → `true`, one ulp below → `false`, and at the tight bound with the
  jet's radius of slot 7735 (coordinate 1's `d1` slot) **one ulp above** the ledger's → `false`;
- energy: the same three, on `v0` (7731) → `true`, `false`, `false`.
- **Observation (not a control):** at torsion, the jet's radius of slot 7744 one ulp above the ledger's still
  passes X_N(0,0) (`TJObsJetUlp`, `= true`): the outward rounding of `upMul` in the propagated radius absorbs one ulp
  (`⌈δ ‖N‖/2^128⌉` with ‖N(0,0)‖ < 1). Not a soundness issue: the jet's radius is certified by the jet check's export
  test (kamx-packed's one-ulp export controls), and the consumer reads it (the 2²⁰-ulp control).

**Against the landed consumers on T′** (run18 ledger, read only):

| | landed (run18) | packed (this gate) |
|---|---|---|
| invariance | `Final.InvRow0..3`, `Final.Invariance`: 5 modules, 52.8 CPU-s, ≤ 1.97 GB | 6 processes, 41.4 CPU-s, ≤ 1.07 GB |
| energy | `Final.EnergyRes`: 4.5 CPU-s | 2 processes, 9.7 CPU-s |
| their composition input | `TP.Full.*` (cfgFull `Slp.compose`): 1,637 modules, 32,255 CPU-s | the packed cfgFull chain (kamx-packed) |
| torsion | `TP.Torsion.*`: 628 modules, not yet run in run18 (on lg00-cert's data, run20e: 637 modules, 12,126 CPU-s) | 43 processes, 868.3 CPU-s (+ 127 CPU-s of shared data, once) |
| its composition input | `TP.Low.*` (cfgLow `Slp.compose`): 2,484 modules; the 2,062 run so far took 45,670 CPU-s | the packed cfgLow chain (kamx-packed) |

- The consumers' own cost is of the order of the landed consumers' (invariance, energy) or ≈ 10× below
  (torsion: 868 CPU-s, ≈ 1,150 CPU-s with the shared Gram link and the shared data, against 12,126 CPU-s; a
  cross-torus comparison). **The saving that matters is that no landed
  composition is needed:** the consumers read the packed chains, so the 4,121 landed `Low` and `Full` modules can go once kamx-packed's chain theorems are in place (on
  T′, 77,925 CPU-s for the 3,699 of them run so far; 422 `Low` modules are still to run).
- Against B3b's torsion (lg00-cert: 64 processes, 1,292 CPU-s with per-probe data), the J torsion drops the 20
  `DX_H`/`DH` boundary probes and per-probe data elaboration.

## Gate on LG00 T″ (`docs/campaign/studies/V2-PACKED-CONS-GATE/TPP/`)

The same gate on T″'s data, at T″'s own claims (σT − μ = 0.21399, err = 6.56·10⁻¹⁶, `bT = 116`). The caveats are
those of T′:
- the jet nodes are an untrusted mirror's output, made here from T″'s generator state with the landed extractor
  and kamx-packed's `--mirror-only` mirror;
- the jet chain conjunct is not decided;
- T″'s `TPP/Data` is untracked in lg00-app, so the receipts pin it by the sha256 of the copied sources.

**All 98 modules decide as stated**, one process each under 4 GB, largest 2.77 GB.

| group (T″) | processes | CPU | kernel | max charge |
|---|---:|---:|---:|---:|
| certificate copy / shared consumer data | 18 / 4 | 78.0 / 86.8 s | — | 0.56 / 1.41 GB |
| Gram link (shared) | 10 | 70.3 s | 35.8 s | 1.99 GB |
| **torsion** | **43** | **408.4 s** | 254.5 s | **2.77 GB** |
| **frames** `sup \|T\| ≤ 116` | **1** | **16.9 s** | 14.5 s | 2.14 GB |
| **invariance** | **6** | **31.9 s** | 9.0 s | 1.05 GB |
| **energy** | **2** | **8.1 s** | 0.9 s | 0.62 GB |
| controls (with the frames test at its tight bound) | 13 | 110.1 s | 57.6 s | 2.17 GB |

- **Torsion:** ‖S‖ = 0.212666, δ_T = 4.9·10⁻⁹; margin 1.32·10⁻³.
- **Frames:** sup |T| = 115.676 against 116.
- **Invariance:** norms 1.258·10⁻¹⁶, **6.545·10⁻¹⁶**, 1.34·10⁻¹⁷, 6.8·10⁻¹⁸ plus radii ≤ 1.08·10⁻²¹. The worst
  coordinate has **slack 1.52·10⁻¹⁸, 0.23 % of err** (T′: 0.11 %). In both tori the slack is set by the choice of
  err, not by the radii.
- **Energy:** deviation 1.3·10⁻²³, radius 5.0·10⁻²³.
- **Controls:** as on T′, every one decided as stated (the jet radius + 1 ulp is again absorbed at torsion's X_N).
- **CPU and load.** The CPU per probe is about half of T′'s, mostly lower system time on a less loaded machine. CPU
  in these gates is load-sensitive; kernel times compare better.

## Checks and their output

- **Targeted builds** (`nice -n 5`, `systemd-run --scope -p MemoryMax=4G`, one at a time):
  `lake build KAM.CertificateSharp.Packed.JetConsTests` (which builds `JetConsTors`, `JetConsTorsSound`,
  `JetConsInv`, `JetConsEnergy`, `JetConsFrames`, `JetBase`) → `Build completed successfully (3557 jobs)`, no
  warning in the new modules.
- **Toy kernel tests** (`JetConsTests.lean`, default build, B3b's toy integrable case with `DX_H ∘ K`, `DH ∘ K` and
  `H ∘ K` read from toy jet slots): the torsion core passes with the bound 3 and fails with 1; `ivGuard` passes;
  every invariance coordinate passes at `err = 1/1000`, and coordinate 0 fails with `∂_{I₁} H = 2`; `enGuard`
  passes; the energy passes at `E₀ = 0` and fails at `E₀ = 1`.
- **`#print axioms`** → `[propext, Classical.choice, Quot.sound]` for `trAJ_encloses`, `trD1J_encloses`,
  `trXNmJ_encloses`, `torsRJ_sound`, `jetLowOk_sound`, `checkTorsionJ_sound`, `checkTorsionJ_of`, `torsRCoreJ_of`,
  `ivX_encloses`, `jetFullOk_sound`, `checkInvarianceJ_sound`, `checkInvarianceJ_of`, `checkEnergyJ_sound`,
  `checkEnergyJ_of`, `trT_chainJ`, `checkFrameTRJ_sound`, `checkFrameMajorantsRJ_sound`, `checkFrameMajorantsRJ_of`,
  `routeARefinedPackedJ`, `jetBase`, `checkV2With_jetBase_sound`, `checkV2With_jetBasePackedJ_sound`,
  `jetBase_check_of`, and (V2-PACKED-CONS-FIX) `jetCheck_mono`, `jetLowOk_of`, `jetFullOk_of`. The audit also
  checked kamx-packed's API theorems (`jetPacked_sound`, `jetCheck_of`, `jetChainOk_sound`, …): standard axioms.
- **No `Slp.compose`** (a scratch meta-program over definition bodies, theorems not followed): `checkTorsionJ`,
  `checkInvarianceJ`, `checkEnergyJ`, `checkFrameMajorantsRJ`, `refinedTestPackedJ`, `checkGramPacked`,
  `checkHamBounds`, `checkEmbedding`, `checkStatic` → `false`; `checkTorsionR`, `checkFrameMajorantsR`, landed
  `checkInvariance` → `true`; `checkTorsionJ` reaches `jetCheck` (`true`) and neither `torsionModels` nor `gramCheck`.
- **`scripts/lint_sources.sh`:** `check_lean_modules: PASS`, the frozen-anchor tests `OK` and `FROZEN-ANCHOR GUARD
  OK`. Two pre-existing failures: the ABI step (a frozen planetary module's `.olean` is not built in this worktree)
  and one line of 106 characters in kamx-packed's `JetKeyedTests.lean:35` (not my file). My files: no line over 100
  characters, at most 331 lines, no forbidden token. `gen_root_imports.py --check` exits 0.
- **Additivity:** against `origin/main` (`7b81f9b9`), the only changes under `KAM/` are new `Packed/*.lean` files
  (mine and kamx-packed's merged `e4bb0b16`) and the generated `KAM/Root/CertificateSharp.lean`.

## Scripts (new, `scripts/packed/`)

- `cons_gate_gen.py`: T′'s data and the bit-exact mirrors (Gram core, `D²K`, the J torsion chain on the jet's box
  and width, the invariance arrays, the energy, the frames' row sums), the shared data modules and the probes.
- `cons_run.sh` (one module of the scratch package under a cap, with the anon-memory wait), `cons_run_plan.py`
  (all modules in order, resumable), `cons_gate_sum.py` (the summary).

## Owner questions (answered by the orchestrator)

1. **Landing order.** This branch contains kamx-packed's `e4bb0b16` (the `jetCheck` API it calls).
   *Answered:* `v2-packed-cons` lands together with or after `v2-packed-prod`. If kamx-packed changes
   `jetCheck`/`jetPacked_sound`, only `jetLowOk`, `jetFullOk`, their two `_sound` lemmas and `JetConsLoad.lean`
   need adapting (the cores depend on `JSlotsEnc` only).
2. **Design section number.** *Answered:* §14 for CONS (kamx-pk-gen uses §15 if it adds design text).
3. **`JetBridge`.** A production proof states the consumers at `lg00Cert.ham.jet`, i.e. rewrites it to the
   literal `lg00Jet` with `lg00Ham_jet` (`LG00.JetBridge`). *Answered:* `LG00.JetBridge` is already built in
   lg00-app; kamx-packed reuses it (or one solo build at 7.5 GB).

## V2-PACKED-CONS-FIX (AUDIT-V2-PACKED-CONS-1: PASS WITH CHANGES, Lean sound)

- **C1** (106-character line in `JetKeyedTests.lean:35`): fixed by kamx-packed on `v2-packed-prod` and merged here
  from `3a84cc28`. `lint_sources.sh` now reports no line over 100 characters; only the pre-existing ABI step
  fails, because a frozen planetary `.olean` is not built in this worktree. After the merge, `JetCheck` (which only
  gained the prefix lemma `jetPacked_sound_prefix`), `JetKeyedTests` and every consumer module down to
  `JetConsTests` rebuild with no warning.
- **C2:** the Result bullet now says "every consumer-side conjunct, on the mirror's nodes", and that the jet chain
  conjunct was not decided in the gate.
- **C3:** the invariance jet-radius control changes slot 7735 (coordinate 1's `d1` slot), not 7732.
- **Optional items:** §14 now states the invariance slack as 0.1 % of err. The torsion comparison now counts the
  shared Gram link and data (≈ 10×, not ≈ 14×).
- **L1, the jet's load bound** (agreement with kamx-packed, message of 2026-11-01). The consumers keep their books'
  bounds (`rb.bA` in `jetLowOk`, `ib.bJ` in `jetFullOk`), and kamx-packed's chain theorem keeps its generated
  `b<C>` (the largest load of a wanted node). The new `JetConsLoad.lean` bridges them:
  - `jetCheck_mono`: a passing `jetCheck` passes at every larger bound (only `jetWantedOk` depends on it);
  - `jetLowOk_of hL hP jetLow_check_cert (by decide : bLow ≤ rb.bA)` closes the torsion's jet conjunct, and
    `jetFullOk_of` the invariance and energy one.
  The consumers' generator sets `rb.bA = ib.bJ =` the largest wanted load (2¹⁴⁰ on T′), so the side condition is an
  equality in practice. No change on `v2-packed-prod`.
  **Confirmed by kamx-packed** (message of 2026-11-01, `v2-packed-prod` `3a84cc28`):
  - `LG00P.TP.jetLow_check_cert` and `jetFull_check_cert` are built (standard axioms), at `bLow = bFull = 2¹⁴⁰`;
  - `jdLow.jb.Lb = ⟨[-25, -25], [51, 51], [101, 1], 392, 1⟩` at scale `P = 128`, which is the consumers' `rb.Lb`;
  - so T′'s torsion jet conjunct is `jetLowOk_of hL rfl jetLow_check_cert le_rfl`, with `hL` the decided
    `layoutEq` (`TJJet`), and likewise `jetFullOk_of` for the invariance and energy.
- **L2** (ledger lookups): measured afterwards on the real ledgers (V2-PACKED-CONS-LOOKUP, next section).

## V2-PACKED-CONS-LOOKUP: the jet-slot reads on kamx-packed's real ledgers (`…/V2-PACKED-CONS-GATE/LOOKUP/`)

- **The ledgers.** kamx-packed's T′ ledgers are copied read-only and built here: cfgLow 31 modules, 553 CPU-s;
  cfgFull 20, 780 CPU-s; ≤ 1.42 GB.
  - They hold **1,129 and 706 entries** (block exports only; the "about 3,800" estimated before was the live-slot
    count).
  - The wanted slots come last, so every read walks the whole ledger (a left-nested `++` of 29 and 18 parts).
- **Method.** A/B twins of the consumer probes that read jet slots: X_N(0,0), Y, invariance row 1, energy. They
  read the whole ledger (R) or the gate's wanted-only one (W), and are measured in the same session. Every twin
  decides `true`: the real ledger's wanted nodes are the gate's.
- **Result.**
  - The searches add ≈ 16 s of kernel time to torsion (2.5 % of 662 s), ≈ 0.2 s to invariance (1.5 %) and 0.36 s
    to energy (its kernel time is 1 s): **2.5 % of the consumers' kernel time** in all.
  - With the import of the whole ledgers' oleans (+1.74 s user per process), the CPU delta is ≈ 29 s, 3.2 % of the
    consumers' CPU. It is 15–17 % for the two small consumers, invariance and energy, but that is the import, not
    the reads.
- **Decision.** Under the ~10 % threshold, so no wanted-slot table and the consumers are unchanged.
- **Options for production:**
  - kamx-packed's generator can list the wanted slots' entries first (no Lean change; producer and consumer read
    the same `look`);
  - a literal wanted-slot table with a transfer lemma would remove the ledger import from the 14 consumer processes
    (≈ 24 s per torus, minus one checking process).

## Uncertainties and open points

- **Production assembly unmeasured.** The gate decides each conjunct separately. Not built for T′: the instances
  of the `_of` lemmas, and `jetBase`'s Boolean from them (`jetBase_check_of`).
- **Ledger lookups: measured** (V2-PACKED-CONS-LOOKUP, above). The searches cost 2.5 % of the consumers' kernel
  time; no wanted-slot table is needed.
- **Invariance margin on T′:** 8.3·10⁻¹⁹ on coordinate 1, i.e. 0.1 % of err. It passes in the kernel, but a
  different box, precision or rounding could tip it; the energy and torsion margins are wide.
- **The frames' tight-bound probe** (`FRTJ`) and the claim probe (`FRTJClaim`) are the same test at two bounds;
  production needs the claim only.
- **The kernel times** of this gate (`type checking took`) and B3b's handoff figures (89.8 s for 36 boundary
  probes) are not measured the same way; B3b's own receipts show 8.3 s of `type checking` for `TRE_D2_0_0_0`
  against 13.8 s here. The CPU columns compare directly.
- Process notes: two generator mistakes cost reruns, both fixed and recorded here. Probes stated with
  `= some (CertFixed …)` cannot be decided (no `DecidableEq`), so they now compare mantissas as B3 did. The first
  jet-radius control turned out to be the observation above.

## Errata and deviations

- **Errata:** none in a pinned source.
- **Deviations from §12.2:** (a) each consumer holds its jet check, so `jetBase` holds `jetFullOk` twice as the same
  Boolean term (shared in an assembly); (b) `ptPackOk` is reused with the memo's `ax`/`d1` empty rather than a new
  packing guard, for verbatim sharing with §13's frames; (c) the invariance aligns `X_H ∘ K` to `2^(2P)` by an exact
  unit shift before subtracting `DK (s ω)` (exact, no rounding).

V2-PACKED-CONS DONE
