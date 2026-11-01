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
- **Follow-up (kamx-packed, 2026-11-01):** `v2-packed-prod` `2796f8c8` makes `jet_prod_gen.py` list the wanted slots'
  entries first in `led<C>` (no Lean change). The T′ instance already built (`3a84cc28`) keeps the old order, so the
  2.5 % above stands for it; future emissions read the wanted slots from the head of the ledger.

## V2-PACKED-CONS-PERF: the two "slow" torsion assemblies (`…/V2-PACKED-CONS-GATE/PERF/`)

kamx-pk-gen booked `TorsJ.Core` (`torsRCoreJ_of`) at 166 CPU-s and `TorsJ` (`checkTorsionJ_of`) at 401 CPU-s on the
T′ jet route (integration log `runJ`). B3b's counterparts took 4.3 and 7.3 s.

- **The assemblies are not slow.** Elaborated alone by `lean` against the built oleans (read only, one process under
  4 GB, two interleaved passes; `cons_perf_run.sh`):
  - jet: `TorsJ.Core` 2.29–2.45 CPU-s and `TorsJ` 2.07–3.31;
  - B3b: `Tors.Core` 2.17–2.18 and `Asm.Tors` 2.43–2.57;
  - elaboration < 30 ms and kernel < 3 ms everywhere, peak ≤ 0.91 GB; the rest is the import;
  - nothing unfolds `jetSlots`, the ledger or `lg00Ham_jet`: the parts match the lemmas' hypotheses syntactically.
- **Cause: the driver's accounting, not Lean.** `run_packed.py` resumes by skipping the modules whose last ledger
  row passed, without asking Lake. `gen_packed.py` re-emitted the torsion stages twice during `runJ` (between 16:50
  and 17:30: `jdLowW`, `lg00Jet`; at 17:37: `pkHamJet`, the `RouteSharp` import). Each time, the next target's
  `lake build` rebuilt the stale stages inside its own process, and the ledger booked them to that target:
  - `TorsJ.Core`'s process built 17 modules: its own job 1.8 s, the rebuilt stages 162.8 s;
  - `TorsJ`'s built 92: its own job 1.4 s; the rebuilt data, Gram, D²K, fronts and every stage took 385.0 s.
- **The whole ledger** (`cons_perf_attr.py`; receipt `runJ/`, sha256-pinned): six rows rebuilt 123 dependencies,
  596.7 s of job time, so the ledger's 2,503 CPU-s double-count about 24 %. A single pass would read about
  1,906 CPU-s. Torsion assemblies: 567.0 booked, 19.2 after the correction (Lake's start-up and trace check
  included), 2.7 s of Lean jobs.
- **Fix: kamx-pk-gen's driver.** `PERF/run_packed_resume.patch` against `v2-packed-gen`'s `run_packed.py`
  (`305612780`; not applied, since that branch is read only here):
  - on resume, one batched `lake build --no-build` over the passed modules, bisected to the stale ones, which are
    then built in their own rows;
  - a warning when a row's process built more than its target.

  `cons_perf_drvtest.sh` tests the patch on a toy package with V2-PACKED-GEN's layout:
  - **unpatched:** after one source changes, the next target's process builds that module too;
  - **patched:** the stale module gets its own row, and the target's process builds only the target.
- **No Lean change:** the consumers and the `_of` lemmas are unchanged.
- **Checks:** `lint_sources.sh` gives the same result as before:
  - `check_lean_modules: PASS` (4,421 files), the 25 anchor tests `OK`, `FROZEN-ANCHOR GUARD OK`;
  - only the ABI step fails, as before: the frozen planetary module `AngularMomentum3`'s olean is not built in this
    worktree.

## V2-PACKED-CONS-BRIDGE: the packed theorem about LG00's own constants (`…/V2-PACKED-CONS-BRIDGE/`)

AUDIT-V2-PACKED-PROD-1 C2: kamx-pk-gen's `LG00P.<T>.pk_kamTorus` is about kamx-packed's copies (`LG00P.<T>.lg00Cert`
and the renamed definitions). LG00's statements are about LG00's own constants.

- **The bridge is definitional** (AUDIT-V2-PACKED-JETROUTE-1 §1; the orchestrator's instruction).
  - Every field the statement reads is equal in the copy and the original by `rfl`; the copy differs only in its
    empty witnesses and advice.
  - So LG00's statement, verbatim (LG00's namespace and `open` line), is proved by `:= LG00P.<T>.pk_kamTorus`.
- **Modules** (`cons_bridge_gen.py`, built by `cons_bridge_build.sh` with `lean` against kamx-pk-gen's packages, read
  only):
  - `LG00B.<T>.Main`: `LG00.<T>.lg00_kamTorus_packed`, `…_kamTorusStatement_packed` and `…_certifiedTorus_packed`;
    T″ also `lg00_hamBounds_packed` (kamx-conf's request), by `checkHamBounds_congr` with `LG00B.TPP.Fields`.
    Unfolding would make the kernel evaluate the check: killed at 4 GB, probed on T′.
  - `LG00B.<T>.Check`: LG00's statements extracted verbatim from `lg00-app`'s `<T>/Main.lean`, elaborated against
    the theorems, and `#print axioms`.

  The oleans are at `.lake/v2-packed-bridge/build/lib/lean`, which kamx-conf reads.
- **T′: built and checked.**
  - `Main` 2.3 CPU-s, 0.34 GB (578 ms of elaboration, 31 ms of kernel time); `Check` 2.0 CPU-s.
  - Axioms: `propext`, `Classical.choice`, `Quot.sound`.
  - kamx-conf recompiled against it: `lg00_kamTorusStatement_packed` plugs into `lg00_confinement_of_tori`.
  - The first version (`989deddbc`: explicit field equalities plus a congruence lemma) is superseded with the same
    names, types and path.
- **T″: built and checked** (22:25 UTC), on kamx-pk-gen's `LG00P.TPP.PK.MainJ` (22:23) and
  `LG00P.TPP.Balls.HamBounds`.
  - `Main` 1.95 CPU-s, 0.33 GB; `Fields` 1.3 CPU-s; `Check` 1.6 CPU-s.
  - Standard axioms for all four theorems, `lg00_hamBounds_packed` included; LG00's T″ statements, verbatim,
    elaborate against them.
  - LG00's `LG00.TPP.Data.Cert` comes from `kam-lg00` (kamx-pk-gen's hardlinks of `lg00-app`'s build).
  - kamx-conf is notified.
- **Names fixed with kamx-conf.** It imports `LG00B.TP.Main` and `LG00B.TPP.Main`, and the declarations
  `LG00.TP.lg00_kamTorusStatement_packed`, `LG00.TPP.lg00_kamTorusStatement_packed` and
  `LG00.TPP.lg00_hamBounds_packed`. kamx-pk-gen confirmed `LG00P.TPP.pk_kamTorus` in `LG00P.TPP.PK.MainJ`.
- **Runner fix:** `/usr/bin/time` reports `exit 0` for a signal kill. `cons_perf_run.sh` now marks an OOM kill or
  signal as a failure. No earlier build was affected.
- **Scope:** the theorems are LG00's statements about LG00's constants, proved through the packed route. They do
  not use LG00's landed checker run. The packed proof's own premises (the chains, the solo-exception
  `LG00P.lg00Ham_jet`, T′'s `Xfer`) are kamx-pk-gen's and kamx-packed's.

## V2-PACKED-CONS-DATA: the Data stage of the packed whole-torus route (`…/V2-PACKED-CONS-DATA/`)

kamx-pk-gen's T′ table books Data at 326 modules and 3,673 CPU-s, 36 % of the packed route.

- **90 % is LG00's landed advice**, which the packed route never reads: `LG00.TP.Data.A*`, 254 modules, 3,295 CPU-s
  (run18).
  - It is in the closure because `LG00.TP.Data.Cert` imports it. T′'s `Xfer` imports LG00's Hamiltonian bounds,
    whose disc pass reads four of `LG00.TP.lg00Cert`'s fields.
  - Any theorem about LG00's own `lg00Cert`, the bridge's included, imports `LG00.<T>.Data.Cert` and so all of the
    advice. This holds for T″ too, although its packed `MainJ` has no LG00 data.
  - The rest of the row: the packed route's own data 252 CPU-s, LG00's other data 83, kamx-packed's copy 42.
- **Why an advice module costs 13 CPU-s:**
  - elaborating about 34,000 numerals per module (8.7 M in all, 94.9 % zeros): `A100` takes 5.1 s of elaboration
    against 26 ms of kernel time;
  - the fixed cost per module is only 1.2–1.8 CPU-s.
- **Measured fix: packed advice** (`cons_data_gen.py`/`cons_data_build.sh`, additive modules `LG00X.*`).
  - Same definitions (names, types, values), stored as at most 88-digit literals: fixed-width, LEB128 or run-length
    over LEB128, decoded by structural functions the kernel evaluates with GMP.
  - **Cost:** a packed part costs about the empty-module floor, 1.3–2.5 CPU-s against 7–18 for the original (5–10×).
    Three parts in one module: 2.35 CPU-s against 41.3.
  - **Faithful:** `packed = original` by `decide +kernel` for every list of three parts (6.5–11 kernel-s per part, an
    audit cost).
  - **Whole T′ advice:** 104 modules at ≤ 1,400 lines; three of them were built at 1.4–1.8 CPU-s each. That projects
    to about 170 CPU-s against 3,295, saving about 3,100 CPU-s per torus (about 30 % of the route).
  - **Trade-off:** a consumer that reads the values pays more in the kernel (`A100`: 9.2 against 3.2 kernel-s for
    every value). The packed route never reads them; LG00's landed chains would.
- **Options** (owner's and orchestrator's choice; not applied):
  - (A) an advice-free `lg00CertCore` in LG00's generator, with every statement at the core: saves the whole
    3,295 CPU-s and leaves the landed route unchanged;
  - (B) packed advice in LG00's generator: saves about 3,100 CPU-s, with no statement change;
  - (C) small: drop `JetFront` on wanted-first ledgers (84 CPU-s; T″ and later), pack the memos (perhaps about
    100 CPU-s).
- **Not the cause:**
  - nothing is re-elaborated: LG00's modules are reused artifacts;
  - the copy duplicates only about 42 CPU-s;
  - the fixed cost per module is about 10 % of an advice module's cost.

## Resume after reboot (lemma.farm reboots 2026-11-02 05:00 UTC; `/tmp` is wiped)

- **State:** everything is committed on `v2-packed-cons`. Nothing of this task lives only in `/tmp`:
  - the PERF receipts are under `docs/campaign/studies/V2-PACKED-CONS-GATE/PERF/`;
  - `runJ/` carries the ledger and the `Built` lines of kamx-pk-gen's `/tmp` logs, which the reboot will lose;
  - the BRIDGE receipts are under `docs/campaign/studies/V2-PACKED-CONS-BRIDGE/`;
  - the DATA receipts are under `docs/campaign/studies/V2-PACKED-CONS-DATA/` (logs, tables, pins of the sampled
    `lg00-app` sources).
- **Built outputs that survive (`/home`):**
  - T′ gate: `.lake/v2-packed-cons/pkg` (prefix `LG00C`, with kamx-packed's ledgers);
  - T″ gate: `.lake/v2-packed-cons/pkg-tpp` (prefix `LG00D`);
  - the core's `.lake/build` of this worktree;
  - the bridge: `.lake/v2-packed-bridge/{src,build,logs}` (sources regenerated by `cons_bridge_gen.py`; kamx-conf
    reads `build/lib/lean`; T′ `Main`/`Check` and T″ `Fields` are built);
  - the data study: `.lake/v2-packed-data/{src,build,logs}` (regenerated by `cons_data_gen.py`).
- **The bridge after the reboot:**
  - **T′:** nothing to do.
  - **T″:** built (22:25 UTC); nothing to do.
  - **kamx-pk-gen's re-wrap** of `RouteSharpJ`/`JetFront` (int `e9d941830`, 22:4x UTC) rewrote no package olean:
    Lake keeps downstream traces on the public interface. Checked against the pins: both `MainJ` and T″'s
    `HamBounds` oleans are byte-identical, so the bridge's hashes stand.
  - kamx-conf's `lg00_confinement` is built against them (FINAL OK, 22:26 UTC, standard axioms).
  - **If the integration PK oleans ever change:** rerun both trees' commands below, refresh the pins in
    `…/V2-PACKED-CONS-BRIDGE/{TP,TPP}/`, commit, and send kamx-conf (`lg00-conf-13`) the new olean hashes.
    ```
    cd /home/scott/KAM-dev-worktrees/v2-packed-cons
    python3 -I scripts/packed/cons_bridge_gen.py --tree=TP && scripts/packed/cons_bridge_build.sh TP 4G
    python3 -I scripts/packed/cons_bridge_gen.py --tree=TPP && scripts/packed/cons_bridge_build.sh TPP 4G
    ```
- **Lost at reboot (not needed):**
  - the scratch copies of the measured sources (pinned by `PERF/alone/sources_sha256.txt`);
  - the toy driver packages (`cons_perf_drvtest.sh` recreates them);
  - the T″ script copies (made by the `sed` recipe in `TPP/README.md`).
- **Next steps:** none pending. The DATA options are for the owner and orchestrator. To re-measure after the
  reboot:
  ```
  cd /home/scott/KAM-dev-worktrees/v2-packed-cons
  python3 -I scripts/packed/cons_perf_attr.py docs/campaign/studies/V2-PACKED-CONS-GATE/PERF/runJ
  scripts/packed/cons_perf_drvtest.sh ../v2-packed-gen/scripts/packed/run_packed.py <patched copy> <scratch dir>
  # assemblies alone: copy the module source to SRC/<its path>, then
  ROOT=SRC scripts/packed/cons_perf_run.sh 4G <core worktree> <package> SRC/<path>.lean NAME LOGS -Dprofiler=true
  # the data study (DATA/README.md, Reproduce)
  python3 -I scripts/packed/cons_data_gen.py A0 A100 A253 && scripts/packed/cons_data_build.sh 4G LG00X.Pack …
  ```

## Uncertainties and open points

- **Production assembly: built by kamx-pk-gen and measured** (V2-PACKED-CONS-PERF, above). The `_of` instances
  for T′ (`pkTorsCoreJ`, `pkCheckTorsionJ`, …) are built on `v2-packed-gen-int`. Measured alone, the torsion
  assemblies take 2–3.3 CPU-s each, as B3b's do.
- **Ledger lookups: measured** (V2-PACKED-CONS-LOOKUP, above). The searches cost 2.5 % of the consumers' kernel
  time; no wanted-slot table is needed.
- **Invariance margin on T′:** 8.3·10⁻¹⁹ on coordinate 1, i.e. 0.1 % of err (the kernel brackets the bound at
  err − 8.275·10⁻¹⁹; kamx-packed's 7.9·10⁻¹⁹ is the landed generator's float estimate for `checkInvariance`, not a
  packed figure, on the same cfgFull nodes). It passes in the kernel, but a
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
