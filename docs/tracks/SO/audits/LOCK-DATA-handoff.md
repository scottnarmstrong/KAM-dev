# LOCK-DATA handoff and seal-key audit request: the N = 65 lunar lock (SO-3) data chain

- **Branch:** `inp-lockdata`, worktree `/root/code/KAM-inp-lockdata`.
- **Commits:** the frozen chain commit is `447772bf1cd2506da75b60501edc6fbf7d1a3c9a`; HEAD adds docs and tooling only.
- **Status:** nothing is frozen or landed here. The four LOCK-FREEZE statements are on branch `inp-lockfreeze`
  (worktree `/root/code/KAM-inp-lockdesign`), Phase A done, bodies `sorry` (DRAFT_SORRY).
- **This audit:** the second key before the LOCK-FREEZE seal (D63, pre-approved). It covers the whole data chain
  and the four frozen statements.

## 1. The final theorems (`KAM/SpinOrbit/Data/LockN65/AssemblyN65.lean`)

```lean
theorem lock_barrier :
    Nonempty (LockBarrier ((cert.Ω : ℚ) : ℝ) (KAM.SpinOrbit.Lock.lockCentre cert.cs)
      ((cert.graph.pLo : ℝ) - cert.graph.base.params.disp)
      ((cert.graph.pHi : ℝ) + cert.graph.base.params.disp))

theorem lunar_sync_lock_N65 (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 129 / 10000) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 21 / 100 ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 26 / 1000 ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z
```

**How they are proved.**
- `lock_barrier` is `lockBarrier_of_certV2K` (`LockGraphK.lean`), the landed `lockBarrier_of_certV2` with the graph
  check `checkSoGraphK`. Its inputs are:
  - `lock_passes : checkTorusCertificateV2 routeAV2 base (Sum.inr (Sum.inr refinedWit)) = true`. This is
    `checkTorusCertificateV2_refined_of (landedBase_check_of lock_static lock_hamBounds lock_embedding
    lock_csInvariance lock_csEnergy lock_csGram lock_csTorsion) lock_hamClaim lock_frame lock_core`.
  - `lockGraph_passes : checkSoGraphK graph = true`.
  - `lock_freq`: the √5 box enclosure, `algFreq_encloses`.
  - `lock_dio`: `lunarRotFreqPlusN_isDiophantine_65` at the certificate's γ = 1/67, τ = 1.
- `lunar_sync_lock_N65` is the landed, **explicitly conditional** helper `lunar_sync_lock_of_barrier_check`
  (`KAM/SpinOrbit/Lock/Assembly.lean`). Its hypotheses are discharged by `lock_barrier`, two `decide +kernel` bounds
  (`13155/1000000 ≤ pLo − disp`, `pHi + disp ≤ 163/10000`) and `lock_literalCheck65` (`decide +kernel` of
  `lockLiteralCheck`).
- The only remaining hypothesis is the frozen statement's own `h₀`.

**Which definitions it uses.**
- `lunarOmega`, `lunarSyncOrbit` and `libAction` resolve to the *landed* `KAM.SpinOrbit.Lock.*` definitions, because
  nothing under `KAM/SpinOrbit/Lock` imports the frozen `Defs`.
- `soField` is the band-sealed frozen `KAM.SpinOrbit.soField`, through `KAM.SpinOrbit.Model`.

## 2. The four LOCK-FREEZE statements (`inp-lockfreeze`, `KAM/Frozen/SpinOrbit/Theorems/`)

| Frozen theorem | Statement |
|---|---|
| `lunar_sync_lock` | character for character the conclusion above, over the **frozen** `KAM.SpinOrbit.{lunarOmega, lunarSyncOrbit, libAction, soField}` |
| `lunarSyncOrbit_spec` | `IsSyncOrbit lunarSyncOrbit` |
| `lunarSyncOrbit_unique` | `(ψ : ℝ → ℝ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit` |
| `lunarSyncOrbit_bound` | `(φ : ℝ) : |lunarSyncOrbit φ| ≤ 17 / 1000000 ∧ |deriv lunarSyncOrbit φ| ≤ 27 / 200000` |

**Bridges** (`inp-lockfreeze` 41934621, `KAM/SpinOrbit/Lock/FrozenBridge.lean`):
- `frozen_isSyncOrbit_iff`/`_eq` (via `soField_eq`);
- `frozen_lunarSyncOrbit_eq`;
- `frozen_libAction_eq` (`rfl`).

The frozen `lunarOmega` and `Lock.lunarOmega` are both the literal `8 / 65 : ℚ`.

**Providers.** The providers of the three `lunarSyncOrbit_*` theorems are prepared there; the frozen bodies are
unchanged. The headline provider is written at the seal (Phase B, after this chain lands): the bridges, then
`lunar_sync_lock_N65`.

## 3. Literals (exact mirrors; `scripts/spin_orbit/lock_gen.py` `FINAL`; `Params.lean`, `Domain.lean`)

| Item | Value |
|---|---|
| Support | diamond 100 × 20; CertFixed 112; cut-offs 100000 / 250; ρ 1/100; ρ∞ 1/100000; μ 1/1000 |
| σK / σB / σT / M | 371/200 / 1017/200 / 103/50 / 93020 |
| err / disp | 27/(25·10²¹) = 1.08e-21 / 1/781250000000000 = 1.28e-15 |
| Domain | ρ_H 19539/10⁶; centre (14799/10⁶, 99971/200000); radius (851/200000, 11739/10⁷); Taylor order 30 |
| Box | `lunarRotFreqPlusN_eq 65 1` at a √5 enclosure of width 10⁻⁶⁰ |
| Frame claims | bL 1.779, bN 2.129, bNt 2.244, bT 6.805 (1361/200) |
| v2 threshold | 10^−19.23 against err 10^−20.97, a margin of 1.74 decades |
| Graph band | [13155/1000000, 163/10000] (deviation D1, §8) |

## 4. The data and the proof

**Volume.** 13,668 LockN65 modules at 242.1 MB, against the ~265 MB D70 accepted:
- 65 tracked lock-owned modules (0.22 MB, about 7k lines);
- 13,603 generated data modules, untracked by design (D47/D52/D55/D67/D70). They are per-file links into
  `kam-data/so-lock/lean/{src,sosk,dk,graphk3,segd55z2,zx1,d4c,d5c}`.

**Structure.** The proof is the segmented one (SO-CSPLIT route E, the generators `csplit_*.py` plus the lock shim
`lock_cseg.py`):
- **Composition chains** (`Seg/Chain`): 187 cfgFull and 386 cfgLow segments, each `segOk` by `decide +kernel`.
- **Ledgers:** `LedgerFull*`, `LedgerLow*`.
- **Memos:** `Memo*`.
- **Packed products:** `Seg/Prod/M*`. Each has shard, decode and assembly theorems, with every side check in its
  own module (variant ii, D67).
- **Gram:** `Seg/Gram/*`.
- **Torsion:** `Seg/Tors/*`, through `torsionModels_eq_of_stages`/`frameNModels_eq_of_stage`.
- **Checks** (`Seg/Checks/*`):
  - energy tail and invariance rows 0–3;
  - torsion;
  - frame T and N, one theorem per row (or column) and vertex since DELTA-LAM-5 (§6).
- **Embedding/static/Ham passes:** `Pass/*`.
- **Graph check:** `checkSoGraphK`, chunked by key range: `GraphK/`, `GraphChunk*`, `RealLowerK*`.

**Lock-owned Lean** (tracked, all under `KAM/SpinOrbit/Data/LockN65/`; no `sorry`/`axiom`/options):

| Role | Modules |
|---|---|
| Data encodings and decoders | `Format`, `ZCode`, `ZCodeX` (whitened rows, DELTA-LAM-3), `ZRows`, `PairCode` |
| Route lemmas (exp/inv/sqrt arms, memos, splits) | `SegRoutes`, `SegSupport`, `SegDecide`, `DecSplit`, `RemSplit`, `MemoBridge`, `AdvLookup`, `AdvLookupSub`, `FallbackMul`, `ExpSplit`, `ErrRadiusTbl` |
| Graph | `GraphK`, `LockGraphK`, `GraphChunk`, `GraphChunkFixed`, `RealLowerK`, `RealLowerKSq`, `SegGraph` |
| Jet and Ham | `Jet`, `JetEq`, `JetOps0–2`, `BallChain`, `HamBridge`, `HamOk`, `EmbBridge` |
| v2 core and certified bites | `Core`, `Site0B`, `Site0D`, `Site1B`, `Site1D`, `Site2B`, `Site3B` |
| Parameters | `Params`, `Num` |
| Passes and assembly | `Pass/*`, `Passes`, `AssemblyN65` |
| Frame split | `CornerSplit` (DELTA-LAM-5) |
| Toy probe | `SegRoutesProbe` (inv/sqrt arms on exact ℚ data) |

**Trust boundary.** The generated data are untrusted: every fact about them is a `decide +kernel` against a landed
checker, or a lock-owned lemma above. `SegDecide` holds one deliberate orphan instance,
`deriving instance DecidableEq for SlpOp`. Only generated segment modules import it.

## 5. Kernel evidence

- **The remote run** (lam, 2026-11-04/05, `lam-reports/kam-complete.md`): `done lock ok=13665 fail=0 skip=0 todo=0`,
  i.e. every module of AssemblyN65's closure was built by the kernel. lam's
  `lake build --no-build KAM.SpinOrbit.Data.LockN65.AssemblyN65`: up to date (17247 jobs), at HEAD 447772bf.
- **Returned outputs:** `kam-data/so-lock/remote-20261105/lock/{lib/lean,ir}/…/LockN65` (`*.setup.json` not
  extracted: Lake writes it at compile time and does not read it for up-to-date checks). This worktree's
  `.lake/build/{lib/lean,ir}/KAM/SpinOrbit/Data/LockN65` links there.
- **Up-to-date checks here:**
  - `lake build --no-build KAM.SpinOrbit.Data.LockN65.AssemblyN65`: up to date (17247 jobs), rc 0;
  - over all 13,668 modules of `gen_root_imports.py --modules KAMLunarLock`: up to date (17250 jobs), rc 0. The 29
    modules outside the closure were built here; 26 stale import hubs were moved out to
    `kam-data/so-lock/quarantine-hubs-20261105/`.
- **Kernel replay sample** (the runbook's audit method: seed 65, 5 % of `Seg/**` plus Pass/*, Passes, AssemblyN65;
  627 modules), done 2026-11-05 00:51–10:24 UTC:
  - **Here: 621 modules, 621 rc 0.** These are the 627 minus the 6 whose lam build peak was above 9 GiB.
    - Method: `leanchecker`, one module at a time, MemoryMax=10G, under `orchestrator-tools/.kernel-probe.lock`.
    - Totals: 9.1 h of checker time; the longest replay 494 s; peak RSS 13.5 GB (file-backed pages included; the
      10G cgroup cap held).
    - Families: 541 Seg.Prod, 22 Seg.Low, 18 Pass, 10 LedgerLow, 7 LedgerFull, 7 Seg.Full, 4 Memo, 3 Rad, 3 Tors,
      2 Stage, Chain, Checks (the leaf `Seg.Checks.*` module sampled), Passes, AssemblyN65.
    - None of the 621 has descendant modules, so each run replayed exactly that one module (see the next point).
  - **On lam at 32G: 8/8 rc 0**, on the frozen 447772bf (`lam-reports/heavy-leanchecker.txt`): the 6 over
    9 GiB (Pass.FrameL0/FrameL1, Seg.Prod.M1918ShG1, Seg.Low.S221, Seg.Tors.E2_1_0, Seg.Full.S136) plus S108/S109,
    which are not in the seeded sample. Peaks 13.7–23.3 GiB, walls 97–210 s. None of the 8 has descendant
    modules.
  - **So the seeded sample is complete: 627/627 rc 0** (621 here plus 6 on lam), with S108 and S109 replayed in
    addition.
  - **Correction (audit-1).** `leanchecker <M>` without `--fresh` replays every module whose name has M as a prefix
    (LeanChecker.lean:109), not only M. The auditor therefore replayed leaf modules only, and elaborated GraphK and
    Seg.Checks from exact source copies.
  - **Counts.** 29 modules were outside AssemblyN65's closure before the 26 stale hubs were quarantined; 3 remain
    (ErrRadiusTbl, ExpSplit, SegRoutesProbe).
- **Audit-1 (codex-2):** PASS WITH NOTES, `LOCK-DATA-audit-1.md`. No mathematical, smuggling, codec or
  frozen-fit failure. The seal application of `lunar_sync_lock` elaborates with the standard three axioms. Phase B
  must also assign the headline provider and frozen anchor to KAMLunarLock (D51) before the provider imports
  AssemblyN65.

## 6. Deltas after the D70 run (each a frozen commit, re-checked on lam)

| Delta | Change |
|---|---|
| DELTA-LAM (01411a26) | lockM segment bridge; witness advice lookups |
| DELTA-LAM-2 (529f798c) | memo applications matched syntactically (maxRecDepth class) |
| DELTA-LAM-3 (679c1678) | data rows XOR-whitened (`ZCodeX`), because big literals with equal low 64 bits collide in the kernel's caches (`docs/explorations/lean-kernel-nat-literal-hash.md`) |
| DELTA-LAM-4 (e1e4aa85) | `Seg/Chain` length lemmas by `decide +kernel` (elaborator `rfl` hit maxRecDepth at 386 segments); `AssemblyN65` names `KAM.SpinOrbit.Lock.lockCentre` in full (Domain's data `lockCentre` shadowed it) |
| DELTA-LAM-5 (447772bf) | the frame checks one row/column and vertex per declaration (`CornerSplit`), because the stage coefficients are ≡ 0 mod 2^64 (same collision class) |

## 7. Design signals (no option raised anywhere)

1. The elaborator `rfl` on long lists hit maxRecDepth, so lengths and list facts go by `decide +kernel` (Chain,
   SegDecide, HamBalls).
2. The kernel's per-declaration caches degrade on big literals with equal low limbs (decoding intermediates and
   values ≡ 0 mod 2^64), so the data were whitened and the frame checks split (kernel note, census included).
3. Inline `none` decides and nested decides share one heartbeat budget, so every side check has its own theorem.
4. Memory: heavy segments need 18–25 GB (lam's 32G lanes); every local job stayed under 10G.

## 8. Errata and deviations

- **Errata in pinned sources:** none.
- **Deviations (reported earlier, unchanged):**
  - D1, the graph band literal: lo = 13155/1000000 (not 132/10000), through `lunar_sync_lock_of_barrier_check`. The
    headline literals are unchanged.
  - The packed-advice keys [7,1]/[7,2] are lock-owned copies of the landed graph check with the key as a parameter
    (`RealLowerK`, `GraphK`).
  - The lock data are untracked per-file links, transferred dereferenced.
  - `SegDecide`'s orphan instance.

## AUDIT FOCUS

1. **Seal fit.** `lunar_sync_lock_N65` plus the `FrozenBridge` equalities gives exactly the frozen `lunar_sync_lock`
   (binder order, literals 129/10000, 21/100, 26/1000, 1/4; `soField`; the frozen definitions).
   - Probe: `example : type_of% @KAM.SpinOrbit.lunar_sync_lock := by <bridges>; exact @lunar_sync_lock_N65`, in
     `.lake/abi-scratch/`. The frozen modules may need a light targeted build through
     `orchestrator-tools/inp_lake_build.sh`.
   - Check that the three `lunarSyncOrbit_*` providers (lockfreeze 41934621) prove exactly their frozen types.
2. **No smuggling.** The chain's only hypothesis is `h₀`. `lunar_sync_lock_of_barrier_check`'s premises are
   discharged by kernel facts. There are no conclusion-shaped hypotheses (AGENTS rule 6).
3. **Lock-owned lemmas.**
   - Soundness and statement intent of `CornerSplit`, `ZCodeX` (`zdecsX` = the original rows; checked in Python
     and by `decide +kernel` per family), `RealLowerK`/`GraphK` (copies of the landed graph check with the key as a
     parameter), `GraphChunk*`, `SegRoutes`, `MemoBridge`, `AdvLookupSub`, `DecSplit`, `RemSplit`.
   - The orphan `DecidableEq SlpOp`.
4. **Composition.** `lock_passes` covers every conjunct of `checkTorusCertificateV2 routeAV2` with the refined
   witness, and `lockGraph_passes` covers `checkSoGraphK`. The assembly uses only landed bridges.
5. **Hygiene.**
   - `#print axioms lunar_sync_lock_N65` and `lock_barrier`: the standard three. This needs the whole environment,
     about 6 GB.
   - No `sorry`/`axiom`/options in tracked or generated files.
   - Files ≤ 1500 lines and ≤ 100 columns.
   - Lint: only the root-parts item (the orchestrator regenerates them) and the ABI scratch gap
     (`KAM/Frozen/SpinOrbit/Defs/IsSyncOrbit.olean` is not built in this worktree).

## Orchestrator notes for the auditor

- **Replay scope.** `lake env leanchecker <Module>` replays only the listed modules' declarations.
  - Replay `AssemblyN65`, `Passes`, `CornerSplit`, `LockGraphK`, `ZCodeX`, and any other module you pick.
  - Run each one ALONE:
    `flock /mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock systemd-run --user --scope -p MemoryMax=10G -p MemorySwapMax=0 nice -n 10 …`.
    The lock is shared with the background sample replay of §5.
  - leanchecker does not walk symlinked module directories. Use
    `LEAN_PATH="$(lake env printenv LEAN_PATH):/mnt/HC_Volume_106379410/kam-data/so-lock/remote-20261105/lock/lib/lean"`
    (the returned directory LAST).
  - The whole chain was kernel-checked by the remote build; a full replay is out of scope.
- **Memory.** At most one lean/lake/leanchecker process at a time, every one capped at 10G. Never build a heavy data
  module.
