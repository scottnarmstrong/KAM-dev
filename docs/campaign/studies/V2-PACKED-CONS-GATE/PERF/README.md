# V2-PACKED-CONS-PERF: the two "slow" torsion assemblies of the T′ jet route

kamx-pk-gen's jet-route run on the integration branch (`v2-packed-gen-int`, log `runJ`; V2-PACKED-GEN handoff)
booked two assemblies at far more than their B3b counterparts:
- `LG00P.TP.PK.TorsJ.Core` (`pkTorsCoreJ := torsRCoreJ_of …`): 166 CPU-s;
- `LG00P.TP.PK.TorsJ` (`pkCheckTorsionJ := checkTorsionJ_of …`): 401 CPU-s;
- B3b's `Tors.Core` and `Asm.Tors`: 4.3 and 7.3 s.

**Finding: the assemblies are not slow.** Each costs 2–3.3 CPU-s, about the same as B3b's. The 166 and 401 CPU-s
are the cost of stale dependencies that the driver let Lake rebuild inside the assemblies' processes. No Lean
change is needed; the consumers are unchanged.

## 1. The assemblies alone (`alone/`)

Each source (`sources_sha256.txt`; copies of the packages' files, byte-identical) was elaborated by `lean` directly:
- against the packages' built oleans, read only (no Lake, nothing written into the packages);
- one process under the 4 GB cap, after the 20 GB anon wait (`scripts/packed/cons_perf_run.sh`), with
  `-Dprofiler=true`;
- in two interleaved passes, jet and B3b alternating.

| assembly | pass | user s | sys s | CPU s | import | elaboration | kernel | peak |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| jet `TorsJ.Core` | 1 | 1.42 | 0.87 | **2.29** | 3.35 s | 5.1 ms | 0.33 ms | 0.91 GB |
| | 2 | 1.40 | 1.05 | 2.45 | 3.38 s | 7.9 ms | 0.35 ms | 0.46 GB |
| B3b `Tors.Core` | 1 | 1.35 | 0.83 | **2.18** | 2.11 s | 7.1 ms | 0.26 ms | 0.35 GB |
| | 2 | 1.50 | 0.67 | 2.17 | 1.98 s | 5.2 ms | 0.35 ms | 0.33 GB |
| jet `TorsJ` | 1 | 1.63 | 1.68 | **3.31** | 8.47 s | 6.3 ms | 0.37 ms | 0.49 GB |
| | 2 | 1.43 | 0.64 | 2.07 | 1.95 s | 9.3 ms | 0.36 ms | 0.31 GB |
| B3b `Asm.Tors` | 1 | 1.55 | 0.88 | **2.43** | 2.48 s | 26.8 ms | 2.04 ms | 0.36 GB |
| | 2 | 1.66 | 0.91 | 2.57 | 2.41 s | 4.0 ms | 0.65 ms | 0.38 GB |

- Elaboration is under 30 ms and kernel checking under 3 ms everywhere. `torsRCoreJ_of` and `checkTorsionJ_of` (with
  the `rw [pkHamJet]`) unify each part with its hypothesis syntactically, so neither the elaborator nor the kernel
  unfolds `jetSlots`, the ledger or `lg00Ham_jet`.
- The rest is the import. `Core`'s is about 1.3 s longer on the jet (it imports the ledger and the fronts); `TorsJ`'s
  is about the same as B3b's (pass 2: 1.95 s against 2.41 s).
- Pass 1 of `TorsJ` read its imports from a cold page cache (8.5 s wall, of which 1.7 s system).
- Lake's own job times in `runJ` agree: `TorsJ.Core` 1.8 s and 1.3 s, `TorsJ` 1.4 s.

## 2. Where the 166 and 401 CPU-s went (`runJ/`, `attr_runJ.txt`)

`run_packed.py` (V2-PACKED-GEN) books each `lake build MODULE` process to MODULE. When it resumes, it skips every
module whose last ledger row passed and does not ask Lake whether that module is still up to date. Between the runs
of `runJ`:
- `gen_packed.py` re-emitted the stage modules twice (`v2-packed-gen` commit times, UTC):
  - between 16:50 and 17:30, for the front-loaded ledgers `jdLowW` (`f90db0447`, 16:58), `Data.Front`'s imports
    (`a78956b8a`, 17:00) and the jet literal `lg00Jet` (`931260a4e`, 17:27);
  - at 17:37, for `pkHamJet` (`0eb49ee32`) and `public import …RouteSharp` in every module (`b2a6d7c86`); the
    current sources are dated 17:37:29;
- the stages had passed before (from 16:50 on) and were skipped;
- the next target's `lake build` rebuilt them in its own capped process, and the ledger charged them to that target.

The `Built` lines of the two logs:
- `TorsJ.Core` (17:30–17:33): 17 jobs, 164.6 s. Its own job took 1.8 s; the other 16 (`StN`, `Pack`, `Lay`, `StDL`,
  `StDG`, `StC`, `StDGi`, eight `StDN_*`, `StDN`) took 162.8 s.
- `TorsJ` (17:37–17:44): 92 jobs, 386.4 s. Its own job took 1.4 s; the other 91 took 385.0 s: every packed data
  module, the Gram stage, the 16 D²K entries, the fronts, every torsion stage and `Core`.

`scripts/packed/cons_perf_attr.py` re-attributes the whole ledger. Pinned: `ledger.tsv` sha256 `4e878982…`,
587 rows, last written 21:15 UTC. The receipt `runJ/` holds the ledger and every log's `Built` lines, and replays to
the same output. Six rows built more than their target:

| row | CPU-s booked | own job | dependencies rebuilt | their job time |
|---|---:|---:|---:|---:|
| `PK.TorsJ.Core` | 166.0 | 1.8 s | 16 | 162.8 s |
| `PK.TorsJ` | 400.9 | 1.4 s | 91 | 385.0 s |
| `PK.InvJ` | 29.5 | 1.3 s | 9 | 24.3 s |
| `PK.FramesJ` | 18.1 | 1.5 s | 3 | 12.8 s |
| `PK.InvJ.FullOk` | 14.3 | 1.4 s | 3 | 9.7 s |
| `PK.EnJ` | 6.5 | 1.2 s | 1 | 2.1 s |
| **all** | | | **123** | **596.7 s** |

Per group (the V2-PACKED-GEN table's groups):
- **ledger:** user + sys of each module's last row, as `run_packed.py --summary` computes;
- **ledger − deps:** the same less the rebuilt dependencies' job time;
- **final:** each module's last build, by Lake's job time (no Lake start-up).

| group | rows | ledger | ledger − deps | final |
|---|---:|---:|---:|---:|
| torsion assemblies (`TorsJ.Core`, `TorsJ`) | 2 | 567.0 | **19.2** | 2.7 |
| torsion on the jet (stages, D²K, `LowOk`) | 46 | 423.6 | 423.6 | 244.3 |
| packed data and fronts | 38 | 255.5 | 255.5 | 109.2 |
| Gram (B2) | 10 | 76.3 | 76.3 | 40.7 |
| frames on the jet | 4 | 44.8 | 32.0 | 14.3 |
| invariance on the jet | 7 | 76.5 | 42.5 | 16.3 |
| energy on the jet | 2 | 12.5 | 10.4 | 3.3 |
| jet-route assemblies (`PK.Asm`, `PK.Xfer`, `MainJ`) | 5 | 33.1 | 33.1 | 12.7 |
| ported Hamiltonian balls | 65 | 363.8 | 363.8 | 250.1 |
| ported chain-free LG00 proof | 67 | 650.2 | 650.2 | 506.7 |
| **total** | 246 | **2,503.1** | **1,906.4** | 1,200.3 |

Reading:
- The ledger double-counts ≈ 597 s, 24 % of its total. In a single pass (generate once, then build), the route's
  ledger would read about 1,900 CPU-s. The stage rows hold their first builds, which were then re-emitted and
  rebuilt; they stand in for the rebuilds at about the same cost.
- `TorsJ`'s 19.2 s after the correction is still above the 3.3 s measured alone. The difference is Lake's start
  and trace check over about 3,900 jobs, plus 18 replayed logs, in one process.
- The "final" column is the Lean jobs alone. The gap between "ledger − deps" and "final" (≈ 2.9 s per row) is Lake's
  start-up per process.

## 3. The fix (kamx-pk-gen's driver; `run_packed_resume.patch`, tested in `drvtest.txt`)

The fix belongs to `run_packed.py` on `v2-packed-gen` (`305612780`). It is not applied here: that branch is read only
for this task. The patch makes two changes:
- **On resume,** it checks the passed modules with one batched `lake build --no-build` and bisects to the stale ones
  (the driver's own `no_build` and `stale_set`). Those modules leave `done` and are built in their own rows.
- **After each row,** it warns when the process built more than its target (for sources changed during a run).

`scripts/packed/cons_perf_drvtest.sh ORIG PATCHED WORKDIR` reproduces both behaviours on a toy package laid out as
V2-PACKED-GEN's (a core package, and a scratch package requiring it from `../..`):
- **Unpatched:** after A's source changes (a comment), resuming with target D skips A, and D's process builds A and D.
- **Patched:** resuming from the same ledger finds A, B and C stale again. A is built in its own row; B and C are
  checked in their own rows, found up to date (a comment does not change A's interface) and recorded as `reused`.
  E's process builds only E.

The patch adds one batched `--no-build` call per resume, a few seconds on `runJ`'s 566 modules.

## Reproduce

```
I=/home/scott/KAM-dev-worktrees/v2-packed-gen-int; G=/home/scott/KAM-dev-worktrees/v2-packed-gen
# copy <pkg>/LG00P/TP/PK/TorsJ/Core.lean to SRC/LG00P/TP/PK/TorsJ/Core.lean (and TorsJ.lean; B3b: LG00Packed/TP/…)
ROOT=SRC scripts/packed/cons_perf_run.sh 4G $I $I/.lake/lg00p SRC/LG00P/TP/PK/TorsJ/Core.lean CoreA LOGS \
  -Dprofiler=true -Dprofiler.threshold=50
ROOT=SRCB scripts/packed/cons_perf_run.sh 4G $G $G/.lake/lg00-packed SRCB/LG00Packed/TP/Tors/Core.lean CoreB LOGS \
  -Dprofiler=true -Dprofiler.threshold=50
python3 -I scripts/packed/cons_perf_attr.py docs/campaign/studies/V2-PACKED-CONS-GATE/PERF/runJ   # the receipt
scripts/packed/cons_perf_drvtest.sh $G/scripts/packed/run_packed.py PATCHED.py WORKDIR
```
