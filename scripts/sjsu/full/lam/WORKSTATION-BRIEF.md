# Brief: SJSU-FULL go/no-go gate computations on this workstation

You are running one fully scripted batch job for the KAM project: floating-point measurements (Python/numpy) of
normal-form remainders for the planar Sun–Jupiter–Saturn–Uranus problem (gates G1, G3 and a G6 confirmation), and
one throwaway Lean measurement (G5: the same packed product checked by the Lean kernel, by `native_decide` and by
a compiled executable). Nothing of the KAM library is built; the Lean part is a 200-line core-only scratch
package. Everything is in `run.sh`. Do not edit or rebuild anything by hand and do not "fix" a failing job;
report it instead.

## Prerequisites

- Tailscale logged in with the same account as the KAM server `ubuntu-16gb-nbg1-1`; the package is served at
  `http://100.124.142.13:8765/` (kam-bb gives the exact URL if it differs; then `export BASE=...`).
- Root (`sudo -i`). Disk: ~0.5 GB download and unpacked data, a few hundred MB of results.
- Lean v4.35.0 under `/root/.elan` (already installed by the earlier SJSU replay; `setup` installs it otherwise).

## Steps

```bash
sudo -i
curl -sSfO http://100.124.142.13:8765/run.sh
bash run.sh setup      # apt (python3-venv, zstd, time), venv with numpy 2.2.6 + mpmath 1.3.0, Lean check, scopes
bash run.sh fetch      # downloads and verifies SHA256SUMS
bash run.sh unpack     # unpacks, builds the G5 scratch package (lake build: one small module + one executable)
bash run.sh check      # smoke tests against shipped reference outputs, ~2 min; must end with "check OK"
bash run.sh run        # detached pool
bash run.sh status     # every 30-60 min
bash run.sh return     # after "done pass=N not_passed=0": packs results and sends them by Taildrop
```

## What runs, cost and memory

| Jobs | What | Count | Memory cap each | Expected time each |
|---|---|---:|---:|---|
| `g1c_*`, `g3c_*` | grid-convergence checks at the nominal point and point 0 | 4 | 100–110 GB | 1–3 h |
| `g1_*` | G1: Stage-I ladder to order 5 at one slow point (64×64×32 grid) | 57 | 32 GB (48 GB for 2 with census) | 10–20 min |
| `g3_*` | G3: Stage-I order 3 + Stage-II ladder to order 6 at one slow point (48×48×24) | 57 | 44 GB | 15–30 min |
| `g6_*` | G6: averaged secular Hamiltonian at mass order 2–4 to eccentricity degree 6–10 | 4 | 32 GB | 0.5–8 h |
| `g5k_*`, `g5n_*` | G5: one Lean file per product block, kernel (`decide +kernel`) / `native_decide` | 91 + 91 | 48 / 24 GB | ~0.5–5 min |
| `g5exe` | G5: the compiled checker on all 91 blocks | 1 | 32 GB | minutes |

Total about 40–50 CPU-hours; the memory caps of running jobs are limited to `BUDGET_GB=230` (sum of caps) and at
most `LANES=24` jobs, so the wall time is about 4–8 h. The caps are 1.5–2× peaks extrapolated from small local
runs; each job's real peak is recorded. Python jobs are single-threaded.

## Rules

- **Stop and report** on any `STOP:` line. Do not edit files, do not run `lake` yourself, do not raise the caps.
- If `status` lists failed jobs after the pool ends, run `bash run.sh run` once more (passed jobs are skipped). If
  they fail again (for instance a memory-cap kill, `rc` 137 or a `systemd` OOM), run `return` anyway and report the
  failing job ids and their `log/<id>.err`.
- Leave the machine otherwise alone while it runs. To stop early: `bash run.sh stop` (kills the exact pool PID,
  which stops its jobs by their exact process groups). Never kill by process name.

## Report back

The final `status` output, the `return` output (archive name, size, sha256), and any failures. The archive holds
`res/<job>.json` (rc, verdict, wall time, peak RSS), `out/` (the measurement JSON files), `log/` (stdout/stderr of
every job, including Lean's profiler lines), `smoke/` and `RETURN-MANIFEST.txt`.
