# Brief: build the KAM magnetic-barrier certificate chain on this workstation

**Reissue 3 (2026-11-09, after MAG-2).** Same flow. Since MAG-2: every consumer of a product equation now uses
the product's remainder bound as a literal, computed in 4,000-slot range modules (`M*RemR*`, measured ~100 s and
3.5 GB each here); the forced segments check their plan lookups by the kernel (no more recursion-depth failures);
M109's side checks are split per window; the pool admits modules on committed caps (no more over-commit) and runs
at most two 48 GB modules at once; `fetch` re-downloads stale small files. The 4,788 chain modules built so far ship
prebuilt (`unpack` overwrites the existing tree with identical files; stale ones from MAG-2 are rebuilt).

You are running one fully scripted batch job for the KAM Lean 4 formalization: Lake BUILDS about 1,020 generated Lean
modules (the certificate data of the magnetic field-line barrier, `KAM.Magnetic.Data`), one module per process, each
checked by Lean's kernel in its own memory scope. Everything is in `run_mag.sh`. Do not edit Lean files, change the
Lean version, or "fix" a failing module; report instead.

## Prerequisites (the owner)

- Tailscale is logged in on this machine with the same account as the KAM server `ubuntu-16gb-nbg1-1`. The package
  is served by the KAM orchestrator (default `BASE=http://100.124.142.13:8765/mag`; it tells you the URL).
- Root (`sudo -i`). The job uses `/root/xfer-mag` (download, size in SHA256SUMS), `/root/kam-mag`,
  `/root/kam-mag-packages`, `/root/kam-mag-chain` (~25 GB unpacked plus ~30-40 GB of build outputs).

## Steps

```bash
sudo -i
curl -sSfO $BASE/run_mag.sh
bash run_mag.sh setup      # apt, elan + Lean v4.35.0, systemd memory scopes for root
bash run_mag.sh fetch      # resumable; verifies SHA256SUMS
bash run_mag.sh unpack
bash run_mag.sh check      # must end with "check OK" (nothing rebuilt; builds ONE smoke module, ~1 min)
bash run_mag.sh run        # detached; LANES=20 by default
bash run_mag.sh status     # every 30-60 min; expected total 1.5-3 h
bash run_mag.sh return     # after `done ... fail=0 skip=0 todo=0`: packs the new oleans, sends them by Taildrop
```

## How it runs

- First 4 probe modules (the largest remainder-range module, one Full and one Low segment, product M109) at a
  48 GB cap. The other modules of a probed class start once ONE probe of the class has passed, at 1.3 x the largest
  COMPLETED probe peak (at least 5 GB). Other modules: 16 GB. A module killed at its cap is retried once at 48 GB.
  A probe that does not finish with rc 0 (killed, failed or timed out) stops the run with a `STOP:` line.
- Every module has a wall-clock limit of 1800 s (`MAG_TIMEOUT`; product assemblies `M<k>`: 5400 s): past it its build is killed and recorded as
  `rc=TIMEOUT` (not an OOM, no retry). Report any `rc=TIMEOUT`.
- A module starts only when all its imports are built, the caps of all running modules plus its own plus 16 GB fit
  in RAM (caps stay committed until a module exits), and its cap + 2 GB is available; at most 2 modules run at the
  48 GB cap at once. Do not raise
  LANES above 24.

## Rules

- **Stop and report** on any `STOP:` line, in particular if `check` says the shipped build is not up to date. Do not
  run `lake build KAM` or rebuild the core library or Mathlib.
- If `status` shows failures after the run ends, run `bash run_mag.sh run` once more (built modules are skipped in
  seconds). If they fail again, run `return` anyway and report the failing modules (`grep ' rc=[1-9k]'
  /root/kam-mag-chain/pool.out`).
- No other heavy jobs while it runs. Kill only by exact PID (`bash run_mag.sh stop`), never by name.

## Report back

The final `status` output, the `return` output (archive name, size, sha256), the wall time, and any failures. The
archive holds the built `.olean`/`.ilean`/`.ir`/`.c` files of every built module (with `sha256.txt`), `results-run.tsv`
(per module: rc, pass/fail, wall, peak bytes, cap, oom, attempt, olean sha256, lane), `pool.out` and `STATUS`.
