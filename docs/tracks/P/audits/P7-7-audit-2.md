# P7-7 audit 2 — lint-only delta

**Overall package verdict: PASS, with the explicitly permitted stale generated-root exception.** Both assigned nodes, `bpP:p7:d25` (the dictionary API) and `bpP:p7:average`, PASS. The eight-line formatting finding H1 from [audit 1](P7-7-audit-1.md) is closed. The remaining stale `KAM.lean` message is the brief's allowed integration exception, not a new package defect. This package contains infrastructure theorems, not a frozen theorem/provider seal; no physical headline closure is claimed.

## Snapshot and delta

- Worktree: `/root/code/KAM-inp-p77`; date: 2026-10-28.
- Audited parent: `c526f74620570598b5e6d5d5579f3db4e0bcd8cd`.
- New HEAD: `50f8e8c4a287c8c1fa793a1e9cbe2da35077adb0`, `P7-7b: wrap long lines in D25`.
- Parent D25 SHA-256: `95532e7ca2a1544ca3a798f2db5f6de33a8a04cc9d9d65143e119c78f660cdf8`, exactly the audit-1 snapshot.
- New D25 SHA-256: `c04461efb630b0f0d3ac22c4ead217db563d20189db93eac1f2e141b09e7b690`.
- Audit-1 report SHA-256: `621bf73dc9853ed3249e50b7e2c3f699c37b2f7fc69a52dc911f3344a10774dd`.

`git diff HEAD^ HEAD` changes exactly `KAM/Planetary/Poincare/D25.lean`: 16 insertions and 8 deletions in eight wrapping hunks. I read the entire diff: comments, signatures and proof expressions are only reflowed. All non-whitespace bytes are identical. The working file matches the committed HEAD. The file grows from 331 to 339 lines, and its maximum Unicode line length is now 99.

Reproduction of the content checks (exit 0):

```python
import hashlib, re, subprocess
from pathlib import Path
p = 'KAM/Planetary/Poincare/D25.lean'
a = subprocess.check_output(['git', 'show', 'HEAD^:' + p])
b = subprocess.check_output(['git', 'show', 'HEAD:' + p])
assert hashlib.sha256(a).hexdigest() == (
    '95532e7ca2a1544ca3a798f2db5f6de33a8a04cc9d9d65143e119c78f660cdf8')
assert b == Path(p).read_bytes()
assert re.sub(rb'\s+', b'', a) == re.sub(rb'\s+', b'', b)
assert subprocess.check_output(
    ['git', 'diff', '--name-only', 'HEAD^', 'HEAD']).decode().splitlines() == [p]
assert max(map(len, b.decode().splitlines())) == 99
```

`git diff --check HEAD^ HEAD` exits 0 with no output. No frozen file, manifest, generated root, README, dependency or mathematical source changed. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` remains empty, with the same informational multiple-merge-base warning recorded in audit 1.

## Declaration and finding disposition

The source-facing binder/definition/proof audit in audit 1 carries forward because the entire module differs only in whitespace. No new `def`, `abbrev`, `structure`, assumption, declaration or import occurs. The previous counts remain TYPING=28, SOURCE=12, STANDING=10, RULED=0, EXCESS=0 for the ten source-facing signatures. No axiom census was rerun in this delta: audit 1 printed all 19 exports with exactly `[propext, Classical.choice, Quot.sound]`; this delta freshly rebuilds and kernel-replays the unchanged statements/proof text.

All names below have prefix `KAM.Planetary.`; locations refer to D25.lean at the new HEAD.

| Node / role | Declaration | Line | Verdict |
|---|---|---|---|
| `auxiliary` | `planetBlock_assemble` | 53 | PASS |
| `d25` | `secularGamma_eq` | 60 | PASS |
| `d25` | `secularRoot_eq` | 66 | PASS |
| `d25` | `secularEccVector_eq` | 71 | PASS |
| `d25` | `secularAxis_eq` | 76 | PASS |
| `auxiliary` | `poincare_block_eq_ellipse` | 81 | PASS |
| `d25` | `ellipsePhase_eq_poincareProd` | 99 | PASS |
| `d25` | `ellipsePhase_eq_poincareProd_self` | 125 | PASS |
| `d25` | `keplerFunctions_poincareProd` | 139 | PASS |
| `d25` | `exists_poincareProd_of_progradeElliptic` | 179 | PASS |
| `auxiliary` | `integral_via_keplerPhi` | 190 | PASS |
| `auxiliary` | `orbitalUnit_add_two_pi` | 210 | PASS |
| `auxiliary` | `ellipsePosition_add_two_pi` | 213 | PASS |
| `auxiliary` | `longitudeJacobian_add_two_pi` | 217 | PASS |
| `auxiliary` | `ellipseMomentum_add_two_pi` | 221 | PASS |
| `auxiliary` | `ellipsePhase_update_add_two_pi` | 225 | PASS |
| `auxiliary` | `continuous_assemble_update` | 243 | PASS |
| `average` | `average_via_eccentric_longitude` | 257 | PASS |
| `average` | `poincareProd_means` | 307 | PASS |

- **H1 CLOSED:** all eight formerly overlong lines are wrapped; no overlong-line lint diagnostic remains.
- **H2 ALLOWED:** stale generated `KAM.lean` remains for the orchestrator to regenerate.
- **N1 unchanged:** unused `hm` warnings at 99:54 and 125:59, and unused `hw` at 126:5. These are the same redundant design-signature premises from audit 1 and do not affect validity.
- Suspected new blueprint/pinned-source defects, semantic deviations or heartbeat/design signals: none.

## Fresh verification

The following commands ran **sequentially**, one Lean/lake/checker operation of this audit at a time, all with `LEAN_NUM_THREADS=1`. The compile-gate wrapper invokes `nice -n 5 lake build`; replay and lint inherit `nice -n 5`, including lint's ABI Lean subprocess. No clean, update or dependency-cache operation was run.

### Targeted build — exit 0

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p77 KAM.Planetary.Poincare.D25
```

Output includes:

```text
[inp-gate] slot 1 acquired 04:50:19 for KAM.Planetary.Poincare.D25
Build completed successfully (9117 jobs).
```

The only D25 warnings are the three unchanged unused-premise warnings above. No elaboration failure occurred.

### Kernel replay — exit 0

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Poincare.D25
```

Exact output:

```text
replaying KAM.Planetary.Poincare.D25
```

### Source lint

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, caused solely by the permitted stale generated-root message. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (397 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All other checks pass. There is no `Lean lines over 100 characters` diagnostic or other lint failure.

## Closeout

Audit 1's mathematical/source PASS is preserved; its additional lint failure is resolved. The package satisfies the requested delta checks, subject only to the explicitly permitted stale-root exception. The earlier package-decomposition and downstream-closure limits remain as stated in audit 1.

Only this report was written by the delta auditor; audit 1, the handoff and Lean sources were left unchanged. No probe file was needed or created for this delta.
