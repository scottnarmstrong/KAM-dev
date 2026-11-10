# LAM-REPLAY-1: independent kernel replay of the SJSU certificate (D76 seal follow-up)

Date: 2026-11-08. Host: the owner's 64-core workstation (128 threads, 251 GB), Lean v4.35.0 (`eb6cafb7`). Package:
`kam-data/sjsu-g2/replay-lam/` (the compiled `.olean` files of `inp-sjsu-g2` at `7cdc184ee`, sha256-pinned per file).
Tool: `leanchecker --verbose`, one process per module, each in its own memory scope with no swap.

## Result

| Set | Replayed and accepted | Not replayed | Kernel rejections |
|---|---|---|---|
| `KAMSJSU` modules outside the core replay (ledger data, checkers, Ham, the frozen anchor and provider) | 4,494 of 4,495 | 1 (`Ham.Hw`, memory) | 0 |
| the 131 submodules of `Ham.Hw`, one per process | 131 of 131 | 0 | 0 |

Combined with the local seal replay (core `--fast` 387/387 and 192 of 194 non-ledger modules, 2026-11-07), every
module of the sealed SJSU proof has been independently replayed by the kernel except the single parent module
`KAM.EffectiveStability.SJSU.Ham.Hw`:

> `Ham.Hw`: all 131 submodules independently kernel-replayed and accepted (131/131). The parent module was
> kernel-checked when it was built; its independent replay loads all 131 submodules into one process and needs more
> than 220 GB (killed at 220.78 GB, still growing about 1 GB/s; the children's peaks sum to 203.9 GB), so it was not
> completed.

## Run notes

- Main pass 10:24–14:09 UTC (four pool runs, 1.79 h wall, 11.2 CPU-h of module time). Largest ordinary module 2.63 GB.
- Three harness fixes during the run, all reported by the workstation agent: `lean` on PATH; a verdict rule that
  accepts a parent replaying its own submodules in any order; memory caps from completed runs, not from kill readings
  (`Ledger.F` needs 27.1 GB, `Ham.HtBridgeInst` 30.2 GB).
- Returned archives (verified: archive sha256, per-module olean sha256 against the package, verdicts re-derived
  locally with the final rule):
  - [`lam-replay/sjsu-replay-results-20261108-1410.tar.zst`](lam-replay/sjsu-replay-results-20261108-1410.tar.zst),
    sha256 `7c6a02ff073702127af3fda4ea506c1902ee165035738f2d2a63ed988ee2e554`;
  - [`lam-replay/hw-children-20261108-1416.tar.zst`](lam-replay/hw-children-20261108-1416.tar.zst),
    sha256 `42e4fc70cef7c566b2b097ef0f68221a1b398c0139af80380b627184d4d7a120`.
