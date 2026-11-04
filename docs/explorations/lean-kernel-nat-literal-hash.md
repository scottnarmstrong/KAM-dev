# Kernel slowdown from big `Nat` literals that share their low 64 bits

**Context:** the N = 65 lock data run (DELTA-LAM-3, 2026-11-04), Lean v4.35.0. This is a candidate for an upstream
performance report.

## Summary

Inside one declaration, the kernel slows down superlinearly when evaluation creates many distinct big `Nat` literals
(≥ 2^64) that share their low 64 bits. The measurements match literals being hashed by their low limb alone, so such
literals, and the expressions built over them, collide in the kernel's per-declaration caches. Every lookup then
walks a collision chain.

## Where it showed up

The lock's data rows are 40-byte literals, decoded by `zdecs` (`KAM/SpinOrbit/Data/LockN65/ZCode.lean`):
`zvar` walks n, n/256, n/256², …, so each row produces about 26 big intermediate literals.

Large fixed-point coefficients are stored as long runs of `0x80`, `0xff` and `0x00` bytes. In the 410 rows of one
ledger chunk (`lockL2037T.c0`), 10,536 intermediates have only 6,569 distinct low 64-bit limbs. The values
`0xffffffffffffffff` and `0x8080808080808080` alone occur 1,029 and 987 times.

## Measurements

All measured with `decide +kernel` in scratch files, no options set.

### Cost grows faster than the data

| Values decoded in one declaration | Kernel time |
|---|---|
| 900 | 2.0 s |
| 1,800 | 11.8 s |
| 3,600 | 62.7 s |

That is roughly n^2.5. Traversing the same data a second time in the same declaration is free, so the cache itself
works.

### The data, not the code, decides

| Rows (same sizes, same decoder) | Kernel time |
|---|---|
| The real 410 rows | 67.7 s |
| Random rows | 1.5 s |

Synthetic rows with random high bits and the same low 64 bits reproduce the slowdown (1.8 s for the `.2` walk
alone). The same synthetic rows with random low bits take under 0.05 s.

### Removing the collisions removes the slowdown

The same data were tried in two other storage forms:

| Storage form | Kernel time | Data layout |
|---|---|---|
| As 64-bit words (every literal below 2^64) | 2.2 s | changed |
| Each row's bytes XOR-whitened with a row-salted key stream (`ZCodeX.zdecsX`) | 3.2 s | unchanged |

### Effect on whole modules

| Module | Before | After whitening |
|---|---|---|
| Low.S62 | > 20 min | 151 s |
| Low.S281 | > 5 h on lam | 359 s |
| Decoding `lockM1900T` (Tors data) | 76.9 s | 3.6 s |

## Reproduction

The scratch files, prepared during the run, are:
- `rows0` with the original decoder, against `rowsRnd`;
- the synthetic rows that share their low 64 bits;
- the word and whitened variants.

The probe numbers are in `.drafts/PROGRESS.md` (DELTA-LAM-3).

A minimal upstream repro could look like this:

```lean
-- two lists of 2000 distinct big naturals; A shares its low 64 bits, B does not
def A : List ℕ := (List.range 2000).map fun i => (i + 1) * 2 ^ 64 + 0x8080808080808080
def B : List ℕ := (List.range 2000).map fun i => (i + 1) * 2 ^ 64 + i * 0x9E3779B97F4A7C15 % 2 ^ 64
-- then time `decide +kernel` of a property that forces many `/ 256` steps over each
```

## Mitigation used in the lock

`ZCodeX.zdecsX` (lock-owned): each stored byte is XOR-ed with a key of (salt, row, position), so the decoding
intermediates have pseudo-random low limbs.

The rows are kernel-checked equal to the original `zdecs` rows:
- over a whole ledger chunk, 410 rows;
- over one representative definition of each of 14 data families.

The data stay untrusted.
