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

### A second case: the values themselves (DELTA-LAM-5)

Whitening fixes the decoding intermediates, not the decoded values. The lock's stage models (the torsion matrix
`T`, the frame matrix `N`, the Gram and DG families) were computed at about 45-bit precision and stored as
fixed-point mantissas at `P = 112`, so every big coefficient is a multiple of `2 ^ 64`.

| Family | Big coefficients | Low 64 bits = 0 |
|---|---|---|
| lockTb (5151 terms) | 5123 | 100% |
| lockN0 (8537 terms) | 8519 | 100% |
| lockBG*, lockDG*, lockDGi*, lockDN*, lockGE*, lockTGi | all | 100% |
| lockY, lockTL, lockTDL, lockXN1 | | 0% |

The frame checks sum, at every vertex `l` of `signLists 2`, `normUp c · expUb(dot k l)` over every term. Each
`|re| + |im|` and each product with an exponential bound is again a multiple of `2 ^ 64`, so a single
`decide +kernel` creates tens of thousands of distinct literals with the same low limb.

Measured on exact copies of the whitened data (10G scope, walls with about 6 s of import loading):

| One declaration | Wall |
|---|---|
| 1 model × 1 vertex | 23 s |
| 1 model × 4 vertices | 35 s |
| 2 models × 1 vertex | 65 s |
| 2 models × 2 vertices | 226 s |
| the same, with the coefficients' low bits randomized | 23 s |
| 2 models × 4 vertices (one row of `checkFrameT`) | > 600 s |
| all of `checkFrameT` (2 rows) | > 1500 s |

The cost grows superlinearly with the number of colliding literals per declaration. That is the signature of the
same low-limb hashing, now on values that are legitimately equal mod `2 ^ 64`.

**Mitigation used:** one declaration per row (or column) and vertex. Kernel caches are per declaration, so each
stays small. `LockN65/CornerSplit.lean` reassembles the per-vertex facts into `rowCornerLeq` and the `List.all`
over rows; no data or arithmetic changes.

**For an upstream report:** a hash over all limbs (or a mix of the low and high limbs) of big `Nat` literals would
remove both cases. Multiples of a large power of two arise naturally in fixed-point data of lower precision than
its storage format.

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
