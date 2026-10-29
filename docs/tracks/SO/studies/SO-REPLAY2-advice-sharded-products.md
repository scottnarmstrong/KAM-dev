# Handoff SO-REPLAY2 (advice-checked Kronecker-packed product shards)

Branch `inp-soreplay`, committed (prototype, not for landing). New: `KAM/Certificate/Prototype/Packed.lean` (177 lines),
`Replay2.lean` (tiny `decide +kernel` instances + controls), `scripts/so_replay2_gen.py` (shard-data generator from
`lower.json`). Scratch data/logs are in the session scratchpad (not committed; multi-MB).

## Verdict: GO (with the architecture below), data volume and elaboration are the real costs, not the kernel
Shard size recommendation: factor blocks of **32 rows x 256 stride = 8192 slots** (product window 16384 slots), slot
width **w = 896 bits** (2*440 + 16 guard/sign), real data (E_re of `lower.json`, 1e-130: 18683 terms, box 254 x 63).
The kernel numeral cap does NOT bind: only `Nat.pow` results are capped at 2^24 bits; `Nat.mul` results of 2^26 bits
passed (scratch `cap.lean`). So blocks are limited by memory/elaboration, not literal size.

## Design (sound, measured pieces)
- Signed packing as an Int `sum c_i 2^(w i)` (borrows between slots are harmless; injective on slots |c_i|<2^(w-1);
  real product slots <= 19k * 2^880 < 2^895). Built in the kernel from lists as separate positive/negative Nat parts with
  kernel-accelerated **shifts** (`soShLoop`); my first version used `a + b*2^k` (a full big multiplication per node) and was
  superlinear (whole-product shard >20 min and killed; with shifts 67 s).
- Shard = `sum_{i+j=s} pack(A_i) * pack(B_j) = pack(T_s)` (`soShardSum`/`soDotSum`): one Nat/Int multiplication per
  block pair (GMP), no unpacking. Advice = `T_s` (as rows of 256 zigzag `Nat` literals; `soZig`).
- Tie literal <-> coefficients: **pack-and-compare** (`soTiePack`) is the cheaper sound route; unpack-and-compare
  (`soTieUnpack`, list-based, mod/div) was ~4-10x costlier (r=32: A 7-9 s, C 21 s vs pack A 0.7-1 s, C 4-6 s, before the
  shift rewrite). Literals A_i/B_j can be given once per polynomial as chunk literals (2^14-bit chunks assembled by shifts,
  `soAsmS`) and tied once (`tie_A0`: 0.15-0.4 s per 8192-slot block), then every shard uses the literals.
- Remainder alternative ("design B": ship only the rounded in-box coefficients r, and check `A*B - 2^440 pack(r)` with
  `soIntSlotsBound`): `soIntSlotsBound` on a 16384-slot window costs ~2.5 s (pack 2.35 s) -- same order as packing; tiny
  instances in `Replay2.lean`. NOT run end-to-end with the rounding glue.

## Measurements (`decide +kernel`, LEAN_NUM_THREADS=1, ulimit -v <= 28 GB; machine load 5-17 on 8 cores, so +-30%; kernel time = Lean profiler "type checking took", RSS = /usr/bin/time peak incl. ~0.8-1.5 GB import baseline; data in an imported compiled module)
Shard sum over i+j=S at the middle output block, E*E, w=896 (before/after the shift rewrite where noted):
| block rows (slots/factor block) | pairs | list shard kernel s (pack all in kernel) | literal shard kernel s (A,B chunk literals; T from list) | RSS GB (list / literal) |
|---|---|---|---|---|
| 4 (1024) | 128 | 24-30 (old) / 12 (shifts) | 2.0-2.7 | 3.2 / 1.8 |
| 16 (4096) | 32 | 31-43 (old) / 14 (shifts) | 3.0-4.4 | 3.6 / 2.1 |
| 32 (8192) | 15 | 45-76 (old) / 16 (shifts) | 4.4-8.6 | 3.8 / 2.4 |
| whole polynomial, 512 rows (131072 slots, T=262144 slots, 233 Mbit) | 1 | 67 (shifts, one declaration) | - | 10.8 |
Other: tie of one 8192-slot literal 0.15-0.4 s; pack of a 16384-slot window ~2.4 s; slot-bound of one window ~2.5 s;
linear downstream pass (round/abs/sum over 16384 880-bit slots) 1.3 s (~80 us/slot); single multiplication check of
8192-slot literals ~0.2-0.5 s incl. assembly. Negative control (advice slot +2) returns `false`; no run exceeded 20 min
except the first (superlinear) whole-product attempt, which I stopped (my PID).
Elaboration (NOT kernel): a nested list literal of >= ~64 outer rows or >= ~4096 flat elements fails with
"maximum recursion depth" (elaborator) and a flat `def` of ~4k Int literals exceeds default heartbeats; `def` of data needs
`noncomputable def` (the compiler recurses too deeply); data must be split into <= 32-row groups, each its own def.
Hex literal parsing is quadratic (1 Mbit literal 45 s), so literals are chunked (2^14 bits). Data elaboration is ~18 s per
MB of source (9.4 MB whole-product data: 166 s, 6.4 GB) and dominates kernel time.

## Extrapolation to the full residual check (model, not measured end to end)
Per real product at 1e-130 with 16 x 16 blocks of 32 rows: 31 output shards, ~2-5 s kernel each (<= 2.4 GB literal /
3.8 GB list route) + ties 16 blocks x 0.4 s per polynomial => ~1.5-3 CPU-min kernel per real product.
Advice volume per product: design A (ship T_s, 880-bit slots, 260k slots) ~70 MB source text, ~20 min elaboration -- too big;
design B (ship rounded in-box r: 65k slots x 440 bits) ~8-9 MB decimal (7 MB hex), ~2.6 min elaboration, +~1 min kernel
for remainder bounds. With 30 real products: kernel ~0.75-1.5 CPU-h, elaboration ~1.3 CPU-h, ~260 MB of source (about
1700 files at the 1500-line/100-char limits -- a packaging problem to decide). 120 real products (complex x4): x4.
Peak memory per declaration <= ~4 GB with 32-row blocks (10.8 GB for a whole-polynomial shard).
Support shrink (model: per-slot cost 0.05+0.1*w/896 ms, box area ~ terms, w = 2*bits+16, bits ~ 440*digits/130):
| support | terms | w | slots/product (T) | kernel s per real product | per-shard memory |
|---|---|---|---|---|---|
| 1e-130 | 18.7k | 896 | 260k | ~90 (31 shards) | <= 2.4-3.8 GB |
| 10x fewer (~1e-48) | 1.9k | ~340 | 26k | ~5 (one shard) | < 1 GB |
| 100x fewer (~1e-14) | 190 | ~115 | 2.6k | < 0.5 | negligible |
(1e-110: 13.2k terms, ~70 s; 1e-60: 3.7k terms, ~10 s, whole-polynomial single shard ~1.5 GB.) Data volume scales with slots x bits, i.e. 10x support => ~25x less text.

## Uncertainties / not done
- Not done: Lean proof that `soPack` of rows equals the mathematical packing and injectivity (soundness lemmas), the slot-bound
  <-> rounding error glue, the end-to-end design-B shard, complex (re/im) products, the 128-row middle size (r=64/128 data
  generation/compile failed or was cut: nested-literal elaboration limit; not a kernel limit).
- Timings are single/double runs on a loaded shared machine; the "old vs shifts" rows were also taken at different load.
- Extrapolations to 100x-10x and to products-count are model estimates.
- Generated data files are not committed (multi-MB; lines >100 chars, would violate lint): the lint requires <=100 chars/line and
  <=1500 lines/file, so real shard data needs a chunked line format (or an out-of-tree data mechanism) -- design signal.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated root; I may not edit). Build of `Replay2` (and Packed) OK;
  `#print axioms` for tiny instances: [propext]. No maxHeartbeats/recursion overrides, no native_decide/axiom.

## Errata / deviations
No source errata. Machine etiquette: I started one stray `cat` waiting on stdin (killed by PID); no name-based kills this session.
