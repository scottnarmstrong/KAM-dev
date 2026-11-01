# V2-PACKED profile: where certificate kernel time and memory go

Status: study (2026-11-01), brief V2-PACKED step 1. Read-only analysis of existing measurements; no new
certificate run. Companion: the design [`V2-PACKED.md`](../design/V2-PACKED.md).

**Sources.**
- LG00 at L = 20: the final shard-run ledger `run20e.tsv` (5,183 modules) and the generated theorem modules
  of branch `lg00-cert` (`KAM/LG00Cert/{Low,Full,Torsion,Gram}/T*.lean`, `Data/*.lean`), read in place.
  Handoff: `docs/campaign/handoffs/LG00-CERT.md` on that branch (pilot calibrations).
- SO lunar tori: [SO-CSPLIT](../../tracks/SO/design/SO-CSPLIT.md) and its measured
  [gate](../../tracks/SO/studies/SO-CSPLIT-GATE.md) (lower N = 65 torus); D52 and D55 for the lock.
- Kernel micro-costs: [SJS-FEAS §5](../../explorations/sjs-feasibility.md#5-kernel-arithmetic-brief-item-4)
  (`scripts/sjs/results/kernel_probes.md`).

**Reproduce.** `python3 scripts/packed/ledger_profile.py <run20e.tsv> <lg00-cert>/KAM/LG00Cert` prints
every LG00 number of §1.

## 0. Findings

1. **Packed products are about half of LG00's kernel time.** They take about 12.6 of 26.4 user hours
   (shard groups 6.1 h, decode chunks 4.5 h, heads/parts/assembly 0.8 h, witness residual products 1.2 h).
   **Per-coefficient model operations** (the regular compose segments) take 8.2 h, the import baseline 2.0 h,
   and data and ledger elaboration about 2.5 h.
2. **None of it is big-integer arithmetic.** LG00's 560 real packed products hold 1.05·10⁹ factor bits in
   total. At the measured kernel GMP rate of 6.6 ns per bit, every multiplication of the certificate together
   costs about **7 seconds**. The kernel spends about 11 hours around them: a ratio of about 5,000.
3. **The cost is interpretive overhead per element, times the number of passes.** The floor is 190 µs and
   21 kB to walk one literal list cell; 0.2–1.5 ms per packed, decoded or advice slot; 0.13–0.30 ms per
   backend call. Precision barely matters: 170-bit and 300-bit coefficients cost the same.
4. **Memory follows work, not data.** The kernel keeps every reduction of a declaration cached, at about
   0.08–0.13 GB per kernel second. This alone forces the split into thousands of modules (LG00: 5,183; ≤ 6.2 GB
   each), and each module pays its import baseline again.
5. **Consequence for the design.** As long as models are lists, every product boundary packs and decodes
   per slot: per element at least 0.2–1.5 ms, and every model operation is per coefficient. A faster packed
   product inside today's list interfaces can remove only the shard share (≈ 26 %). Orders of magnitude need
   models that **stay packed across operations** (GMP-resident). The segments then shrink too.

## 1. LG00 at L = 20 (one certified torus)

**Totals** (run20e, every module passing): 5,183 modules, **26.4 h user + 3.7 h system = 30.1 CPU-h**.
Max RSS 7.60 GB; max cgroup charge 6.39 GB (the one approved exception, `Low.T1898`). Every module ran at a
5,900 MiB cap, at most two at a time.

**By family** (user time; `T` = theorem modules, `L`/`V`/`D` = literal modules):

| family | modules | user h | % | max RSS GB | max charged GB |
|---|---:|---:|---:|---:|---:|
| `Low.T` (cfgLow chain: segments, products, witnesses) | 1,909 | 11.63 | 44.0 | 7.60 | 6.39 |
| `Full.T` (cfgFull chain) | 1,092 | 8.42 | 31.9 | 7.26 | 6.19 |
| `Torsion.T` (torsion stages: products) | 569 | 3.06 | 11.6 | 3.64 | 2.44 |
| `Data.A`, `Data.Leaves` (certificate literals) | 269 | 1.63 | 6.2 | 1.98 | 1.61 |
| `Low.L`, `Full.L` (ledger literals) | 923 | 0.81 | 3.1 | 1.60 | 0.58 |
| `Gram.T` | 81 | 0.36 | 1.3 | 3.45 | 2.28 |
| frames, balls, finals, the rest | 340 | 0.5 | 1.9 | 7.05 | 6.00 |

**By piece kind.** Each theorem module states its pieces (`Pieces:` docstring): `segment` (a regular compose
segment, ≤ 40 k backend calls and ≤ 150 operations), `group` (packed-product shard group), `chunk` (decode chunk
of 1,500 product slots), `head`/`part`/`product` (rest of a product), `residual` (a character-witness residual
product), and others. Below is a non-negative least-squares fit of module user time on piece counts, with the
import baseline fixed at 2.0 s per module (the import-only control of LG00 and SO). The fit has R² = 0.25,
because piece sizes vary widely; it attributes shares, not per-piece laws.

| piece | s each | count | user h | share of T-module time |
|---|---:|---:|---:|---:|
| `group` (shards) | 7.1 | 3,079 | 6.05 | 25.8 % |
| `chunk` (decode, 1,500 slots) | 5.5 | 2,996 | 4.54 | 19.4 % |
| `head` + `part` + `product` | 0.3–6.9 | 2,810 | 0.80 | 3.4 % |
| `residual` (witness products) | 45.7 | 95 | 1.21 | 5.1 % |
| **packed products, total** | | | **12.6** | **53.7 %** |
| `segment` (per-coefficient model ops) | 16.2 | 1,832 | 8.22 | 35.0 % |
| import baseline | 2.0 | 3,651 | 2.03 | 8.6 % |
| other (plan, entries, assembly) | | | 0.13 | 0.6 % |

**Model-free check.** In modules that hold a single kind of piece, a segment costs a median 18.9 s
(p10–p90 10.5–32.5 s). A shard group costs 11.7 s (7.3–20.6) and a decode chunk 6.1 s (5.1–8.2), i.e. about
4 ms per decoded slot. Those figures include the 2 s import.

**The products themselves** (census of the advice books, `Data/*.lean`):
- 560 real packed products (four real products per complex product, the zero ones omitted);
- dense factor lengths: median product 7,125 slots, largest 10,127 × 9,185 slots at 245 bits;
- slot widths 193–277 bits;
- 1.05·10⁹ factor bits and 4.1·10⁶ product slots in total.

Each product's kernel work is a constant number of passes over its slots:
- **pack** every block from its term list (balanced `spPack` tree, per term);
- **validate** every advice slot: `reconFitsAux`, `adviceZeroOK` with `inBox`, i.e. a mixed-radix `div`/`mod`
  digit test per slot;
- **decode** every window slot (`intSlotsBound`: mask/shift halving, then digit by digit against per-slot
  logs);
- **decode the target** (`targetTerms`: `zip`, `filterMap`, `prodKey` per slot; `dyadicTerms` per term);
- **sum the remainder** (`remainderBound`: per product slot `inBox`, `slotDeg` via `prodKey`, and
  `num^d den^(D-d)` powers, plus a `maxSlotDeg` pass).

The big-integer multiplications inside are negligible: 7 s for all 560 products at 6.6 ns per factor bit,
against ≈ 11 h of kernel time on the passes above.

**Segments** run the landed model algebra coefficient by coefficient on `CertFixed 128`: merges, `addC`/`mulC`
with error terms, `upMul`/`ofRatUp` of `w^{|k|₁}` weights, truncation, `toDeg` with rational `(2π)^e`
factors. The pilot calibrated this at 0.18–0.30 ms and 41–67 kB of kernel memory per backend call.

**Memory.** Kernel memory accumulates over the declarations of a module, at about 80 MB per kernel second
(LG00 T1). A regular segment's memory also grows with its program position (≈ 2.4 GB at the start, ≈ 5.3 GB
past slot 7,000). That is why segments are cut at 40 k calls and products are proved in shard groups,
decode chunks and heads. The cap, not the arithmetic, sets the module count.

## 2. SO lunar tori (SO-CSPLIT gate, lower N = 65 torus, `CertFixed 96`, L = 20)

| item | measured | per torus |
|---|---|---:|
| census call (segment work) | 0.125–0.131 ms, 11.8–14.8 kB | 6.9 M calls: 0.25 h |
| packed shard (1,312-slot windows, w = 207) | ≈ 3.9 s, 0.46 GB | 667 shards: 0.55–0.75 h |
| decode | ≈ 0.8 ms, 0.1 MB per target slot | 351 k slots: 0.08 h |
| fixed per theorem | ≈ 5 s wall | ≈ 380 theorems: 0.5 h |
| literal modules | ≈ 0.05 s per kB + 4.5 s per module | 0.3 h |
| **total** | | **1.6–2.5 CPU-h** |

- **Memory law:** 0.10–0.13 GB per user second (G2–G6).
- **The unsplit 503 × 503 product** `[0,10]`: 69 s and 9.89 GB when forced whole, against 3.84 GB for its
  7 shards alone. Proving it whole does not fit the cap.
- **Lock (SO-3, D52/D55):** about 21–22 CPU-h of kernel, 2–2.5 k modules and 150–200 MB of literals. Its
  models are 6.5× larger and its program 3.6× longer than the lunar tori's.

## 3. Kernel micro-costs (SJS-FEAS probes; machine load 12–14, ±30 %)

| operation | cost |
|---|---|
| walk one literal list cell | 190 µs, 21 kB |
| pack one factor term (sparse tree) | 1.25–1.48 ms, 260 kB |
| one advice slot (packed) / one decoded slot | 0.6–0.95 ms / 0.20–0.34 ms |
| per-coefficient model pass (`supNormUp`, `add`, `toDeg`) | 0.5–1.6 ms per term, linear |
| GMP `Nat.mul` in the kernel (4·10⁸-bit operands) | 6.6 ns per bit |
| GMP `Nat.add`, `&&&`, `>>>` | 4–17 ms per 10⁸ bits (0.04–0.17 ns per bit) |

Precision is nearly free; elements are not. A model operation done as one GMP operation on a packed integer
costs ns per coefficient instead of ms: a factor of 10⁴–10⁵ per element.

## 4. What this means for V2-PACKED

- **Ceiling of a product-only fix inside the landed list interfaces.** The landed product route takes and
  returns term lists, and its output (`targetTerms`, `remainderBound`) is defined by per-slot functions of list
  advice. A faster shard check can replace only the `group` share: ≈ 6 h of LG00's 26, at most ≈ 1.3×
  overall. Decodes and remainders stay per slot, because the consumers read lists.
- **Ceiling of GMP-resident models.** Products and segments become a constant number of GMP operations per
  model operation. The leftover is literal ingestion, one import per (much smaller) module, and the few
  scalar/rational steps (frames, `refinedCore`). The handoff `V2-PACKED.md` projects the resulting LG00 cost from the
  gate's measurement.
- **The gate must therefore measure both:**
  - the landed product (shards, decode, remainder) under the cap;
  - the packed product on the same operands, both from term lists (the boundary cost) and GMP-resident
    (packed literals in, packed literal out).
