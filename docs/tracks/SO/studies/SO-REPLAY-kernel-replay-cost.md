# Handoff SO-REPLAY (kernel replay-cost prototype, go/no-go gate)

Branch `inp-soreplay`, all committed (code under `KAM/Certificate/Prototype/`, not meant to land).
**Verdict: NO-GO for the naive sparse design at pilot scale; CONDITIONAL GO only with a redesign
(sharded Kronecker-packed products, see Recommendation). Measurements below are from a shared,
busy machine; wall times are noisy (±30%) and include ~5–8 s of import baseline.**

## Files
`Gen.lean` (terms, structural merge sort, strict folds, splitmix hash in Nat ops),
`Fixed.lean` (fixed-point Int, outward error `err : Nat` in ulps, multiplier `(k1 ν+k2)²` exact in ℚ(√5) with `S≈√5·2^P`
enclosure, weighted-ℓ¹ checker), `Exact.lean` (same over `Rat`), `Kron.lean` (blocked Kronecker-packed product),
`Bench.lean` (`soFpBench`/`soQpBench op S P`; op 0 gen+norm, 1 add, 2 product, 3 full checker, 4/5 packed
product/checker), `Replay.lean` (S=16 instances proved by `decide +kernel` + a `false` control).
Checker: `‖D²v + cs·(−i)(H − refl H)‖_w ≤ B`, `H = F·E` truncated to |k1|≤256, |k2|≤64, weights 1.032^|k|₁.
Data are generated inside Lean (hash PRNG), so no data shards were needed (all files <200 lines).

## Checks
- `lake build` through the gate of `KAM.Certificate.Prototype.Replay` (all 6 modules): success.
- `sh scripts/lint_sources.sh`: only message is "KAM.lean is out of date" (generated root; I may not edit it); other guards PASS.
- No maxHeartbeats/recursion overrides, no native_decide, no axiom; lines ≤100.
- `#print axioms`: soFpBench_replay, soKpBench_replay, soFpCheck_control: `[propext]`; soQpBench_replay:
  `[propext, Classical.choice, Quot.sound]` (from `Rat` lemmas). Control `soFpCheck … B:=1 = false` confirms non-vacuity.
- Correctness test (scratch, not committed): blocked Kronecker product equals sparse product at D=1 (S=20, L1 equal).
  Not tested: soundness of rounding/error accounting beyond design (benchmark data only, B is generous).

## Measurements (`/usr/bin/time -v`-style %e s / peak RSS, LEAN_NUM_THREADS=1, one `decide +kernel`)
Baseline (import + trivial): 6–8 s, 1.5 GB.

| op | rep | S | P | time s | RSS GB |
|---|---|---|---|---|---|
| gen+norm | Fp | 64 / 1024 / 4096 | 64 | 6.6 / 22 / 54 | 1.5 / 2.5 / 6.2 |
| gen+norm | Fp | 1024 / 4096 | 448 | 38 / 88 | 3.0 / 8.2 |
| gen+norm | Qp | 64 / 1024 / 4096 | 64 | 9 / 32 / 81 | 1.6 / 3.0 / 8.1 |
| gen+norm | Qp | 1024 / 4096 | 448 | 50 / 104 | 3.5 / 10.0 |
| add | Fp | 64 / 256 / 1024 / 4096 | 64 | 7.7 / 7.6 / 18 / 58 | 1.5 / 1.7 / 2.6 / 6.4 |
| add | Qp | 64 / 256 / 1024 / 4096 | 64 | 6 / 12 / 29 / 78 | 1.6 / 1.8 / 3.1 / 8.3 |
| add | Fp / Qp | 1024 | 448 | 38 / 54 | 3.1 / 3.5 |
| product | Fp | 64 | 64 / 256 / 448 | 15.5 / 12.1 / 14.1 | 2.2 / 2.2 / 2.2 |
| product | Fp | 128 / 256 | 64 | 41.9 / 156 | 4.4 / 12.4 |
| product | Qp | 64 | 64 / 256 / 448 | 29 / 21 / 29 | 3.0 |
| full check | Fp | 64 | 64 / 256 / 448 | 31.7 / 18.3 / 22.8 | 2.7 |
| full check | Qp | 64 | 64 / 256 / 448 | 68 / 49 / 49 | 4.2 |
| packed product (op 4) | Fp | 64 | 64 | 71 | 5.9 |

The S=128 Qp product, S=128 packed product and S=256 packed product hit `bad_alloc` under my `ulimit -v 14 GB`
(RSS 4.5–11 GB at abort; the limit is on virtual size, so these are NOT clean failure points). The S=256 Qp
product and the S=256 packed checker were killed by me to protect the shared machine. S=1024/4096 products were
not run (extrapolation below). Early S=4096 rows with rc=134 in my scratch log were `ulimit` artefacts; the clean
reruns are the 4096 rows above. Raw logs: scratchpad `results*.txt` (not committed).

## Scaling / extrapolation
- Product, sparse: time ≈ 2.3 ms per pair-term (156 s / 65 536), exactly quadratic (4× per doubling of S);
  memory ≈ 190 KB per pair-term (12.4 GB at S=256), also quadratic. Qp ≈ 2× Fp in time. Precision 64→448 bits has
  **no visible effect**: the cost is kernel interpretation, not bignum arithmetic.
- Linear ops (generate, add, norm): ≈ 12–15 ms per term at P=64 (≈ 20 ms at P=448), memory ≈ 1–2 MB per 1000 terms.
  Qp ≈ 1.4× Fp.
- Pilot scale: if each factor has S≈65 536 (512×128 grid), one sparse product is 4.3·10⁹ pairs ≈ 10⁷ s (≈ 115 days)
  and ~800 TB of kernel cache per product. Even S=4096 would be ≈ 16.8 M pairs ≈ 11 h and ≈ 3 TB. 10–30 products make this
  hopeless. The linear part (≈ 65 k terms × few ops ≈ 15 min, ~100 GB if in one declaration) is also over the memory budget in one declaration.
- Packed (Kronecker) product: cost is bounded by the box (65 k slots) not by S²: ≈ 70 s and 6 GB at S=64, P=64
  (dominated by the interpreted D&C unpack: ~2 M slot visits), growing slowly with S. It beats the sparse product from
  S ≈ 100–200 on, but still needs ≳ 10 GB per product in one declaration.

## Design signals (nothing overridden)
1. **Kernel laziness**: fold accumulators (`List.foldl`, Rat sums) become unevaluated chains and the kernel dies with
   `(kernel) deep recursion detected` at ~4 k terms. Fixed by strict folds forcing Nat/Int/Rat literals each step
   (`soNatWith`, `soFoldNat`, `soFoldQ`); fuel arguments are a big literal (2^40) so lists are never measured.
   `maxRecDepth` is not a kernel knob and is forbidden anyway.
2. **Memory is the binding resource**: the kernel caches every intermediate for the whole declaration, so memory ∝
   total work (≈190 KB/pair-term). One `decide +kernel` cannot exceed a few ×10⁷ elementary steps on this machine (~12 GB).
3. **Numeral size limit**: kernel refuses numerals above 2^24 bits (`LEAN_NAT_MAX_SIZE`, an environment variable, not a
   Lean option; 2^(2^24) passes, 2^(2^25) fails). Kronecker packing must be blocked so `w·2^Lb ≤ 2^24` (done: Lb=16 for P≤64,
   Lb=14 for P=448; 4 resp. 16 row blocks, 16 resp. 256 block pairs).
4. `decide`/`Nat.sqrt`-style wf recursion is avoided (own Newton with fuel); `Rat` ops reduce in the kernel but cost ≈ 2× Fp.

## Recommendation
- Representation: fixed-point `Int` with a global scale 2^P and a separate `Nat` error bound (≈2× cheaper than `Rat`, simpler
  error accounting); use Rat only at the interface (inputs/weights).
- The full 1e−103 certificate (≈ 10–30 products over ~65 k-term supports, 440-bit data) is **not feasible with the naive
  sparse convolution** and not within one kernel declaration with any representation tried here. Needed:
  (a) shard every product into many small `decide +kernel` theorems (block pairs as in `soKpPair`, each ≲ 2 GB and a few
  minutes), with partial results supplied as DATA (Lean literals, shard files < 1500 lines) and each shard checking
  `packed(advice) = packed(a)·packed(b)` (one GMP multiplication + `Nat.beq`, no unpacking, no rounding) — this removes the
  interpreted unpack, which dominated; (b) a final cheap theorem summing shard norms with weights; (c) keep the support
  as small as possible (lower precision and fewer retained modes cut the linear cost; precision itself is nearly free
  up to the 2^24-bit numeral cap, so choose w from the bound, not from cost).
- Comfortable target (my estimate, not measured): supports ≲ 4096 per factor, ≲ 450 bits, ≲ 30 products, each as ≲ 16
  advice-checked shards of ≲ 1.5 GB: tens of CPU-hours total, bounded memory. The advice-shard path was NOT prototyped
  (only the unpack-based product was), so its cost is a projection: the Nat.mul step is native, but generating the packed
  literals from the advice still costs ~10–15 ms per coefficient.
- Next step if SO continues: prototype advice-checked packed shards for one block pair at P=448 (measure; expect
  seconds) before committing to the architecture.

## Uncertainties / incidents / errata
- Timings noisy (shared machine, other jobs). Single run per cell.
- **Incident (mine):** while stopping my own benchmark loop I ran `pkill -x lean`, which signals every process named
  `lean` on the machine, possibly including other agents' builds; later I used PID-specific kills. If any other worker reports
  a sudden `Terminated`/rc=143 around 11:04 UTC on 2026-10-29, that was me.
- Packed product matches the sparse product only after rounding differences (sparse floors per pair; packed floors
  the exact sum); verified equal at D=1 only.
- No source errata found (the proposal was only used for the potential's role and ν±=1±(79−√5)/3118, derived from
  1/(40+g)=(79−√5)/3118; I did not check the §2.3 table against Celletti).
