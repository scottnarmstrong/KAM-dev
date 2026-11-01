# V2-PACKED handoff: packed big-integer kernel arithmetic

Brief: `/home/scott/kam-tools/briefs/V2-PACKED.md` (improvement #5), rules `V2-COMMON-RULES.md`, including the
tightened rule of 2026-11-01: no existing `KAM/**.lean` edited, renamed or deleted. Branch `v2-packed` from
`origin/main` at `f80bdf6e`; local commits only.

## Result

- **Profile (step 1).** [`docs/campaign/studies/V2-PACKED-PROFILE.md`](../studies/V2-PACKED-PROFILE.md),
  reproducible by `scripts/packed/ledger_profile.py`. LG00 at L = 20 spends 26.4 user-h:
  - packed products ≈ 12.6 h: shards 6.1, decode chunks 4.5, heads and assembly 0.8, witness residual
    products 1.2;
  - per-coefficient model segments 8.2 h, import baseline 2.0 h, literal elaboration 2.4 h.

  The certificate's 560 real products hold 1.05·10⁹ factor bits: about **7 s of GMP multiplication**. The
  kernel time goes to interpretive overhead per slot and list cell, and the memory cap forces 5,183 modules.
- **Design (step 2).** [`docs/campaign/design/V2-PACKED.md`](../design/V2-PACKED.md) covers:
  - the representation: signed Kronecker packing on the landed layouts, load bounds, a shared fixed-point
    exponent, carries handled by injectivity, offset digits for masks;
  - guard rules for every operation;
  - advice-free rounding by mask and shift, with an a-priori error budget;
  - the exact correctness lemmas;
  - bridges B1 (prototyped) and B2 (planned packed `BaseChecker`);
  - the gate (§8). `V2-PACKED DESIGN READY` was printed at `ac3e6102`.
- **Prototype (step 3).** Five new modules in `KAM/CertificateSharp/Packed/` (1,014 lines), all main results on the
  standard axioms:
  - the packed product, its exact correctness (unpack ∘ product = convolution, under metadata guards);
  - advice-free round-to-nearest of every slot;
  - the strip contract **in the landed `packedRealProduct_sound` shape**;
  - the complex product **with the landed `CertPoly.mulPacked_sound` conclusion** (bridge B1).
- **Gate (step 4).** One LG00-sized product (8,134 product slots), under the same 4 GB cap on the cgroup
  charge (max RSS runs ≈ 1.2–1.3 GB higher):

  | route | kernel time | processes under the cap | soundness theorem |
  |---|---|---|---|
  | landed | ≈ 70 s; the one-piece decode and the whole product are OOM-killed at 4 GB | ≥ 7 | landed |
  | packed, lists in and out | 14.9 s, **4.7×** (upper estimate) | 1 | **bridged** (B1) |
  | GMP-resident, literal I/O included | 0.18–0.30 s, ≈ 235–380× | 1 (0.60 GB) | **unbridged** |
  | GMP-resident compute | 20–23 ms, ≥ 3,000× | — | **unbridged** |

  At LG00's largest size (19,311 slots) a single landed shard does not fit in 4 GB; the GMP-resident product
  takes 0.65 s and 0.90 GB with literals, 23 ms without (unbridged).
- **What is and is not covered by a theorem (audit AUDIT-V2-PACKED-1, M1/M2).**
  - Only the lists-in/lists-out route is bridged, by `gmpRealProduct_sound` and `CertPoly.mulGmp_sound`.
  - The GMP-resident rows measure checks that **no soundness theorem covers yet**. They require B2: a packed
    meaning of packed inputs and outputs (today `PRep` needs a term list `x` with `L.dense x = some d`),
    the inputs' `loadOk` checks (cheap, but not in the measured `Pcore`), and a packed consumer of the
    output.
  - The bridged route is **not a drop-in** either. The landed `CertModel.polyProduct` is hard-wired to
    `CertPoly.mulPacked` through the closed `ProductAdvice` (`direct` | `packed`), and both files are
    off-limits. Using `mulGmp` in a checker needs a parallel `polyProduct`/`mul`/evaluator/`BaseChecker`
    chain, which is B2's size.
  - Its 4.7× is an **upper estimate**: G8k's landed advice covers the whole window (`outLog 0`), which makes
    the landed decode (≈ 16 s of the ≈ 70 s) larger than for LG00's typical advice.

## V2-PACKED-MOVE (orchestrator, 2026-11-01)

The modules moved from `KAM/Certificate/Packed/` (the SO track's directory) to
`KAM/CertificateSharp/Packed/`, namespace `KAM.CertificateSharp.Packed`. They still import
`KAM.Certificate.*` modules read-only. The code is unchanged apart from the module names, the namespace and
the `open` lines; the roots were regenerated (`KAM/Root/Certificate.lean` is back to `main`'s content). All
five modules rebuild, and the axioms of the main results are unchanged (standard three; `natUnmask` only
`[propext, Quot.sound]`). The gate generator emits the new import and namespace. The probes were regenerated,
and `C19kCompute` and `G8kPcore` re-run green (24 ms, 0.22 s). The committed receipts predate the move (same
code); the JSONs' `probe_bytes` are refreshed.

## V2-PACKED-FIX (audit AUDIT-V2-PACKED-1: PASS WITH CHANGES)

- **M1/M2 (wording).** The gate rows and the LG00 lines now say which checks a soundness theorem covers
  (only lists in/out, B1) and which are unbridged (the GMP-resident rows: they need B2). B1 is stated to be
  **not a drop-in** (the landed `CertModel.polyProduct` is hard-wired to `mulPacked`), and its 4.7× an upper
  estimate. The same changes are in design §0, §4 and §8.
- **L1.** New `natUnmask : (a ^^^ r) ^^^ r = a` and `natRamp_eq : natRamp b n = natPack b ((range n).map
  (· + 1))` (`0 < b`), in `Round.lean`. The `natRamp` docstring now says that only distinct left spines get
  distinct low limbs (one spine's partial results share theirs; harmless) and that the mask does not affect
  soundness. A kernel test checks the unmask on a joined literal.
- **L2.** New `unpack_mul_eq_conv` (`Product.lean`): under the landed `convFits`,
  `unpackSlots w |conv| (packSum w a * packSum w b) = listConv a b`. This is the brief's unrounded
  "unpack ∘ packed product = coefficientwise product". The design's unproved `B/2^s + 1` load is replaced by
  the proved `2^l` (`roundSlot_abs_le`).
- **L3.** `G8k.json`/`G19k.json` regenerated: data fields identical, `probe_bytes` refreshed.
- **L4.** Memory figures are labelled as cgroup charge (max RSS ≈ 1.2–1.3 GB higher).
- **INFO.** Timings are given as ranges with the audit's re-run (`G8kPcore` 0.18–0.30 s).

## Files

| file | content |
|---|---|
| `KAM/CertificateSharp/Packed/Digits.lean` (new) | `natPack`, `periodic` (closed form), `land_split`, `natPack_land_mask`, `natPack_clear_shift`, `natPack_injective`, `natPack_digits`, `packSum_add_periodic` |
| `KAM/CertificateSharp/Packed/Round.lean` (new) | `digitShift`, `gmpRound`, `roundSlot`, `round_err`, `roundSlot_abs_le`, `gmpRound_spec`; `loadOk`, `loadOk_sound`; `natJoin`, `natRamp`, `natUnmask`, `natRamp_eq` (literal ingestion); `natDigitsSh`, `unpackSlots`, `unpackSlots_packSum` |
| `KAM/CertificateSharp/Packed/Product.lean` (new) | `PRep`, `packOf`, `packRepOk`, `packRepOk_sound`; `GmpSpec` (`guard`, `round`, `terms`, `degCap`, `rem`), `GmpSpec.round_spec`, `unpack_mul_eq_conv`, `intEval_gmpTerms`, `GmpSpec.round_sound`; `gmpRealProduct`, `gmpRealProduct_sound` |
| `KAM/CertificateSharp/Packed/Bridge.lean` (new) | `CertPoly.mulGmp`, `CertPoly.mulGmp_sound` |
| `KAM/CertificateSharp/Packed/Tests.lean` (new) | small `decide +kernel` tests (default build, about 1 s) |
| `KAM/Root/Certificate.lean` | generated by `scripts/gen_root_imports.py` (+5 imports) |
| `scripts/packed/ledger_profile.py` | the profile of step 1 |
| `scripts/packed/gate_gen.py`, `scripts/packed/run_probe.sh` | gate generator (landed advice from the landed mirror `sofx_packed.py`) and the capped one-process runner |
| `kernel-tests/Packed/README.md` | how to regenerate and run the gate (the probes are generated outside the sources: see Deviations) |
| `docs/campaign/studies/V2-PACKED-GATE/` | the receipts: `*.cost` (wall, user, sys, max RSS, sampled cgroup peak, OOM kills, exit), `*.out` (profiler, errors), `G8k.json`, `G19k.json` |
| `docs/campaign/studies/V2-PACKED-PROFILE.md`, `docs/campaign/design/V2-PACKED.md` | study and design |

**Compliance.** Relative to the branch point, the only `KAM/` changes are the five new modules and the generated
root: `git diff --name-status $(git merge-base HEAD origin/main) -- 'KAM/**'`. No existing `.lean` file was
edited, renamed or deleted. LG00 data were read in place on `lg00-cert`; nothing there was written.

## Approach

- **Reuse.** The prototype reuses:
  - `packSum`, `packSum_injective`, `packSum_listConv`, `abs_conv_entry_le` (`Poly/Packed`);
  - the layouts and `PackLayout.intEval_mul_of_compat` (`Poly/Layout`);
  - `spPack`, `packFill` and their lemmas (`Poly/Sparse`);
  - `toMants`, `dyadicTerms`, `ofDyadic` (`Poly/MulPacked`).

  The new parts are digit-wise mask arithmetic and what is built on it.
- **Rounding needs no advice.** Offset digits, one periodic mask, one subtraction, one shift and the offset
  removed give `⌊(d + 2^(s-1))/2^s⌋` in every slot exactly (`gmpRound_spec`). The error is ≤ `2^(s-1)` per slot.
- **The remainder is a-priori.** It is `prodLen · 2^(s-1) · w^degCap / 2^P2`, where `degCap` comes from the
  mixed-radix digit caps of the window and is computed from the layouts alone. On the gate it cost 3 bits of
  rounding shift against the landed box-adaptive remainder.
- **Bridge B1.** Two theorems have the landed conclusions word for word, with `2^s` for `2^scale`:
  - `gmpRealProduct_sound` (the landed `packedRealProduct_sound`);
  - `CertPoly.mulGmp_sound` (the landed `CertPoly.mulPacked_sound`, which `CertModel.polyProduct_sound`
    consumes).
- **Bridge B2 (design §4).** A future `packedBase : BaseChecker` proves the landed `BaseFacts`, so the landed
  `checkV2With_sound` gives the landed `CertifiedTorus`. This is not implemented; it is the large part.

## Checks and their output

- **Targeted builds**, each `nice -n 5 systemd-run --user --scope -p MemoryMax=4G … lake build
  KAM.CertificateSharp.Packed.<M>` for `Digits`, `Round`, `Product`, `Bridge`, `Tests`: `Build completed successfully`
  (2904 / 2905 / 2915 / 2916 / 2917 jobs). No warnings in the new modules.
- **`#print axioms`** (scratch file importing `KAM.CertificateSharp.Packed.Bridge`) gives
  `[propext, Classical.choice, Quot.sound]` for each of: `gmpRound_spec`, `loadOk_sound`,
  `unpackSlots_packSum`, `GmpSpec.round_spec`, `GmpSpec.round_sound`, `gmpRealProduct_sound`,
  `CertPoly.mulGmp_sound`, `packRepOk_sound`, `natPack_land_mask`, `natPack_clear_shift`,
  `intEval_gmpTerms`, and (V2-PACKED-FIX) `natRamp_eq`, `unpack_mul_eq_conv`; `natUnmask` uses only
  `[propext, Quot.sound]`.
- **`scripts/lint_sources.sh`** exits 1:
  - no line over 100 characters, no file over 1,500 lines;
  - `check_lean_modules: PASS (3666 Lean files…)`, `FROZEN-ANCHOR GUARD OK`;
  - the **ABI-hash step fails**: `object file …/KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean …
    does not exist`. This worktree's build snapshot lacks that frozen module and its `KAM.Planetary.*`
    dependencies. It is unrelated to this branch (no frozen or planetary file is touched); I did not rebuild
    that part of the library.
- **Not built:** the root part `KAM.Root.Certificate`. `lake build --no-build` lists 17 landed modules missing
  from this snapshot (e.g. `KAM.Certificate.Tests.Toy3Data`), so building it would compile unrelated landed
  modules. Every module it gains from this branch is built.

## Measurements

Full table: design §8. Receipts are in `docs/campaign/studies/V2-PACKED-GATE/`.

**Method.** Each forced `decide +kernel` theorem is alone in one Lean process under
`systemd-run --scope -p MemoryMax=4G -p MemorySwapMax=0`, `LEAN_NUM_THREADS=1`, `nice -n 5`. Kernel time is
the profiler's `type checking took …` of the theorem. Memory figures are the **cgroup charge**
(`memory.current` sampled every 0.2 s; this kernel has no `memory.peak`), not RSS: max RSS runs ≈ 1.2–1.3 GB
higher, from mmapped oleans already charged elsewhere. The machine load was about 20 on 16 cores, so
timings are ±30 %; the audit's re-run measured `G8kPcore` at 297 ms (184 ms here) and `C19kCompute` at
20 ms (23 ms here).

**G8k** (41 × 51 by 43 × 48 boxes, 8,134 product slots, width 263):

| piece | kernel | charged peak |
|---|---|---|
| landed shards | 11.2 / 9.5 / 8.9 s | 2.9 / 2.8 / 2.6 GB |
| landed prefix | 12.7 s | 3.6 GB |
| landed remainder | 11.0 s | 2.8 GB |
| landed decode, whole | OOM at 4 GB | — |
| landed decode, first 1,500 / 3,000 terms | 5.2 / 8.6 s | 1.8 / 2.7 GB |
| landed product, whole | OOM at 4 GB | — |
| packed boundary pack | 3.0 s | 1.1 GB |
| packed boundary decode | 12.4 s | 3.2 GB |
| packed a-priori remainder | 3.6 ms | 0.38 GB |
| `gmpRealProduct`, whole | 14.9 s | 3.7 GB |
| GMP-resident core | 0.18 s | 0.60 GB |
| literal ingestion alone | 0.24 s | 0.59 GB |

- The landed decode extrapolates at 2.3 ms and 0.58 MB per term to ≈ 16 s and ≈ 4.6 GB.
- Controls: import 1.25 s user and 0.40 GB.

**G19k** (LG00's largest product: 10,127 × 9,185 dense slots, 19,311 product slots, width 264):

| piece | kernel | charged peak |
|---|---|---|
| landed shard 0 | OOM at 4 GB | — |
| landed remainder | OOM at 4 GB | — |
| GMP-resident with literals | 0.65 s | 0.90 GB |
| literal ingestion alone | 0.58 s | — |
| `C19kCompute`: product + rounding + load check, operands built in the kernel | 23 ms | 0.38 GB |
| `C19kCompute10`: ten products | 183 ms | 0.43 GB |

**Output size.**
- Landed: advice windows 159 kB plus decoded terms 146 kB of source per real product.
- Packed: no advice. A packed output memo is 681 kB (all window slots at full width, guard bits included).
  Decoded terms are 152 kB.
- Inputs: zigzag term lists of 70 kB each, against packed literals of 300 and 317 kB.

**Literal ingestion** (micro-probes in the session scratchpad):
- 288-bit chunks: ≈ 16 µs kernel per chunk, 0.9–1.3 µs elaboration per bit, 36–85 B charged per bit.
- 256-kbit chunks (64 k-digit lines): 5.2 Mbit cost 5 ms of kernel and ≈ 6 B per bit, but 26.6 s of
  elaboration (the numeral parser is quadratic).

**Kernel hash finding.** `instance : Hashable Nat` is `hash n := UInt64.ofNat n`, so many big literals that
share their low 64 bits degrade the kernel's caches:
- 4,096 chunks: 37 ms with random low limbs, 20.8 s with zero low limbs;
- the gate's unmasked literals: 11.9 s, against 0.24 s after the `natRamp` XOR mask.

## What it means

**One LG00 torus** (26.4 user-h, 30.1 CPU-h, 5,183 modules):
- **Products, GMP-resident** (measured rates of **unbridged** checks; they become a certificate cost only
  once B2 supplies the packed meaning, the input `loadOk` checks and a packed consumer). 4.1 M product slots
  cost:
  - ≤ 5 s at the measured compute rate (≤ 1.2 µs per product slot);
  - ≤ 140 s if every product's operands and result were literals (34 µs per slot, G19k).

  With B2, products would fall from ≈ 12.6 h to ≤ 0.04 h.
- **Products, lists in and out (bridged, not a drop-in).** It measured 4.7× on products, an upper
  estimate. Using it at all needs a parallel model-algebra chain (`polyProduct`/`mul`/evaluator/
  `BaseChecker`), which is B2's size. Inside such a chain LG00 would go from 26.4 h to about 16.5 h at best
  (≤ 1.6×), with about 7× fewer product processes; the boundary decode then dominates.
- **The rest is untouched by the product alone:** 8.2 h of model segments, 2 h of imports, 2.4 h of literals.

  With B2 (packed models throughout; **projection, not measured**), each model operation is a few GMP
  primitives of the kind measured at ≤ 2–3 ms each at LG00 sizes. The ≈ 17 k model operations of both chains
  and the stages then take minutes, and boundary packing of the inputs (≈ 3·10⁴ terms at 0.9 ms) about 30 s.
  The unconverted parts (frames, `refinedCore`, Hamiltonian disc passes) cost ≈ 0.3 h in the ledger.

  One LG00 torus would then be **≈ 0.5–1 CPU-h instead of 30**, in tens rather than thousands of modules,
  and two LG00 tori a few CPU-h.
- **Conditions of the projection:** B2 implemented and audited, packed derivative ramps and weighted norms
  (designed, not prototyped), and literal I/O kept small.

**SJS** (SJS-FEAS: route B, GMP-resident, 34–351 CPU-h at an assumed 3.4·10⁻⁸ s per factor bit):
- **Arithmetic is not the obstacle.** The measured compute rate is 4.5·10⁻⁹ s per factor bit (23 ms for
  5.1 Mbit, rounding and load check included). This is below SJS-FEAS's model at the measured size; at 10⁹
  bits GMP's own 6.6 ns per bit applies. I did not measure beyond 5 Mbit operands.
- **The binding cost is literal I/O.** With 288-bit chunks, at the measured 36–47 B per literal bit, one 4 GB
  declaration ingests ≈ 75–100 Mbit. A route-B SJS factor (3.6·10⁶ slots × 212 bits ≈ 7.6·10⁸ bits) cannot be
  ingested in one declaration on this machine.
- **Long-line chunks** (≈ 6 B per bit; 5 µs per bit of parsing at 64 k digits, predicted ≈ 0.3 µs per bit at
  4 k digits from the quadratic law) would make one SJS factor ≈ 4.5 GB and a few hours of elaboration per
  input set. That is feasible on this machine, but needs an owner waiver (Q1).
- **The Lean hash hazard** must be avoided throughout (`natRamp`), or fixed upstream (Q3).

## Owner questions (overnight mode: none blocked work)

1. **Generated packed literals and the line/file caps.**
   - Should the 100-character line cap and the 1,500-line file cap be waived for *generated* packed-literal
     data modules (chunks of about 4 k hexadecimal digits)?
   - Measured: ≈ 6 B per bit instead of 36–85, and a thousandfold less kernel ingestion time.
   - Without a waiver, packed literals of more than about 0.4 Mbit cannot sit in one repository file. The gate
     probes therefore live outside the sources (Deviations). For SJS-size operands this is decisive.
2. **Commission B2?** A packed `BaseChecker`: the packed jet evaluator, Gram/torsion stages and frame inputs,
   with ramps, weighted norms and diamond truncation masks; ≈ 3–5 k lines plus an audit. Its statement interface
   is fixed by the landed `BaseChecker`/`checkV2With_sound`.
3. **Kernel hash hazard.** Report upstream that `Hashable Nat` uses only the low 64 bits and that this degrades
   kernel caches on big literals (minimal repro: the `mbN` probe, 4,096 chunks with zero low limbs, 20.8 s
   against 37 ms)? Meanwhile producers must mask.
4. **A home for generated probes and data.** The SO gates' `/mnt/HC_Volume_106379410/kam-data` does not exist on
   this machine. Mine are regenerable into `.lake/v2-packed-gate`.

## Deviations and uncertainties

- **Gate probes are not in `kernel-tests/`.** Their packed literals need one 288-bit chunk per line and so exceed
  the 1,500-line cap. `kernel-tests/Packed/README.md` and `scripts/packed/gate_gen.py` regenerate them
  deterministically (seeded; verified byte-identical on regeneration). Receipts are committed.
- **Synthetic data.** The coefficients are LG00-like (boxes, widths, `CertFixed 128`, decay), not LG00's own.
  - The landed advice's target box covered the whole window (`outLog 0`, scale 167), against LG00's typical
    scale ≈ 204 and smaller target box. The per-slot landed work (shards, `inBox`, decode, remainder) is the
    same kind, but the number of nonzero output terms differs.
- **The landed decode** was measured in prefixes (`take`), not by LG00's own `chunkOk` (branch `lg00-cert`).
  The whole-decode figure is a linear extrapolation that predicts the observed OOM.
- **Memory is a sampled `memory.current`** (0.2 s), so short spikes may be missed. OOM kills are exact.
- **The GMP-resident compute** was measured on constant-slot operands built in the kernel. GMP's cost does not
  depend on the digits, and the literal-ingesting probes on real data agree within ingestion cost.
- **Not prototyped:** packed truncation masks, absolute values, weighted norms, derivative ramps, chaining of
  packed outputs as next inputs (design §2; the "gap slots stay zero" invariant needs a box mask), and B2.
- **The a-priori remainder** is cruder than the landed box-adaptive one: 3 bits on the gate. Precision is cheap
  in the packed route.

## Suspected errata

None in pinned sources. One toolchain performance hazard (Q3, `Hashable Nat`) is reported above. It is not an
erratum of a pinned source.

V2-PACKED DONE
