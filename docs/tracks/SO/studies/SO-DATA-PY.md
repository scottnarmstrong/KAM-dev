# SO-DATA-PY: the advice emitter for the lunar certificate (track SO, Python part of SO-DATA)

Branch `inp-sodatapy`. This package is Python and generated data only. No hand-written Lean is in `KAM/`, and no
generated Lean is committed. Inputs are design Revision 7 (`docs/tracks/SO/design/SO-LEAN-DESIGN.md`, §5, §6,
§7, §7.2), the signatures `.drafts/design/SOSignatures.lean` and `SOSignaturesLunar.lean`, the landed
`KAM/Certificate/Poly/Packed.lean` (SO-POLY-A), SO-GEN2's R1 data, and SO-ADVCOUNT's recorded pipeline.

## Verdict

The generator side of SO-DATA is ready before the Lean checker exists.

- **Every product the Revision 7 checker performs is enumerated and given its advice.** There are 148 recorded
  products per torus. 128 are genuine and get `ProductAdvice.packed P rr ii ri ir`. The other 20 have a scalar
  or empty factor and get `ProductAdvice.direct`.
- **The advice is in the exact `PackedAdvice` layout.** That means the factor layouts, the target box,
  `scale ≥ 1`, `outLog` and the rounded windows of `2·blockLen − 1` slots, with zeros off the box.
- **The Python mirror of the checker passes all of it, for both tori.** Each of the 4 × 128 real products per
  torus passes `checkPackedProduct`: `shapeOK`, the F14 raw lengths, the shard count, and on every shard the block
  and window lengths, `shardFits`, `reconFits` and `intSlotsBound`. Each also satisfies the conclusion of
  `checkPackedProduct_sound`, tested directly on the exact convolution.
- **Corrupted advice fails.** 2,268 corruptions per torus are rejected. The design's §8 negative tests (audit 5's
  carry cancel, scale 0, the F14 alias `[0]` vs `[0, 0]`) are reproduced and rejected.
- **The option-A Lean data for the lower torus is emitted.** It is 31 modules and 2.70 MB, at most 1,401 lines
  and at most 100 columns per file. The largest literal is 80 characters.
- **The modules elaborate.** In a scratch build against a verbatim stand-in of the §B′ types, all 31 elaborate at
  default settings. The kernel decodes real advice windows, and their lengths and checksums equal the Python
  advice (§5).
- **Everything is deterministic.** A rerun reproduces the recorded factors, the advice JSON and the Lean tree byte
  for byte (§6).

**The main caveat.** The advice is computed against SO-GEN2's Python pipeline (`rot_build` / `rot_norms`), which
stands in for the checker's own factor values. Until SO-MALG, SO-EMB and SO-TORS fix the Lean model arithmetic
(rounding, trimming, product order), those values are not guaranteed bit-exact with the Lean checker. The emitter
is parametric in the factors. Once a bit-exact mirror of the Lean model operations exists, only step 1 changes.

## 1. Pipeline (`scripts/spin_orbit/sodata_*.py`)

| Step | Script | What it does |
|---|---|---|
| 0 | `sodata_test.py` | Unit tests of the mirror and the builder (seeded; < 2 s) |
| 1 | `sodata_record.py which REC.json` | Reruns SO-ADVCOUNT's recorded pipeline: `rot_build.build(which, 88, 88, 88, 318)`, checked against `<which>_rot.json`, then `rot_norms.norms`, then the `checkSoGraph` SOS witnesses. Writes every product with its factors and a `ProductKey` (≈ 40 s). |
| 2 | `sodata_emit.py REC.json ADV.json` | Builds and verifies every product's advice and runs the negative tests. Writes the advice book as deterministic JSON plus `_stats.json` (≈ 8.5 min per torus; the 3 full products take ≈ 2.5–3 min each). |
| 3 | `sodata_lean.py ADV.json OUTDIR` | Writes the option-A Lean data modules (< 1 s) |

The modules are:
- `sodata_packed.py`: the Python mirror of A-E §B′. It has one function per Lean declaration, named after it.
- `sodata_advice.py`: the advice builder.

### 1.1 Mirror of the checks and the bodies it assumes (for SO-POLY-B)

**Mirrored literally (landed).** These are `packSum`, `packShift`, `listConv`, `maxAbs`, `slotRep` and
`intSlotsBound`. The big cases use a fast balanced-digit decoder instead of the landed loop. It is equal to the
literal loop on 3,000 random cases, including out-of-range digits and nonzero leftovers.

**Mirrored from the signature.** These are `reconFits`, `reconSlots`, `prodLen` and `denseLen` (Revision 7).

**Bodies that are still `sorry` in the signatures.** The emitter follows the docstrings, made precise as below.
SO-POLY-B should adopt these readings, or tell SO-DATA where it differs. Each one is a single function in
`sodata_packed.py`.

| Declaration | Reading used |
|---|---|
| `PackLayout.slot` | `Σ_j (k_j − lo_j) stride_j` if `k` has `n` coordinates and `lo ≤ k < lo + dims`, else `none` |
| `PackLayout.dense` | `none` on an out-of-box key; repeated keys add (docstring). The variant that skips zero entries is used only by the non-default `minimal` policy (§3). |
| `PackLayout.prodKey La Lb i` | `La.lo + Lb.lo + digits(i)`, greedy mixed-radix digits by the shared strides (`d₀ = i / stride₀`, `d₁ = (i % stride₀) / stride₁`, …) |
| `PackLayout.compat n La Lb` | All lists have length `n`; equal strides and widths; every extent `≥ 1`; last stride `1`; for each `j < n − 1`, `stride_j > Σ_{j'>j} (dimsA_{j'} + dimsB_{j'} − 2) stride_{j'}` (for `n = 2`: `stride₀ ≥ colsA + colsB − 1`) |
| `PackedAdvice.blockLen` | `la.blockRows * la.stride.headD 1` (32 rows of the leading axis) |
| `PackedAdvice.cut` | Blocks of `blockLen`, the last one zero-padded |
| `shardConv`, `shardFits` | The docstrings. `shardFits` is `2·(s+1)·L·maxAbs(A.flatten)·maxAbs(B.flatten) < 2^w`. |
| `PackedAdvice.inBox i` | `i < prodLen ∧ prodKey la lb i ∈ target box` |
| `PackedAdvice.shardLogs s i` | `if inBox (s·blockLen + i) then scale − 1 else outLog` |
| `PackedAdvice.combined` | Overlap-add at offsets `s·blockLen`, zero-extended, `take prodLen` |
| `PackedAdvice.shapeOK` | `1 ≤ scale`; `0 < la.width`; `0 < la.blockRows = lb.blockRows`; `compat`; equal widths of `la`, `lb`, `target`; `target` has `n` axes and is a sub-box of the product window; `0 < blockLen`; window lengths `2·blockLen − 1`; advice zero on every non-`inBox` slot. The target's own stride and `blockRows` are not used. |
| `checkShard`, `checkPackedProduct` | The docstrings, in that guard order. The shard sum uses `getD`, so missing blocks are zero. |

### 1.2 Advice choices (the generator's freedom)

Each real product gets the following.
- **Layouts.** Each factor is laid out on its key box, with rows on the first key coordinate, the no-wrap stride
  `colsA + colsB − 1` and `blockRows = 32`.
- **Mantissa scale.** `P = max(SA, SB)`, raised by 8 at a time if a budget falls below the resolution
  `2^(1−2P)`. This never happened on the lunar data.
- **Target box and `outLog`.** These are the smallest whose out-of-box remainder
  `2^(outLog+1−2P) Σ_{non-box slots} W(|k|₁)` is at most half the budget. `W ≥ e^{2πρ|k|}` on `T_{1/70}`, the
  integer table of `rotlib`.
- **`scale`.** The largest one (≥ 1) whose in-box remainder `2^(scale−2P) Σ_box W` is at most half the budget.
- **Advice.** `r_s = round(T_s / 2^scale)` on the in-box window slots, and 0 elsewhere.
- **Width.** The least `w` with every `shardFits` and every `reconFits`.

The budgets are SO-ADVCOUNT's: 1e-80 for the full-precision products and 1e-13 for cfgLow and graph.

### 1.3 Product keys (PROPOSED)

`ProductKey = [site, sub, ordinal]`, with A-E's site codes:
- `[0, 10]`: the energy compose, SLP slot 10 `(A0*A0)`, which is the only MM slot of the jet (`adv_jet.py`);
- `[1, 0, j]`: the exp-witness residuals `(∂_j g₀)·E`;
- `[3, 0|1, o]`: Gram `DKᵀDK` and `B·G`;
- `[4, sub, o]`: torsion, `sub` numbering the nine call sites in order;
- `[7, side, 0]`: the SOS products.

The products sit in three books: `full` (cfgFull), `low` (cfgLow) and `graph`. Keys are unique (asserted). They
are the order of the Python mirror's calls. SO-MALG, SO-EMB and SO-TORS fix the real call-site keys, and then only
the `KEY_SITE` table in `sodata_record.py` changes.

## 2. Results (both tori; per torus, lower / upper)

| | lower | upper |
|---|---:|---:|
| recorded products: packed / direct (scalar 4, empty 16) | 128 / 20 | 128 / 20 |
| real products checked by the mirror (4 per packed product) | 512 | 512 |
| of which nonzero (exactly one per product, by parity) | 128 | 128 |
| nonzero-part shards (`checkShard` theorems) | 465 | 467 |
| block-pair multiplications in them | 978 | 982 |
| zero-part shards (`support` policy, all-zero windows, `w = 2`) | 1,395 | 1,401 |
| nonzero advice slots | 140,905 | 143,129 |
| largest packed-remainder of a full product (in + out) | 4.2e-81 | 5.5e-81 |
| corruptions rejected | 2,268 | 2,268 |
| advice JSON SHA-256 | `66fab530…` | `cd133617…` |

**Full-precision products (lower).**

| Product | `P` | `w` | shards | `blockLen` | `scale` | `outLog` | nonzero advice | remainder | time |
|---|---:|---:|---:|---:|---:|---:|---:|---|---:|
| energy `p̃·p̃` `[0, 10]` | 319 | 656 | 23 | 5,664 | 327 | 298 | 19,406 | 2.8e-81 + 9.8e-83 | 183 s |
| witness `[1, 0, 0]` | 319 | 654 | 23 | 5,664 | 326 | 298 | 19,673 | 2.9e-81 + 9.6e-83 | 150 s |
| witness `[1, 0, 1]` | 319 | 641 | 23 | 5,632 | 327 | 299 | 19,347 | 4.0e-81 + 1.9e-82 | 151 s |

The result mantissas are at `2^−(2P−scale) = 2^−311`. SO-ADVCOUNT's simulation agrees to within 2 bits of width
(it had `w = 654`, scale 327, outLog 298). **`P = 319 ≤ soPrecision = 320`.** The cfgLow products have
`P = 72`, `w` 83–158 and 1–5 shards. The SOS products have `P = 40`.

**Per-family table (lower).** "Shards" counts the nonzero part only.

| Family | n | shards | pairs | max `w` | nonzero advice |
|---|---:|---:|---:|---:|---:|
| energy `p̃·p̃` | 1 | 23 | 144 | 656 | 19,406 |
| exp-witness residual | 2 | 46 | 288 | 654 | 39,020 |
| Gram `DKᵀDK` | 9 | 27 | 36 | 157 | 4,886 |
| Gram `B·G` | 8 | 28 | 41 | 158 | 4,792 |
| torsion N | 12 | 36 | 48 | 157 | 6,793 |
| torsion DG | 24 | 72 | 96 | 153 | 15,406 |
| torsion D(G⁻¹) | 16 | 52 | 72 | 154 | 11,752 |
| torsion DN | 24 | 75 | 102 | 154 | 17,156 |
| torsion `V_QQ·N` | 8 | 26 | 36 | 147 | 5,490 |
| torsion `Nᵀ Ω W` | 16 | 56 | 82 | 158 | 12,402 |
| torsion `DH(K)·N` | 6 | 20 | 28 | 152 | 3,623 |
| SOS `g·g*` | 2 | 4 | 5 | 83 | 179 |

## 3. Zero re/im parts and the empty-factor policy (design signal)

Revision 7 rejects empty raw factors. The signatures' `toMants` and `dense` keep every key, so a zero real part
is laid out on the polynomial's own key box with all-zero slots. This is the default `support` policy. Each such
product has:
- a one-slot target, `scale = 1`, `outLog = 0` and `w = 2`;
- all-zero windows, emitted as `List.replicate (2L−1) 0`;
- the same shard count as its nonzero sibling.

This adds **1,395 / 1,401 cheap shard theorems per torus**: each multiplies zeros and decodes a window of
zero 2-bit slots. The cost is the design's "×4 shard theorems", but not ×4 kernel time.

Policy `minimal` (`--policy minimal`, implemented and unit-tested) puts a zero part on the one-slot box at key 0
with raw factor `[0]`. That cuts the zero-part shards to about 721 − 128 = 593 per torus. It needs `dense` (or
`toMants`) to ignore zero entries, which is a one-line change and sound because zero terms evaluate to 0.

A cleaner fix is in SO-POLY-B's hands: `mulPacked` could skip a real part whose decoded mantissas are all zero.
This is SO-ADVCOUNT's lever 2. **Recommendation:** SO-POLY-B picks one of the three. The emitter supports the
first two now; the third needs only a flag that marks the zero parts.

## 4. Option-A Lean data (lower torus; scratch only, not committed)

The command is `sodata_lean.py adv_lower.json .drafts/scratch/data`. It writes the following files.

| Files | Count | Lines | Bytes |
|---|---:|---:|---:|
| `KAM/SpinOrbit/Data/Lower/Adv/Chunk000–024.lean` (run-length-coded window chunks) | 25 | 109–1,393 | 2.62 MB |
| `…/Part000–004.lean` (`PackedAdvice` of the 512 real products) | 5 | 1,016–1,401 | 0.21 MB |
| `…/Book.lean` (`fullBook`, `lowBook`, `graphBook : AdviceBook`) | 1 | 208 | 9 KB |
| **total** | **31** | **≤ 1,401** | **2.70 MB** |

Every line is at most 100 columns. The largest literal is 80 characters (the hex form of a 311-bit mantissa).
Each literal is written in decimal or hex, whichever is shorter. The tree SHA-256 is in
`emit_report_lower.json`.

**Format (fixed here for SO-DEFS and SO-DATA).**
- **Run-length coding.** A window is a flat token list. A nonzero slot is written as itself. A run of `n` zero
  slots is the pair `0, n`, so every zero is followed by its count.
- **Chunks.** Token lists are cut into `def p<i>.<part>W<s>C<c> : List Int` of at most 512 tokens. SO-REPLAY2
  measured elaborator failures at about 4,096 literal elements.
- **Windows.** A window is `unzero (C0 ++ C1 ++ …)`. An all-zero window is `List.replicate (2L−1) 0`.
- **The decoder.** It is the only new glue, proposed for `KAM/SpinOrbit/Data/Format.lean`:
  ```lean
  def unzero : List Int → List Int
    | [] => []
    | 0 :: n :: t => List.replicate n.toNat 0 ++ unzero t
    | v :: t => v :: unzero t
  ```
  The advice is untrusted, so the decoder is not trusted either: `checkPackedProduct` checks whatever it
  denotes.
- **Module shape.** Every module is `@[expose] public noncomputable section`, because the kernel must unfold the
  data. All definitions sit in namespace `KAM.SpinOrbit.Data.<Torus>`. The planned imports are
  `KAM.Certificate.Poly.Packed` (SO-POLY-B), `KAM.Certificate.Model.Ops` (SO-MALG, `AdviceBook`) and
  `KAM.SpinOrbit.Data.Format`.
- **Volume.** Run-length coding plus decimal/hex literals give 2.70 MB for one torus, zero parts included.
  SO-ADVCOUNT's list-literal estimate counted only the in-box rows and was 4.0 MB.

Sample (head of `Chunk000.lean` and one `PackedAdvice`):

```lean
module

/-! Generated advice data (run-length coded windows of packed products; see `Part*`). Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.Lower

def p0.rrW4C0 : List Int := [
  0, 7518, 1, 0, 353, 8, 1, 0, 351, 1, 60, 4, 0, 351, 9, 515, 30, 2, 0, 350, 54, 3665, 170, 10, 1,
  …]
…
/-- Advice of the `rr` real product of product 3 (key [3, 0, 0]). -/
def p3.rr : PackedAdvice where
  la := ⟨[-28, -8], [57, 17], [33, 1], 157, 32⟩
  lb := ⟨[-28, -8], [57, 17], [33, 1], 157, 32⟩
  target := ⟨[-36, -10], [73, 21], [33, 1], 157, 32⟩
  scale := 85
  outLog := 77
  rounded := [
    unzero p3.rrW0C0,
    unzero p3.rrW1C0,
    unzero p3.rrW2C0]
```

## 5. Elaboration and kernel test (scratch)

This test was not a build of `KAM`. Instead, the toolchain's `lean` (v4.35.0) compiled each of the 31 generated
modules, one at a time, under `nice`. They were compiled against a scratch stand-in module that holds the §B′ types
(`PackLayout`, `PackedAdvice`, `ProductAdvice`, `ProductKey`, `AdviceBook`, copied verbatim from A-E) and the
`unzero` decoder, in core Lean only. The machine load was 12–13 on 8 cores. There were no overrides and no
errors.

| Modules | Elaboration | Peak RSS |
|---|---|---|
| 25 chunk files (2.62 MB) | 943 s in total; 10–89 s per file | 0.34–0.86 GB |
| 5 part files | 1.7–2.4 s each | 0.36 GB |
| `Book` | 0.7 s | 0.34 GB |
| **total, one torus** | **≈ 16 min** | **< 0.9 GB** |

- **Elaboration rate.** It is ≈ 350 s/MB, with the chunks of small cfgLow numbers slowest (≈ 0.7 s per KB),
  against §7.2's 18 s/MB. The causes are integer literal elaboration and machine load. Both tori would take
  ≈ 32 min of elaboration, which is acceptable but 20× the design's figure. **Lever:** larger tokens (packed
  limbs) or option C would cut it, but not needed now.
- **Kernel test** (`decide +kernel`, scratch):
  - the decoded full window `p0.rr.rounded[11]` has length 11,327;
  - `p0.rr.rounded.length = 23` and `scale = 327`;
  - `fullBook.length = 3` and `lowBook.length = 143`;
  - a cfgLow window's index-weighted checksum equals Python's;
  - a verbatim copy of the landed `packShift`, applied to the decoded windows `p3.rr[1]` (2,111 slots) and
    `p0.rr[11]` (11,327 slots, `w = 656`), equals Python's `pack_sum` mod 1,000,003.
  So the data denote exactly the emitted advice. The two `packShift` evaluations took 12.6 s and **8.0 GB peak
  RSS**.
- **Design signals for SO-POLY-B and SO-DATA:**
  - The 8.0 GB peak is about 2× SO-REPLAY2's ≤ 3.8 GB per shard. It probably comes from the lazy `Nat`
    accumulators of `packShiftAux` and from decoding through `unzero` in the kernel. Strict accumulators, or
    `blockRows = 16` for the three full products, would lower it.
  - A lazy `foldl` checksum over an 11,327-element window hits the kernel's deep-recursion limit. This is a
    property of the test, not of the data. Any SO-POLY-B list pass over full windows must keep its accumulators
    strict, as `packShiftAux` does with literals.

## 6. Determinism and input pins

- Step 1 rerun: `rec_lower.json` SHA-256 `2352bf83…0005` on both runs (upper `29e71837…a490`).
- Step 2 rerun (lower, from the rerun record): advice SHA-256 `66fab530…ecc6` on both runs.
- Step 3: two runs give the same tree SHA-256. The emitted bytes depend only on the advice JSON and the options.
- The pipeline uses NumPy FFTs (SO-GEN2's Gram approximate inverse `B` and the SOS `g`). It is therefore
  deterministic on a fixed NumPy and platform. The environment was Python 3.12.3, NumPy 2.5.0 and mpmath 1.3.0.
  The SHA-256 of `rec_*.json` is the input pin of steps 2 and 3, and the advice JSON records it.

| Input | SHA-256 |
|---|---|
| `certificates/lunar-spin-orbit/lower.json` | `8ff43d2d0b7f4d824658d8e968865394e20eebd9ae5f384c3da0e064946c8d49` |
| `certificates/lunar-spin-orbit/upper.json` | `dfb59273bf4b7383470da2bee2f0ad185658a387d48912f7644d687e8bf5ae5f` |
| `certificates/lunar-spin-orbit/lower_rot.json` | `dbdb7b934b08aca43e5b453a0a9fba0bca1049a3cf1329d69be4fd9734f3f9bb` |
| `certificates/lunar-spin-orbit/upper_rot.json` | `009b8b7ac98eb19ab2b5b9a07cdfe7f29d40a8bd32eeb595dbdcef4feeba31ae` |
| `scripts/spin_orbit/model.py` | `657424f9f76a0dd702a81bf2eaa693ab27d6eee4f1d2821ec11111a553668ade` |
| `scripts/spin_orbit/rotlib.py` | `176e3a186806dad818114adfa1c7d232fa688ea5a007b45f0bd765c8bd50819a` |
| `scripts/spin_orbit/rot_build.py` | `9d0a70f948a6c06bcf71dc3ea8883663df123a8c9097e56de7cc93c9e837e200` |
| `scripts/spin_orbit/rot_norms.py` | `c1d5bddea8093f5206cb219c68aef737a762b073c30587d58cc4c2f253e2198e` |
| `scripts/spin_orbit/adv_count.py` | `45a92dd9dfbed6d1dc2e3a8c954b27b4b2f3bbaac11cf3bf96f825467474f394` |
| `.drafts/design/SOSignatures.lean` (main checkout) | `9a4652019186e914a0ccfdba6e01c903e458b679d0c057ac4cf7b7d353a4c1cc` |
| `.drafts/design/SOSignaturesLunar.lean` (main checkout) | `f898ee080a52c631387764a2b7d1ab18e2df79b50442b18e5e05aa43f3209c6c` |
| `docs/tracks/SO/design/SO-LEAN-DESIGN.md` (Revision 7) | `4576b12f60f8eec34eac5bd93f14870aa0c1c90dd74c303546b0b06ff1617d8f` |
| `KAM/Certificate/Poly/Packed.lean` (landed SO-POLY-A) | `7f7ed7f499168a8091230ee88a46d48f7095d5e625dc1cfde04add0328bb2948` |
| record (step-1 output) `rec_lower.json` / `rec_upper.json` | `2352bf836e062baa3ac9fa72a0b0ff85540a6e134d7b880f0026b3556dce0005` / `29e71837228476da4f3aa87cb92accb004d716f7550257f707442436b961a490` |
| advice (step-2 output) `adv_lower.json` / `adv_upper.json` | `66fab530a2f98a8a119e2b86ac457a97429210c25ffb408791aab08fdeb9ecc6` / `cd13361742b0c76424cae806ccee4f604a37fd2dac28ca7dc1097e12a4aecc6e` |

Reproduce:

```
cd scripts/spin_orbit
python3 sodata_test.py
python3 sodata_record.py lower REC.json && python3 sodata_emit.py REC.json ADV.json
python3 sodata_lean.py ADV.json OUTDIR
```

## 7. Negative tests

- **The §8 contracts** (`sodata_test.py`):
  - audit 5's `packSum 4 [16, -1, 0] = 0` holds and `reconFits 4 1 _ [16, -1, 0] = false`;
  - the whole carry-cancel product is rejected;
  - `scale = 0` is rejected;
  - the F14 alias `[0]` vs `[0, 0]` is rejected, while the honest `[0, 0]` call passes.
- **Corruptions that must FAIL.** Each of these is run on the nonzero part and on one zero part of every
  cfgLow/graph product, and the cheap subset on the three full products. All 2,268 per torus were rejected.
  - an in-box advice slot +2;
  - nonzero advice off the box;
  - `scale 0`;
  - `outLog − 1`;
  - a short window;
  - a missing window;
  - swapped windows;
  - `width − 1`;
  - the raw factor `da ++ [0]` (F14) and a truncated raw factor.
- **Probes** (`sodata_test.py`, random products). These are mutations the checker MAY accept: a target box moved by
  one row or column, `scale − 1` with unchanged advice, and a tampered factor. Every acceptance (439 of 1,258 box
  shifts) satisfied the `checkPackedProduct_sound` conclusion on the exact convolution. That is a sanity check of
  the proposed bodies, not a proof.

## 8. Uncertainties

1. **The factor values are Python's** (SO-GEN2's `rot_build`/`rot_norms`), not the Lean checker's. The advice
   fails if the Lean model arithmetic produces different mantissas. One exception: a change confined to
   out-of-box slots that stays within `outLog`. A bit-exact Python mirror of SO-MALG's operations is the next
   step of SO-DATA.
2. **The SO-POLY-B bodies are this package's readings** (§1.1). The two most likely to differ are:
   - `shardFits`: whether it takes the max over all blocks or only over the paired blocks;
   - whether the target's stride is checked.
   Any change costs a rerun only.
3. **`ProductKey`s and books are proposals** (§1.3), as is the zero-part policy (§3).
4. **Volumes cover the advice only.** The embedding and witness data (≈ 1.06 MB per torus, SO-ADVCOUNT) are not
   emitted here.

## 9. Errata and deviations

- No pinned-source errata are suspected.
- **Design signals:**
  - the empty-factor policy multiplies the shard theorems by 4 (§3);
  - elaboration measured ≈ 350 s/MB, against §7.2's 18 s/MB (§5);
  - a full-window `packShift` in the kernel peaked at 8.0 GB (§5).
- **Deviation:** this package proposes a decoder, `unzero`, as new SO-DATA glue (§4). It is not in the
  signatures.
