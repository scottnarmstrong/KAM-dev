# V2-PACKED: GMP-resident packed Fourier models for the kernel

Status: design (2026-11-01), brief V2-PACKED step 2, with a prototype (step 3) and a measured gate (step 4).
No frozen statement, landed definition or certificate changes. Every new Lean file is a new module under
`KAM/CertificateSharp/Packed/`. Profile: [`V2-PACKED-PROFILE.md`](../studies/V2-PACKED-PROFILE.md).

## 0. Summary

- **Problem (profile).**
  - Products are 54 % of LG00's attributable kernel time and per-coefficient model operations 35 %.
  - Inside them, the big-integer multiplications cost 7 s of 26 h. The rest is interpretive overhead of
    0.2–1.5 ms per coefficient, advice slot or list cell, times the number of passes.
- **Idea.** Keep every Fourier model *packed*: one signed big integer per real coefficient array (Kronecker
  substitution in base `2^w` on the landed box layouts). Then:
  - each model operation is a constant number of kernel GMP operations (`Nat.mul`, `+`, `&&&`, `>>>`);
  - a product is one `Int.mul`;
  - rounding is one mask and one shift, with an a-priori error budget and **no advice**;
  - bounds are one mask test.
  No list is walked between operations.
- **What exists and is reused, not duplicated.**
  - `packSum` with its injectivity and Kronecker lemma (`Poly/Packed.lean`);
  - the layouts and the Fourier-side Kronecker theorem `PackLayout.intEval_mul_of_compat` (`Poly/Layout.lean`);
  - the sparse packer `spPack` (`Poly/Sparse.lean`);
  - the fixed-point backend `CertFixed` (exponent alignment: a model's coefficients share the scale `2^-P`);
  - `ofDyadic`, `toMants` and `dyadicTerms` at the list boundary.
- **New.**
  - Digit-wise mask arithmetic on base-`2^w` naturals (`Packed/Digits.lean`).
  - Advice-free rounding, the load check and balanced unpacking (`Packed/Round.lean`).
  - The packed real product, its exact correctness lemma and its strip contract in the landed shape
    (`Packed/Product.lean`).
  - The complex product with the landed `mulPacked_sound` conclusion (`Packed/Bridge.lean`).
- **Bridges (additive).**
  - **B1, product contract.** `gmpRealProduct_sound` states exactly `packedRealProduct_sound`'s proposition.
    `CertPoly.mulGmp_sound` states exactly `CertPoly.mulPacked_sound`'s, which is what
    `CertModel.polyProduct_sound` and hence `CertModel.Encloses.mul` consume. This is a product-level
    bridge, **not a drop-in**: the landed `CertModel.polyProduct` is hard-wired to `CertPoly.mulPacked`
    through the closed `ProductAdvice` type (`direct` | `packed`), so a checker can use `mulGmp` only
    through a parallel `polyProduct`/`mul`/evaluator/`BaseChecker` chain, i.e. through B2.
  - **B2, certifier (plan).** A packed `BaseChecker` (`packedBase`) whose `sound` yields the landed
    `BaseFacts`. The landed `checkV2With_sound packedBase E` then gives the landed `CertifiedTorus c ωstar`
    unchanged, and every application consumer applies verbatim.
- **Gate (§8).** Measured on an LG00-sized product. The handoff reports the speedup and what it implies for one
  LG00 torus and for SJS.

## 1. Representation

A **packed real array** on a landed `PackLayout L` (box `lo ≤ k < lo + dims`, mixed-radix strides, slot
width `w = L.width`) is a signed integer
`Z = packSum w d = Σ_i d_i 2^{w i}`, where `d = L.dense x` is the dense slot list of integer Fourier data `x`.
It carries metadata:

| field | meaning | kernel cost |
|---|---|---|
| `L` | layout (keys ↔ slots, landed) | none |
| `B : ℕ` | load bound: `|d_i| ≤ B` for every slot | none |
| `P : ℕ` | fixed-point exponent: the coefficient is `d_i / 2^P` (shared by all slots) | none |
| `Z : ℤ` | the packed value | one GMP integer |

A **packed model** is a degree `deg`, packed real and imaginary arrays on one layout at one exponent `P`, and a
radius (as in `CertModel`). Its meaning is the landed `CertModel` obtained by unpacking. A model therefore
*denotes* exactly what the landed algebra denotes, so the landed enclosure predicate `CertModel.Encloses`
applies to it.

- **Signed slots and carries.** `Z` is a plain integer: negative slots borrow from the next slot, and no digit
  is ever stored. A list is determined by `Z` whenever every slot satisfies `2|d_i| < 2^w`
  (`packSum_injective`, landed). All arithmetic is on `Z`; digits are read only through masks (§2), on the
  **offset** natural `Z + Σ_i O 2^{w i}`, whose base-`2^w` digits are `d_i + O ∈ [0, 2^w)` once `O ≥ B` and
  `O + B < 2^w`.
- **Exponent alignment.** Models at exponents `P ≤ P'` are aligned by `Z ↦ 2^{P'-P} Z` (exact; the load grows
  by `P' − P` bits). A product has exponent `P_a + P_b`; rounding by `s` bits lowers it to `P_a + P_b − s`.
  As in `CertFixed`, the exponent is shared, never per coefficient.
- **Literal ingestion.** Certificate inputs (embedding, witnesses, Hamiltonian data) arrive either:
  - as landed term lists, packed once by `spPack` (per term, about 1.3 ms per term; §8 measures it); or
  - as packed literals: 288-bit hexadecimal chunks (72 digits, so that a line stays ≤ 100 characters) joined
    by a balanced `natJoin` tree. The chunks are XOR-ed with the closed-form ramp `natRamp 288 m`, so that no
    two partial results share their low 64 bits (§7: the kernel hashes a natural literal by its low 64 bits).
    The load of such a literal is certified by one mask test (`loadOk`, §2).
- **Literal costs** (gate): about 16 µs of kernel time per chunk, plus 0.9–1.3 µs of elaboration per
  literal bit. Longer chunks would cut the kernel's share 50×, but the numeral parser is quadratic: 64 k-digit lines
  cost 1.2 s each to elaborate. Generated packed data therefore needs either the line cap or an owner waiver
  (handoff, owner questions).

## 2. Kernel operations and their guard rules

Below, `N` is the number of slots, `w` the width, and `M_t = periodic w N (2^t − 1)` the periodic mask of the
low `t` bits of every slot. `periodic w N m = m · (2^{wN} − 1)/(2^w − 1)` costs one power, one subtraction,
one division and one multiplication: kernel GMP, no loop.

| operation | packed formula | guard (metadata only) | result load |
|---|---|---|---|
| add / subtract | `Z_a ± Z_b` (same layout, exponent) | `2(B_a + B_b) < 2^w` | `B_a + B_b` |
| scalar `m ∈ ℤ` | `m · Z` | `2 |m| B < 2^w` | `|m| B` |
| product (Kronecker) | `Z_a · Z_b` on `compat` layouts | `2 min(N_a, N_b) B_a B_b < 2^w` | `min(N_a,N_b) B_a B_b` |
| round by `s` bits | `R = ((Y − (Y &&& M_s)) >>> s) − periodic(2^{l−s})`, `Y = (Z + periodic(2^l + 2^{s−1})).toNat` | `B ≤ 2^l`, `1 ≤ s ≤ l`, `l + 2 ≤ w` | `2^l` (`roundSlot_abs_le`) |
| load check `|d_i| < 2^l` | `Y = (Z + periodic(2^l)).toNat < 2^{wN}` and `Y &&& M_{l+1} = Y` | `l + 2 ≤ w` | `2^l` |
| box mask (truncation to a sub-box) | `Y &&& Mbox`, `Mbox = Π_axes` 1-D interval masks (one product per axis) | as load check | unchanged |
| absolute value | sign masks: `S = (Y >>> l) &&& periodic 1`; `|d| = (Y &&& S(2^{l+1}−1)) − S 2^l + (1−S) 2^l − (Y &&& (1−S)(2^{l+1}−1))`, digit-wise | as load check | `B` |
| weighted ℓ¹ norm `Σ |d_k| W_k` | `(A · W^rev) >>> (w(N−1)) &&& (2^w − 1)`, `A` = absolute values, `W^rev` = reversed packed weight table | `N B 2^m < 2^w` (`W_k ≤ 2^m`) | scalar |
| axis ramp `Σ k_j d_k 2^{w·slot(k)}` (derivatives, `ω·∂`) | Leibniz at the packed level: `T^{(j)}_{ab} = T^{(j)}_a Z_b + Z_a T^{(j)}_b` | as product | as product |

**Rounding** (`gmpRound`, prototyped).
- **Digits.** Adding `O = 2^l + 2^{s−1}` per slot turns slot `d` into the digit `e = d + 2^l + 2^{s−1}`,
  with `0 ≤ e < 2^w`.
- **Mask and shift.** `Y − (Y &&& M_s)` clears the low `s` bits of every digit. The shift by `s` then gives the
  digits `⌊e/2^s⌋ = ⌊(d + 2^{s−1})/2^s⌋ + 2^{l−s}` exactly: no carry crosses a slot, because the cleared digits
  are multiples of `2^s` below `2^w`.
- **Result.** Removing the offset `2^{l−s}` per slot leaves round-to-nearest (ties up):
  `r_i = ⌊(d_i + 2^{s−1})/2^s⌋`, `|d_i − 2^s r_i| ≤ 2^{s−1}`.
- **Cost.** Four GMP operations and no advice. The landed route instead walks the advice, the windows and
  every slot's log.

**Error budget.** A rounded product's slots err by at most `2^{s−1}` each, and every product slot carries
`|χ_k| ≤ w^{|k|₁}` on the strip. The remainder is therefore at most
`2^{s−1} Σ_i w^{deg_i} ≤ 2^{s−1} · N · w^{D}`.
- `D = degCap` bounds every slot degree of the product window from the layout alone: per axis
  `max(|lo_j|, |lo_j + cap_j|)`, with mixed-radix digit caps `cap_0 = (N−1)/s_0`,
  `cap_{j+1} = (s_j − 1)/s_{j+1}`.
- The cost is `O(dims)` rational operations, not per slot.
- **Lossiness.** For decaying analytic data the geometric weight sum is dominated by its largest terms. The
  crude `N w^D` overestimates the exact `Σ w^{deg}` by `N(w−1)²/4`-ish (a factor ≈ 7, i.e. 3 bits, on LG00's
  boxes). Precision is cheap in the packed representation (§8: cost ∝ bits, not slots), so the producer adds
  those bits.
- **Exact alternative (design only).** `Σ_box w^{|k|₁}` factorizes over the axes. It is the weighted-norm
  primitive of the table above, applied to the all-ones array.

**Truncation and the weighted norm** (design only; not prototyped).
- **Truncation.** The landed `truncPoly` drops `|k|₁ > cutoff`, a diamond, not a box. Its packed mask is one
  interval mask per row: `M (B^b − B^a)/(B − 1)`, `O(1)` GMP each, so `O(√N)` operations for 2-D, once per
  (layout, cutoff). The dropped part's weighted norm goes to the radius.
- **Weighted norm.** The landed radius terms `|P|_w r` and `errRadius` need `Σ |c_k| w^{|k|₁}`. Packed:
  - the absolute values come from sign masks;
  - one product with a reversed packed weight table gives the dot product as the middle digit;
  - no carry reaches that digit if `N B 2^m < 2^w`. At product-ready widths `w ≈ 2 log₂ B + log₂ N`, weights
    of `m ≈ log₂ B` bits fit.
  - For a 2-D box the table is the outer product of two 1-D tables, i.e. one GMP product of a row table and a
    column table.

**Pointwise multipliers** (derivatives `∂_j`, the invariance operator `ω·∂`, `toDeg` with `(2π)^e`).
- `(2π)^e` is a scalar.
- `k_j c_k` is a Hadamard product, which no single convolution provides. Instead each packed model carries
  its axis ramps `T^{(j)}`. Keys add under products, so ramps propagate by the Leibniz rule (two products
  each), and linearly through sums.
- Ramps of the certificate inputs are made once at the boundary (per slot, once per input).
- This is forward-mode differentiation on the Kronecker variable. It matches the jet compiler, which already
  makes derivatives explicit program slots.

## 3. Correctness lemmas

**Exact product** (the brief's "unpack ∘ packed product = coefficientwise product when the guard bits
suffice"). Assume `compat` layouts and `L.dense x = some d_a`, `packSum w d_a = Z_a` (likewise for `b`), with
`|d_a| ≤ B_a` and `|d_b| ≤ B_b`. Then:
- **pack:** `Z_a Z_b = packSum w (listConv d_a d_b)` (landed `packSum_listConv`);
- **unpack** (`unpack_mul_eq_conv`): `unpackSlots w N (Z_a Z_b) = listConv d_a d_b`,
  `N = |d_a| + |d_b| − 1`, provided `2 min(N_a, N_b) max|d_a| max|d_b| < 2^w` (the landed `convFits`). It
  follows from `packSum_listConv`, `slotsBounded_listConv` (landed) and the balanced unpacking
  `unpackSlots_packSum`;
- **meaning:** the product's Fourier meaning is the landed `PackLayout.intEval_mul_of_compat`.

**Rounding** (`gmpRound_spec`). Under the rounding guard, `gmpRound w N l s (packSum w d) = packSum w r` with
`r_i = (d_i + 2^{s−1}) / 2^s` (floor), `|d_i − 2^s r_i| ≤ 2^{s−1}` (`round_err`) and `|r_i| ≤ 2^l`
(`roundSlot_abs_le`; a tighter `B/2^s + 1` holds but is not proved). The proof is
digit-wise:
- `natPack_land_mask`: `natPack w e &&& periodic w N (2^t − 1) = natPack w (e mod 2^t)` for digits
  `e_i < 2^w`, from `testBit_two_pow_mul_add` and `and_two_pow_sub_one_eq_mod`;
- `packSum_add_periodic`: the offset as digits;
- `periodic_eq_natPack`: the closed form as a digit list.

**Load check** (`loadOk_sound`). If `loadOk w N l Z = true`, then `Z = packSum w d` for some `d` of length
`N` with `−2^l ≤ d_i < 2^l`: the digits of a natural below `2^{wN}` exist (`natPack_digits`), and the mask
fixes them below `2^{l+1}`.

**Strip contract** (`gmpRealProduct_sound`). With `R = gmpRound(Z_a Z_b)` and `T = gmpTerms R`, the
keyed nonzero slots of `unpackSlots R` on the product window (landed `prodKey`):
`‖intEval x · intEval y − 2^s intEval T‖ ≤ (N 2^{s−1} w^D / 2^{P2}) · 2^{P2}` on `T_ρ`. This is the statement
of the landed `packedRealProduct_sound`, with the gmp output in place of the advice output.

## 4. Bridges: how a packed check proves what the landed checker consumes

**B1 (prototype).** The landed model-product chain is
`packedRealProduct_sound` → `CertPoly.mulPacked_sound` → `CertModel.polyProduct_sound` → `CertModel.Encloses.mul`.
The prototype supplies the first two links for the packed route, **with identical conclusions**:
- `gmpRealProduct (g : GmpSpec) W P2 x y : Option (List (CertKey × ℤ) × ℚ)`: the landed signature, with a
  spec in place of the advice;
- `CertPoly.mulGmp dec W P g_rr g_ii g_ri g_ir a b : Option (CertPoly α × α)`: the landed `mulPacked`
  assembly with the four gmp real products, and `CertPoly.mulGmp_sound`, the `mulPacked_sound` proposition.

A consumer proof written against the landed contracts therefore applies verbatim to the packed route **once
the consumer definitions are duplicated**: the landed `CertModel.polyProduct` calls `CertPoly.mulPacked`
through the closed `ProductAdvice` and cannot call `mulGmp`. That duplication (`polyProduct`, `mul`, the
evaluator, a `BaseChecker`) is B2's size.

**B2 (plan, not prototyped).** The certifier is already parametric in its sub-checks:
`checkV2With (B : BaseChecker) (E : EngineV2)`, `checkV2With_sound` (`KAM/CertificateSharp/V2/Engine.lean`).
A new `packedBase (book : PackedBook) : BaseChecker`:
- converts the certificate's inputs once at the boundary (embedding, witnesses: about 3·10⁴ terms for LG00,
  about a minute at the measured per-term cost);
- evaluates the jet program, the Gram and torsion stages and the frame inputs on packed models;
- proves `BaseFacts c ωstar` by the same chain as `landedBase.sound`, with each landed enclosure lemma
  replaced by its packed twin (product: B1; sum, scalar, rounding: §2).

Then `checkV2With_sound (packedBase book) E h hω hdio : CertifiedTorus c ωstar` is the **landed** conclusion,
and `lg00_certifiedTorus_iff`, the lunar consumers and every frozen statement are untouched. No landed file
changes: the book is a parameter, so the final theorem's statement does not mention it.

**What is deliberately not bridged.** A memo proof `packedRealProduct adv W P2 x y = some (T, e)` of the
**landed** list route (as SO-CSPLIT and LG00 use) cannot be made cheap by a packed check. Its value is defined
by per-slot list functions of the advice (`targetTerms`, `remainderBound`), which the kernel must evaluate.
A packed shard check could remove only the shard share (≈ 26 % of LG00). That is not worth a completeness
proof of `intSlotsBound`.

## 5. Coordination

- **Fixed point.** `CertFixed P` stays the backend of the boundary (`toMants`, `ofDyadic`, `mantCheck`). Packed
  models use its convention, one shared exponent per model. No new real-number backend.
- **Outward rounding.** The landed outward operations (`upAdd`, `upMul`, `ofRatUp`) keep handling radii, which
  are scalars. Packed rounding is coefficient rounding with an a-priori budget added to the radius, as the
  landed packed remainder already is.
- **SO segmentation.** SO-CSPLIT's M1/M2 split the landed Bools into memoized pieces. A packed base checker
  needs no ledger of model literals, because intermediate models are never materialized as lists. Its
  declarations are split only by the memory of the big integers they create (the gate, §8, measures it),
  against 80–130 MB per kernel-second for list work.
- **Owned files.** None touched: `KAM/CertificateSharp/**`, `KAM/Certificate/**` (existing), `KAM/Sharp2/**`,
  `KAM/Iso/**`, `KAM/SpinOrbit/**`, `KAM/Frozen/**`, `manifest/**` are unchanged.

## 6. Prototype (step 3): modules

| module | content |
|---|---|
| `KAM/CertificateSharp/Packed/Digits.lean` | `natPack`, `periodic`, `natPack_land_mask`, `natPack_injective`, `natPack_digits`, `packSum_add_periodic` |
| `KAM/CertificateSharp/Packed/Round.lean` | `gmpRound`, `gmpRound_spec`, `loadOk`, `loadOk_sound`, `unpackSlots` (balanced), `unpackSlots_packSum` |
| `KAM/CertificateSharp/Packed/Product.lean` | `PRep`, `packRepOk` (list boundary), `GmpSpec`, `degCap`, `gmpTerms`, `gmpRealProduct`, `gmpRealProduct_sound` |
| `KAM/CertificateSharp/Packed/Bridge.lean` | `CertPoly.mulGmp`, `CertPoly.mulGmp_sound` |
| `KAM/CertificateSharp/Packed/Tests.lean` | small default kernel tests (cheap) |
| `scripts/packed/gate_gen.py`, `run_probe.sh` | the gate probes, generated outside the sources (their literals exceed the 1,500-line cap; `kernel-tests/Packed/README.md`) |

## 7. Risks

- **Kernel caching of large integers.** Every intermediate big integer of a declaration stays cached. Packed
  declarations are therefore sized by the bits they create (§8 measures the rate), not by operations.
- **Kernel hashing of big literals (measured).** Lean's `instance : Hashable Nat` is
  `hash n := UInt64.ofNat n` (`Init/Data/Hashable.lean`), so an expression's hash sees only the low 64 bits of
  its natural literals. When many distinct big literals share their low limb, the kernel's caches degrade:
  - a tree of 4,096 random 288-bit chunks is ingested in 37 ms;
  - the same tree with zero low limbs takes 20.8 s;
  - the gate's first, unmasked packed literals took 11.9 s instead of 0.24 s.
  Producers must keep low limbs distinct: the `natRamp` XOR mask for literals, and few big intermediates per
  declaration. An upstream fix (hash all limbs) would remove the hazard; this is an orchestrator item.
- **Literal parsing** is quadratic per literal; with lines ≤ 100 characters, chunks are 288 bits (§1).
- **Literal volume and memory.** The gate measured 36–47 bytes of charged memory per packed literal bit
  (elaboration plus kernel) and 0.9–1.3 µs of elaboration per bit. At SJS's 3–4 GB of input literals this is the
  binding cost, not the arithmetic; see the handoff's SJS paragraph.
- **Widths.** Product-ready widths (`2 log₂ B + log₂ N` + guard) are about 2× the coefficient precision, as in
  the landed advice (193–277 bits for `CertFixed 128`). Weighted norms need `log₂ N + log₂ B + m` bits;
  rounding before a norm keeps that within the same width.
- **B2 is the large part.** The packed jet evaluator, the Gram/torsion stages and the frame inputs total
  roughly the size of `KAM/Certificate/Model` + `Expr` (≈ 3–5 k lines). It has its own audit. The landed
  statement and soundness interface are fixed, which limits the risk.

## 8. Gate (measured; receipts in `docs/campaign/studies/V2-PACKED-GATE/`)

**Setup.** One LG00-sized real product, `G8k`:
- 41 × 51 by 43 × 48 boxes: 1,611 and 1,614 terms, 3,971 and 4,164 dense slots, 8,134 product slots;
- width 263; `CertFixed 128` mantissas;
- landed advice from the landed mirror: 3 shards of 3,136-slot blocks.

The packed route rounds by `2^164`, and its a-priori remainder 2^-71.2 is no larger than the landed 2^-70.5.
Each forced theorem ran alone under a 4 GB charged cap. The table gives kernel time and the peak
**cgroup charge** (sampled `memory.current`); max RSS runs ≈ 1.2–1.3 GB higher, from mmapped oleans
already charged elsewhere (e.g. `G8kPall` 4.9 GB RSS against 3.67 GB charged). "Under 4 GB" means the
charge.

The column *bridged* says whether a soundness theorem covers the forced check. Only the list-in/list-out
route is bridged (`gmpRealProduct_sound`, `CertPoly.mulGmp_sound`). The GMP-resident rows are **unbridged**:
no theorem yet gives a packed integer a Fourier meaning without a term list (`PRep` needs `L.dense x`), the
inputs' `loadOk` checks are not in the measured `Pcore` (cheap, but required), and nothing consumes `gR`.
They need B2.

| route | what is forced | kernel | charged |
|---|---|---:|---:|
| landed | `checkShardSp`, shards 0 / 1 / 2 | 11.2 / 9.5 / 8.9 s | 2.9 / 2.8 / 2.6 GB |
| landed | prefix: `allSlots`, `shapeOK` (advice-zero walk), ordering | 12.7 s | 3.6 GB |
| landed | decode `targetTerms`, whole | **OOM at 4 GB** | — |
| landed | decode, first 1,500 / 3,000 terms | 5.2 / 8.6 s | 1.8 / 2.7 GB |
| landed | `remainderBound` | 11.0 s | 2.8 GB |
| landed | `packedRealProduct = some (T, e)`, whole | **OOM at 4 GB** | — |
| **landed, sum of pieces** (decode extrapolated: 2.3 ms per term) | | **≈ 70 s, ≥ 7 processes** | ≤ 3.6 GB each |
| packed, list boundary | `packRepOk` + `packOf`, both factors | 3.0 s | 1.1 GB |
| packed, list boundary | read-back `GmpSpec.terms` | 12.4 s | 3.2 GB |
| packed | a-priori remainder `GmpSpec.rem` | 0.004 s | 0.38 GB |
| **packed, lists in and out** (bridged) | `gmpRealProduct = some (T', e')` | **14.9 s, 1 process** | 3.7 GB |
| **GMP-resident** (unbridged) | guard, product, rounding, equality with the packed output (3 literals ingested) | **0.18 s** (audit re-run: 0.30 s) | 0.60 GB |
| GMP-resident (unbridged) | literal ingestion alone | 0.24 s | 0.59 GB |

Controls: import 1.25 s user and 0.40 GB; landed data elaboration 7.7 s and 0.66 GB; packed literals 5.8 s and
0.54 GB.

**At LG00's largest product size** (`G19k`: 10,127 × 9,185 dense slots, 19,311 product slots, 4 shards of
5,024-slot blocks):
- GMP-resident with literals: 0.65 s and 0.90 GB.
- One landed shard, and the landed remainder alone: each **OOM at 4 GB**. LG00 ran them under 5.9 GiB.
- **Compute without literals** (`C19kCompute`, unbridged: operands built in the kernel, product, rounding,
  load check): 23 ms for one product (audit re-run: 20 ms), 183 ms for ten, +4–5 MB each.

**Speedups on the same product.**
- **Lists in and out (bridged, not a drop-in):** 4.7× kernel time, and one process instead of seven. The
  boundary decode (12.4 s) is now the cost. This is an **upper estimate**: G8k's landed advice covers the
  whole window (`outLog 0`, scale 167), so its landed decode (≈ 16 s of the ≈ 70 s) is larger than for
  LG00's typical advice. Using it in a checker needs the parallel chain of B2.
- **GMP-resident with literal I/O (unbridged):** about 235–380× (0.18–0.30 s across runs).
- **Compute only (unbridged):** ≥ 3,000×. The 19 k-slot compute time bounds the 8 k-slot one.
- **Precision:** the packed route matched the landed remainder with 3 fewer bits of rounding shift.

**Output size** (source bytes).
- **Landed:** advice windows 159 kB plus decoded terms 146 kB per real product.
- **Packed:** no advice. A packed output memo is 681 kB, because every slot of the window is stored at the full
  width with guard bits. The decoded terms are 152 kB.
- In a GMP-resident pipeline, intermediates are never literals.

The handoff draws the consequences for one LG00 torus and for SJS.

## 9. B2, first stage (built on branch `v2-packed-b2`; details in `docs/campaign/handoffs/V2-PACKED-B2.md`)

The Gram stage is now packed end to end. It is the first B2 stage, and it reaches the landed `CertifiedTorus`
on the standard axioms.

- **Modules.** `Slots` (slot semantics, exact products on window layouts), `Norm` (the packed weighted ℓ¹ norm
  and its strip bound), `Complex` (packed complex arrays), `Gram` (`gramPackedCheck_sound`: the landed
  `gramCheck_sound` conclusion), `GramBase` (`gramPackedBase : BaseChecker`, `checkV2With_gramPacked_sound`).
- **Changes against §2–§4.**
  - The Gram products are exact, at scale `2^(3P)`, with no rounding or read-back. Their meaning is slot
    data (`SRep`), not term lists.
  - The defect is bounded by one packed norm product, not by a decoded remainder.
  - The DK boundary is the landed per-coefficient models, memoized and re-checked one entry per
    declaration. Building the DK entries packed from `K` (the derivative ramps of §2) is not done yet.
- **Gate (LG00's data, a stage measurement).** 9 processes, ≈ 73 CPU-s, ≤ 2.23 GB charged, against the
  landed stage's 89 modules, 1,425 CPU-s, 2.28 GB: ≈ 19.5×. The packed arithmetic is ≈ 3 s of it; the boundary
  is 23 s.
- **No end-to-end saving yet.**
  - The landed `checkTorsion` matches on the landed `gramCheck`, so the 89-module landed Gram stage is still
    required by `checkTorsion`. In LG00, `lg00_checkTorsion` consumes `lg00GramCheck`.
  - With `gramPackedBase` the net change is therefore +73 s.
  - The saving appears only with a packed torsion stage (B3) that takes the Gram result from the packed
    check.

## 10. B3, the torsion stage (branch `v2-packed-b3`; details in `docs/campaign/handoffs/V2-PACKED-B3.md`)

The packed torsion check is built and proved end to end (`checkTorsionPacked_sound`: the landed
`checkTorsion_sound_of` conclusion; `torsPackedBase`: packed Gram and torsion, landed `CertifiedTorus`, with no
landed Gram certificate). It is **exact**: packed models (`PEnc`, `PMat`) with exact products, radii through
`‖a‖ s + r ‖b‖ + r s`, and averages read from the zero-key slot.

**At LG00 size the exact chain does not fit the kernel.**
- The windows grow additively, up to 263 × 315 for `T`, at 1,168-bit slots: numbers of up to 97 Mbit.
- The kernel refuses `Nat.pow` results above 16.8 Mbit (`LEAN_NAT_MAX_SIZE`).
- It also keeps every intermediate of a declaration: one entry of `DG⁻¹` takes 4.1 GB.

The boundary (36 entries, 218 CPU-s), the guards and the Gram link pass on LG00's data.

**The design consequence (B3b, proposed).** The packed chain must be bounded like the landed one:
- round each node back to scale `2^P` (`gmpRound`), with the exact residual's packed norm in the radius;
- truncate each node to the `ℓ∞` box of half-width 24, with the tail's packed norm in the radius;
- decide the final test entry by entry, handing over centres and radii as small literals.

Every number then stays ≤ 3.5 Mbit, and each process is estimated at ≤ 2 GB. "Exact, no rounding" (§9) works
for the Gram stage because its windows stay small; it does not carry over to deep chains.
