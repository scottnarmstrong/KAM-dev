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
  - A packed torsion stage (B3) that takes the Gram result from the packed check is necessary, but not
    sufficient. Route A refined's frame checks (`checkFrameN`, `checkFrameT`, `Frame/Majorants.lean`) re-run the
    landed Gram check and torsion models, so an LG00 saving also needs packed frames and a matching engine
    (AUDIT-V2-PACKED-B3-1 M1; V2-PACKED-FRAMES).

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

## 11. B3b, the rounded and truncated torsion stage (branch `v2-packed-b3`; `docs/campaign/handoffs/V2-PACKED-B3B.md`)

The B3 design consequence, built.
- Every node of the torsion chain is an untrusted memo on one box: the ℓ∞ box of half-width 25, which contains
  the landed `cfgLow` truncation. It is held at scale `2^128`.
- The kernel checks each node entry by its exact residual against the exact product of the memoized inputs on
  one window (`stageOk`). The rounding and truncation errors therefore enter the radius and are never assumed.
- The averages of `T` and `Y` are checked against small tables, and the landed test runs on the tables.

Every number stays ≤ 3.67 Mbit (360-bit slots on a 101 × 101 window), and every process ≤ 3.19 GB.

**Gate on LG00's data:** 64 processes, 1,292 CPU-s (269 s kernel), against the landed Torsion stage's 637
modules and 12,126 CPU-s. Together with B2's packed Gram stage, the two **sub-checks** cost 1,365 CPU-s against
13,561 (≈ 9.9×, a stage-cost comparison; production assembly unmeasured).

**There is no LG00 saving yet.** Route A refined's `checkFrameN`/`checkFrameT` re-run the landed Gram check and
torsion models, so the landed stages stay (AUDIT-V2-PACKED-B3-1 M1). Packed frames and a matching engine are the
next step (V2-PACKED-FRAMES, built in §13: with them the gate figures give ≈ 12,700 CPU-s; the production assembly is
unmeasured). The jet compositions
(`Low`, `Full`) are unchanged.

**The memo-and-residual pattern** (a node verified by `packRepOk` and the packed norm of its exact residual) needs
no digit lemma about the rounding or the truncation. It applies to any chain of packed products, including a
packed jet evaluator.

## 12. The packed jet evaluator (design §12.1–§12.8; built and measured from §12.9 on)

The remaining dominant cost of an LG00-shaped certificate is the composition of the Hamiltonian's jet with the
embedding. This section designs its packed replacement, with the check-by-residual pattern of §11.

### 12.1 What the Low and Full stages compute

**The program.**
- `Slp.compose n p K wit W cfg pe wanted` (`KAM/Certificate/Expr/Compose.lean`) runs the jet program
  `p = c.ham.jet.prog` slot by slot on Fourier models of `θ ↦ slot(K θ)`.
- `composeStep` dispatches on the operation:
  - `const re im deg`: `constModel`;
  - `action j`: the action data `(2π)^{dA_j} A_j`;
  - `char k`: a character witness, checked once and cached (`charSlot`);
  - `add`: `CertModel.add` (degree conversion through the π enclosure);
  - `mul`: `CertModel.mulN` (an advice-checked packed product, truncated to `cfg.cutoff`, rounded);
  - `exp`, `inv`, `sqrt`: witnesses checked by `expWitnessRadius`, `invWitnessRadius`, `sqrtWitnessRadius`.
- It returns the models of the wanted slots.

**What its contract gives.** `Slp.compose_sound` gives only the **enclosure** of each wanted slot function
`θ ↦ p.val n (K.eval n θ) i` on `T_ρ` (`SlotsEnclose`). That is all any consumer uses:

| stage | call | consumer | what the consumer uses |
|---|---|---|---|
| **Low** | `Slp.compose … cfgLow (torsionSlots)`: the `2n` first and `(2n)²` second derivatives of `H` along `K` | `checkTorsion` (and the B3/B3b packed torsion) | `dxhModels_encloses`, `d1Models_encloses` from `SlotsEnclose` |
| **Full** | `Slp.compose … cfgFull (d1Slots)` and `… [v0]` | `checkInvariance` (`invarianceModel`, sup bound ≤ `err`), `checkEnergy` (`energyOk`: zero mode of `H∘K − E₀`) | the enclosures of `∂_a H ∘ K` and `H ∘ K` |

**LG00's program** (`lg00Jet`) has 7,816 operations: 4,310 `mul`, 1,854 `add`, 1,508 `const`, 120 `char`, 20
`action`, 2 `inv`, 2 `sqrt`, 0 `exp`. LG00's census puts it at about 690 genuine (non-scalar) products in the two
chains after pruning; most `mul`s multiply by a constant.

**How LG00 proves it today.** The landed segment check `ComposeCkpt` (`KAM/CertificateSharp/Kernel/Seg*.lean`)
cuts the program into segments; each one replays the landed `composeStep` on its live operations from a ledger of
imported slot models, and the chain theorem `ComposeCkpt.compose_eq` gives `Slp.compose … = some ledger`. In
`run20e`:

| | modules | CPU |
|---|---:|---:|
| `Low.T` (segments) | 1,911 | 48,096 s (13.4 h) |
| `Full.T` (segments) | 1,094 | 34,630 s (9.6 h) |
| their literal modules (`L`, `D`, `V`, `K`, `P`, `Ckpt`) | 1,054 | 4,533 s |

That is **24.2 of LG00's 30.1 CPU-h**. LG00's own analysis puts the cost in three places:
- regular segments, about 115 M per-coefficient backend calls for additions, scalar products and degree
  conversions: ≈ 9.6 h;
- product shard groups and product segments (decode, truncation, ledger): ≈ 11 h;
- witness certification: ≈ 0.8 h.

**Note (AUDIT-V2-PACKED-B3-1 M1).** The landed `checkFrameT` of route A refined re-runs the landed
`torsionModels`, and that includes the `cfgLow` composition. The jet's `Low` saving therefore also needs the
packed frames of V2-PACKED-FRAMES, whose `T` comes from the packed torsion.

### 12.2 The bridge: at the enclosure, not at the landed segment check

**Why not the landed segment check.** `segOk` asserts **bit-equality** of the replayed state with the landed
rounded models: `pairBeq`, then `compose_eq`, then `Slp.compose … = some ledger`. A packed evaluator rounds
differently (it rounds the exact window product to `2^P` and truncates to a box), so it cannot satisfy it.

**Bridging B1-style, by accelerating the landed products inside the landed segments, is rejected.** It keeps the
9.6 h of per-coefficient regular segments and the ledger volume, and V2-PACKED measured its product gain at about
4.7× on products alone.

**The bridge proposed** is the content of `Slp.compose_sound` itself:

```
theorem jetPacked_sound … (h : jetCheck n p K wit W pe jb jm wanted = true) :
  ∀ i ∈ wanted, PEnc jb.Lb jb.bR jb.P (jetNode jm i) (jetRad jm i) (jetNb jm i) n W.rho
    (fun θ => p.val n (K.eval n θ) i)
```

These are packed models (§11's `PEnc`, scale `2^P`, degree 0) of the same slot functions.

**The consumers.** Each consumer gets a packed variant that takes these packed models where it took
`SlotsEnclose ms`:
- **Torsion:** `checkTorsionJ` is B3b's `checkTorsionR` with its `DX_H ∘ K` and `DH ∘ K` boundary read from the
  jet nodes. This removes `ptAOk`/`ptD1Ok` and the landed `cfgLow` composition.
- **Invariance:** `checkInvarianceJ` takes the packed `X_H(K) − DK (s ω)` from the jet's `d1` nodes, `DK` (the Gram
  memo) and the frequency constant. It then needs one packed norm (§B2 `pcNorm`) plus radii, ≤ `err`.
- **Energy:** `checkEnergyJ` takes the zero-key slot of the `v0` node (`PEnc.average`, B3) ± radius, ≤ `err`.

The base checker `jetBase : BaseChecker` combines the landed `checkStatic`, `checkHamBounds` and `checkEmbedding`
with the packed Gram stage (B2), the packed torsion (B3b/J), the packed invariance and the packed energy. It
reaches the landed `CertifiedTorus` through the landed `checkV2With_sound`. No landed `Slp.compose` remains.

**Landed contracts reused:**
- `SlpOp.step`/`Slp.val` (the semantics);
- `charSlot_sound`, `invWitness_sound`, `sqrtWitness_sound`, `expWitness_sound` (the nonlinear operations);
- the landed `invarianceModel`/`energyOk` statements as the target conclusions;
- `torsion_eq_models` (via B3b).

### 12.3 The packed representation

- **A jet node** is a packed model on a **box** `Lb`: an ℓ∞ box of half-width `h`, stride `4h + 1`, slot width `w`.
  It is held at scale `2^P` and **degree 0**, with a radius and a norm bound.
- **Degrees are removed at the constants.** A `const re im d` becomes the dyadic ball of
  `(re + i im)(2π)^d`, with the π enclosure (`pe`) in its radius. The same holds for the `(2π)^{dA_j}` of `action j`.
  The landed models keep degrees to avoid π rounding; at `P = 128` the rounding is about `2^-120` relative, which
  is negligible against `cfgLow`/`cfgFull` truncation.
- **Products** land on the window `Lw = win Lb Lb`, at scale `2^(2P)`.
- **Linear operations stay exact and on the box.** `add`, and `mul` by a constant, are done with mixed scales:
  `c x` with `c` at scale `2^Pc` lands at `2^(P + Pc)`, and summands are aligned by an exact unit shift. The scale
  is re-normalized only at the next reduce.
- **Box per chain.**
  - `Low`: `h = 25`, the B3b box, which contains the `cfgLow` cutoff (ℓ¹ 24). The window is 101 × 101, about
    3.6 Mbit at `w ≈ 360`.
  - `Full`: `h = 48`, which contains the `cfgFull` cutoff 48. The window is 193 × 193, about 13.4 Mbit, under the
    16.8 Mbit numeral cap with no `LEAN_NAT_MAX_SIZE` change. The invariance tolerance (`err = 8.1·10⁻¹⁸`) needs
    the larger box: the tail beyond `|k| = 48` must sit far below `err`. The generator checks this before
    emitting.

### 12.4 The residual check, in two forms

The core lemma is §11's `PEnc.stage`. `x` is the exact value on the source layout and `x'` a candidate on the box.
If the residual's packed norm plus the propagated radius stays below the candidate's radius, the candidate is a
packed model of the same function. The lemma needs only an `SRep` of `x'`. There are two ways to obtain it:

- **(M) Memo.** `x'` is a generator literal validated by `packRepOk`, exactly as in B3b. This needs no new
  lemma, but costs one literal per reduced node. LG00 has about 690 products, at about 1.2–2.5 k terms per node
  (both parts), which comes to ≈ 40–80 MB of source per certificate.
- **(Z) Computed in the kernel.**
  - `x'` is computed by the kernel itself. `gmpRound` (Round.lean, already proved) rounds to scale `2^P`; one
    mask on the offset digits zeroes the slots outside the box; one exact shift moves it onto `Lb`.
  - `x'` is then validated by one Boolean `boxOk Lb l x'`. This is `loadOk` (Round.lean) restricted to the box:
    the offset `2^l` sits on the box slots only, the mask allows `l + 1` bits on the box slots and 0 elsewhere,
    and there is one comparison.
  - **Lemmas.** `boxOk_sound : boxOk L l Z = true → ∃ d, SRep L (2^l) Z d` needs a digit-wise `&&&` lemma (an
    induction on `land_split`, Digits.lean) and the closed form of the box mask. The mask is one row pattern times
    `periodic (w·S) R 1`, proved like `periodic_eq_natPack`. Estimate: 150–250 lines.
  - **No literal** is needed inside a segment. The correctness of `gmpRound` or of the mask is **not** needed:
    `boxOk` and the residual decide everything, so a wrong computation fails closed.

**Recommendation: (Z).** It removes the per-node literal volume, which is LG00's other cost centre (≈ 125 MB of
source and 3.6 CPU-h of elaboration at L = 20), and keeps segments long. (M) remains the fallback for nodes whose
inputs come from another process: the ledger.

**The nonlinear operations:**
- **`char k`** (120 operations, 24 witnesses). The operand is the embedding's `U`, not a chain slot, so the landed
  witness check runs unchanged (`charSlot`, cached). Its output, the landed `shiftModel`, is packed by `pcOfPoly`
  with `pcOfPolyOk` (B2, `PCRep.ofPoly`); the generator checks its keys fit the box. LG00 measured one
  certification at about 22 s, i.e. 24 per chain.
- **`inv`, `sqrt`, `exp`** (4 operations in LG00). The operand is a chain slot.
  - Its box node is written once as a landed `CertPoly` memo `Q₀`. The kernel checks that
    `pcOfPoly Q₀ = x'` (one packed equality), and converts the `PEnc` into a landed `CertModel.Encloses` of
    `⟨0, Q₀, ofRatUp r⟩` (`PEnc.toModel`, new, about 40 lines, via `srep_of_packRepOk`/`intEval`).
  - The landed witness check then runs on that model.
  - These operations stay landed because they are rare: four witnesses at 10–20 s each.

### 12.5 Segments and the ledger

The program is cut into **segments** of consecutive operations, as in the landed plan but simpler.
- **The state.** A segment's state is a list of packed nodes (box, scale, radius, norm bound), with no cache and
  no `nExp`/`nInv` counters. Witness indices are static functions of the program (the number of `exp`/`inv`
  operations before slot `i`, and the slot itself for `sqrt`), computed in the plan.
- **Seeding.** A segment is seeded from the **ledger**: (M)-memos of the slots it imports, each validated by
  `packRepOk`. It runs its live operations in the kernel (linear operations exact, products followed by a (Z)
  reduce, nonlinear operations as above) and **exports** its ledger slots.
- **The export check.** It compares the exported node with its ledger memo (packed equality and `ble` of radius
  and norm bound).

**The plan check.**
- Segments tile the program.
- Imports come earlier and are exported.
- Every wanted slot is on the ledger.

The landed `planOk`/`segsTile` logic carries over without the metadata.

**The chain theorem** (`jetChain_sound`) is a strong induction on the slot index. If every live slot of a
segment is a packed model of its slot function given its operands' models, and every import is one by the
induction hypothesis (through the ledger), then every export is one. The per-operation lemmas are:
- `const`, `action`: exact data and a π radius;
- `add`, scalar `mul`: `PEnc.add`, `PEnc.mul` with a constant, the unit shift (§9–§11);
- product `mul`: `PEnc.mul`, then `PEnc.stage` with the (Z) validator;
- `char`, `inv`, `sqrt`, `exp`: the landed witness soundness through `PCRep.ofPoly` / `PEnc.toModel`.

Dead operations (not on a path to a wanted slot) are skipped, as the landed `shadowStep` does; `opDeps` and
liveness are computed by the plan.

### 12.6 Cost model (LG00 rates from B3b; ±2×, to be gated)

- **Per genuine product** (box `h`, one complex product plus a (Z) reduce plus a residual norm): about 0.5 s of
  kernel time at `h = 25`. This scales from B3b's `TRStN`: 12.4 s for 8 entries of 2 complex products, packing
  included. At `h = 48`, about 2 s: ×4 sizes, near-linear GMP.
- **Per linear operation:** 10–50 ms (GMP additions and small multiplications on numbers of at most 4 Mbit).
- **Per witness:** landed, 10–22 s.
- **Per segment:** import plus ledger elaboration, about 15–30 s. Segment length is bounded by kernel memory:
  about 30 MB per product kept by the kernel, so about 50 products and 1.5 GB per segment, ≤ 4 GB.

| chain | products | linear ops | witnesses | segments | estimate |
|---|---:|---:|---:|---:|---:|
| Low (`h = 25`) | ≈ 345 × 0.5 s | ≈ 3,000 × 0.03 s | 26 × 20 s | ≈ 10 × 25 s | ≈ 1,000 CPU-s |
| Full (`h = 48`) | ≈ 345 × 2 s | ≈ 3,000 × 0.03 s | 26 × 20 s | ≈ 15 × 25 s | ≈ 1,700 CPU-s |

**Total:** ≈ 0.75 CPU-h against 24.2 CPU-h landed, about 30× on the two chains, and ≈ 20× with consumer and data
overheads. These are estimates. The first gate measures one `Low` segment of 50 products at LG00 size.

**Memory and the numeral cap.** Every number is at most one window (3.6 Mbit `Low`, 13.4 Mbit `Full`), so no
`LEAN_NAT_MAX_SIZE` change is needed. Every process is planned at ≤ 2 GB.

### 12.7 Lean work, in order (after the audit findings)

1. `boxOk`, `boxOk_sound`, and the (Z) reduce with its `PEnc.stage` instance. Gate: one LG00 product at
   `h = 25` and `h = 48`.
2. Jet nodes and the per-operation lemmas (`const`, `action`, `add`, scalar and genuine `mul`, `char`, `inv`,
   `sqrt`, `exp`), including `PEnc.toModel`.
3. Segments, the ledger, the plan, and `jetChain_sound` → `jetPacked_sound`.
4. The consumers: `checkTorsionJ` (B3b on the jet's boundary), `checkInvarianceJ`, `checkEnergyJ`, and
   `jetBase` → `CertifiedTorus`.
5. The generator: a plan cutter by product count and memory, ledger memos, the (Z) mirror (bit-exact, as
   `torsr_gate_gen.py`), and the gate on LG00's two chains.

### 12.8 Open points for the owner

- **(M) or (Z).** (Z) is recommended: no literal per node, 150–250 lines of digit lemmas.
- **The `Full` box (`h = 48`, window 13.4 Mbit) against a split of the invariance residual into two boxes.** The
  generator decides it from the measured tail, below `err`.
- **The production data module** (owner decision 1) is shared with the jet ledger and the B3b memos.

**Decided (orchestrator, overnight, 2026-11-01):**
- (Z): the reduced values are computed in the kernel and validated by `boxOk`; literals only as a fallback.
- The larger `Full` box is accepted (13.4 Mbit, under the numeral cap, no `LEAN_NAT_MAX_SIZE` change).
- The jet ledger shares the production data module.

### 12.9 First gate (measured; `docs/campaign/handoffs/V2-PACKED-JET-GATE.md`)

**Built.** `Packed/Box.lean` (`boxOk`, `boxOk_sound`: the digit lemma in closed form), `Packed/StageZ.lean`
(`zPC`, `PEnc.reduceZ`), `Packed/JetNode.lean` (nodes, `jAdd`, `jMul` with the reduce, `jRed`),
`Packed/JetSeg.lean` (`jSegOk`, `jSegOk_sound`: imported nodes enclosing their slot functions give exported
ones), `Packed/JetIngest.lean` (narrow ledger literals spread in the kernel) and `Packed/JetTests.lean`.

**Gate.** LG00's cfgLow slots [7099, 7292): 55 box-by-box products, 13 products by constants (reduced in place),
46 sums; 53 imports, 35 exports; 83 landed segments.

| | landed (run20e) | packed |
|---|---:|---:|
| processes | 228 modules | 23 sub-segments |
| CPU (user + sys) | 4,815 s | 512 s (279 s kernel) |
| largest charge | 5.27 GB | 4.29 GB (4 GiB cap) |

That is **9.4×** on the range, with the production assembly unmeasured. The range's 53 imports are landed models,
rounded to packed form and taken as hypotheses of `jSegOk_sound` (not kernel-checked). Superseded by §12.11, where
every import is an earlier packed export.

**The cost model of §12.6 was optimistic:**
- **Kernel time** is 4.1 s per heavy step inside a run, against 0.5 s estimated. Standalone, a product with its
  reduce takes 0.65 s, and each of its two packed norms 0.8 s.
- **Kernel memory** is about 0.5 GB per heavy step inside a run, against 30 MB. The kernel keeps every
  intermediate of a declaration.
  - So a 4 GB process holds at most 4 heavy steps, and fewer when a piece carries many ledger memos.
  - The 55-product segment in one process is OOM-killed.
- **The ledger memos are box nodes** (2,601 coefficients, against about 515 landed terms). Each is ingested in
  0.18 s and about 30 MB.

**Next.** Memory engineering of the run: why the run keeps far more than the sum of its operations. Then the
chain theorem over the sub-segments and the plan (§12.7 item 3).

### 12.10 Kernel memory of the run (V2-PACKED-JET-MEM; `docs/campaign/handoffs/V2-PACKED-JET-MEM.md`)

**What held the memory.** Not the packed arithmetic: a product with its reduce and its two norms keeps about
5–20 MB. Two costs scaled with the run.

- **The program read.**
  - The probe wrote the program as `ops_0 ++ ops_1 ++ … ++ ops_36`. `++` associates to the left, so every cell of
    the first chunk passed through 36 appends.
  - `jRun` also read `p.ops.getD i` from slot `0` at every step.
  - One read at slot 7291 took 4.6 s and 1.1 GB of kernel, and a run step about 0.4 GB.
  - **Fix:** right-nested appends in the generator, and the segment runs on `p.ops.drop start`, computed once
    and shared, at `i - start` (`jSegOk … start …`, `getD_drop_sub`).
- **Literal ingestion.**
  - The digit-by-digit re-spacing (`respace`) was one kernel operation per digit: 0.22 s and 37 MB per part.
  - **Fix:** `jSpread` spreads in about 18 whole-number steps. In each block the upper half moves by one
    closed-form mask, one multiplication and one addition.
  - Literal widths are rounded to multiples of 8, so the masks are shared, and zero parts are written `0`.
  - Cost: about 0.02 s and 13 MB per part.

**Measured** (the same LG00 range as §12.9: 68 heavy steps, 53 imports, 35 exports):

| cut | processes | heavy steps per process | CPU | kernel | largest charge |
|---|---:|---:|---:|---:|---:|
| §12.9 | 23 | ≤ 4 | 512 s | 279 s | 4.29 GB |
| one process | 1 | 68 | 29.0 s | 6.0 s | 3.90 GB |
| **34 (chosen)** | 2 | 34 | 54.9 s | 8.4 s | 2.65 GB |
| 20 | 4 | ≤ 20 | 71.3 s | 11.1 s | 2.22 GB |

- **The kernel now takes 0.09–0.16 s per heavy step.**
- **CPU is now mostly data elaboration.** The data control is 19–25 CPU-s per process: the elaborator, not the
  kernel. A shared data module (production assembly) would remove most of it.
- **Comparison with the landed range** (228 modules, 4,815 CPU-s): 88× at the chosen cut. The landed column
  counts theorem modules only, while each packed process also elaborates its own ledger data. The 53 imports are
  landed models, rounded to packed form and taken as hypotheses (not kernel-checked); superseded by §12.11.


### 12.11 The whole Low chain (V2-PACKED-JET-LOW; `docs/campaign/handoffs/V2-PACKED-JET-LOW.md`)

**Built.**
- **`Packed/JetLeaf.lean`.** Leaves from landed models: `toDeg` to degree 0, then box truncation into the radius,
  then packing.
- **`Packed/JetChain.lean`.**
  - `chain_sound`, an induction on the block order;
  - segments, the action block and given blocks.
- **`Packed/JetChar.lean`.**
  - Characters `character(k) · ∏ᵢ exp(σᵢ i 2π angleAtᵢ)^{|kᵢ|}`;
  - the exponential as a Taylor sum with Mathlib's `exp_bound'` remainder;
  - powers and products.
- **`Packed/JetWit.lean`.**
  - `inv` and `sqrt` in residual form, with an untrusted candidate validated by `boxOk` and the bounds
    `inv_sub_le` (Neumann) and `sqrtE_sub_le`;
  - `jRenorm`, which restores the cancellation a sum node's norm bound loses;
  - the whole-chain theorem `jChainW_slot`: every exported slot is a packed enclosure of the program's slot
    function at the embedding.
- **No given blocks.**

**Measured on LG00's whole cfgLow chain** (`lg00-cert` `fd82fef5`):
- 3,745 live slots, 20 wanted;
- 60 blocks, one process each: 41 segments (≤ 34 heavy steps), actions, 4 exponentials (Taylor degrees 17 and
  22), 4 power blocks, 6 character blocks (≤ 8 keys), 2 `inv`, 2 `sqrt`.

**What is checked (AUDIT-V2-PACKED-JET-1 M1).**
- Every one of the 60 blocks passes in the kernel, as a **separate theorem** over a probe-local copy of the
  program, the embedding, the weight and the π enclosure.
- **The LG00 instance of `jChainW_slot` is not built.** Its hypotheses are not discharged in Lean for LG00:
  - `hfirst` (the block order) and `hng` (no given block). Both hold as data; the audit checked all 944 imports.
  - `jBookOk`, which is checked inside each segment only.
  - `checkWeight gW` and `checkPiEnclosure lgPe`, which appear in no probe.
- **The probe program is a prefix.** It is the first 7,752 of the 7,816 operations of `lg00Jet.prog`, so a prefix
  lemma (`Slp.val_append`) is needed unless the data module names `lg00Jet.prog` itself.
- `JNode`, `PC` and `CertFixed` have no `DecidableEq`, so `hfirst` as stated (membership of `(key, node)` pairs)
  cannot be decided. With a shared data module it can be shown by name; alternatively, derive `DecidableEq` or index
  the ledger by key.

| | landed Low stage (run20e) | packed |
|---|---:|---:|
| CPU (user + sys) | 50,440.0 s (14.01 h) | **1,415.0 s** (321.3 s kernel) |
| largest charge | — | 3.62 GB (4 GiB cap) |

**That is 35.6×, with the production assembly unmeasured:**
- the shared data module;
- one theorem over the 60 blocks with its order proof (the instance of `jChainW_slot`, above);
- the consumer bridge.

The landed figure counts each module's last, successful run. With LG00's two failed earlier attempts of one
module it is 50,514.9 s, and 35.7×.

**By kind:**

| kind | ratio |
|---|---:|
| segments and actions | 35.9× |
| characters | 39.8× |
| `inv`/`sqrt` | 7.6× |

**Where the CPU goes.** The kernel takes 0.20 s per heavy step. About 18 CPU-s per process is import and data
elaboration.

**Controls.** A one-ulp lower radius on an exponential, a power, a character, an `inv` and a `sqrt` export
decides `= false`.

**Accuracy (configuration against configuration, not method against method).**
- The packed configuration's radii on the wanted slots are 1e-17 to 3e-15, against 2e-4 to 3e-2 for the landed
  configuration.
  - The landed cfgLow trims to a sparse diamond (70–625 terms) and puts the tail in the radius.
  - The packed nodes keep the dense 51 × 51 box, about 5× the ledger volume.
- The norm bounds agree to about 1e-5 relative.
- The margin that matters is the downstream torsion check. It cannot be measured until the consumer exists.

**`P = 64`.**
- **Precision.** The margin is large: about 10 orders even with 10⁴ growth (estimate).
- **Design.** The leaf conversion needs `jb.P` equal to the arithmetic's precision (`CertFixed.toMant`).
  - Recommended: keep `CertFixed 128` and the landed embedding, and add a leaf conversion that rounds to
    `2^jb.P` into the radius.
  - Then measure.

### 12.12 The whole Full chain (V2-PACKED-JET-FULL; `docs/campaign/handoffs/V2-PACKED-JET-FULL.md`)

**Built.** `Packed/JetStage.lean` stages the exponential, since a whole Taylor sum on the 97 × 97 box does not
fit one process:
- the keys `TKey` (`w`, the Taylor term and the partial sum at `m`), so the chain runs over `JKey ⊕ TKey`;
- the blocks `tstart`, `tstep` (`k` Taylor steps from any `m`), `texp` (the partial sum plus `jExpRem`) and
  `pows` (powers from any power);
- `JBlockT.sound`, `jChainT_sound` and `jChainT_slot`.

**Measured on LG00's whole cfgFull chain** (`lg00-cert` `fd82fef5`):
- 1,837 live slots and 5 wanted (`v0`, `d1`), on the box `H = 48` (window 193 × 193, slots of 400 bits);
- 169 blocks, one process each:
  - 88 segments (at most 8 heavy steps and 15 imports + exports);
  - 5 action blocks;
  - the staged exponentials (4 `tstart`, 28 `tstep` of at most 3 Taylor steps, 78 in all, 4 `texp`; Taylor
    degrees 17 and 22);
  - 12 power blocks (at most 2 powers each, 20 in all), 24 character blocks (2 keys each), 2 `inv` and 2
    `sqrt`.

**What is checked.** As for Low (§12.11): each block is a separate theorem over probe-local data.
- The LG00 instance of `jChainT_slot` is not built: `hfirst`, `hng`, `jBookOk`, `checkWeight` and
  `checkPiEnclosure` are not discharged in Lean.
- The per-block theorems do not check the degree or power labels of their imports (a `texp` fed a lower-degree
  sum, or a `pows` fed a lower power, passes its own check). Only the block order `hfirst` ties the labels, so
  it is load-bearing. AUDIT-V2-PACKED-JET-FULL-1 checked it as data: all 892 imports equal an earlier export,
  key and literal node alike.
- The probe program is the first 7,736 of the 7,816 operations of `lg00Jet.prog`.

| | landed Full stage (run20e) | packed |
|---|---:|---:|
| CPU (user + sys) | 36,734.5 s (10.20 h) | **4,382.8 s** (945.7 s kernel) |
| largest charge | — | 4.08 GB (4 GiB cap) |

**That is 8.4×, with the production assembly unmeasured:**
- the shared data module;
- one theorem over the 169 blocks with its order proof;
- the consumer bridge.

With the ledger's failed attempts the landed figure is 36,743.3 s, still 8.4×.

**Where the CPU goes.**
- **The kernel** takes 1.04 s per heavy step in the segments, 5.8× Low's, for 3.7× the bits.
- **The fixed part is 78% of the CPU:** 20.3 s per process. The imports are 2.2 s and the probe's copy of the
  program, book and embedding 9.6 s; the block's own node literals are the rest.
- **The shared data module** would remove about 1,620 CPU-s. Estimate, unmeasured: about 13×.
- **By kind:**

| kind | ratio |
|---|---:|
| segments and actions | 8.8× |
| characters | 7.7× |
| `inv`/`sqrt` | 6.6× |

**Memory.** At Full the nodes a process holds dominate its memory: about 0.125 GB per import or export, against
0.13 GB per heavy step.
- A segment of 8 heavy steps and 24 nodes was OOM-killed at 4 GiB.
- Segments are now cut at 15 nodes (`--seg-io`). They took 1.62–4.08 GB.

**Controls.** A one-ulp lower radius on a `tstart`, a `tstep`, a `texp` and a `pows` export (from the power 3)
decides `= false`.

**Accuracy (configuration against configuration).**
- The packed radii on the 5 wanted slots are 5.8e-23 to 1.2e-21, 1.1–2.8% of the landed cfgFull radii (3.0e-21 to
  4.1e-20).
- The norm bounds agree to 6e-8 relative.

## 13. Packed frames and the packed route-A-refined engine (branch `v2-packed-frames`; `docs/campaign/handoffs/V2-PACKED-FRAMES.md`)

Route A refined tests `checkHamClaim && checkFrameMajorants && refinedCore`. The landed `checkFrameMajorants`
(`Frame/Majorants.lean`, unchanged) re-evaluates the landed Gram check and torsion models. `Packed/Frames.lean`
reads the same four bounds from the objects of B2 and B3b.

- **`|Lᵀ| ≤ bL`** (`checkFrameLR`): column sums of `nb + r` over the packed `DK` entries `ptK` (the Gram memo,
  checked by B2's `pgEntries`).
- **`|N| ≤ bN`, `|Nᵀ| ≤ bNt`** (`checkFrameNR`): row and column sums of `nb + r` over the verified memo of
  `N = Ω₀ (L G⁻¹)` (stage `trStN`).
- **`sup |T| ≤ bT`** (`checkFrameTR`): row sums of `pnorm + r` over the packed `T = Nᵀ Ω₀ X_N` on the window.
  These use every B3b stage through `X_N` and the guard `aT ≤ aW`.
- **`|ω*| ≤ bOm`**: the landed `checkFrameOmega`.

**Soundness.** `checkFrameMajorantsR_sound` has the conclusion of the landed `checkFrameMajorants_sound`
(`FrameMajorants c b ωstar`), under its hypotheses. Each entry is bounded by `‖f θ‖ ≤ nb + r` of its `PEnc`
(`PEnc.norm_le_bound`); for `T` the bound uses the packed weighted norm (`PEnc.renorm`).

**Engine.** `routeARefinedPacked bk mm rb tm rm : EngineV2` keeps the landed `checkHamClaim` and `refinedCore` and uses
the packed frames. `checkV2With_packed_sound` concludes the landed `CertifiedTorus` from
`checkV2With (torsRBase …) (routeARefinedPacked …) c w = true`. No landed Gram product, torsion model or frame model
is evaluated.

**Sharing.** Each frame check repeats, as the identical Boolean terms, the conjuncts it shares with
`checkTorsionR`: `gramPackedCheck`, `Slp.compose`, `ptEntries`, `trLayOk`, `trNormOk`, `ptPackOk` and the seven
`trSt*`. A production proof establishes each once and assembles the result with `checkFrameMajorantsR_of` (and
`checkTorsionR_of`). The kernel work specific to the frames is only `trFrameLOk`, `trFrameNOk` and `trFrameTOk`.

**Gate (LG00, `lg00-cert` `fd82fef5`).**
- `FRL`: 2.0 s kernel, 7.0 CPU-s.
- `FRN`: 0.02 s kernel, 8.6 CPU-s.
- `FRT`: 8.9 s kernel, 22.1 CPU-s, 2.43 GB.

Packed value against LG00's claim:

| bound | packed | claim |
|---|---:|---:|
| `\|Lᵀ\|` | 1.3620 | 1.37 |
| `\|N\|` | 1.1992 | 1.21 |
| `\|Nᵀ\|` | 1.4397 | 1.45 |
| `sup \|T\|` | 117.504 | 118 |

**End to end.**

| | modules / processes | CPU-s |
|---|---:|---:|
| landed modules the packed route removes (from lg00-cert's import graph) | 732 | 14,138 (run20e) |
| packed replacement (B2 9 + B3b 64 + frames 3) | 76 | 1,402.5 |

- The net saving is **12,736 CPU-s ≈ 3.54 CPU-h**, i.e. **11.8 %** of LG00's 30.08 CPU-h (30.08 → 26.54).
- **Production assembly is unmeasured:** the shared data module and the assembly theorems are not in the packed
  figure.
- The `Low` and `Full` jet compositions (24.2 CPU-h) are unchanged; they are §12's target.
