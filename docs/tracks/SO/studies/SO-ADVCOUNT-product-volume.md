# SO-ADVCOUNT: the real products and the advice volume of the lunar certificate (track SO)

Branch `inp-soadv` (off `inp-sogen2`). Python and a report only: no Lean file was touched or built.
Inputs: design Revision 5 (`KAM-inp-design-so:docs/tracks/SO/design/SO-LEAN-DESIGN.md`, §1, §5, §7.2), the
signatures `.drafts/design/SOSignatures.lean` / `SOSignaturesLunar.lean`, the LANDED jet compiler on `inp`
(`KAM/Certificate/Expr/{DiffBuild,DiffNode,Diff}.lean` at `074bd0c5`), SO-REPLAY2's measurements, and the
R1 data `certificates/lunar-spin-orbit/{lower,upper}_rot.json` (SO-GEN2, L = 88, 318 bits).

## Verdict

**The count is 128 genuine model products per torus, not 30–120.** Only **3** of them are at full precision.
Their advice is about **4 MB per torus and 8 MB for both tori**, against §7.2's 66–310 MB per torus.

| | per torus (lower / upper) | both tori |
|---|---:|---:|
| genuine complex model products | 128 / 128 (131 if `gramModels` computes both off-diagonal entries) | 256 |
| real products under the re/im split, nominal (×4) | 512 | 1,024 |
| real products that are not identically zero | **128** (exactly one of the four, by parity) | 256 |
| of which full precision (≈ 318-bit factors, 8.3–8.5k terms) | **3** | 6 |
| design-B advice, best of decimal / hex list literals | 3.91 / 4.03 MB | **7.95 MB** |
| + embedding and witnesses (v, p, J, E, B, S) | 1.06 MB | 2.13 MB |
| shard theorems (`checkShard … = true`) | 463 / 465 | 928 |
| kernel, SO-REPLAY2 model | 0.10–0.15 CPU-h | **0.21–0.29 CPU-h** |
| elaboration of the data (18 s/MB) | ≈ 1.5 min | ≈ 3 min |

The real danger is somewhere else. The jet of `c·H'` contains **478 scalar×model `mul` slots**. Of these,
308 per torus lie on the invariance, energy and torsion paths. If `Slp.compose` sent them through
`CertModel.mul`'s packed route, each would cost ≈ 0.39 MB of advice and ≈ 20–25 s of kernel. That adds
**≈ 120 MB and ≈ 2 CPU-h per torus**, 15 times everything else. **`Slp.compose` must multiply by constant
slots as scalars** (SO-EMB). This needs no signature change, but it is a hard implementation requirement.

## Method

1. **Products of the Hamiltonian composition.** `scripts/spin_orbit/adv_jet.py` is an operation-by-operation
   Python mirror of the landed `slpCompile` / `HamExpr.jet`. This includes `none` folding and `slpScaleO`'s
   `const`·`mul` emission. It is applied to `soRotHamExprScaled c` verbatim from A-L.
   - The program has 887 slots and 486 `mul` ops.
   - Composition with K is modelled by slot kind:
     - `action j` gives the data component (M);
     - `char k` gives a shift of the character witness (M; `χ_k∘K = χ_k·E`, an exact `CertPoly.shift`);
     - a constant is C.
   - Each `mul` is then classed as CC, CM or MM over the dependency closure of each `compose` call.
2. **Products of the sub-checks.** `scripts/spin_orbit/adv_count.py` reruns SO-GEN2's pipeline and records
   every `SPoly.mul` with its factors and calling line.
   - The pipeline is `rot_build.build(which, 88, 88, 88, 318)`, whose term counts are asserted against
     `<which>_rot.json`, followed by `rot_norms.norms`, the checker-style Gram/torsion chain of the literal
     `extendedTorsion`.
   - SO-GEN2 used its cfgLow stage there: 72-bit models, trim 2⁻⁵⁶.
   - It adds the `checkSoGraph` SOS witnesses, which are constructed here.
3. **Every genuine product is simulated as the design-B packed product** (`scripts/spin_orbit/adv_pack.py`).
   - **Layout.** Dense box layout with rows = first key, the no-wrap stride `colsA + colsB − 1`, and
     `blockRows = 32`. Slot width w = max(`convFits` minimum, `bitsA + bitsB + 16`).
   - **Exact window sums.** Every shard window T_s = Σ_{i+j=s} conv(A_i, B_j) is computed exactly by
     Kronecker packing with GMP integers. The overlap-add is checked against direct convolution.
   - **Advice.** The target box, the rounding scale (P_out) and `outLog` are the smallest that keep the
     packed remainder within a stated budget. The remainder is in-box 2^−P_out·Σ_box W(|k|) plus out-of-box
     2^(outLog+1)·Σ W(|k|), W ≥ e^{2πρ|k|}, ρ = 1/70.
     - Budget 1e-80 for full products. This is ≤ 2 % of r_φ = 5.4e-79, ≤ 0.06 % of r_ψ = 1.7e-77, and
       ≪ e = 4.03e-78 for the energy.
     - Budget 1e-13 for cfgLow products, whose radii are ≥ 1e-12 in SO-GEN2.
   - **Volume.** The rounded in-box values of **every window** are counted. Windows overlap by one block, so
     interior slots are shipped twice. They are counted with exact digit counts as list literals:
     `n, ` in decimal, `0x…, ` of the zigzag in hex, and `0, ` for zeros.
   - **Costs.** Kernel and elaboration use SO-REPLAY2's measured constants:
     - window pack + slot bound 0.27–0.33 ms/slot at w = 896;
     - 0.2–0.5 s per 8192-slot multiplication;
     - 0.15–0.4 s per block tie;
     - 80 µs/slot for the linear passes;
     - the width factor (0.05 + 0.1w/896)/0.15;
     - 18 s/MB of elaboration.
4. `scripts/spin_orbit/adv_report.py` aggregates the results. Raw results are in
   `certificates/lunar-spin-orbit/logs/advcount/`.

Reproduce (≈ 7 min per torus):
```
cd scripts/spin_orbit
python3 adv_count.py lower L.json
python3 adv_count.py upper U.json
python3 adv_report.py L.json U.json S.json
```

## 1. Inventory: every product of one torus

| Sub-check | Products (genuine MM) | Notes |
|---|---:|---|
| `checkStatic`, `checkSmallness` | 0 | rationals |
| `checkHamBounds` | 0 | ℚ ball arithmetic on D, no Fourier products |
| `checkEmbedding` (ball, DK) | 0 | DK by `ofDeriv` (exact multipliers), row sums are norms |
| `checkInvariance` (`compose`, wanted = d1) | **0** | closure: 170 slots, 72 CM + 3 CC. `∂H'` is linear in the data and the shifts of E. `DK·(sω)` is scalar×model. |
| `checkEnergy` (`compose`, wanted = v0) | **1** full: `(1·p̃)·p̃` | the only MM slot in the whole jet (`pow` 2); plus 25 CM |
| exp / character witnesses | **2** full: `(∂_ψ g₀)·E`, `(∂_φ g₀)·E` | one character witness serves all 14 keys ±(2, 2−m) (normalized index (2,0); −k by `conjReflect`). The pin is a scalar `certCExpReduced`. There is no `exp` slot. |
| reciprocal witnesses | 0 | `H'` is division-free |
| `checkGram` | 9 (`DKᵀDK`, symmetric) + 8 (`B·G`) | generic `gramModels` with both off-diagonal entries: 12 + 8 |
| `checkTorsion` | 106 | N 12, DG 24, D(G⁻¹) 16, DN 24, DX_H(K)·N 8, Nᵀ Ω W 16, DH(K)·N 6. Plus 16 with an empty factor (zero rows of D²K[sω] and DK) and 4 scalar (the constant row (0, 1) of DK). The composed d1/d2 slots: 201 CM + 7 CC, 0 MM. |
| `checkSoGraph` | 2 (SOS g·g*) | p range, window side (37–39-term g) and band side (11 terms). `mono` needs none: g = 0 gives m = 1 − ‖∂_ψv/2π‖ ≈ 0.64 ≫ disp/ρ∞ ≈ 3e-38. |
| **total** | **128** (3 full + 125 cfgLow) | 2 SOS included |

**Real versus complex.** Each factor has a definite parity: either all coefficients real, or i·real. This
holds for v, p, J, E, their derivatives, and every product in the chain. So exactly one of the four real
products (re·re, im·im, re·im, im·re) of each complex product is nonzero. The design's "four real products per
complex product" is 512 nominal per torus. **The packed route must treat an all-zero part as free** (an empty
layout and an empty product). Otherwise kernel time is ×4 and shard theorems ×4.

## 2. Per product (lower torus; the upper torus agrees to within 5 %)

Every row is a family of real products with one nonzero part each.

| Family | prec | n | terms | bits | w | P_out | block slots | shards each | pairs | advice slots | dec MB | hex MB | fixed-width MB | kernel s |
|---|---|---:|---|---|---|---|---|---|---:|---:|---:|---:|---:|---|
| energy `p̃·p̃` | full | 1 | 8475 × 8475 | 319/319 | 654 | 311 | 5664 | 23 | 144 | 90950 | 0.845 | 0.784 | 7.46 | 80–118 |
| witness `(∂_j g₀)·E` | full | 2 | 8306–8390 × 8307 | 317/318 | 638–651 | 311–312 | 5632 | 23 | 288 | 185288 | 1.713 | 1.585 | 15.19 | 158–232 |
| Gram `DKᵀDK` | low | 9 | 212–260 | 73/73 | 130–162 | 57–59 | 1056–1184 | 3 | 36 | 22512 | 0.089 | 0.094 | 0.43 | 8–10 |
| Gram `B·G` | low | 8 | 235–375 | 49/73 | 108–138 | 57–60 | 1248–1312 | 3–4 | 36 | 21978 | 0.088 | 0.092 | 0.42 | 9–11 |
| torsion N = Ω₀DK·G⁻¹ | low | 12 | 212–289 | 68/73 | 131–162 | 57–60 | 1120–1248 | 3 | 48 | 31064 | 0.123 | 0.130 | 0.59 | 12–15 |
| torsion DG | low | 24 | 212–282 | 68/73 | 133–157 | 58–60 | 1120–1248 | 3 | 96 | 66600 | 0.273 | 0.288 | 1.27 | 24–29 |
| torsion D(G⁻¹) | low | 16 | 235–422 | 73/69 | 126–158 | 58–60 | 1312–1376 | 3–4 | 72 | 49950 | 0.203 | 0.214 | 0.95 | 19–24 |
| torsion DN | low | 24 | 212–466 | 68/73 | 125–158 | 58–60 | 1184–1312 | 3–4 | 102 | 75328 | 0.303 | 0.319 | 1.43 | 26–33 |
| torsion V_QQ·N | low | 8 | 263–366 | 66/68 | 137–150 | 58–60 | 1248–1376 | 3–4 | 36 | 24144 | 0.097 | 0.103 | 0.46 | 9–12 |
| torsion Nᵀ Ω W | low | 16 | 235–462 | 68/68 | 126–162 | 58–61 | 1376–1440 | 3–5 | 82 | 55884 | 0.222 | 0.234 | 1.07 | 22–27 |
| torsion DH(K)·N | low | 6 | 239–371 | 63/68 | 134–156 | 58–59 | 1120–1312 | 3–4 | 28 | 16548 | 0.065 | 0.069 | 0.31 | 7–8 |
| SOS g·g* | low | 2 | 11–37 | 37/37 | 90 | 52–56 | 32–160 | 1–3 | 5 | 611 | 0.004 | 0.004 | 0.01 | < 1 |
| **total** | | **128** | | | | | | | 973 | 640857 | **4.02** | **3.91** | 29.6 | **375–519** |

Column notes:
- *terms*: factor term counts (A × B where they differ).
- *bits*: largest mantissa bit lengths.
- *P_out*: result mantissa scale needed for the budget.
- *advice slots*: in-box slots summed over windows (the overlap is counted twice).
- *fixed-width*: the same slots as fixed P_out-bit hex. This is SO-REPLAY2's "full width per slot"
  assumption, about 7× the list format.

**Full products in detail.**
- Lower `p̃·p̃`:
  - factor box [−178, 178] × [−44, 44];
  - stride 177; 12 + 12 blocks of 32 rows (5664 slots); 23 shards of 11328 window slots; 144 block pairs;
  - product 34,703 terms;
  - target box [−212, 212] × [−53, 53] (45,475 slots), of which 79 % of the shipped slots round to 0;
  - P_out = 311, rounding scale 327, outLog = 298;
  - remainder 2.8e-81 in-box + 9.8e-83 out-of-box.
- The witness products are similar: P_out 311–313, remainder ≤ 4.0e-81.
- **P_out ≤ 313 < 318**, so `soPrecision` = 318 bits suffices for every product. No guard bits beyond the
  data precision are needed.
- Kernel memory per shard is about 7.4 Mbit per window, below SO-REPLAY2's measured 2.4–3.8 GB case.

**Why §7.2's per-product estimate (2.2–2.6 MB) is 3× too high.**
- §7.2 assumed every in-box slot carries ≈ P bits.
- The coefficients decay from O(1) to 1e-88 and beyond. Advice values are short in the tail, and most box
  slots round to 0.
- Shipped as fixed-width numbers (or as packed chunk literals of r), the same advice would be **7.5 MB per
  product**. **The list-literal format is a volume lever in its own right.**
- §7.2 also counted single coverage. Design B checks each window separately, so interior rows are shipped
  twice. That is included above.

## 3. Totals and the §7.2 packaging options (both tori)

| Scenario | products | advice MB | data MB (+ embedding 2.13) | A: lint-clean files (greedy 100-col lines; one per product / packed) | A: one coefficient per line | B: files (one per product / packed at 6 MB) | C: data files + ≈ 30 Lean modules | shard theorems | kernel CPU-h |
|---|---:|---:|---:|---|---:|---|---|---:|---|
| **S1 as designed** | 256 | 7.95 | 10.07 | 302 / **72** | 1,055 | 258 / **2** | 258 (or 2–4 grouped) | 928 | 0.21–0.29 |
| S2 = S1 + against-data checks | 230 | 2.79 | 4.92 | 246 / 35 | 621 | 232 / 1 | 232 | 730 | 0.07–0.09 |
| S3 = S2 + zero-mode-only torsion | 186 | 2.22 | 4.34 | 202 / 31 | 496 | 188 / 1 | 188 | 576 | 0.06–0.07 |
| S4 = S3 + DG symmetry | 162 | 1.94 | 4.06 | 178 / 29 | 436 | 164 / 1 | 164 | 504 | 0.05–0.06 |
| naive scalar route (avoid!) | +616 | +240 | ≈ 250 | ≈ 1,800 (packed) | — | ≈ 42 | — | +7,400 | +3.5–4.3 |

Notes on the columns:
- *Option A*: ≤ 1,450 data lines of ≤ 100 characters per file.
  - "Greedy" packs consecutive short coefficients on one line.
  - A full-precision coefficient has ≤ 95 decimal digits plus sign (P_out ≤ 313 bits), so it still fits a line with
    no limb splitting.
  - "One per product" starts a new file for each product: the 250 small cfgLow products are about 0.01 MB
    each, so they would mostly be one file each.
  - "Packed" lets products share files.
- *Option B*: the design's ≈ 6 MB / ≈ 2 min per file.
- *Option C*: one data file per product (or one per torus and stage), with the design's ≈ 30 Lean modules.

**Recommendation for §7.2.** At S1 every option is manageable.
- **Option A is affordable at about 72 lint-clean generated files** (both tori, products sharing files).
  That needs no lint exemption and no meta-program in the build path.
- About 30 files are needed if the levers of §4 are taken.
- Option B (2 files) and option C (≈ 260 data files) buy little at this volume.

## 4. Volume levers, cheapest first

1. **Scalars are not products** (implementation requirement, no signature change). `Slp.compose` multiplies
   any `mul` with a constant-kind operand by `CertModel` scalar multiplication. Without this: +120 MB and
   +2 CPU-h per torus.
2. **Zero re/im parts are free** (implementation requirement). Parity makes 3 of the 4 real products of every
   complex product identically zero. Without this: kernel and shard theorems ×4. Volume barely changes, since
   zero windows are cheap text.
3. **Advice as variable-length list literals, not fixed-width or packed chunks**: a factor of 7 (§2).
4. **Against-data checks** (a design addition: `checkPackedProduct` with the advice replaced by a polynomial
   the certificate already carries). Check `pack(A)·pack(B) − pack(target)` with slot log-bounds only:
   - witness residual: the target is `∂_jE`, and the slot bound IS r_j;
   - energy: the target is −2(J̃ − Σ εA_m Re(e_m E)), with residual ΔJ (B₀ = 1.2e-80);
   - SOS: the target is f − m₀, and the slot bound is r;
   - `B·G`: the target is I, and the slot bound is δ.

   Effect: −65 % of the advice (−5.2 MB both tori) and −70 % of the kernel. All three full products lose
   their advice. This replaces each by a norm bound in effect. Only per-window (or per-row) log-bounds
   remain as advice.
5. **Zero-mode-only products.** The torsion check reads only the averages of the Nᵀ Ω W block and of the last
   row DH(K)·N. These 22 products become dot products Σ a_k b_{−k}, plus the cross radii, with no advice:
   −0.6 MB and −154 shard theorems (both tori). The energy check is the same shape (an alternative to lever 4 for p̃·p̃).
6. **Symmetry.**
   - DG = A₁ + A₁ᵀ saves 12 products.
   - The Gram matrix needs only its upper triangle: 9, not 12. SO-GEN2 already does this; a generic
     `gramModels` should too.
   - N reuse in DN does not save a product.
7. **No product can be removed outright.** The two witness residual products need 1e-80 absolute accuracy,
   which no norm bound gives. Lever 4 is the way to avoid their advice.

## 5. Uncertainties

- **The kernel figures are SO-REPLAY2's model**, extrapolated to w = 90–656 and 32–5,792-slot blocks. Nothing
  here was run in Lean.
  - The cfgLow products are small (1–2.5k-slot windows). Their cost may be dominated by a per-declaration
    overhead that the model does not include. At ~0.5–1 s per theorem, 928 shard theorems add 8–15 min.
- **cfgLow = SO-GEN2's stage** (72-bit models, trim 2⁻⁵⁶, the `rot_norms` order of operations). The design
  does not fix these numbers. Changing them changes the 125 small products roughly linearly in support.
- **Budgets and boxes are my choices.** The design leaves the target box, `outLog` and `scale` to the
  generator. I minimized them against the stated budgets, using the actual window partial sums.
- **`Slp.compose`, `gramModels` and `torsionModels` are not written yet.**
  - The counts assume the dependency closure of the wanted slots.
  - They assume the matrix products of the literal `extendedTorsion` as SO-GEN2 implements them.
  - A naive whole-program fold would evaluate the jet's d3 table too: 887 slots, but still only 1 MM.
- **SOS.** With a strip-weighted residual, the p-range SOS stalls at a residual floor of ≈ 1.3e-4.
  - A window-side slack of 1e-4 is therefore infeasible. 3e-4 works (37–39-term g).
  - The certified window then loses 3e-4 per side: lower torus max p = 0.98181 → pHi = 0.98211; upper torus
    min p = 1.01820 → pLo = 1.01790.
  - The band side has 9e-4 slack: lower min p = 0.96801 against 0.967, and the upper side likewise.
  - Residuals were computed in double precision, as an estimate.
- Advice digit counts are exact for the stated budgets. File counts use the §7.2 conventions: ≤ 1,450 data
  lines per file, ≤ 97 usable columns, ≈ 6 MB per option-B file.

## 6. Errata and deviations

- **No pinned-source errata suspected.**
- **Design notes for the orchestrator, not errata:**
  1. §7.2's counts table should be replaced by §3 here. Its "30–120 real products" and 2.2–2.6 MB per product
     are both off: there are 128 nonzero products, 3 of them large, ≈ 0.85 MB each.
  2. Decision 16's "four real products per complex model product" should say that zero parts are skipped
     (lever 2).
  3. The SO-EMB brief should state lever 1 as a requirement.
  4. SO-POLY could add the against-data variant (lever 4) and a zero-mode product (lever 5) before SO-DATA.
     Both are sound by the same chain as `checkPackedProduct_sound`.
  5. Design §6 lists R1's time scale as 7/4, while the emitted package uses c = 237/125. SO-GEN2 already
     reported this; I counted at 237/125, and the scale does not affect any count.
