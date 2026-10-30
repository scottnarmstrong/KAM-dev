# SO-DATA-1: the complete lunar certificates, mirror-checked against the landed checker

Branch `inp-sodata1`. Python, generated data and Markdown only. No Lean file was touched, and nothing was built:
the worktree has no `.lake`.

## Verdict

**Both tori pass all eight sub-checks and `checkSoGraph`.** The checker is a fixed-point mirror
(`CertFixed 320`) of the landed checker, including the landed packed route. The run is a fresh CHECK pass over
exactly the emitted advice books.

- **Ruling.** The first run stopped because `checkHamBounds` failed for R1 (§6). The owner ruled under D29:
  M := 203/100, with σK, σB and σT unchanged.
- **Gate (§3).**
  - **Key coverage:** emitted keys = looked-up keys. The one exception is `[7]`, which the checker supplies itself
    (`realLowerModel` appends `([7], direct)`).
  - **Negative controls:** the controls must fail, and they do (§4).
  - **Determinism:** a rerun must reproduce the output byte for byte (§4).
- **Volume.** Per torus: about 2.1 MB of advice (run-length-coded JSON) and 1.4 MB of certificate data.
  129 packed products, of which 63 have an 8.3–8.7k-term factor, and 1,157 shards.
- **Design signal for SO-DATA-2: kernel memory of the model evaluation (§5).** The packed shards are not the
  risk. The risk is `Slp.compose`, which carries about 500 slots of 8.5k-term 320-bit models. The projection below
  is not a measurement.

## 1. The data (per torus; literals as emitted)

| | lower ν₋ | upper ν₊ |
|---|---|---|
| `ham` | `soRotHamExprScaled lunarR1TimeScale` | same |
| `params` | `lunarR1 lunarLowerErr lunarLowerDisp`, M = 203/100 | `lunarR1 lunarUpperErr lunarUpperDisp` |
| **`lunarLowerErr` / `lunarUpperErr`** | **101/(5·10⁷⁹) = 2.02e-78** | **393/10⁸¹ = 3.93e-78** |
| **`lunarLowerDisp` / `lunarUpperDisp`** | **173/(5·10⁴⁴) = 3.46e-43** | **21/(3.125·10⁴³) = 6.72e-43** |
| frequency box | `κ(ν−1)` from √5 ∈ [a, a+1]/10¹¹⁰ (`checkRootEnclosure 2 5`), radius 3.0e-114; `(κ, 0)` | same, b = −1 |
| weights | ρ = 1/70; ρ_H = 257/10000; `w = ratExpUp(2 piUpQ ρ, 12, 30)` rounded up at 10⁻³⁰ | same |
| `expHalvings`, `expOrder` | 12, 30 | same |
| domain | c = (48769/50000, 24983/50000), r = (191/12500, 127/20000) | SO-GEN2's upper domain values |
| π enclosure | Machin (k, j) = (72, 21), width ≈ 1e-100; centre `ofRatDown` of the midpoint; radius half-width + 4 ulp | same |
| embedding | (ψ + v/2π, φ, p, p + J) as `CertRealPoly`s at 2⁻³²⁰ (4237 / 4233 half terms of v) | |
| witnesses | one character witness E (8307 / 8322 terms) under key (2, 0), pinHalvings 0, **pinOrder 70** | |
| Gram witness B | SO-GEN2's 48-bit B (345 / 315 / 291 terms; B₂₁ = B₁₂) | |
| torsion witness S | inverse of the mirror's own averaged centre, at 2⁻⁴⁰ (complex `CC`) | |
| cfgFull | cutoff 100000, taylorN 30, halvings 12; 3 packed keys `[0,10]`, `[1,0,0]`, `[1,0,1]` | |
| cfgLow | cutoff 30, taylorN 30, halvings 12; 126 packed keys | |
| graph | mono 0.6397713, pLo 0.9676314, pHi 0.9821229 | mono 0.6397153, pLo 1.0178820, pHi 1.0323666 |

**The O1 band holds.** Lower `pLo − disp = 0.96763 ≥ 0.967`, and upper `pHi + disp = 1.03237 ≤ 1.033`. Both have
6.3e-4 to spare. The confinement window lies between the two tori: (0.9821229, 1.0178820), widened by disp.

**Packed-remainder budgets:** 1e-80 per cfgFull product and 1e-8 per cfgLow product.

## 2. Margins (CHECK pass)

| sub-check | lower | upper |
|---|---|---|
| `checkStatic` | ray margin 8.96e-7; weight margins 6.4e-31 / 5.3e-31 | same |
| `checkHamBounds` | bounds [1.97995, 1.896, 1.896, 1.56489, 2.02053] ≤ 2.03 (margin 0.00947) | [1.97996, …, 2.02053] |
| `checkEmbedding` | DK rows 1.36035 (margin 0.6204); ι 0.005148 (margin 1.64e-5); action margin 2.99e-5 | 0.6203; 1.53e-5; 3.44e-5 |
| `checkInvariance` | rows [1.66e-86, 4.68e-96, **2.0110e-78**, 5.57e-79] ≤ err (margin 9.0e-81) | [3.32e-86, 4.68e-96, **3.9196e-78**, 9.70e-79] (margin 1.04e-80) |
| `checkEnergy` | 1.44e-80 | 2.42e-80 |
| `checkGram` | δ = 1.18e-7, β = 1.979942; margin `σ − β − σδ` = 8.07e-4 | δ = 1.17e-7, β = 1.980060; 6.89e-4 |
| `checkTorsion` | ‖I−SC‖ = 1.1e-12, ‖S‖ = 0.53929, R = 0.4516, δ_T = 0.2435; margin 0.959 | δ_T = 0.2442; 0.958 |
| `checkSmallness` | C₁ ratio 0.00207; C₂ ratio 0.998 (disp is the minimum, rounded up) | 0.00402; 0.9995 |
| `checkSoGraph` | disp 3.46e-43 < mono·ρ∞ = 9.1e-6; SOS margins 3.3e-7 / 3.0e-7 / 3.8e-7 | 6.72e-43 < 9.1e-6; 2.3e-7 / 3.2e-7 / 2.4e-7 |

**Notes on the margins.**
- The invariance rows reproduce SO-GEN2's c·η: 2.010e-78 and 3.919e-78.
- err was chosen as the largest bound × 1.001, at three digits. That is smaller than SO-GEN2's G-J budget of
  4.03e-78, which the landed checker does not need.
- The torsion radius `R = 0.45` comes from the cfgLow truncation at cutoff 30. The σT slack absorbs it with a lot
  of room, so a smaller cutoff is a lever (§5).

## 3. Key coverage

| | emitted | looked up | difference |
|---|---:|---:|---|
| cfgFull | 3 | 3 | none |
| cfgLow | 126 | 127 | `[7]` (`realLowerModel`'s own `([7], direct)`; verified by running `checkSoGraph` alone: lookups = {(7,)}, misses = ∅) |

No `[5, a, l]` or `[4, 10, …]` key is emitted or looked up, because `freqModel` is constant and takes the scalar
route (SO-TEST-B N1). The witness keys are full keys `[1, 0, j]`, from `forWitness 1 (expWit.length + 0)`.

## 4. Cross-checks, negative controls, determinism

- **The toy cross-check** (`sofx_toyxcheck.py`) on T2, T2d, T3 and TR uses the mirror over ℚ, against the aligned
  toy mirror's recorded results.
  - The verdicts match: all sub-checks pass on all four toys.
  - Every compared exact quantity agrees to 1e-12. These are the invariance bound, the energy value, Gram δ and β,
    torsion δ_T and ‖S‖, and all five ham bounds.
  - Over `CertFixed 320` and 448, T2 and T3 pass every sub-check.
  - T2d (err 1e-192) and TR (err 0) fail only invariance and energy. Their err sits below any 320- or 448-bit
    rounding, which is expected and not a mirror defect.
- **Negative controls** (`sofx_negative.py`): **all four rejected** (`{lower,upper}_negative.json`).
  Tightened err gives `checkInvariance = false` on both tori. The corrupted `[0,10]` slot gives `checkEnergy = false` on both.
  1. err := 0.99 × the largest invariance row must fail `checkInvariance`.
  2. One in-box advice slot of `[0, 10]` raised by 2 must make `checkPackedProduct` reject the product. The crude
     fallback then must fail `checkEnergy`.
- **Determinism:** a second full run into a separate directory, compared by SHA-256. **Byte-identical** (§8);
  details in §8.
- **Data.** Under `certificates/lunar-spin-orbit/`, and mirrored to `/mnt/HC_Volume_106379410/kam-data/so-data1/`.
  Every file is under 20 MB. SHA-256s are in `SO-DATA-1.sha256`. Regenerate with
  `cd scripts/spin_orbit && nice -n 10 python3 sofx_gen.py lower|upper OUTDIR`, then
  `python3 sofx_negative.py lower|upper OUTDIR`.

## 5. For SO-DATA-2: what goes to the kernel, and an estimate of time and memory

**Per-product sizes (lower; upper within 3 %).**
- Every packed product has P = 320, so factor mantissas are 320 bits and the slot width w is 640–659 bits.
- blockRows = 32. The blockLen is 5,632–5,664 slots for full-box factors and 2 blocks' worth for the small ones.

| family | n | factor terms A × B | blocks | shards | w | nonzero advice |
|---|---:|---|---|---:|---:|---:|
| cfgFull `[0,10]` p̃·p̃ | 1 | 8475 × 8475 | 12 × 12 | 23 | 658 | 19,277 |
| cfgFull `[1,0,j]` witness | 2 | 8306–8390 × 8307 | 12 × 12 | 46 | 657 | 39,020 |
| cfgLow `[3,0]` Gram DKᵀDK | 9 | 8306–8660 × same | 12 × 12 | 207 | 659 | 1,929 |
| cfgLow `[1,0,j]` witness | 2 | 8306–8390 × 8307 | 12 × 12 | 46 | 657 | 381 |
| cfgLow `[0,10]` | 1 | 931 × 8475 | 2 × 12 | 13 | 656 | 237 |
| cfgLow `[4,0]`, `[4,2]`, `[4,6]` (DK × small) | 36 | 8306–8660 × 164–900 | 12 × 2 | 468 | 658 | 9,471 |
| cfgLow `[4,1]` (small × DK) | 12 | 870–900 × 8306–8660 | 2 × 12 | 156 | 652 | 4,189 |
| cfgLow `[3,1]`, `[4,3]`–`[4,5]`, `[4,7]`–`[4,9]` (small × small) | 66 | 158–931 × 156–297 | 2 × 2 | 198 | 640–655 | 14,265 |
| **total** | **129** | | | **1,157** | | **88,769** |

**The design-level cost: 63 heavy products, not 3.** Of the 129 products, 63 have an 8.3–8.7k-term,
320-bit factor. This is the confirmed note 1.

**Kernel time of the packed checks.** This scales from SO-REPLAY2: 2–5 s per 32-row shard at w = 896, and the
width factor `(0.05 + 0.1w/896)/0.15` ≈ 0.82 at w ≈ 655 gives ≈ 1.6–4 s per shard.
- 12 × 12 products: 23 shards, ≈ 40–90 s each. There are 14 per torus.
- 12 × 2 products: 13 shards with short partners, ≈ 10–25 s each. There are 49.
- 2 × 2 products: 3 shards, ≈ 3–6 s each.
- **Total ≈ 0.5–1.3 CPU-h per torus, 1–2.6 CPU-h for both,** plus per-declaration overhead for 1,157 shard
  theorems per torus (≈ 10–20 min at 0.5–1 s each).

**Kernel memory of the packed checks.** Expect ≤ 2.4–3.8 GB per shard declaration with literal blocks (SO-REPLAY2).
- SO-DATA-PY measured **8.0 GB** when a full 11k-slot window was decoded through `unzero` and packed in the
  kernel.
- Shards must be separate declarations with their block packings tied once (`tie_A0` style), not decoded and
  re-packed per shard.

**Kernel memory of the model evaluation: the main risk.**
- **The SO-TEST-A comparison.** T2d's checkEnergy needed 12 GB for a 531-term exact-ℚ witness, and its
  checkInvariance took 19 GB and was still growing.
- **The lunar workload is far larger in terms.** `checkInvariance` and `checkEnergy` each run `Slp.compose` over
  all 887 slots. About 500 of them hold 8.3–8.5k-term models: shifts of E and scalar multiples, which are kept in
  `ComposeState`. That is roughly 4·10⁶ live terms of 320-bit `Int`s, plus per-step `mergeErrTerms`, `sumUp` and
  `supNormUp` passes.
- **The lunar workload is cheaper per term.** Fixed-point `Int` arithmetic does not grow the way the exact ℚ
  denominators do, which is what blew up T2d.
- **My estimate (not measured):**
  - per call, the live term data is a few GB at minimum, at ≈ 0.5 KB per kernel term-node set;
  - the kernel's whnf caching could multiply that 5–20×, giving **10–50 GB per `compose` call** if one
    `decide +kernel` proves `checkInvariance` whole;
  - checkTorsion runs a third compose at cfgLow, and checkGram and checkTorsion each build the 8.5k-term DK
    models.
- **The Python mirror for scale:** 210 s (invariance) and 200 s (energy) per CHECK pass, and 500 s for Gram and
  420 s for torsion, with packed checks included.
- **Recommendation for SO-DATA-2:**
  - first measure one `compose` prefix (for example the first 100 slots) in the kernel;
  - if it extrapolates past about 16 GB, the design needs a split. Options: per-slot or per-row lemmas over a
    certified cache of slot models, or `checkInvariance` split by row through a sound decomposition lemma.
  - Lowering the cfgLow cutoff (R = 0.45 leaves room) shrinks only the small factors.

## 6. History: the STOP and the ruling

The first run stopped because `checkHamBounds` failed for R1.
- **The failing bound.** Σ_{a,b}|∂_a∂_b H| = 2.02053 > 1.987. A closed form confirms it. No domain helps, because
  ρ_H is pinned by `checkEmbedding`.
- **The suspected erratum** is in SO-GEN2's majorant 1.047601; the landed form gives 1.06568 at c = 1.
- **The ruling:** M := 203/100 (D29 overnight mode, logged for the owner). SOSignaturesLunar §I.4 has been updated,
  and SO-R1B is changing LunarParams.lean to match.

## 7. Deviations and errata

- **Suspected erratum, not in a pinned source:** SO-GEN2's ‖D²H‖ majorant (§6), now resolved by the ruling.
- **SO-GEN2's `pinOrder = 1` cannot pass.** `certCExp` always adds `eRem(N+1)`, which is 3/4 at N = 1, so the pin
  error is 0.75. The data uses pinOrder 70 (`eRem(71)` ≈ 1e-102).
- **`lunarR1Box` (√5 to 1e-6) is a pre-check helper only.** Its 6e-10 radius enters the Q1 invariance row
  directly (8.5e-10 ≫ err). The certificate uses a √5 enclosure at 10⁻¹¹⁰.
- **The torsion witness S is recomputed.** It is the inverse of the mirror's own average centre, not SO-GEN2's
  c = 1 witness.
- **The certificate's own err** (2.02e-78 / 3.93e-78) replaces SO-GEN2's G-J budgets (4.03e-78 / 7.84e-78).
- **Data convention:** `J_cos` is stored at scale 318, not at `J0_scale_bits`.
- **Inputs not extracted from Lean:**
  - The jet comes from `adv_jet.py`, the Python mirror of the compiler; Diff* has had no changes since 074bd0c5.
    The toy jets agreed with Lean (SO-TOYGEN).
  - The B₁₂ parity is inferred from the data's symmetry.

## 8. Determinism result

A second full `sofx_gen.py` run of both tori, into a separate directory, gives **byte-identical** certificate and
advice files:

| file | SHA-256 (both runs) |
|---|---|
| lower_cert.json | c9ea2311218d3811a4d4cf3893325d31b540d61d84a18b570d406b3cc25b0827 |
| lower_advice.json | 261e832fdfcda9dc5c2130ff626ef09f5af6cca7399bac77065143d09dd2f31e |
| upper_cert.json | 12738836f6e613cc6bf6aa38824582f57af7447f4ae433804b3459cfb4c291ac |
| upper_advice.json | 28121f04009907f813c143a12bac7e1e99b3cd7ea99972cbf0e3f9c212981a1d |

The `*_report.json` files differ only in the wall-clock fields (`seconds`, `generate_seconds`, `check_seconds`).
Every verdict, margin and size field is identical.
