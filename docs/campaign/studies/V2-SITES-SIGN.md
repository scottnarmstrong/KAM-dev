# V2-SITES-SIGN: sharp small-divisor sites for LG00

Date: 1 November 2026. Decision taken by the orchestrator from these numbers: **both tori at L = 18, route A refined with
the sign-tolerant sharp sites.** Reproduce:

```sh
nice -n 10 python3 -B -I scripts/certifier/lg00_sites.py   [--tpp] --json OUT     # the sites of T′ (T″)
nice -n 10 python3 -B -I scripts/certifier/lg00_margins.py [--tpp] --json OUT     # the table below
```

## Result

Margin is `e*/err`. "`refinedCore`" is the exact-rational mirror of the whole numerical test at a concrete witness, at the
`err` of a real dry run. `kp` is the number of certified prefix stages.

| Torus | L | support | `err` | classical | sharp `kp = 3` | sharp `kp = 4` | `refinedCore` (`kp = 4`) | `disp` needed |
|---|---:|---:|---:|---:|---:|---:|---|---:|
| T′ | 17 | 487 | 8.47·10⁻¹⁵ | 0.1× | 8.5× | 14.7× | true | 1.02·10⁻¹⁰ |
| **T′** | **18** | **551** | **7.20·10⁻¹⁶** | **1.1×** | **99.9×** | **173×** | **true** | **8.45·10⁻¹²** |
| T′ | 20 | 683 | 8.06·10⁻¹⁸ | 99× | 8,921× | 15,469× | true | 9.44·10⁻¹⁴ |
| **T″** | **18** | **553** | **6.56·10⁻¹⁶** | **0.01×** | **9.0×** | **15.9×** | **true** | **1.57·10⁻¹¹** |
| T″ | 20 | 685 | 7.76·10⁻¹⁸ | 1.0× | 764× | 1,342× | true | 1.83·10⁻¹³ |
| T″ | 21 | 749 | 9.74·10⁻¹⁹ | 7.8× | 6,086× | 10,692× | true | 2.29·10⁻¹⁴ |
| T″ | 22 | — | not available | not available | — | — | — | — |

Thresholds: T′ `10^-15.098` classical, `10^-13.143` (`kp = 3`), `10^-12.904` (`kp = 4`). T″ `10^-17.118`, `10^-14.227`,
`10^-13.982`. The classical figures reproduce LG00-T2's.

- **Least L at a margin of at least 10×:** T′ L = 17 (14.7×, `kp = 4`), T″ L = 18 (15.9×, `kp = 4`).
- **At the chosen L = 18, T″ needs `kp = 4`:** `kp = 3` reaches only 9.0×. T′ passes at either, so `kp = 4` can be used for both.
- **The T″ L = 22 row is not available:** kamx-certside's classical run failed on a precision budget, unrelated to sites. So
  no measured classical route reaches 10× on T″; the best measured is 7.8× at L = 21.

`r″` also has a negative last coordinate (`-41.27`), and the sign-tolerant site covers it, with `γ/κ = 7/100`.

**The lower L fits LG00's other budgets.** The largest `disp` above is `1.02·10⁻¹⁰` (T′ at L = 17), and at L = 18 it is
`1.6·10⁻¹¹` at most. `disp` enters confinement as `corr = disp/ρ∞`, which is `2.7·10⁻⁶` at L = 18 against `λ ≈ 0.28`, and
moves TR2 by about `6·10⁻⁸` against a margin of `0.003`. The frequency window takes `disp/‖ω*‖ ≈ 4·10⁻¹³` against `5·10⁻¹⁰`.
LG00 should pass these numbers through its own confinement mirror.

## Projected kernel cost

**Sites, measured.** Every site of both tori passes in the kernel under a 4 GB cap:

| Torus | Sites | Blocks | Kernel CPU, net of imports | Slowest process |
|---|---:|---:|---:|---:|
| T′ | 8 | 4 direct, 24 blocks | 292 s | 16 s |
| T″ | 8 | 4 direct, 32 blocks | 331 s | 16.5 s |

**Certificates, projected.** This scales LG00's L = 20 ledger (30.11 CPU-h, 5,183 modules) by support, using LG00's own
measured ratios from L = 18 to L = 20 (calls ×1.3, shards ×1.25, targets ×1.5). It is a projection, not a measurement.

| Certificate | Support | CPU-h | Range | Modules |
|---|---:|---:|---:|---:|
| T′ L = 20 (classical, 99×) | 683 | 30.1 | measured | 5,183 |
| T″ L = 21 (classical, 7.8×, short of 10×) | 749 | 33.8 | 33–36 | ≈ 5,800 |
| **T′ L = 18 (sharp)** | 551 | **23.1** | 20–24 | ≈ 4,000 |
| **T″ L = 18 (sharp)** | 553 | **23.2** | 20–24 | ≈ 4,000 |

So the two tori cost about **46 CPU-h against at least 64**, a saving of about 18 CPU-h (27 %). That baseline understates it,
since T″ at L = 21 does not reach 10× classically. The sites add about 0.17 CPU-h in all.

## What was built

- **Sign.** `sdConst_ray_of_neg` reflects a small-divisor constant, because `cohR (-ω) g = -cohR ω g`. So landed `siteOk` runs
  unchanged on the reflected box, and `SmallDivQ.lean` is byte-identical. The lemma is about `SDConst`, not one checker, so it
  also serves kamx-3freq's `fiberSiteOk` with no change on that side.
- **Engine.** `routeARefinedS` is `routeARefined` with the sites on a box of the witness. `refinedCoreS_ofRefined` shows a
  landed witness passes at its own box.
- **Shards.** `biteOk_of_shards` proves `biteOk` from blocks with short rational bounds. The test itself is unchanged.

## What the measurements changed

- **The short box does not save kernel cost.** I expected it to, since it cuts the exact sum from 120 kbit to 14 kbit. Measured
  on real sites, long and short boxes cost the same (`l = 10`: 13.71 s and 5.19 GB against 13.76 s and 5.14 GB). The cost is
  the kernel's cache, about 0.86 MB per mode, which matches kamx-3freq's 0.8 MB per fibre for exact rationals. The witness box
  stays because it carries the reflection, and it keeps the literals short.
- **Sharding is what fits the cap.** A whole `l = 11` bite is killed at the 4 GB cap, and lunar's `l = 12` took 123 s and about
  9 GB. In blocks of `2⁹` fibres, no block exceeds the cap, even at `l = 13`.
- **`kp = 4` was needed.** My first estimate put T′ at 11.8× at L = 17; the real dry run gave 8.5× at `kp = 3`. One more certified
  stage gives 14.7×. `kp = 5` adds little (16.2×) and needs `l = 14`.
- **Certified constants are close to the float ones,** within 1.4 % of `c_freq`, and `c` is about 4 times below the classical
  constant at the prefix stages.

## Scope and caveats

- **`refinedCore` here is the mirror.** The site constants are kernel-checked and the mirror matches Lean on the checked
  quantities, but no complete T′ or T″ certificate has run through `routeARefinedS` yet. That is kamx-certside's run.
- **The whole opt-in files were not run.** Under the rule against building `kernel-tests/`, each block ran alone in a scratch
  copy, and the assembly was checked with the blocks stubbed.
- **Margins assume the claim of the dry runs** (`dh`, `dx`, `d2x`, `d2h`, frame bounds), which do not change with L.
- **The saving is a projection** by support, and it ignores any lower precision a smaller L might allow.
