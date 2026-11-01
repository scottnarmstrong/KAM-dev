# V2-SITES-SIGN handoff: sharp sites for a negative last coordinate

Branch `v2-sites`, based on `origin/main` at `ebc762be`. Not pushed, not merged. v2-energy and v2-3freq were not merged and
are not needed. Full tables: [V2-SITES-SIGN study](../studies/V2-SITES-SIGN.md).

## Result

| Torus at L = 18 | `err` | Classical | Sharp `kp = 3` | Sharp `kp = 4` | Mirror `refinedCore` | Kernel, all 8 sites |
|---|---:|---:|---:|---:|---|---:|
| T′ | 7.20·10⁻¹⁶ | 1.1× | 99.9× | **173×** | true | passes, 292 s |
| T″ | 6.56·10⁻¹⁶ | 0.01× | 9.0× | **15.9×** | true | passes, 331 s |

**T″ needs `kp = 4` at L = 18:** `kp = 3` is short of 10×. Least L at 10× or more: T′ 17, T″ 18. Projected cost of the two
certificates: about 46 CPU-h against at least 64, a saving of about 27 %.

**Not yet done:** no complete certificate has run through `routeARefinedS`; that is kamx-certside's run. The lint's ABI step
could not run (see Checks).

## Using it (for kamx-certside)

- **Engine:** `routeARefinedS`, or `routeV2AllS` with witness `Sum.inr ws`. Soundness:
  `checkTorusCertificateV2_routeARefinedS_sound`, or `checkTorusCertificateV2_sound`.
- **Witness:** `RefinedWitS` is `⟨base, neg, bw⟩`, with `neg := true` and `bw` the short reflected box.
  - `base.κ` is the **positive** `|κ|`, the last coordinate of `bw`.
  - `base.core.kp := 4`, `c := [c(δ₀..δ₃)]`, `cbar := [c(b₀..b₃)]`.
  - `base.sites := [(some ⟨E1, l, 8, B⟩ at δ_s, same at b_s), …]`.
- **Data:** `docs/campaign/studies/v2-sites-data/sites_tp.json`, `sites_tpp.json`: `bw`, `kappa`, `gamma` and per site `b`, `E1`, `l`,
  `B`, `c`. The cut-offs are `l = 10, 11, 12, 13` at `δ₀..δ₃` and `8, 9, 10, 11` at `b₀..b₃`, on both tori. `J = 8`.
- **Concrete witness numbers:** `margins_tp.json`, `margins_tpp.json` give `Xs` and `disp`, including L = 18.
- **Large sites:** prove `biteOk` by `biteOk_of_shards` with `l₀ = 9` for `δ₁, δ₂, δ₃, b₃`, then `siteOk_some_of`, then the landed
  `sitesOk_of`. The other four fit one declaration. The blocks' bounds and a generated template are in
  `kernel-tests/CertificateSharp/V2/SitesLG00.lean` and `SitesLG00T2.lean`; move the blocks to your package as needed.
- **`coverOk`** on your real box is a cheap decide. **`disp`:** use at least the table's value, and rerun your confinement mirror.

## Files

No existing `.lean` file is edited. `git diff --diff-filter=MDR --name-only origin/main...HEAD -- '*.lean'` gives only the
generated `KAM/Root/CertificateSharp.lean`. `SmallDivQ.lean` and `Majorants.lean` are byte-identical to main, and nothing is
under the restricted Moon-track paths.

- `KAM/CertificateSharp/V2/SiteSign.lean`: `negBox`, `cohR_neg`, `sdConst_ray_of_neg`, `signBox`, `signVec`, `coverOk`,
  `sdConst_of_siteOk_sign`.
- `KAM/CertificateSharp/V2/SiteShard.lean`: `balAll_of_shards`, `balSum_le_of_shards`, `sideOk`, `shardOk`, `biteOk_of_shards`,
  `siteOk_some_of`.
- `KAM/CertificateSharp/V2/RouteARefinedS.lean`: `RefinedWitS`, `refinedCoreS`, `refinedCoreS_of`, `refinedCoreS_ofRefined`,
  `refinedCoreS_sound`, `refinedTestS`, `routeARefinedS`, `routeV2AllS`.
- `KAM/CertificateSharp/V2/Tests/SiteSign.lean`: the negative-clock toy.
- `KAM/CertificateSharp/V2/Tests/SiteSignMirror.lean`: generated cross-language test.
- `kernel-tests/CertificateSharp/V2/SitesLG00.lean`, `SitesLG00T2.lean`: generated, opt-in, with `kernel-tests/README.md` updated.
- `scripts/certifier/`: `bite_sign.py`, `lg00_sites.py`, `lg00_margins.py`, `lg00_sites_emit.py`. `scripts/apost_sharp/structured_b.py`
  is unchanged here.
- `docs/campaign/studies/V2-SITES-SIGN.md`, `docs/campaign/studies/v2-sites-data/` (dry-run JSONs, sites, margins).

## Approach

- **Sign at the `SDConst` level.** `cohR (-ω) g = -cohR ω g` gives `sdConst_ray_of_neg`, so any site test run on `negBox box` serves
  `ω*`. `sitesOk` is called unchanged, on the witness's box.
- **`refinedCoreS_sound`** copies `refinedCore_sound`; only the site step differs.
- **Shards prove `biteOk`,** so no new test enters the checker. A block's short bound `u` replaces the exact accumulator.
- **`Mh1`-free:** this branch does not need v2-energy.

## Checks and output

```text
lake build KAM.CertificateSharp.V2.Tests.SiteSign KAM.CertificateSharp.V2.Tests.SiteSignMirror   # one at a time, 4 GB scope
Build completed successfully
```

- **Toy (`decide +kernel`):** `toyNeg` is T2 with `H ↦ -H`, `ω ↦ -ω`, and every base sub-check runs on it.
  - The landed `routeARefined` rejects it, in `clockOk`.
  - `routeARefinedS` accepts it, on the reflected box and on a short box, and inside `routeV2AllS`.
  - A box that misses the certificate's box is rejected, and so is the wrong sign.
  - T2 itself passes at `neg = false`. `toyNeg_torus` gives the torus at `-(ν₋/2, 1/2)`.
- **Mirror against Lean:** `bal_up` lands under all five of lunar's Lean-derived `B` within their `10⁻³` rounding, up to `l = 12`. The
  exact `balBound` matches the kernel by fingerprint on a toy bite and on T′'s real site `b₀`. The mirror reproduces LG00's
  classical `X⋆ = 121/10⁹`, threshold and displacement coefficient `1.68·10⁵`. A real site, `lg_bite`, is in the default build (6 s).
- **Shards:** 24 blocks of T′ and 32 of T″, each alone under a 4 GB cap: all pass.
- **Assembly:** `biteOk_of_shards` with its real `sideOk`, `hB`, `hnum`, in a scratch copy with the blocks stubbed: compiles.
- **Dry runs:** T′ L = 17, 18 run by me with LG00's generator (read only). T″ L = 18, 20, 21 are kamx-certside's. All seven landed
  sub-checks pass in each.

**`scripts/lint_sources.sh`: exit 1, from the ABI step only.** Line length, modules (`check_lean_modules: PASS`), root check and
`FROZEN-ANCHOR GUARD OK` pass. `abi_hashes.py` stops at a missing olean: 43 of the 179 anchors have none in the seed. This branch
touches no frozen file, but **the ABI check has not been run on it**, and neither has a full `lake build`.

## Axioms

```text
sdConst_ray_of_neg                             [propext, Classical.choice, Quot.sound]
sdConst_of_siteOk_sign                         [propext, Classical.choice, Quot.sound]
biteOk_of_shards                               [propext, Classical.choice, Quot.sound]
refinedCoreS_sound                             [propext, Classical.choice, Quot.sound]
checkTorusCertificateV2_routeARefinedS_sound   [propext, Classical.choice, Quot.sound]
toyNeg_torus                                   [propext, Classical.choice, Quot.sound]
SiteMirror.lg_bite                             [propext, Classical.choice, Quot.sound]
SiteMirror.toy_bite_of_shards                  [propext, Classical.choice, Quot.sound]
```

## Measurements

| Site cost, T′ | `b₀` | `b₁` | `δ₀` | `b₂` | `δ₁` | `b₃` | `δ₂` | `δ₃` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cut-off `l` | 8 | 9 | 10 | 10 | 11 | 11 | 12 | 13 |
| blocks of `2⁹` | direct | direct | direct | direct | 4 | 4 | 8 | 16 |
| net kernel CPU | 2.8 s | 5.5 s | 11.4 s | 10.9 s | 24 s | 24.5 s | 58.5 s | 156 s |

T″ is similar, 331 s in all. Largest RSS: 5.16 GB for a whole `l = 10` bite and 4.90 GB for a block, of which 3.39 GB is the
import baseline.

## Owner questions

Nothing here blocks.

1. **The clock index (kamx-3freq's question).** My recommendation, sent to that session: keep the clock last and let the application
   reorder its coordinates. The sign was cheap because `cohR` is odd in `ω`; a permutation is a change of variables on the torus.
   The decision is yours, and I have not had a reply.
2. **`kp = 4` for both tori?** T′ does not need it at L = 18 (99.9× at `kp = 3`), and using `kp = 3` there would skip `δ₃`'s 156 s. Using 4
   for both is simpler for the generator, and costs almost nothing. I recommend 4 for both.

## Deviations and errata

- **Memory:** several processes exceeded 4 GB RSS (5.16 GB at most), from mapped imports. The 4 GB `MemoryMax` scope held for
  every passing run, and it is the scope that killed the whole `l = 11` bite.
- **`kernel-tests/`:** those files were not built, per the rules; the blocks ran from scratch copies.
- **Disproved hypothesis:** the short box was meant to save kernel cost and does not. See the study.
- **Corrections to my own estimates:** T′ at L = 17 was 11.8× by extrapolation and 8.5× measured at `kp = 3`.
- **T″ L = 22:** not available, as kamx-certside's run failed on a precision budget, unrelated to sites.
- **T″ at L = 17** was not measured; the decision does not need it.
- **Suspected errata in pinned sources:** none.
