# Handoff SO-TOYFIX2 (T2d kernel feasibility), round 2 after the option-2 ruling

Branch `inp-sotoyfix2`, worktree `/root/code/KAM-inp-sotoyfix2`.

## Verdict: done. `toyCert2d_passes` and `toyCert2d_torus` are proved; every kernel run stays under the 6 GB cap
- Round 1 (commit `3f067bbc`): with `a = 3`, steps 1-3 of the brief cannot fit T2d. That T2d's threshold is
  1e-188.8, so its err is 1e-192, so its 531-term witness at 2^-683 is minimal. Even at a cfgFull cutoff of 270,
  `checkTorsion`, `checkEnergy` and `checkInvariance` are OOM-killed at 6 GB (551 s, 162 s and 95 s wall).
- Round 2 (this commit, per the ruling): the denominator is now `a + cos 2πq` with **a = 10^30**. The signed
  type, the reference vector and the signed statements are unchanged.

## The chosen data
| quantity | old (a = 3) | new (a = 10^30) |
|---|---|---|
| strip ρ / ρ_H / μ / ρ∞ / r | 1/125, 1/100, 1/1000, 1/1250, 3/2000 | **9, 9.02, 1/100, 1, 1/50** (T2's) |
| M = σK = σB = σT | 1598.76 | **2.97** |
| threshold γ⁴ρ⁴/isoC1Q | 10^-188.8 | **10^-38.23** |
| err (positive) | 10^-192 | **10^-42** |
| reciprocal witness | 531 terms, K = 265, 2^-683 | **15 nonzero terms, K = 9, dyadic at 2^-895** |
| root enclosure digits | 194 | 44 |
| cfgFull / cfgLow cutoff | 270 / 30 | **10^6 / 10^6** (no truncation needed) |
| pair products, full / low | 1.79 M / 357 k | **7,994 / 4,100** |

Choosing a: a sweep over a ∈ {10², 10³, 10⁵, 10¹⁰, 10²⁰, 10³⁰} and ρ_H ∈ [1/4, 9.02] (jets re-extracted from Lean
for each a). The strip constrains a: the ball pass needs `a > cosh(2πρ_H)`, and the witness decays like
`(w/(2a))^k`. Only a ≳ 10^25 reaches T2's ρ = 9; a = 10^20 tops out at ρ_H = 5 (threshold 1e-42.3). With
a = 10^30 the threshold equals T2's (10^-38.23). The witness is shorter than the ~50 terms the ruling estimated
(15 nonzero terms, since `(w/2a) ≈ 2e-6` per mode). It still exercises the reciprocal witness, the ball pass with
a certified denominator, `div`, the character witness and the advice book (34 keys per stage).

Margins (mirror):
- invariance bound 4.5e-46 and energy bound 1.1e-46, both against err 1e-42;
- smallness ratio_C1 1.7e-4;
- torsion deltaT 4.5e-12.

## Kernel measurements
One process each, `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 /usr/bin/time nice -n 5 lake env
lean` on a probe `example : checkX toyT2dCert = true := by decide +kernel`. Wall time includes about 8 s of
imports. Max RSS includes the mapped .oleans (the import baseline is about 3.3 GB).
| sub-check | kernel ("type checking") | wall | max RSS |
|---|---|---|---|
| checkStatic | 0.16 s | 10.0 s | 3.35 GB |
| checkHamBounds | 10.4 s | 18.7 s | 4.10 GB |
| checkEmbedding | 0.43 s | 9.1 s | 3.36 GB |
| checkInvariance | 34.3 s | 42.8 s | 4.76 GB |
| checkEnergy | 18.7 s | 29.2 s | 4.36 GB |
| checkGram | 0.95 s | 10.5 s | 3.38 GB |
| checkTorsion | 59 s | 68.5 s | 5.80 GB |
| checkSmallness | 0.16 s | 8.8 s | 3.35 GB |
| whole checkTorusCertificate (probe only) | 65.2 s | 75.9 s | 6.39 GB (RSS; the cgroup did not kill it) |

Because the whole check sits at the edge of the cap, `toyCert2d_passes` is not one `decide`. It is assembled
from the eight separate `decide +kernel` sub-check theorems (`checkTorusCertificate` is their `&&`). The whole
module `Tests/Toy2d.lean`, run under the cap: **rc 0, 114.5 s wall, 4.23 GB max RSS**. Gate build: 126 s.

## Files
- NEW `KAM/Certificate/Tests/Toy2d.lean` (72 lines):
  - `toyCert2d`;
  - `toyCert2d_{static,hamBounds,embedding,invariance,energy,gram,torsion,smallness}`;
  - **`toyCert2d_passes`**, `toyCert2d_freq`, **`toyCert2d_torus`**.
- `KAM/Certificate/Tests/Toy2.lean`: T2 only now. `toyCert2d`, `toyCert2d_freq` and the five light T2d
  theorems moved to Toy2d.lean, under the same names.
- `KAM/Certificate/Tests/Toy2dData.lean` (186 lines, was 1147): re-emitted by `toy_lean_cert.py`.
  `expHalvings := 8` in the hand-written whole-certificate block now matches the JSON (it was 2).
- `scripts/spin_orbit/toy_gen.py`:
  - `T2D_A = 10**30` and the new T2d plan defaults (T2's geometry);
  - `r = 1/(a + √(a²-1))` without cancellation;
  - optional `cut_full`;
  - the emit assertion is now "only T2d may truncate".
- `scripts/spin_orbit/toy_lean_extract.py`: T2d's constant is `T2D_A` (env override, default 10^30).
- `scripts/spin_orbit/toy_negative.py`: the §8.6 negative "denominator ball contains 0" now uses ρ_H = 12
  (w_H ≥ 2a), since ρ_H = 1/5 no longer reaches the denominator's zero.
- `certificates/so-toys/{jets,T2d,negative,summary}.json`: regenerated.

## Checks
- `toy_lean_extract.py` with `T2D_A=3` reproduces the old jets.json exactly. The new jets.json differs only in
  T2d's constant.
- `toy_gen.py … T2d`: `T2d passes {all 8 True}` in 3.5 s.
- `toy_keys.py`: T2/T2d/T3/TR OK (T2d (34, 34, 0, 0) per stage), exit 0, key coverage exact.
- `toy_negative.py … /root/code/KAM-inp-sotoyfix2`: `all as intended: True  lean controls false: True`.
  Diffs in negative.json:
  - the §8.6 test label;
  - the §8.4 charWit mutation no longer also fails checkTorsion (it still fails its intended
    checkInvariance).
- `toy_crosscheck.py`: jets identical in Lean and Python for all toys, and every landed predicate is true.
- Gate `inp_lake_build.sh … Tests.Toy2d Tests.Toy3 Tests.Rat` (Toy2 built before): `Build completed successfully
  (3313 jobs)`.
- `scripts/lint_sources.sh`: modules PASS, frozen anchors OK, ABI OK. The only complaint is `KAM.lean is out of
  date` (generated, rule 10; it now also needs `KAM.Certificate.Tests.Toy2d`). No line is over 100 columns.
- `main_shortname_check.py <wt> …Toy2d …Toy2 …Toy2dData`: OK.
- `#print axioms toyCert2d_torus`, `toyCert2d_passes` and `toyCert2_torus` each give
  `[propext, Classical.choice, Quot.sound]`.
- No heartbeat or other option overrides.

## Deviations / notes
- New names beyond §J: `toyCert2d_invariance`, `toyCert2d_energy`, `toyCert2d_torsion`. The other T2d helper
  names are unchanged and have only moved module.
- These still describe T2d as `3 + cos 2πq` (I did not edit them): `docs/tracks/SO/design/SO-LEAN-DESIGN.md:720`
  and `:2025`, `docs/tracks/SO/studies/SO-TOYGEN.md:127`.
- No errata in pinned sources.

AUDIT FOCUS: (1) toyCert2d_passes and toyCert2d_torus have exactly the signed names and types of /root/code/KAM-inp/.drafts/design/SOSignatures.lean §J (`checkTorusCertificate toyCert2d = true`; `CertifiedTorus toyCert2d ![lunarNuMinus / 2, 1 / 2]`), and toyCert2d : TorusCertificate 2 ℚ; (2) the new T2d matches the overnight ruling recorded in the §J docstring: H = J + (p²/2)·((a + cos 2πq)/(a + cos 2πq)) with rational a = 10^30 > 1, and it still genuinely exercises `div`, the ball pass with a certified denominator and the reciprocal witness (the witness is not trivial, the denominator's ball excludes 0 by a check, not by assumption); (3) toyCert2d_passes is assembled correctly from the eight sub-check theorems (checkTorusCertificate is their conjunction, in the landed definition's order); (4) toyCert2d_torus is a genuine black-box application (checkTorusCertificate_sound, the frequency enclosure, lunarNuMinus_half_isDiophantine), no hypotheses; (5) the data are faithful emissions of certificates/so-toys/T2d.json; the mirror (toy_gen, toy_keys, toy_negative) green; (6) every kernel test fits in memory (the handoff's measurements), kernel replay, axioms, lint, 1500/100 limits.
