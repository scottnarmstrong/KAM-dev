# Handoff SO-TEST-A (positive toys through the whole checker)

Branch `inp-sotesta`, worktree `/root/code/KAM-inp-sotesta`.

## Verdict
T2, T3 and TR pass the whole checker in the kernel. T2 and T3 give full black-box `*_torus` theorems.
**T2d does NOT pass within bounded kernel resources. This is a design signal. I stopped there as the brief
requires, and I did not weaken the data.** No rotated-frame T2 exists: `certificates/so-toys/` has no rotated data.

## Files (lines)
| file | lines | content |
|---|---|---|
| KAM/Certificate/Tests/ToyLit.lean | 42 | `toyNat/toyPos/toyNeg/toyQ/toyScaledPoly` (90-digit chunks for ≤100 columns; `mkRat`) |
| KAM/Certificate/Tests/Toy2Data.lean | 113 | T2 data `toyT2*`, `toyT2Cert`, root/alg-box data |
| KAM/Certificate/Tests/Toy2dData.lean | 1147 | T2d data; the 531-term reciprocal witness is split into 14 chunks of 40 terms each (see design signal 2) |
| KAM/Certificate/Tests/Toy3Data.lean | 158 | T3 data |
| KAM/Certificate/Tests/RatData.lean | 88 | TR data |
| KAM/Certificate/Tests/Toy2.lean | 92 | `toyCert2`, `toyCert2d`, `toyCert2_passes`, `toyCert2_freq`, `toyCert2d_freq`, `toyLunarFreq_eq_algFreq`, `toyCert2_torus`, T2d light sub-checks |
| KAM/Certificate/Tests/Toy3.lean | 62 | `toyHam3`, `toyCert3`, `toyCert3_ham`, `toyCert3_err_pos`, `toyCert3_passes`, `toyCert3_freq`, `toyCert3_torus` |
| KAM/Certificate/Tests/Rat.lean | 27 | `toyRatCert`, `toyRatCert_passes` |
| scripts/spin_orbit/toy_lean_cert.py | — | emitter JSON → Lean data. Untrusted, and its output is exact: the data are the same ℚ values as the JSON |

The data are emitted from certificates/so-toys/*.json as-is (SO-PYALIGN hashes), with every advice book, cutoff, π
enclosure and parameter unchanged.

## What each test exercises
- `toyCert2_passes`: all 8 sub-checks for T2 (n=2, τ=1). Every product takes the scalar route, so the books are empty.
- `toyCert2_freq` / `toyCert2d_freq`: `checkRootEnclosure 2 5` (√5) + `checkAlgBox` with coefficients
  `[[3039/6236, 1/6236],[1/2]]`, and `toyLunarFreq_eq_algFreq` (`lunarNuMinus_eq`).
- `toyCert2_torus`: `checkTorusCertificate_sound` with `lunarNuMinus_half_isDiophantine` (γ = 1/42, τ = 1).
- `toyCert3_*`: n=3, τ=2. The frequency comes from `checkRootEnclosure 3 2` (∛2) + `cubicFreq_eq_algFreq` + `checkAlgBox`;
  `toyCert3_torus` uses `cubicFreq_isDiophantine` (γ = 1/12). `toyCert3_ham : toyCert3.ham = toyHam3` holds by rfl.
- `toyRatCert_passes`: checker only (the reference (1/4, 1/2) is resonant), with zero error.
- T2d: `toyCert2d_static/_hamBounds/_embedding/_gram/_smallness` (div, the ball pass with a certified
  denominator, and the static checks).

## Kernel times (`decide +kernel` on `checkTorusCertificate`, profiler "type checking", 6 GB cgroup cap)
| toy | kernel | wall of the `lean` run (incl. imports) |
|---|---|---|
| T2 | 2.91 s | 13.5 s |
| TR | 2.73 s | 6.7 s |
| T3 | 8.88 s | 12.7 s |
| T2d | does not finish (see below) | — |

## T2d sub-checks (one process each, wall incl. ~3 s import, max RSS)
| sub-check | result | wall | max RSS |
|---|---|---|---|
| checkStatic | pass | 10.5 s | 3.3 GB |
| checkHamBounds | pass | 9.0 s | 4.1 GB |
| checkEmbedding | pass | 4.1 s | 3.4 GB |
| checkGram | pass | 4.2 s | 3.4 GB |
| checkSmallness | pass | 3.7 s | 3.4 GB |
| checkEnergy | pass (uncapped) | 97 s | **12.3 GB** |
| checkInvariance | **stopped** by the orchestrator at 165 s | — | **19.0 GB** and still growing (unfinished) |
| checkTorsion | **OOM-killed** by the 6 GB cgroup at 54 s | — | > 6 GB |

The margins could not be compared in Lean for the three heavy checks, because they never finished. No margin
failed: every sub-check that finished returned `true`.

### What dominates (from the mirror's product statistics, T2d.json `verification.products`)
- `cfgFull` (invariance and energy): the whole jet program is composed (196 mul calls, 68 direct). The dominant
  products are `[0,82]` 531×1591 terms (844,821 coefficient pairs), `[0,81]` 531×1061 (563,391) and `[0,80]` 531×531
  (281,961): 3.56 M pair multiplications in total, with |k|₁ up to 1064 and cutoff 10^6 (no truncation). Every
  coefficient is an exact rational whose denominator has about 200 digits. The 531-term factor is the reciprocal
  witness `[2,0]`, multiplied into the d1/d2/d3 slots. `checkInvariance` composes this program and then builds
  four `invarianceModel`s, each with a `toDeg` re-expression of the jet slots of nonzero 2π-degree.
- `cfgLow` (torsion): cutoff 30, but `[0,80]` is still 531×531 before truncation (357 k pairs in total). In
  addition, `checkTorsion` reruns `gramCheck` and `torsionModels` builds ~10 matrix products, each entry passed through `toDeg 0`.
- So the cost is exact-ℚ convolution of a 531-term witness with 200-digit denominators, inside the kernel's
  term-level `List`/`Rat` evaluation. Energy alone (the same composition at one output slot) already needs 12 GB.

### Design options (for the orchestrator; I did not implement any)
(a) Use a rounded backend (CertFixed) for heavy toys, so that coefficients stop growing to 200-digit denominators.
(b) Truncate the witness and the full stage earlier: cfgFull cutoff 10^6 is SAFE_CUTOFF only for the mirror.
(c) Share the composition between `checkInvariance` and `checkEnergy` (SO-PYALIGN §6.6).
(d) Restate T2d with a smaller division (a lower-order reciprocal witness), which is a data change for SO-TOYGEN.

## Design signal 2 (heartbeats)
A single `def` whose body is the 531-element literal list of the reciprocal witness hits the default elaboration
heartbeat limit (`synthesize pending MVars`). I fixed it by splitting the list into 14 chunk definitions (40 terms
each), concatenated with `++`, which leaves the value unchanged. I used no heartbeat options anywhere.

## The `[5, a, l]` question
SO-PYALIGN is right, and this package confirms it independently. `toyCert2_passes` and `toyCert3_passes` pass
`decide +kernel` with empty advice books, so they look up no `[5, a, l]` key (or any other). T2d's books, as
emitted (34 keys per stage: `[2,0]` and 33 `[0,slot]`), contain no `[5,…]` and no `[4,10,…]` key. T2d's
`checkEnergy`, which looks up the cfgFull keys, passes with them. T2d's `checkInvariance` did not finish, so T2d
cannot settle it alone. The structural reason: `dkFreqModel` calls `CertModel.mul … (freqModel …)`, and
`freqModel` is a constant model, so `CertModel.mul` takes the scalar route and never consults the book.

## Checks run
- Gate: `inp_lake_build.sh … KAM.Certificate.Tests.Toy2 KAM.Certificate.Tests.Toy3 KAM.Certificate.Tests.Rat`:
  `Build completed successfully (3312 jobs)`, with no warnings in my files (the data modules were built
  earlier, in the same run chain).
- `scripts/lint_sources.sh`: the only complaint is `KAM.lean is out of date; run scripts/gen_root_imports.py`.
  This comes from my new modules, and KAM.lean is generated (rule 10), so the orchestrator regenerates it at
  landing. Everything else passes: no line over 100 characters, modules PASS, frozen anchors OK, ABI OK.
- `main_shortname_check.py` on all 8 modules: `short-name check OK`.
- `#print axioms`: `toyCert2_torus`, `toyCert3_torus`, `toyCert2_passes`, `toyCert3_passes`,
  `toyRatCert_passes`, `toyCert2d_freq` and `toyCert2d_static` each give `[propext, Classical.choice, Quot.sound]`.

## Deviations / uncertainties
- `toyCert2d_passes` and `toyCert2d_torus` (signed in §J) are ABSENT: design signal, not proved.
- Names added beyond §J: `toyCert2_freq`, `toyCert2d_freq`, `toyLunarFreq_eq_algFreq`, `toyCert2d_{static,
  hamBounds,embedding,gram,smallness}`, the `toyT2*/toyT2d*/toyT3*/toyTR*` data, and the ToyLit helpers.
- Rotated-frame T2: no data, so not done.
- The Python mirror and the Lean checker disagree on nothing I could observe: every sub-check that finished
  returned `true`, as the mirror predicts.
- Errata in pinned sources: none found.
- Process note: my first uncapped T2d probes were heavy. The orchestrator stopped the invariance probe (PID
  444005). Afterwards I stopped my own loop by PID and ran the rest under `systemd-run --user --scope -p
  MemoryMax=6G` (`prlimit --as` breaks Lean's olean mmap).

AUDIT FOCUS: (1) toyCert2, toyCert3, toyRatCert and every proved theorem of §J (toyCert2_passes, toyCert2_torus, toyCert3_ham, toyCert3_err_pos, toyCert3_passes, toyCert3_freq, toyCert3_torus, toyRatCert_passes) have exactly the signed names and types of /root/code/KAM-inp/.drafts/design/SOSignatures.lean §J (lines 1120-1170); toyCert2d_passes and toyCert2d_torus are ABSENT by design signal (T2d does not finish in the kernel), which is acceptable for this round; (2) the *_torus theorems are genuine black-box applications: checkTorusCertificate_sound with the frequency enclosure proved (checkRootEnclosure, checkAlgBox, the landed algFreq identities) and the landed Diophantine facts (lunarNuMinus_half_isDiophantine, cubicFreq_isDiophantine), no hypotheses; (3) the data modules are faithful emissions of certificates/so-toys/*.json (spot-check several literals against the JSON) and the emitter scripts/spin_orbit/toy_lean_cert.py introduces no rounding; the 14-chunk split of T2d's witness leaves the value unchanged; (4) the T2d partial sub-checks are what they claim; (5) kernel replay, axioms (standard three), lint, ≤ 1500 lines, ≤ 100 columns.
