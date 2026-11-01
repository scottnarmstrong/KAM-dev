# Quickstart: from a model to a kernel-checked `CertifiedTorus`

This page takes a small perturbed system, the periodically forced pendulum of
`scripts/certifier/fixtures/forced-toy/`, from a model and a candidate torus to a theorem
`CertifiedTorus cert ωstar` checked by the Lean kernel. It gives the exact commands, their expected output,
what each step costs, and how to read the result. Every command runs from the repository root of a fresh
checkout. The run recorded here was made on 1 November 2026 on an AMD Ryzen 7 7700 (8 cores, 16 threads),
Lean 4.35.0 and Mathlib v4.35.0, with the pinned Python environment below.

**Trust boundary.** Everything in Python is untrusted tooling. It proposes a certificate and a route, and
it can be wrong without consequence: a bad certificate makes the Lean build fail. The theorem is whatever
the kernel accepts, under the axioms it prints (step 6).

## 0. Setup (once)

| What | Command | Cost |
|---|---|---|
| The repository (public) | `git clone https://github.com/scottnarmstrong/KAM-dev.git && cd KAM-dev` | not measured here |
| Lean toolchain manager | `curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \| sh -s -- -y --default-toolchain none` | not measured here; the toolchain named in `lean-toolchain` is fetched on first use |
| Pinned Python tools (≥ 3.12, tested 3.13) | `scripts/setup_python_env.sh && . .venv/bin/activate` | measured: a few seconds with a warm pip cache; 17.2 MB of wheels (Linux x86-64); 86 MB on disk |
| Mathlib build cache | `lake exe cache get` | not measured here (the cache was present); clones the dependencies, then downloads Mathlib's build, 6.7 GB unpacked |
| The checker and a reference certificate | `nice -n 5 lake build KAM.CertificateSharp.V2.Tests.Forced.MicroReading` | measured per module: 421 KAM modules from scratch, 1150 CPU-s in total, 166–177 s critical path; about 3 min on 16 threads and 5–6 min on 4 cores (simulated from per-module times); at most 2.5 GB per Lean process |

`scripts/setup_python_env.sh` creates `.venv/` (git-ignored) and installs exactly the files listed in
`scripts/requirements.txt`: numpy 2.5.3 and mpmath 1.3.0, each with every sha256 PyPI publishes for it
(`--require-hashes`, wheels only). Expected last lines:

```
python 3.13.13, numpy 2.5.3, mpmath 1.3.0
environment ready: .../.venv (activate with: . .../.venv/bin/activate)
```

The quickstart needs nothing more. `scripts/setup_python_env.sh --with-scipy` installs
`scripts/requirements-scipy.txt` instead: the same pins plus scipy 1.18.1, needed only by
`scripts/spin_orbit/dsolve.py` (the spin-orbit double-precision solver).

The last setup command compiles the part of the library that the certifier needs and checks the reference
toy `Micro` in the kernel (`Micro.sharp_torus`, `Micro.real_torus`). A plain `lake build` would compile the
whole core library instead, which this quickstart does not need. The certificate applications (the Moon,
LG00) are separate opt-in libraries, never built by default.

## 1. The model

The forced pendulum in extended phase space, with `z = ((θ₀, θ₁), (p, J))`, where `θ₁` is the time
(period 1) and `J` its conjugate action:

    H = c (J + β p²/2 + Σ_j ε_j cos 2π k_j·θ).

Hamilton's equations (`θ' = ∂_I H`, `I' = −∂_θ H`) give `θ₁' = c` and
`θ₀'' = 2π c² β Σ_j ε_j k_{j0} sin 2π k_j·θ`. The reference frequency is
`ω* = κ (ν₋(N) − 1, 1)` with `κ = c/s`. Its Diophantine property is proved in Lean
(`lunarRotFreqMinusN_isDiophantine`: `γ = κ/(N + 2)`, `τ = 1`, `N ≥ 8`).

The example of this page is the file `docs/certifier/examples/quick-trial.json` (reformatted here):

```json
{"N": 10, "modes": [[[1, 0], "3/1000000000000"], [[1, 1], "1/1000000000000"]],
 "prune_digits": 27, "char_tol": "1/100000000000000000", "gramTol": null, "cutLow": 4,
 "L0": 4, "L1": 3, "machin": [8, 3], "sqrt5_digits": 45}
```

That is `c = β = 1`, `N = 10`, and `θ₀'' = 2π [3·10⁻¹² sin 2πθ₀ + 10⁻¹² sin 2π(θ₀ + t)]`. `L0, L1` bound
the Fourier box of the candidate torus. The truncation `prune_digits = L` drops coefficients below `10^-L`
(weighted on the strip). `char_tol` is the matching truncation of the character witnesses. The remaining
keys are numerical knobs of `forced_cert.DEFAULT_SPEC`. The trial value `L = 27` is generous; step 3
chooses the truncation. To try another model, copy the file and change `N`, `modes`, `c` or `beta`.

Choose a tag for your example: a Lean identifier not used by the checked-in toys (`Tiny`, `Micro`,
`TinyC2`). This page uses `Quick`. The producer writes its pickles to `$FORCED_WORK`:

```sh
export FORCED_WORK=/tmp/forced-work
```

## 2. Route profile: the residual against the truncation (10 s, no Lean)

```sh
python3 -I scripts/certifier/forced/forced_profile.py Quick --spec @docs/certifier/examples/quick-trial.json
```

```
L = 15: err 2.33e-19, product pairs 1308 (producer 1.4s)
L = 17: err 2.33e-19, product pairs 1308 (producer 1.3s)
L = 19: err 2.33e-19, product pairs 1308 (producer 1.5s)
L = 21: err 6.33e-21, product pairs 4520 (producer 1.5s)
L = 23: err 9.76e-23, product pairs 6602 (producer 1.4s)
L = 25: err 4.36e-25, product pairs 9716 (producer 1.5s)
L = 27: err 4.36e-25, product pairs 9716 (producer 1.4s)
wrote scripts/certifier/fixtures/route-select/forced_quick.json
```

For each truncation `L` the producer builds the candidate torus and the whole certificate in the exact
mirror of the Lean checker. It reports the certified invariance error `err` and the certificate's size, as
genuine product pairs of the energy, Gram and torsion checks. Kernel time grows about linearly with that
size (roughly 1 ms per pair). An `L` whose certificate fails a landed check prints
`FAILS in the mirror, left out of the profile:` with the failing checks and their margins. The profile also
records the certificate's constants (`params`, the frequency box and the refined claim `R`), from which
`route_select.py` computes every route's threshold `e*` in step 3. Pass
`--cost-s SECONDS` with a measured kernel time to calibrate the cost column; the checked-in `forced_micro`
profile uses the 38.4 CPU-s measured for `Micro`.

## 3. Route choice: `route_select.py` (1.4 s, no Lean)

```sh
python3 -I scripts/certifier/route_select.py forced_quick --beta 1
```

Expected output (abridged; the table lists the 12 cheapest admissible candidates):

```
  rho 1/8     sharp                    log10 e*  -17.60  exact
  rho 1/8     A.frozen                 log10 e*  -12.33  exact
  rho 1/8     A.refined.classical      log10 e*   -9.22  exact
  rho 1/8     A.refined.cert[kp=1]     log10 e*   -8.25  exact
  ...
  rho 1/8     B.frozen                 log10 e*  -12.39  exact
  rho 1/8     B.refined.classical      log10 e*  -10.49  exact
  rho 1/8     A.L8'                    log10 e*   -8.50  estimate
  rho 1/8     l1-entry                 log10 e*   -7.91  estimate

| route | kind | ρ | L | P | log10 e* | log10 err (source) | margin | support | cost (CPU-h) | sites l |
| sharp | exact | 1/8 | 15 | 96 | -17.60 | -18.63 (measured) | 1.032 | 1308 | 0.000 | - |
...
best (exact mirrors): {'route': 'A.refined.classical', 'rho': '1/8', 'L': 15, 'P': 96, 'margin': 9.41, ...}
baseline fallback (landed sharp; err measured, not observed): {'route': 'sharp', 'rho': '1/8', 'L': 15, 'P': 96, 'margin': 1.03, ...}
hand choice: {'route': 'sharp', 'rho': '1/8', 'L': 27, 'P': 96, 'margin': 6.76, 'cost_h': 0.003, ...}
verdict: differs: predicted cost 0.000 CPU-h against the hand choice's 0.003 (ratio 0.00)
```

What each diagnostic means:

* **Threshold lines** `rho … <route> log10 e* … <kind>`: the largest invariance error each route accepts
  at this model's constants. `exact` means the exact rational mirror of the Lean test. `estimate` and
  `design` are scaled guesses for routes without a mirror; they are never chosen over an exact route at
  equal cost. The `l1-entry` row scales the best refined threshold by the forced toy's kernel-checked
  gain (`+0.29` decades, `estimate`); `--l1-design` uses the R1 design estimate (`+0.75`, `design`)
  instead. A route whose mirror fails prints its error in place of `log10 e*`.
* **Table**: every candidate (route, strip `ρ`, truncation `L`, precision `P`) that is admissible.
  `margin = log10(e*/err)` must exceed the profile's `margin_rule` (1 decade). The err source is
  `measured` at a profiled `L`, otherwise `interpolated` or `extrapolated`. `support` is the size, `cost`
  the predicted kernel CPU-hours, and `sites l` the certified small-divisor sites a route needs; a site
  computed off the package's strip is marked `(not balCheck-verified)`.
* **`best (exact mirrors)`**: the cheapest admissible candidate whose threshold is an exact mirror. Ties are
  broken by margin. **`baseline fallback`**: the cheapest admissible candidate of the landed sharp route.
  **`hand choice`** and **`verdict`**: the profile's reference choice (here the trial spec) and how the
  selection compares with it. **`constrained`** repeats the selection at the hand choice's `ρ` and `P`.
  **`sensitivity`** repeats it under other cost exponents.
* **Failures**: when nothing is admissible, or the sharp fallback is missing, the tool prints
  `no admissible …` followed by one `FAIL route=<route> check=<threshold|margin|sites|precision>: …` line
  per route, with the best margin found and the shortfall in decades. For example,
  `--margin 30` on `forced_micro` prints
  `FAIL route=sharp check=margin: best log10(e*/err) 6.81 at rho 1/8, L 25, P 96 (measured err), short of 30.0 by 23.19 decades`.

**The choice.** For the toy, the one-command witness emitter (`forced_routes.py TAG --frozen`, step 4)
proves the sharp route and the frozen routes A and B in one module, so it needs the sharp route to be
admissible. Take the **baseline fallback**: `L = 15`, `P = 96`, margin 1.03 decades on a measured err,
with about 7 times fewer product pairs than the trial `L = 27`. The `best` row
(`A.refined.classical`) has a larger margin. At this size every candidate costs a few seconds, below the
0.001 CPU-h resolution of the cost column, so ties are broken by margin. Its emitter (`forced_routes.py TAG`
without `--frozen`) needs a built data module and the compiled-Lean site search; see
`scripts/certifier/forced/README.md`.

The chosen spec is `docs/certifier/examples/quick.json`. It differs from the trial in two lines: the
truncation `L = 15`, and `char_tol` from the rule the profile records
(`"truncation": "L = prune_digits; char_tol = 10^-(L - 12 + 2) off the spec's own L"`):

```
<  "prune_digits": 27,
<  "char_tol": "1/100000000000000000",
>  "prune_digits": 15,
>  "char_tol": "1/100000",
```

## 4. Candidate torus, certificate and route witnesses (3 s, no Lean)

```sh
python3 -I scripts/certifier/forced/forced_build.py Quick --spec "$(cat docs/certifier/examples/quick.json)"
python3 -I scripts/certifier/forced/forced_routes.py Quick --frozen
```

```
Quick generated in 1.4s, base passes in the mirror: True
{"sizes": {"angle0": 2, "action0": 2, "action1": 1, "charWit": [1], ...}, "params": {..., "err": "233/1000000000000000000000", "E0": "0", "disp": "1/1000"}, "torus": {"iterations": 2, ..., "terms": {"u": 4, "p": 5, "J": 3}, "L0": 4, "L1": 3}}
route A frozen: Xs 271/5000, threshold e* 4.730e-13, err 2.330e-19
route B frozen: Xs 137/5000000, threshold e* 4.092e-13, err 2.330e-19
```

`forced_build.py` solves for the candidate torus in exact rationals and builds the
`TorusCertificate 2 (CertFixed 96)`: domain, bounds, Gram and torsion witnesses, and `err`. It checks every
landed sub-check in the mirror, then writes the Lean modules `QuickData` (the certificate `Quick.cert`),
`QuickStages` (memoized Gram and torsion stages), `QuickChecks` and `QuickBase` (one kernel run per landed
sub-check) under `KAM/CertificateSharp/V2/Tests/Forced/`. It also writes the report
`scripts/certifier/fixtures/forced-toy/Quick.json`. `forced_routes.py --frozen` chooses the witnesses of the
frozen routes A and B, and writes `QuickFreq` (the frequency enclosure `freq` and the Diophantine premise
`dio`) and `QuickRoutes` (the three routes and their certified tori).

**When a step fails**, it names the route, the check and the shortfall. Before writing anything,
`forced_routes.py --frozen` evaluates every clause of the three route tests in their exact mirrors:
`sharpTest`, `frozenCore` (route A), and `frozenBCore` with its final comparisons `finalBF` (route B). If
one fails it writes nothing. The mirrors are untrusted; their agreement with the Lean checker is tested in
CI (`forced_xlang.py`, and `forced_diag.py --xlang Micro` for route B). For example,
`forced_routes.py Tiny --frozen` (Tiny's err is above all three thresholds) prints one line per clause,
here with its PASS lines omitted:

```
FAIL route=sharp check=sharpTest.smallness: err 4.1e-12, threshold e* 2.84e-18, log10(err/e*) +6.16
FAIL route=A.frozen check=frozenCore.final.smallness: X* 0.0467, err 4.1e-12, threshold e* 8.45e-13, log10(err/e*) +0.69
FAIL route=B.frozen check=finalB.smallness: X* 2.53e-05, err 4.1e-12, threshold e* 5.44e-13, log10(err/e*) +0.88
forced_routes: Tiny --frozen proves the sharp, frozen-A and frozen-B routes in one module and needs all three; nothing written
```

The other clauses print as, for example,
`PASS route=B.frozen check=finalB.displacement: max(c2Q, c3Q) err <= disp γ²ρ^2τ: disp 0.001, needed 1.11e-06`
and `PASS route=A.frozen check=frozenCore.final.sigma_omega: disp 0.001 < (σω - s) |box|_lo 1`.

A certificate that fails a landed sub-check in `forced_build.py` prints one line per sub-check before the
assertion, for example
`FAIL route=landed-base check=checkEnergy: value 3.96e-25, err 1.98e-25, margin -1.98e-25, value/err 10^0.30`.

## 5. Kernel check (27 s)

```sh
nice -n 5 lake build KAM.CertificateSharp.V2.Tests.Forced.QuickRoutes
```

```
✔ [3652/3657] Built KAM.CertificateSharp.V2.Tests.Forced.QuickData (2.8s)
✔ [3653/3657] Built KAM.CertificateSharp.V2.Tests.Forced.QuickFreq (1.7s)
✔ [3654/3657] Built KAM.CertificateSharp.V2.Tests.Forced.QuickStages (2.5s)
✔ [3655/3657] Built KAM.CertificateSharp.V2.Tests.Forced.QuickChecks (8.9s)
✔ [3656/3657] Built KAM.CertificateSharp.V2.Tests.Forced.QuickBase (9.7s)
✔ [3657/3657] Built KAM.CertificateSharp.V2.Tests.Forced.QuickRoutes (2.0s)
Build completed successfully (3657 jobs).
```

27 s wall in total, at most 2.0 GB, once step 0 has built the checker. Every check is a `decide +kernel`:
the kernel evaluates the checker on the certificate's exact rational data. The generated modules use no
`native_decide`, `#eval` or other evaluation outside the kernel; `scripts/lint_sources.sh` rejects them
anywhere in the library. The new modules are not in the generated library root, so a plain `lake build`
does not build them. While they exist, `scripts/lint_sources.sh` fails with `KAM.lean is out of date; run
scripts/gen_root_imports.py`. Delete them afterwards, or add them to the library (step 7).

## 6. Read the result

Write this to a scratch file outside the repository, for example `/tmp/QuickReading.lean`, and run
`lake env lean /tmp/QuickReading.lean` (3.5–6.7 s, 3.6 GB):

```lean
import KAM.CertificateSharp.V2.Tests.Forced.QuickRoutes
import KAM.Application.Certified

open KAM KAM.Certificate KAM.Application KAM.CertificateSharp.V2.Forced

#check @Quick.sharp_torus
#print axioms Quick.sharp_torus

/-- The real reading of `Quick.sharp_torus` (the pattern of `Micro.real_torus`, MicroReading.lean). -/
theorem Quick.real_torus : ∃ (k : (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)) (sinf : ℝ),
    IsRealModelTorus (realHam Quick.cert.H) (sinf • Quick.ωstar) (Quick.cert.params.E0 : ℝ) k ∧
    (∀ θ, ‖k θ - realRestriction Quick.cert.K θ‖ ≤ (Quick.cert.params.disp : ℝ)) ∧
    1 < sinf ∧ sinf < (Quick.cert.params.σω : ℝ) ∧
    |sinf - (Quick.cert.params.s : ℝ)| * ‖Quick.ωstar‖ ≤ (Quick.cert.params.disp : ℝ) ∧
    IsDiophantine (sinf * (Quick.cert.params.γ : ℝ)) (Quick.cert.params.tau : ℝ)
      (sinf • Quick.ωstar) := by
  obtain ⟨Kinf, sinf, hT⟩ := (certifiedTorus_iff Quick.cert Quick.ωstar).1 Quick.sharp_torus
  exact ⟨realRestriction Kinf, sinf, hT.isRealModelTorus Quick.static_ok
    (isRealHolo_of_checkHamBounds Quick.static_ok Quick.hamBounds_ok),
    hT.norm_realRestriction_sub_le Quick.static_ok, hT.1, hT.2.1, hT.abs_sub_mul_norm_le,
    hT.isDiophantine Quick.dio⟩

#print axioms Quick.real_torus
```

```
Quick.sharp_torus : CertifiedTorus Quick.cert Quick.ωstar
'KAM.CertificateSharp.V2.Forced.Quick.sharp_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quick.real_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Which theorem.** `KAM.CertificateSharp.V2.Forced.Quick.sharp_torus : CertifiedTorus cert ωstar`. It is
the soundness theorem of the v2 certifier (`checkTorusCertificateV2_sound`) applied to three facts:
`sharp_passes` (the whole certifier `routeV2All` at the sharp route, `true` by kernel evaluation),
`freq : FreqEncloses 2 cert.freqBox ωstar`, and `dio : IsDiophantine γ τ ωstar` with the certificate's
`γ = κ/12` and `τ = 1`.
`frozenA_torus` and `frozenB_torus` state the same conclusion through the two frozen routes.

**Which axioms.** Exactly `propext`, `Classical.choice` and `Quot.sound`, Lean's standard three. Anything
else, in particular `sorryAx`, means the result is not proved.

**What it says, mathematically.** `CertifiedTorus cert ωstar` unfolds (`certifiedTorus_iff`, `Iff.rfl`)
to the following. There are a complex torus `K∞` and a scalar `s∞` with `1 < s∞ < σω = 2`. `K∞` is
holomorphic, primary and real on the strip of width `ρ∞ = 1/800`, and exactly invariant: its invariance
error at frequency `s∞ ω*` is zero. It lies on the level `H = E₀ = 0`, inside the certificate's domain,
with `‖DK∞‖ ≤ σK − μ/2`. It is within `disp = 10⁻³` of the certificate's own numerical torus `K` on that
strip, and `‖s∞ ω* − s ω*‖ ≤ 10⁻³`. Here `ω* = κ (ν₋(10) − 1, 1)`, `κ = 10⁶/(10⁶ + 1)`,
`ν₋(10) − 1 = (−19 + √5)/178 ≈ −0.0941794`, and `s = 1 + 10⁻⁶`, so that `s ω* = (ν₋(10) − 1, 1)`.

**What it says about the model.** `Quick.real_torus` reads it in the real coordinates `(θ, I) ∈ ℝ² × ℝ²`
through the application adapters (`KAM/Application/`). There is an analytic map `k` with
`k(θ + m) = k(θ) + (m, 0)` for integer `m`. Each line `t ↦ k(θ + t s∞ ω*)` solves Hamilton's equations of
`H = J + p²/2 + 3·10⁻¹² cos 2πθ₀ + 10⁻¹² cos 2π(θ₀ + θ₁)`, and `H ∘ k = 0`. The torus is located:
`‖k(θ) − Re K(θ)‖ ≤ disp = 10⁻³` at every real angle, where `K` is the certificate's own numerical torus
(`realRestriction cert.K`, the data in `QuickData`). The frequency `s∞ ω*` has `1 < s∞ < 2` and
`|s∞ − s| ‖ω*‖ ≤ 10⁻³`, and it is Diophantine with constants `(s∞ κ/12, 1)`. For the forced pendulum
`θ₀'' = 2π [3·10⁻¹² sin 2πθ₀ + 10⁻¹² sin 2π(θ₀ + t)]`, this is an invariant two-dimensional torus in the
extended phase space `(θ₀ mod 1, p, t mod 1)`, filled by quasi-periodic solutions (`J` is fixed by
`H = 0`). Further adapters give the invariance of the image (`IsPhysicalFlowTorus.isInvariantSet`,
`KAM/Application/Invariance.lean`), a graph over the angles (`checkAngleGraphReal`) and observable bounds.
They are not instantiated for this example. A one-line argument, not formalized here: `θ₁` advances at
exactly rate 1 along every solution, so averaging the time component gives `s∞ κ = 1`, that is
`s∞ = s`. Every solution on the torus then has the rotation number `ν₋(10) − 1` per forcing period.

**What it does not say.** It says nothing about solutions off this torus, about other rotation numbers,
or about a physical pendulum whose parameters are known only approximately. The receipt template lists
these limits: [RECEIPT.md](RECEIPT.md), whose worked example is this run.

## 7. Clean up, or keep

```sh
rm KAM/CertificateSharp/V2/Tests/Forced/Quick*.lean scripts/certifier/fixtures/forced-toy/Quick*.json \
   scripts/certifier/fixtures/route-select/forced_quick.json
```

`forced_build.py` also rewrites the shared `Format.lean` at the spec's precision. At `P = 96`, the
precision of every checked-in toy, the file is unchanged; another `P` breaks the checked-in toys. To keep
an example in the library, run `python3 -I scripts/gen_root_imports.py` and `scripts/lint_sources.sh`, as
for any new module.

## 8. Reproduce the checked-in example byte for byte

The checked-in toys `Tiny`, `Micro` and `TinyC2` regenerate exactly:

```sh
python3 -I scripts/ci_checks.py --only forced-regen
```

```
PASS forced-regen             6.6s  forced-toy producer and gen_stepbq regenerate the checked-in files
```

The check runs `forced_build.py` for the three tags, `forced_routes.py Micro --frozen` and
`gen_stepbq.py` in a temporary copy. It then compares 10 emitted Lean files byte for byte (the data,
stages, frequency and route modules, `Format.lean`, `StepBQ.lean`) and 4 JSON fixtures up to their
wall-clock fields. The certificate's Gram and torsion inverses come from floating-point numpy, rounded to
`2⁻⁴⁰`. With the pinned wheels, the run on this machine reproduces the files written earlier with a
different numpy build (conda-forge). Another CPU or BLAS could in principle change a last bit. The kernel
re-checks whatever is emitted, so such a difference would change the certificate's bytes but not its
validity.

## 9. Continuous integration

`.github/workflows/certifier-ci.yml` runs only on demand (`workflow_dispatch`, the owner's decision). Its
actions are pinned by full commit SHA, `checkout` keeps no credentials, elan is a fixed release (v4.2.4)
whose tarball is checked against its sha256 before it runs, and the Python packages are installed with
`--require-hashes`. It has three jobs, and each job is one command that runs the same way locally
(`python3 -I scripts/ci_checks.py --list` names the checks):

| Job | Command | Measured here |
|---|---|---|
| `mirror` | `python3 -I scripts/ci_checks.py --group mirror` | 83–124 s (core packages only): route-B and route-B-constant mirrors, hybrid numbers, the v2 adapter, the three-frequency mirror against its Lean literals, `route_select --validate` against its fixtures, forced-toy regeneration, the `forced_micro` profile, and the failure diagnostics |
| `lint` | `python3 -I scripts/ci_checks.py --group lint` | 113–144 s: `scripts/lint_sources.sh` without its Lean-dependent ABI-hash step, and a check that every third-party import of the producer tools is pinned with hashes (scipy only in the optional file, imported only by `dsolve.py`) |
| `lean-fixtures` (opt-in) | `lake build` of `Tests/Forced/*` and `Fiber3XLang`, then `--group lean` | step 0's cost plus the Mathlib cache; `forced_xlang` (52 comparisons with the compiled checker) 26 s; `forced_diag.py --xlang Micro` (the route-B pre-check's mirror: `c1Q`, `c2Q`, `c3Q` exactly, `frozenBCore`, and `finalBF`/`finalB` on both sides of each displacement threshold; 10 comparisons) 5 s |
