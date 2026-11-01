# Handoff V2-TOOLS (#6 perturbed-model regression suite, #3 producer-side route selection)

Branch `v2-tools` (worktree `/home/scott/KAM-dev-worktrees/v2-tools`), from `origin/main` `f80bdf6e`. Additive
only: no existing `.lean` file under `KAM/` is modified (the only modified Lean file is the generated root
`KAM/Root/CertificateSharp.lean`), nothing is created under `KAM/Certificate/**`, `KAM/SpinOrbit/**`,
`scripts/spin_orbit/**`, `certificates/**` or `docs/tracks/SO/**` (the fixtures first written to
`certificates/forced-toy/` were moved to `scripts/certifier/fixtures/forced-toy/` in `0784d34b`, as the
orchestrator asked). Owned files of other workers were only imported, never edited.

## Part #6: the forced-toy regression suite

### Files

* Producer and mirror (Python, untrusted): `scripts/certifier/forced/` (`README.md` lists every script):
  `forced_model.py`, `forced_cert.py`, `forced_stages.py`, `forced_emit.py`, `forced_build.py`,
  `forced_lean.py`, `forced_witness.py`, `forced_routes.py`, `forced_mutations.py`, `forced_sweep.py`,
  `forced_xlang.py`. They reuse read-only the landed-checker mirror `scripts/spin_orbit/sofx_*.py`,
  `adv_jet.py`, `sodata3_v2checks.py`, `v2_q.py`, `v2_r2.py`, `sharp_q.py` and
  `scripts/apost_sharp/route_b_lean_mirror.py`.
* Fixtures: `scripts/certifier/fixtures/forced-toy/{Tiny,Micro,TinyC2}.json` (spec, mirror report, every
  number of the certificate), `{Tiny,Micro}_witness.json`, `Tiny_mutations.json`, `sweep.json`, `xlang.json`.
* Lean, laid out per the orchestrator's ruling (V2-TOOLS-FIX, below): default build
  (`KAM/CertificateSharp/V2/Tests/Forced/`, new modules only): `Format`, `Lemmas`; data `<T>Data`
  (certificate, `CertFixed 96`), `<T>Stages` (memoized Gram/torsion stage literals), `<T>Freq` for
  `T ∈ {Tiny, Micro, TinyC2}`; the passing certificate `Micro`: `MicroChecksA/B`, `MicroGram`,
  `MicroTorsion1/2/3`, `MicroBase`, `MicroRoutes`; the mutation target `Tiny`: `TinyWitness`, `TinyGram`,
  `TinyMutClaims/Cores/Sites/Denominator/Sqrt/Coef/Residual/Advice/ConvA/ConvB`. Opt-in:
  `kernel-tests/CertificateSharp/V2/ForcedRoutes.lean` (Tiny's base checks and routes A, L8′, B with their tori,
  `mut_frameT`, the TinyC2 chain, `timeScale_*`).

### The model and the three certificates

`H = c (J + β p²/2 + Σ_j ε_j cos 2π k_j·θ)` on `T² × ℂ²` (θ₁ the time), modes `k = (1, 0)` and `(1, 1)`
(their interaction creates `(0, 1)`, `(2, 1)`, … at second order), `β = 1`, `N = 8`, reference vector
`ω* = κ (ν₋(8) − 1, 1) = lunarRotFreq (lunarNuMinusN 8) κ`, `κ = c/s`, `s = 1 + 10⁻⁶`, Diophantine constant
`γ = κ/10` (`lunarRotFreqMinusN_isDiophantine`), strip `ρ = 1/8`, `ρ∞ = ρ/100`, `μ = 1/100`. The torus
`K(θ) = (θ₀ + u/2π, θ₁, p, J)` is a Picard solution in exact rationals; the certificate, the advice books, the
Gram and torsion witnesses and every parameter come from the mirror of the landed checker.

| Toy | ε | err (checked) | M, σT | support (half terms u/p/J, witness) | routes passing in the kernel |
|---|---|---|---|---|---|
| `Tiny` | 1e-7, 2e-7 | 4.1·10⁻¹² | 1.14, 1.16 | 5/5/4, 5 | refined A, L8′, refined B |
| `Micro` | 1e-12, 2e-12 | 4.36·10⁻²⁵ | 1.14, 1.16 | 6/6/4, 5 | landed sharp, frozen A, frozen B |
| `TinyC2` | `Tiny` with `c = 2` | 8.2·10⁻¹² | 2.28, 0.581 | same torus | refined A |

Thresholds (mirror, confirmed by the compiled Lean core): `Tiny` refined A `X⋆ = 382`, `e* = 6.91·10⁻⁹`
(margin 3.2 decades; certified sites at all six bites, `c = 0.0117 … 0.0233` against classical `≈ 0.08`);
L8′ at `X⋆ = 191`, `b_F = b_T = 10⁻³`; refined B `X⋆ = 6.08·10⁻⁴`, `γ⁴ρ⁴/c₁ = 5.33·10⁻¹¹` (margin 1.1);
the sharp engine (`2.8·10⁻¹⁸`) and frozen A (`8.4·10⁻¹³`) reject `Tiny`. `Micro`: sharp `2.84·10⁻¹⁸`
(margin 6.8), frozen A `8.45·10⁻¹³`, frozen B `5.44·10⁻¹³`. `TinyC2`: refined A `X⋆ = 24.1`,
`e* = 6.98·10⁻⁹`.

Main theorems (all `decide +kernel` at default limits, no heartbeat or recursion option):
`Tiny.base_ok : landedBase.check Tiny.cert = true`; `Tiny.refinedA_passes`, `Tiny.refinedR_passes`,
`Tiny.refinedB_passes` (`checkTorusCertificateV2 routeV2All Tiny.cert w = true` at the witness of each route);
`Micro.sharp_passes`, `Micro.frozenA_passes`, `Micro.frozenB_passes`; `TinyC2.refinedA_passes`; the tori
`Tiny.refinedA_torus`, `Tiny.refinedR_torus`, `Tiny.refinedB_torus`, `Micro.sharp_torus`,
`Micro.frozenA_torus`, `Micro.frozenB_torus`, `TinyC2.refinedA_torus : CertifiedTorus _ ωstar`; and
`timeScale_tori`, `timeScale_invariance` (below).

### Approach and the cost finding

* **Kernel cost is quadratic in the Fourier support.** Measured: the landed direct product costs about 1 ms per
  coefficient pair in the kernel (a 23 × 23-term product 0.4–0.9 s, the same with literal or helper-built
  data); a first toy with ~130-term models needed 10.5 GB for `checkEnergy` alone. The toys therefore keep
  every model at a few dozen terms. Two levers made that possible with err ≈ 10⁻¹²: the character witness
  enters the residual multiplied by ε, so it is pruned at err/ε instead of err; and Machin (6, 3) for π.
* **The torsion check needs memoization.** Unsplit, `checkTorsion` exceeded 6 GB even at ~2k product pairs
  (its body binds its stages with `let`). Through the landed `Kernel/Stage.lean` lemmas
  (`gramCheck_eq_of_rows`, `torsionModels_eq_of_stages`, `checkFrameN_eq_of`, `checkFrameT_eq_of`) each stage is
  a literal computed by the Python mirror and re-proved by its own kernel run (`eq_of_matBeq`, new in
  `Forced/Format.lean`); the frame majorants share the same stages. Every stage literal was accepted: the
  mirror agrees bit for bit with the landed checker on the Gram, the 13 torsion stages and the torsion-slot
  composition of all three toys. This is the kernel-side cross-language test.
* Witness search: `#eval` of the compiled checker is the oracle for the ℚ-level parts (sites `balCheck`,
  route cores); the model-level checks cannot be `#eval`ed (`instCertArithFixed` is noncomputable) and rely on
  the mirror, then the kernel. Route B's caps fixed point runs in `route_b_lean_mirror` (an in-Lean iteration
  was too slow and was stopped at 4.9 GB).
* Engine unfolding: `show`/`exact` between `checkTorusCertificateV2 E c w` and the engine's test at concrete
  data makes the elaborator evaluate the certifier (recursion limit). `Forced/Lemmas.lean` states
  `checkV2_eq` and one `*_test` lemma per engine, each `rfl` over variables, applied explicitly.

### Mutations (25 rejections, 2 controls)

Ten default-build modules `TinyMut*` (24 rejections and the 2 controls, 1.4–6.9 s each) and `mut_frameT` in
the opt-in `ForcedRoutes.lean`. Each changes one input and decides that **the rejecting sub-check decides
false** (not `checkTorusCertificateV2` itself; the step from one to the other is a Boolean conjunction, which the
audit proved for two representatives). The 20 the mirror covers are rejected by the mirror too
(`Tiny_mutations.json`, which records each mutation's module).

| Family | Mutation → rejecting check |
|---|---|
| coefficients | amplitude of `(1,0)` × (1 + 10⁻³) → `checkInvariance`; largest `u` coefficient × (1 + 10⁻⁴) → invariance; largest witness coefficient × (1 + 10⁻³) → invariance |
| residual claims | `err/2` → invariance; `E0 + 2 err` → `checkEnergy` |
| frame bounds | `bL`, `bN`, `bT` × 0.99 → `checkFrameL/N/T` (N, T through the stages); `dx` × 0.99 → `checkHamClaim` |
| ray room | `nuRay = 10⁻⁵` → `checkStatic`; `disp = 1` → `finalOkA`, the final clause of route A (room of the ray) |
| schedules | `10 X⋆` → `refinedCore` (`okB`); route B `10 X⋆` → `refinedBCore` (`okB`, quantitative); the domain guards `θ = 1` → `refinedCore` (`wfOk`) and route B `a = 1` → `refinedBCore` (`1 < a`, `δ₀ = 0`) |
| denominator separation | box radius 1/20 (fibers reach the resonance) → `sitesOk`; site bound `B/2` → `siteOk`; `10⁻⁹/(p − p_c)` (ball contains 0) → `checkHamBounds`, control `10⁻⁹/(p + 1)` passes |
| square-root domains | `10⁻⁹ √(p − p_c)` (operand reaches Re ≤ 0) → `checkHamBounds`, control `√(p + 1)` passes |
| advice | first full-stage key removed → energy (crude `p²`); first low-stage key removed → `checkGram` |
| conventions | `u` read at angle degree 0 → invariance; `s = 1 + 10⁻³` against the box of `c/s` → invariance; `H` doubled without the box → invariance; actions emitted as `(J, p)` → invariance |

The mirror caught two weak first drafts (a 10⁻⁶ torus perturbation stays under err; the first full-stage key is
the energy-only `p²` product): both were strengthened/retargeted before emission.

### Variations (mirror sweep, `sweep.json`; err, margins in decades of `log10(e*/err)`)

| Variant | err | sharp | frozen A | refined A (classical sites) |
|---|---|---|---|---|
| base (`Tiny`) | 4.1e-12 | −6.2 | −0.7 | 2.4 |
| separation N = 10 / 14 / 24 | 3.9 / 3.7 / 3.8e-12 | −6.2 / −6.3 / −6.5 | −0.9 / −1.3 / −2.1 | 2.2 / 1.8 / 1.2 |
| twist β = 1/4 / 4 | 3.8e-12 / 9.4e-14 | −7.0 / −5.4 | −1.6 / −1.2 | 2.1 / 2.9 (σT 4.52 / 1.06) |
| support prune 1e-9 / 1e-15 | 8.3e-11 / 5.8e-15 | −7.5 / −3.3 | −2.0 / **+2.2** | 1.1 / 5.2 |
| precision P = 40 / 64 / 128 | 8.1e-9 / 4.1e-12 / 4.1e-12 | | −4.0 / −0.7 / −0.7 | **−0.9** / 2.4 / 2.4 |
| perturbation ε × 10 | 5.8e-12 | −6.3 | −0.8 | 2.2 |
| time scale c = 2 | 8.2e-12 | −6.3 | −0.6 | 2.4 |

Every variant passes the landed base checks in the mirror; the margins move as expected (smaller separation
`γ = κ/(N+2)` costs margin; a richer support turns frozen A on; precision 40 bits turns refined A off). With the
certified sites the refined margin of `Tiny` is 3.2 (kernel). The sweep is mirror evidence, not a kernel claim.

### Equivalent normalizations through their checked transformation

`timeScale_*` (in the opt-in `ForcedRoutes.lean` since V2-TOOLS-FIX): `TinyC2` (H and ω* doubled) carries the same torus (`timeScale_emb`, `rfl`), its Hamiltonian
is `2 · Tiny.H` (`timeScale_H`), its reference vector `2 • Tiny.ωstar` (`timeScale_ωstar`), and
`timeScale_invariance` is `invarianceError_const_mul` instantiated: the invariance error of `TinyC2` is twice
that of `Tiny` at half the frequency, which is exactly the factor between the two independently checked
residual claims (8.2·10⁻¹² against 4.1·10⁻¹²; σT halves, M doubles). Both tori are certified
(`timeScale_tori`); the drift "H doubled without the box" is rejected (`Tiny.mut_timeScale`).

### Cross-language agreement

`python3 -I scripts/certifier/forced/forced_xlang.py`: `ALL AGREE (52 comparisons)` (V2-TOOLS-FIX2, two-sided):
* the whole jet program of each Hamiltonian, operation by operation, and the slot tables v0, d1, d2, d3;
* `sharpTest`;
* each disc-pass sum (dh, dx, d2x, d2h): the claim exactly at the mirror's value passes, 10⁻¹² below fails;
* every route core of every witness (refined A, frozen A, refined B, frozen B) at the witness's `X⋆` and on both
  sides of the mirror's `X⋆` boundary, located by exact bisection to a relative width 10⁻⁵;
* byte-identical regeneration of the stage literals.

Perturbation trials (in memory): a mirror optimistic by ×1.5 or by ×1.001 in `refinedCore`, and a pessimistic one
(×2/3), are each detected. The first version compared only jet lengths and slot indices and probed at 1, 10 and
1/2 × `X⋆`, so it could not catch an optimistic mirror (AUDIT-V2-TOOLS-1). In the kernel: every stage literal
(above). The script writes `xlang.json` only with `--write-fixture`.

### Checks and measurements

Default build, `lake build` per module (wall, peak RSS of the build), after V2-TOOLS-FIX: `TinyWitness` 1.3 s /
1.5 GB, `TinyGram` 3.5 s / 1.7 GB, `MicroGram` 3.3 s / 1.7 GB, `MicroChecksA` 4.2 s / 2.0 GB, `MicroChecksB` 5.3 s
/ 2.0 GB, `MicroTorsion1` 6.2 s / 2.0 GB, `MicroTorsion2` 3.7 s / 1.9 GB, `MicroTorsion3` 2.8 s / 1.7 GB,
`MicroBase` 6.5 s / 2.2 GB, `MicroRoutes` 1.8 s / 1.6 GB; `TinyMutClaims` 3.8 s / 2.0 GB, `TinyMutCores` 1.4 s /
1.6 GB, `TinyMutSites` 1.6 s / 1.6 GB, `TinyMutDenominator` 6.5 s / 2.2 GB, `TinyMutSqrt` 6.9 s / 2.2 GB,
`TinyMutCoef` 4.0 s / 1.9 GB, `TinyMutResidual` 4.6 s / 1.9 GB, `TinyMutAdvice` 5.1 s / 1.9 GB, `TinyMutConvA`
3.3 s / 1.8 GB, `TinyMutConvB` 3.7 s / 1.8 GB; the data modules 1.4–2.6 s. Every default module is at most
6.9 s and 2.24 GB. Opt-in `ForcedRoutes.lean`: 90 s, 3.5 GB peak under `lake env lean` (verified on an identical
copy in the scratch directory, so that nothing under `kernel-tests/` was built). Memory accounting: under
`lake env lean` the bare imports already show 3.4–3.6 GB RSS, under `lake build` the lightest module peaks at
1.5 GB. Before the split the heaviest single theorem was a torsion stage (`XN1_eq`, about 7 s on Tiny).

`#print axioms` (all `[propext, Classical.choice, Quot.sound]`), re-run after the layout: default
`Micro.base_ok`, `Micro.sharp_torus`, `Micro.frozenA_torus`, `Micro.frozenB_torus`, `Tiny.mut_hamCoef`,
`Tiny.mut_frameN`, `Tiny.ctl_sqrtDomain`; opt-in `Tiny.refinedA_torus`, `Tiny.refinedB_torus`,
`Tiny.refinedR_torus`, `TinyC2.refinedA_torus`, `timeScale_tori`, `Tiny.mut_frameT`.

`scripts/lint_sources.sh`: every file-based step passes (forbidden constructs, 100-column lines, 1500-line cap,
`gen_root_imports --check`, `render_errata --check`, `check_lean_modules: PASS (3687 Lean files)`,
`FROZEN-ANCHOR GUARD OK`); the last step `abi_hashes.py --check` cannot run in this worktree: about 30 core
frozen modules (`KAM.Frozen.Planetary.*`, `KAM.Frozen.Wave.*`, `KAM.Frozen.Theorems.*`, …) have no olean in
its build snapshot, and building them all would rebuild the library here. No frozen file is touched by the
branch.

### Not covered (reported, not claimed)

* The ℓ¹ entry (`L1.routeAL1`): `checkL1Claim` recomputes ℓ¹ norms of the frame and torsion models on other
  strips; it would need its own stage memoization like `Kernel/Stage.lean` (a new checker-side bridge, so not
  attempted under the additive rule).
* The hybrid restart (`routeV2Hyb`): needs a Newton step `ΔK` and the hybrid compositions; not cheap at the
  measured kernel rates.
* A rotated-coordinate normalization (`soRotMap`): only the time normalization is tested.
* Packed advice on the toy: all products are `direct`; the packed route (the lunar data's) is untested here.

## Part #3: producer-side route and parameter selection by total kernel cost

### Files

* `scripts/certifier/route_select.py` (the tool), `scripts/certifier/route_profiles.py` (snapshots the inputs);
* `scripts/certifier/fixtures/route-select/`: `lunar65.json`, `lg00.json` (profiles with provenance),
  `ledger_fit.json` (the LG00 run20e ledger by module kind), `validation.json`, `validation.log`.
* `routeV2All` is unchanged; no Lean file is touched by #3.

### What it does

For a profile (a model and its candidate tori: CertParams, box, refined claim, the measured residual against
the truncation L and the strip ρ, the support per L, the measured kernel cost at the hand choice) it evaluates
at every ρ of the profile:

| route | threshold from | kind |
|---|---|---|
| sharp (the baseline, landed) | `sharp_q.sharp` | exact mirror |
| A frozen | `v2_r2.max_Xs('frozen')` | exact mirror |
| A refined, classical sites | `v2_r2.max_Xs('refined')` | exact mirror |
| A refined, certified sites (kp = 1, 2, 3; and SO-V2PKG's d01b) | the same, `c = c_freq × 1.01` where `clockOk` applies and the cut-off `l ≤ 12` | exact mirror (the Lean `balCheck` is the check; sites at a strip other than the package's are flagged "not balCheck-verified") |
| B frozen, B refined | `forced_witness.solve_B` on `route_b_lean_mirror` | exact mirror |
| A with L8′ | refined `e*/2` (on the forced toy L8′ was found passing at half of route A's `X⋆`; the ratio of the maxima is not checked) | estimate |
| ℓ¹ entry | refined `e* × 10^0.75` (`thresholds_v2 --l1` at R1, iso) | design estimate |
| hybrid restart | `sqrt(e₁*/A_meas)`, `e₁*` the refined threshold at `ρ − 3δ₀` | design estimate (needs the model's `A_meas`) |

Where SO-V2PKG §4.6 re-measured the lunar package at another strip (σK, σB and the frame claims re-enclosed), the
d01b route takes the re-measured threshold and every other route at that strip the same shift. It then scans L
and the precision P (predicted err, log-linear in L from the profile's table, each candidate labelled measured,
interpolated or extrapolated; the ρ factor; a floor `10⁴ · 2^-P`, an unmeasured model), removes the precisions
the profile's precision rule forbids (LG00: `2^-P ≤ 10^-(L+12)`, LG00-CERT.md:204, which forced `CertFixed 128`
at L = 20; lunar: `2^-P ≤ 10^-4 err`, one data point of SO-V2PKG §4.1), and reports per candidate: required vs achieved residual, margin, displacement (`disp_coef ·
err`), binding budget (the failing clause at `1.1 X⋆`), support, precision, the certified cut-offs, and the
predicted kernel cost

`C = C_ref (S(L)/S_ref)^β (P/P_ref)^π (1 + extra) + Σ c(l)`,

with `C_ref` the measured cost of the hand choice (lunar 2.0 CPU-h per torus, SO-CSPLIT-GATE's 1.6–2.5; LG00
30.11 CPU-h, the run20e ledger). **π is not measured** (no ledger holds two precisions at one support): the
default π = 1 is an assumption. β is fitted on LG00's L = 8 pilot (`CertFixed 96`) against its L = 20 ledger
(`CertFixed 128`) with the precision ratio `(128/96)^π` divided out: **β = 0.775 at π = 1** (torsion 0.75, Gram
0.80), 0.933 at π = 0; both pairs are reported (packed products are sublinear to linear in the support; the
forced toy's direct route is quadratic instead). `extra` 0 for sharp/frozen/refined (frames, claim and core are 0.7 % of the LG00 run
once the stages are shared, `ledger_fit.json`), 0.5 for the ℓ¹ entry and 1.0 for the hybrid (unmeasured), and
`c(l)` the measured certified-bite costs (SHARP2-C6: l = 8..12: 2.4, 6.1, 10.8, 34.3, 85.2 s; l ≥ 13 is
infeasible, above 10 GB at R1). A candidate is admissible when its **unrounded** margin exceeds the requested
one strictly, its certified sites have `l ≤ 12` and its precision obeys the rule. The tool returns the cheapest
admissible candidate (exact mirrors preferred at equal cost) and the cheapest admissible sharp candidate as the
baseline fallback, whose err is a prediction.

### Validation (`python3 -I scripts/certifier/route_select.py --validate`, 10 s)

Corrected after AUDIT-V2-TOOLS-1 (C1–C3; V2-TOOLS-FIX2). The first version's headline gains (lunar 0.88×, LG00
0.68×) are **withdrawn**: the lunar pick cleared the 1-decade rule only after rounding (1.0046) and fails against
SO-V2PKG's re-measured ρ = 1/70 threshold (margin 0.93); the LG00 pick used `CertFixed 96`, which LG00-CERT.md:204
rules out at these L, and a cost linear in precision that nothing measured.

The exact mirrors reproduce every hand-measured threshold at the hand points: lunar R2 sharp −31.83, frozen A
−27.87, refined A d01b −14.26 (SO-V2PKG: −31.83, −27.87, −14.26); LG00 sharp −32.04, frozen A −27.98, refined A
classical −15.10 (LG00-CERT: the same three).

| | hand choice | tool, constrained to the hand's ρ, P and realized margin | tool, unconstrained (unrounded margin > 1 decade) | sharp fallback (err predicted, never observed) |
|---|---|---|---|---|
| lunar65 | refined A, d01b sites, ρ = 1/140, L = 20, P = 96: 2.04 CPU-h | **reproduces it** (kp = 3 certifies the same five sites) | refined A, kp = 2, ρ = 1/70, L = 20, P = 96: 2.01 CPU-h, **0.99× (about 1 %)**, on sites not checked by `balCheck` and an interpolated err | ρ = 1/70, L = 38, P = 128: 7.9 CPU-h |
| lg00 | refined A, classical sites, L = 20, P = 128: 30.1 CPU-h | **reproduces it** | the same route at L = 19, P = 128: 27.7 CPU-h, **0.92×** (0.90× at π = 0), margin 1.02 on an err interpolated at an L that was never run | L = 37, P = 192 (the precision rule): 121 CPU-h, err from LG00-PREP's predicted table |

Readings:
* **lunar65.** With the re-measured thresholds the 1/70 strip buys about 1 %, and only if its five new certified
  sites pass `balCheck` and the err at 1/70 (SO-V2PKG's "≈ 8e-16") holds: not worth a new package, which
  confirms SO-V2PKG's decision to stay at R2. At the hand's ρ and margin 1 the tool picks kp = 2 instead of 3 at
  equal cost (one fewer b site, about 11 s); at the realized margin it reproduces d01b. The choice is the same for
  every (π, β) pair reported.
* **lg00.** The one lever left is L = 19, which nobody ran; its interpolated err gives a margin of 1.02, at the
  edge of the rule, so the 0.92× is conditional on measuring err at L = 19. The precision rule forbids 96 bits
  (it answers the earlier owner question). LG00's clock coordinate is negative (`−41.48`), so `clockOk` rejects
  certified sites as oriented: classical sites are forced, which the tool detects.
* **Estimates.** Design estimates (ℓ¹ entry, hybrid) and the L8′ estimate are labelled and never chosen over an
  exact-mirror candidate of equal cost; none is the choice in either profile.

### Not covered (#3)

* No forced-toy profile in the tool (its producer could feed one live; the forced suite's direct-route costs are
  quadratic in the support, unlike the packed applications).
* Route B with certified sites is not scanned (the B rows use classical sites); the refined-B threshold of the
  forced toy with certified sites is in part #6.

### Known limitation (deferred to Scott)

The cost model's ℓ¹-entry (+0.5 of the base cost) and hybrid (+1.0) terms are unmeasured guesses, and their
thresholds are design estimates (`thresholds_v2` at R1; the hybrid also needs the model's measured step-0
constant). They are reported as estimates and never chosen over an exact-mirror candidate of equal cost; one
measured trial each would calibrate them (orchestrator: recorded as a known limitation, deferred to Scott).

### Owner questions (#3)

1. Worth measuring LG00's err at L = 19 (one dry run of the producer) to settle the conditional 0.92×?

## Owner questions (#6)

1. The ℓ¹ entry and the hybrid on the forced toy need checker-side memoization bridges (for `checkL1Claim`, and
   the hybrid compositions) analogous to `Kernel/Stage.lean`: commission them after the SO hold lifts?

## V2-TOOLS-FIX (orchestrator ruling on the default-build weight)

Ruling: move anything over ~10 s or ~2.5 GB to `kernel-tests/` with a README line; keep in the default build only
a cheap subset (the mutation checks and one passing certificate, a few seconds each).

* `scripts/certifier/forced/forced_layout.py` lays the generated full modules out (reproducible: the generators,
  then the layout). The passing certificate kept in the default build is `Micro` (sharp, frozen A, frozen B; no
  certified sites, so its routes cost 1.8 s); its base proofs are split into seven modules, the stage proofs
  independent of each other (parallel). The mutations stay on `Tiny`, in ten modules, importing only the
  witnesses (`TinyWitness`, definitions) and the cheap Gram and `[4, 0]` stages (`TinyGram`).
* `mut_dispRoom` now decides the rejecting final clause (`finalOkA` at `disp = 1`) instead of the whole
  `refinedCore`, whose site checks made its module 9.1 s / 3.0 GB (now 1.4 s / 1.6 GB); `mut_frameT` (it needs
  every torsion stage) moved to the opt-in file.
* Opt-in: `kernel-tests/CertificateSharp/V2/ForcedRoutes.lean` (451 lines; imports only library modules; row and
  run line in `kernel-tests/README.md`).
* Re-checked: every default module built (numbers above), the opt-in file elaborated on a scratch copy without
  error, `forced_xlang.py`: `ALL AGREE (31 comparisons)`, axioms as above, `forced_routes.py` gained `--B`,
  `--R XS BF BT` and `--frozen` so the README's pipeline regenerates every route module.

## V2-TOOLS-FIX2 (AUDIT-V2-TOOLS-1: PASS WITH CHANGES, Lean side all PASS)

* `origin/main` merged (`8ad51247`); the conflict in `KAM/Root/CertificateSharp.lean` resolved by regenerating
  the roots (`gen_root_imports.py`, `--check` clean). Main added files only, none in the forced modules' closure.
* `route_select.py`:
  * C1: strict comparison of unrounded margins; SO-V2PKG §4.6's re-measured thresholds anchor the lunar strips (a
    d01b route computed by the tool, the other routes shifted alike); sites off the package strip are flagged. The
    lunar result is about 1 % (0.99×), not 0.88×.
  * C2: per-profile precision rules (LG00-CERT.md:204 for LG00); the precision grid extends to 320 bits; π is
    marked unmeasured. The LG00 result is a conditional 0.92× at `CertFixed 128`, not 0.68×; its sharp fallback is
    at 192 bits.
  * C3: β refitted with the precision ratio divided out (0.775 at π = 1; 0.933 at π = 0), both reported.
  * Minor: the L8′ comment, err sources (measured, interpolated, extrapolated), the fallback labelled as predicted,
    the measured LG00 point at L = 21 added, and no fixture written unless `--write-fixtures` (or `--json`).
* `forced_xlang.py`: two-sided probes and the full jet comparison (52 comparisons, above); docstring corrected.
* Recommended mutation added: `mut_XsB` (route B at `10 X⋆`, rejected by `okB`; `TinyMutCores`, 1.4 s); the
  domain-guard mutations `θ = 1` and `a = 1` are labelled as such.

## Suspected errata and deviations

* No pinned-source erratum suspected.
* Deviations: none in the core checker. Observations in untrusted tooling (not fixed, owned by others or
  historical): `scripts/spin_orbit/v2_q.py` `refinedCore` divides by `1 − θ` without Lean's totalized division
  (a ZeroDivisionError at θ = 1, where Lean's `wfOk` rejects; the mutation suite records it as a rejection); the
  `sofx` mirror and the landed checker agreed bit for bit on every forced-toy stage.
