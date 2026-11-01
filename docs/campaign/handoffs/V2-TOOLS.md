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
* Lean (new modules only, `KAM/CertificateSharp/V2/Tests/Forced/`, all in the default build):
  `Format`, `Lemmas`; per toy `<T>Data` (certificate, `CertFixed 96`), `<T>Stages` (memoized Gram/torsion
  stage literals), `<T>Checks`, `<T>Base`, `<T>Freq`; `TinyClaim`, `TinyRouteA`, `TinyRouteB`, `TinyRouteR`,
  `TinyMutations`, `TinyMutationsInv`, `MicroRoutes`, `TinyC2Claim`, `TinyC2RouteA`, `TimeScale`.

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

### Mutations (24 rejections, 2 controls)

`TinyMutations` (13 + 2 controls, 27 s) and `TinyMutationsInv` (11, 18 s); each decides only the check that must
reject. The 19 the mirror covers are rejected by the mirror too (`Tiny_mutations.json`).

| Family | Mutation → rejecting check |
|---|---|
| coefficients | amplitude of `(1,0)` × (1 + 10⁻³) → `checkInvariance`; largest `u` coefficient × (1 + 10⁻⁴) → invariance; largest witness coefficient × (1 + 10⁻³) → invariance |
| residual claims | `err/2` → invariance; `E0 + 2 err` → `checkEnergy` |
| frame bounds | `bL`, `bN`, `bT` × 0.99 → `checkFrameL/N/T` (N, T through the stages); `dx` × 0.99 → `checkHamClaim` |
| ray room | `nuRay = 10⁻⁵` → `checkStatic`; `disp = 1` → `refinedCore` (room of the ray) |
| schedules | `θ = 1`, `10 X⋆` → `refinedCore`; route B `a = 1` → `refinedBCore` |
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

`TimeScale.lean`: `TinyC2` (H and ω* doubled) carries the same torus (`timeScale_emb`, `rfl`), its Hamiltonian
is `2 · Tiny.H` (`timeScale_H`), its reference vector `2 • Tiny.ωstar` (`timeScale_ωstar`), and
`timeScale_invariance` is `invarianceError_const_mul` instantiated: the invariance error of `TinyC2` is twice
that of `Tiny` at half the frequency, which is exactly the factor between the two independently checked
residual claims (8.2·10⁻¹² against 4.1·10⁻¹²; σT halves, M doubles). Both tori are certified
(`timeScale_tori`); the drift "H doubled without the box" is rejected (`Tiny.mut_timeScale`).

### Cross-language agreement

`python3 -I scripts/certifier/forced/forced_xlang.py`: `ALL AGREE (31 comparisons)` — jet programs (length,
v0, d1, d2) of the three Hamiltonians against `HamExpr.jet`, `sharpTest`, the claim at R and just below the
disc-pass `dx`, the route cores at 1, 10 and 1/2 times each witness's `X⋆`, and byte-identical regeneration of
the stage literals. In the kernel: every stage literal (above).

### Checks and measurements

`lake build` per module (wall, peak RSS of the build): Tiny `Checks` 10 s / 2.0 GB, `Base` 22–32 s / 2.5 GB,
`Claim` 5.4 s / 2.1 GB, `RouteA` 10 s / 2.9 GB, `RouteB` 16 s / 3.0 GB, `RouteR` 10 s / 2.9 GB, `Mutations`
27 s / 3.0 GB, `MutationsInv` 18 s / 1.9 GB; Micro `Checks` 9 s / 2.0 GB, `Base` 17–19 s / 2.3 GB, `Routes`
1.6 s / 1.6 GB; TinyC2 `Base` 23 s, `RouteA` 10 s; `Freq` 1.4 s / 1.5 GB; `TimeScale` 1.3 s. The heaviest single
theorem is a torsion stage (`XN1_eq`, about 7 s). Whole suite ≈ 4 min serial. Memory accounting: under
`lake env lean` the bare imports already show 3.4–3.6 GB RSS, under `lake build` the lightest forced module
peaks at 1.5 GB; the numbers above are `lake build` peaks.

`#print axioms` (all `[propext, Classical.choice, Quot.sound]`): `Tiny.refinedA_torus`, `Tiny.refinedB_torus`,
`Tiny.refinedR_torus`, `Micro.sharp_torus`, `Micro.frozenA_torus`, `Micro.frozenB_torus`,
`TinyC2.refinedA_torus`, `timeScale_tori`, `timeScale_invariance`, `Tiny.mut_hamCoef`, `Tiny.mut_denominator`,
`Tiny.ctl_sqrtDomain`.

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
| A refined, certified sites (kp = 1, 2, 3) | the same, `c = c_freq × 1.01` where `clockOk` applies and the cut-off `l ≤ 12` | exact mirror (the Lean `balCheck` is the check) |
| B frozen, B refined | `forced_witness.solve_B` on `route_b_lean_mirror` | exact mirror |
| A with L8′ | refined `e*/2` (the forced toy's kernel-checked ratio) | estimate |
| ℓ¹ entry | refined `e* × 10^0.75` (`thresholds_v2 --l1` at R1, iso) | design estimate |
| hybrid restart | `sqrt(e₁*/A_meas)`, `e₁*` the refined threshold at `ρ − 3δ₀` | design estimate (needs the model's `A_meas`) |

then scans L and the precision P (achieved err: log-linear in L from the measured table, the ρ factor, a floor
`10⁴ · 2^-P`), and reports per candidate: required vs achieved residual, margin, displacement (`disp_coef ·
err`), binding budget (the failing clause at `1.1 X⋆`), support, precision, the certified cut-offs, and the
predicted kernel cost

`C = C_ref (S(L)/S_ref)^β (P/P_ref)^π (1 + extra) + Σ c(l)`,

with `C_ref` the measured cost of the hand choice (lunar 2.0 CPU-h per torus, SO-CSPLIT-GATE's 1.6–2.5; LG00
30.11 CPU-h, the run20e ledger), **β = 0.93 fitted** on LG00's L = 8 pilot against its L = 20 ledger (torsion
stages 0.91, Gram 0.96: packed products are about linear in the support; the forced toy's direct route is
quadratic instead), π = 1, `extra` 0 for sharp/frozen/refined (frames, claim and core are 0.7 % of the LG00 run
once the stages are shared, `ledger_fit.json`), 0.5 for the ℓ¹ entry and 1.0 for the hybrid (unmeasured), and
`c(l)` the measured certified-bite costs (SHARP2-C6: l = 8..12: 2.4, 6.1, 10.8, 34.3, 85.2 s; l ≥ 13 is
infeasible, above 10 GB at R1). It returns the cheapest candidate above the requested margin (exact mirrors
preferred at equal cost), and always the cheapest passing baseline (the landed sharp route) as fallback.

### Validation (`python3 -I scripts/certifier/route_select.py --validate`, 12 s)

The exact mirrors reproduce every hand-measured threshold at the hand points: lunar R2 sharp −31.83, frozen A
−27.87, refined A d01b −14.26 (SO-V2PKG: −31.83, −27.87, −14.26); LG00 sharp −32.04, frozen A −27.98, refined A
classical −15.10 (LG00-CERT: the same three).

| | hand choice | tool, constrained to the hand's ρ, P and realized margin | tool, unconstrained (margin ≥ 1 decade) | sharp fallback |
|---|---|---|---|---|
| lunar65 | refined A, certified kp = 3, ρ = 1/140, L = 20, P = 96: 2.04 CPU-h | **reproduces it** | same route at ρ = 1/70, L = 19: **1.80 CPU-h (0.88×)** | ρ = 1/70, L = 38, P = 128: 9.9 CPU-h |
| lg00 | refined A, classical sites, L = 20, P = 128: 30.1 CPU-h | **reproduces it** | L = 19, P = 96: **20.4 CPU-h (0.68×)** | L = 37, P = 128: 98 CPU-h |

Readings:
* **lunar65.** The improvement is the wider strip, which SO-V2PKG §4.6 itself identified ("a wider strip gains
  0.7–1.1 orders, about one digit of L") and declined because it needs a new parameter package (re-enclosed
  majorants, new boxes and frozen-adjacent pre-checks). The tool holds σK, σB and the refined claim at their R2
  values across ρ (SO-V2PKG bumped them by 1–2 %), so the 0.88 is an upper estimate of the gain. At the hand's ρ
  and margin 1 it picks kp = 2 instead of 3 at equal cost (one fewer b-site, about 11 s). The choice is the same
  for every β in 0.75–2.
* **lg00.** Two levers: L = 19 already gives one decade (the hand run took L = 20 after L = 18 had none, a
  2-decade margin), and P = 96 instead of 128 (the precision floor is a model, calibrated on the forced toy only;
  LG00's large time scale `κ = 160000` may have motivated 128 bits: an owner question below). LG00's clock
  coordinate is negative (`−41.48`), so `clockOk` rejects certified sites as oriented: classical sites are forced,
  which the tool detects.
* **Estimates.** On lunar65 the hybrid design estimate (L = 14) is second at 1.86 CPU-h, behind the exact choice,
  with its extra cost guessed at one more composition pass; it is the candidate most worth a measured trial
  (`routeV2Hyb` exists). It is never preferred over an exact-mirror candidate of equal cost.

### Not covered (#3)

* No forced-toy profile in the tool (its producer could feed one live; the forced suite's direct-route costs are
  quadratic in the support, unlike the packed applications).
* Route B with certified sites is not scanned (the B rows use classical sites); the refined-B threshold of the
  forced toy with certified sites is in part #6.

### Owner questions (#3)

1. Should the cost model's unmeasured parts (the ℓ¹ entry +0.5, the hybrid +1.0 of the base cost) be calibrated
   by one measured trial each before the tool is used to commit an application run?
2. LG00 at `CertFixed 96`: is there a reason (time scale, jet constants) for 128 bits that the precision-floor
   model does not see? The tool's 0.68 depends on it (0.90 at P = 128, L = 19).
3. Lunar at ρ = 1/70, L = 19 (0.88×): worth a new package for the next lunar run, or keep R2 as SO-V2PKG decided?

## Owner questions (#6)

1. Default-build weight of the forced suite: per-module `lake build` peaks are 1.5–3.0 GB and module walls up to
   32 s (the heaviest single theorem ≈ 7 s), about 4 min serial in all. Keep everything in the default build (as
   now), or move the route/mutation modules over ~2 GB (`TinyRouteA/B/R`, `TinyMutations`, 2.9–3.0 GB) to
   `kernel-tests/`? Nothing in the core imports them except `TimeScale`.
2. The ℓ¹ entry and the hybrid on the forced toy need checker-side memoization bridges (for `checkL1Claim`, and
   the hybrid compositions) analogous to `Kernel/Stage.lean`: commission them after the SO hold lifts?

## Suspected errata and deviations

* No pinned-source erratum suspected.
* Deviations: none in the core checker. Observations in untrusted tooling (not fixed, owned by others or
  historical): `scripts/spin_orbit/v2_q.py` `refinedCore` divides by `1 − θ` without Lean's totalized division
  (a ZeroDivisionError at θ = 1, where Lean's `wfOk` rejects; the mutation suite records it as a rejection); the
  `sofx` mirror and the landed checker agreed bit for bit on every forced-toy stage.
