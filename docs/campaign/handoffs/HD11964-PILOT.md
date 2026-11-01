# Handoff HD11964-PILOT (phase 1: data, design, numerical gate)

Worker HD11964-PILOT, branch `hd11964` (worktree `/home/scott/KAM-dev-worktrees/hd11964`, from `origin/main`
`4cb9f712`). Date: 1 November 2026. No Lean was written (phase 1). Nothing was pushed.

## Files

| file | content |
|---|---|
| `applications/hd11964/README.md`, `CITATION.cff` | project root (D51): system, model, conventions, provenance, what is and is not claimed |
| `applications/hd11964/data/hd11964-pilot.json` | pinned inputs as exact decimal rationals, with errors and provenance |
| `applications/hd11964/data/nasa-exoplanet-archive-ps-20261101.csv` | the archive query (SHA-256 recorded in the JSON) |
| `applications/hd11964/data/LICENSE` | CC BY 4.0 for our data and tables; attribution note for the archive extract |
| `applications/hd11964/scripts/*.py` (Apache-2.0) | `hd11964_model` (model, nominal state, exact-rational `threshold_ok`), `jets`, `normal_form`, `gate`, `checks`, `rigor`, `kscan`, `hiprec`, `summarize` |
| `applications/hd11964/validation/*` | `gate-N4.jsonl` (48 centres), `ladder.json`, `checks.json`, `threshold.json`, `rigor-N3.json`, `kscan-N3-s1.0.json`, `product-census.json`, `slow-radius.json`, `hiprec-*.json`, `conv-*.json` |
| `docs/campaign/design/HD11964-PILOT.md` | the design, including the "Kernel engine" section of the addendum |
| `docs/explorations/hd11964-pilot.md` | the report, with status labels and owner questions |

## Approach

1. **Data.**
   - Rosenthal et al. 2021 rows for both planets, from the NASA Exoplanet Archive (TAP, 1 November). CDS did
     not answer.
   - Pinned as exact decimals. `μ` and `ν` are exact rationals.
   - Minimum masses, coplanar, edge-on.
2. **Geometry.**
   - `B = Λ_c` on the whole action box `U`: the pair threshold is ≥ 0.792 by a monotone lower bound, decided
     in exact rationals (`threshold_ok`, the mirror of the planned Lean check).
   - `δ = 0.0483`, `r = 4·10⁻³`. The certified drift is `d = 10⁻³` on the region
     `R(d) = {Λ ∈ box ± d, Γ_c + Γ_b ≤ 0.012}`, so `e_c ≤ 0.61`.
3. **Gate.**
   - Taylor jets in the six local variables, times fast-angle grids. The chart and the exact Newtonian `f` are
     evaluated in jet arithmetic.
   - A Lie series to order 4 with the slow variables in the brackets.
   - The residual `{F_i, H∘Ψ}` uses the **exact** gradient of the original `H∘Ψ`.
   - 48 centres over `R(d)`, full grids.
   - Validation:
     - self-checks: the chart, symplecticity, rotation invariance, and the flow of a direct N-body
       integration;
     - a cutoff scan;
     - ℓ¹/sup loss factors;
     - grid convergence;
     - long-double reruns and mass scaling.
4. **Design.**
   - The headline shape. The bridge `stoppedDrift_of_approxIntegrals`, built on LP-LIFT and a nested first exit.
   - The certificate checks, with the exact Lie-remainder identity, so that no `O(μ)` cancellation happens in
     the kernel.
   - The kernel engine: the packed models on main, the new Taylor × Fourier layer, cost tables.
   - Owner questions.

## Checks and their output

All commands were run from the repository root.

- **`python3 -I applications/hd11964/scripts/hd11964_model.py`**
  - `mu = 2005497248200/3833351025484041 = 5.2317e-4`, `nu = 1217282799/10027486241`;
  - `Lam = (0.0584106, 1.7846965)`, `C0 = 0.0094553`, `B_pair_lower = 0.858`, `B_equals_Lam0 True`;
  - `beta = 0.1619`, period ratio 51.029;
  - chart checks: action residual ≈ 1e-41, AMD residual 1e-41, both planets prograde.
- **`threshold_ok`** (exact rationals, `validation/threshold.json`): `ok = True`.
  - chamber, `I1 ≥ I0`, `pair_lower = 0.79197 > 0.0625106 = max Λ_c on U` (slack 12.67);
  - `δ = 0.0483105`, `3r ≤ δ/4` with `r = 4/1000`, `2d ≤ r`;
  - the nominal state is in the box and `C0 ≤ Cbar`.
- **`OMP_NUM_THREADS=1 python3 -I applications/hd11964/scripts/checks.py`** (`validation/checks.json`):
  - `symplectic_max_error 6.2e-26`;
  - rotation-invariance rates `[5.7252e-11, 4.1323e-11]` against `[5.7213e-11, 4.1320e-11]`;
  - flow check, 20 yr of direct integration:
    `Lam_excursion [1.88e-05, 1.86e-04]`, `F1_excursion [7.95e-09, 6.45e-08]`, `F2_excursion [5.60e-09, 6.21e-10]`.
- **The sweep:** `gate.py --N 4 --procs 2` under the 8 GB scope, 48 centres, `validation/gate-N4.jsonl`.
  `summarize.py 5 1.45` gives the tables of report §5.2 (`validation/ladder.json`).
- **Cutoff, loss factors, convergence, precision.**
  - `kscan.py 3 1.0 …`: saturation at `K_c` 40 / 73 / 90 for orders 1 / 2 / 3.
  - `rigor.py 3 0.0,0.5,0.85,1.0`: ℓ¹/sup 1.01–1.66 at every order.
  - `conv.py` at `e_c = 0.44` and `hiprec.py 4 0.85 352 64 nolong`: μ-scaling ratios 2.0 / 4.0 / 8.0 /
    15.8–16.0 / 2.0–2.9 for orders 0–4; order 4 is float64-limited.
  - `hiprec.py 4 0.0 48 48 long 0.0 0.0`: HIPREC_SHORT
- **`scripts/lint_sources.sh`**. Every file-based check passes:
  - `check_lean_modules: PASS (4397 Lean files)`, the 25 frozen-anchor tests OK, `FROZEN-ANCHOR GUARD OK`;
  - `gen_root_imports.py --check` and `render_errata.py --check` pass.
  The last step, `abi_hashes.py --check`, cannot run in this worktree: `object file …/KAM/Frozen/Planetary/
  Spatial/Defs/AngularMomentum3.olean … does not exist`. 164 of 307 frozen modules have no `.olean` in the
  copy-on-write snapshot. No Lean file was added or changed.
- **Build:** none. Phase 1 has no Lean modules.

## Axioms

No Lean declarations were added, so there is nothing to `#print axioms`. The planned headline rests on LP0
(`planar_strongAMD_barrier`, manifest state `SEALED`), `strongFirstExit_of_stopped_drift` and
`lpChartLift_of_stopped`. They are on main and not re-audited here.

## Measurements

- **Drift rate by order** (worst sampled, `R(10⁻³)`, `e_c ≤ 0.612`):
  - orders 0–3: `5.35e-4, 4.20e-7, 3.70e-10, 3.25e-13`;
  - order 4: ≤ 7.3e-15, a float64-limited upper estimate; extrapolated ≈ 3e-16.
  The worst point is the low-`Λ_c` corner with all AMD in c.
- **`F − Λ` ranges:** 3.5e-5 (c) and 2.1e-4 (b). The latter is the reduced-mass oscillation of LP's split.
- **Ladder** (margin ≥ 2):
  - 10³ yr at order 2 (margin 4.7; 3.3 with ×5);
  - 10⁶ yr at order 3 (4.7; 3.2);
  - 10⁹ yr at order 4 (3.8; 1.8–3.2 with ×5, see report §5.2).
  The largest `T`: order 2 1.9e5 yr, order 3 2.1e8 yr, order 4 ≥ 5.9e9 yr.
- **Products per cell** (unpruned census): 1.0e3 / 1.0e4 / 7.2e4 / 3.8e5 at orders 1–4.
- **Slow-variable analyticity radii of c:** 0.05–0.16. Cells: 50–200 (*estimated*).
- **Kernel cost** (*estimated*, packed): 10³ yr 70–300 CPU-h; 10⁶ yr 500–2,000; 10⁹ yr 2.5–10e3 before pruning.
  Landed list arithmetic: about 100× more.
- **Python compute:** the sweep took 2.58 CPU-h in all (about 1.3 h wall on 2 processes); per centre 27 s –
  24 min; RSS ≤ about 3 GB per process.

## Owner questions

The conservative option was taken in each case; nothing blocked.

1. **Neighbourhood size.**
   - Baseline: `Cbar = 1/100` (nominal AMD + 6 %) and a `Λ` box of ±(10⁻⁴, 3·10⁻³), the 1σ period of b.
   - The 1σ eccentricities (`C ≈ 0.020`) put `e_c` past the Laplace limit, at about 3–10× per order.
2. **T target.** 10³ yr (order 2) first, then 10⁶ (order 3); 10⁹ (order 4) only after pruning is measured in
   the kernel.
3. **Masses.**
   - `m sin i`, coplanar, edge-on. True masses scale `μ` by `1/sin i`, and the order-`N` rate by
     `(1/sin i)^{N+1}`.
   - Mutual inclination is out of scope (planar model).
4. **Anchoring.** Should the headline go in an application manifest or the core manifest? (APPLICATIONS.md
   leaves it open.)
5. **The LP helper.** Should the LP lane get a signed or weighted variant of
   `strongFirstExit_of_stopped_drift`? Not needed for HD 11964's rungs.
6. **Addendum.** The packed engine needs a new Taylor × Fourier layer and an axis-ramp primitive (design §7),
   placed beside `KAM/CertificateSharp/Packed/`, not in it. Who owns that?

## Suspected errata and deviations

- **Errata in pinned sources:** none. The archive's Rosenthal rows match A7 §5.
- **A note on LP-QUANT (not an erratum).** Its frozen-slow Newton steps overstate the per-step gain at
  HD 11964. With the slow variables in the brackets the Lie series gains ≈ 10³ per order, linearly. So "3 steps"
  corresponds to order 4 for 10⁹ yr. Its own §5.5 caveat 1 anticipated this.
- **Deviations.**
  - The gate runs order 4, not 3. Frozen-slow Newton steps do not transfer.
  - The high-precision leg is 80-bit long double at sample centres, plus a mass-scaling test, not a full
    30-digit rerun.
  - The certificate region is built on the certified drift `d`, not on the helper's `r`. This keeps `e_c` below
    the Laplace limit.
  - The lint's ABI-hash step could not run in this worktree: 164 of 307 frozen modules have no `.olean` in its
    build snapshot. No Lean file changed, so the ABI is unaffected.
