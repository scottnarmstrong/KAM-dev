# Handoff APPS-SCOUT

Branch `apps-scout`. Research and feasibility only: no Lean written or built. The study is
`docs/explorations/striking-applications.md`.

## Results in brief

- **Top target:** the Moon's permanent lock at the true ε. The published rigorous result stops about 5× short (Celletti 1994). Numerical tori exist at the true ε from 5° to 72°; v1 needs about 40 digits and 4k modes.
- **Librational tori are primary in a polar chart**, so they need `HamExpr.sqrt`, not a new KAM theorem.
- **Exact Kepler forcing is an expression**, through the eccentric-anomaly chart and a time change. Kepler-equation analytics are not needed for spin–orbit clients.
- **Mercury's 3:2** costs about what the Moon costs (N_full = 3) and works under the current theorem.
- **12 Victoria (CC07 truncated)** is about 34 digits, 1.1k modes under v1. The exact PCR3BP and Trojans converge numerically but need 300–1300 CPU-h: after v2, heroic.
- **Standard map:** needs a maps theorem; the kernel then reaches k ≈ 0.970–0.971.
- **Sun–Jupiter–Saturn:** infeasible in the kernel, about 10⁷ CPU-h.
- **PlasmaLean's proved tolerance on its own example (10⁻¹⁸·²) beats our v1 (10⁻²⁵ to 10⁻³⁰) by 7–12 orders.** The owner should know this before any "best in class" claim. Cause and lever: `striking-applications.md` §8, §13.
- **Recommended sequence:** (1) Mercury and the Moon band; (2) the Moon's lock; (3) 12 Victoria. In parallel: the maps theorem.

## Files

- `docs/explorations/striking-applications.md`: the study (ranked table first, one section per candidate, recommended sequence, method, reproduction, appendix).
- `scripts/apps_scout/`:
  - library: `kamlib.py`, `models.py`, `pipeline.py`, `thresholds_est.py`, `costmodel.py`;
  - runs: `run_moon_rot.py`, `run_libration.py`, `run_r3bp.py`, `run_stdmap.py`, `run_mag.py`, `run_sjs.py`, `count_products.py`, `v2_levers.py`, `table.py`;
  - `results/*.json`, `results/table.md`: every number in the study.
- `docs/campaign/handoffs/APPS-SCOUT.md`: this file.

Existing tracked files: none changed. `scripts/apost_sharp/thresholds.py` is imported unchanged.

## Approach

A generic double-precision isoenergetic quasi-Newton solver for primary 2-tori of any H given as code, with sampled majorants, then the threshold columns, digits, support and cost.
Literature from arXiv, mp_arc, Springer abstract pages and PlasmaLean's repository.

## Checks and output

- **Validation on R1** (`python3 run_moon_rot.py validate`):
  ```
  p range 0.968007 0.981806 err 4.6e-14 time 0.6
  c 1.00 M 1.0858 sK 1.3739 sB 1.9310 sT 1.0799 cur -75.33 v1 -25.27 v2 -20.99 ell1 -20.14
  c 1.75 M 1.9002 sK 1.3739 sB 1.9310 sT 0.6197 cur -74.36 v1 -24.96 v2 -20.33 ell1 -19.58
  ```
  Published: 0.968007–0.98181; v1 −24.98. Raw σ_K, σ_B, σ_T are 1.3025, 1.8331, 1.022493 (published 1.303, 1.833, 1.022493).
- `python3 thresholds_est.py` gives v1 = −24.98 on R1, exactly the design's figure.
- `python3 count_products.py`: the lunar client gives 3, matching SO-ADVCOUNT.
- `python3 costmodel.py`: the R1 unit returns ratio 0.9988.
- Lint: `scripts/lint_sources.sh` was run once, **and its overall result was not captured** (see the incident). Its lake-free steps were then run individually, all exit 0:
  ```
  gen_root_imports --check            rc=0
  render_errata --check               rc=0
  check_lean_modules: PASS (1427 Lean files, 0 comparator configurations)
  FROZEN-ANCHOR GUARD OK
  ```
  The ABI hash step was not confirmed. It does not apply to this change, as no `.lean` file is touched.
- `git diff --check`: clean. `#print axioms`: not applicable.

## Incident: `.lake` created in this worktree

`scripts/lint_sources.sh` runs `abi_hashes.py`, which calls `lake`. This worktree had no `.lake`, so lake cloned the dependencies into
`.lake/` here (198 MB: `packages`, `config`, `abi-scratch`, created 12:11–12:12). LOCAL-COMMON says not to touch `.lake/packages`.

- No tracked file changed, including `lake-manifest.json`.
- No other worktree was touched.
- No file under `.lake` has a hard link to the shared snapshot (`find -links +1` empty).
- It is gitignored and nothing keeps running.

I left it in place rather than touch the path a second time. It is safe to delete with `rm -rf .lake` in this worktree. `abi_hashes.py` will do the same in any no-build worktree; a guard in the lint script would prevent it.

## Uncertainties

- All tori are double precision; nothing passed an interval check.
- **Support is the weakest number:** S = 1.4·α·L² extrapolates a fit at L = 8–12 by up to 40 digits. The 1.4 comes from one calibration point.
- **Cost tier P excludes composition, Gram and torsion** (not yet measured by SO on the fixed code), and scaling away from the lunar unit is untested. N_full is traced for most candidates as a naive upper bound; the librational figure (15), Kepler (9) and tokamak (12) are hand counts.
- **The v2 column is my estimate,** with no proofs behind it; replace it when SHARP-PLUS reports.
- Saturnian ε comes from shapes, partly from memory (flagged in §5.2). Mercury's ε is the 1998 value.
- The comparison with PlasmaLean uses norm guesses from its bounds and is not like for like.
- "First" claims are from targeted searches. **Celletti 1990 Part II must be read before any Mercury priority claim**, and the full text of Celletti 1994 was not accessible.
- Exact-PCR3BP continuation stalled at e = 0.22 at n ≈ 3.33 and n = [3;2,1̄]; I did not establish why. Three Trojan cases at e = 0.10 failed likewise.
- **Not computed:** Hénon–Heiles (continuation failed at the (1,2) resonance), galactic models, the Levi-Civita chart for Hill, Froeschlé, the secular SJS model, the exact-Kepler librational torus. Elliptic-restricted and other n ≥ 3 entries are scaling arguments only.
- Timelines are rough judgments.

## Suspected errata and deviations

No suspected errata in any pinned source.

Corrections to our own notes (not edited; additive rule):
- `docs/explorations/lunar-band-2p8-2p9.md`: the Moon entry for Celletti 1994 omits the factor of 5. "Beyond the floor" says librational tori need a normal form or a new G1, and a polar chart suffices. The band target is conservative: 2.65 % at N = 80 fits under v1.
- `docs/explorations/lunar-spin-orbit-certificate-proposal.md` §13.1: analytic control of Kepler's equation is not needed.
- The brief's list ("librational or non-primary tori … not yet") should treat librational tori as available given `sqrt`.
- The seven-term coefficients are truncations: A₆, A₇ differ from exact Hansen values by about 1 %. Expected, and stated by the model; relevant only to the "exact model" claim.

Deviations from the brief: the v2 column is estimated, and the verdict list gains "after v1".

## For the orchestrator

- Feed `v2_levers.py` and §13 to SHARP-PLUS: after H_T and c_R, the `sum` and ν branches bind near 10⁻²⁰ on R1.
- `HamExpr` is SO-owned. `sqrt` should live in the sharp certifier's own files or be requested from SO; PlasmaLean's `PolyExprS` isqrt node is a template.
- Owner decisions needed: whether to fund the maps theorem, and whether the exact PCR3BP is worth 300–1300 CPU-h.
