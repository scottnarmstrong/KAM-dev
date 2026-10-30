# SHARP-CERTSIDE handoff: the checker side of the sharp certifier

Brief: `/home/scott/kam-tools/briefs/SHARP-CERTSIDE.md` (Opus), branch `sharp-certside`. LOCAL-COMMON applies.
This is a design study: Python and documents only. No Lean file was added or edited, nothing was built, and nothing
under `KAM/Certificate/**`, `scripts/spin_orbit/**` or `certificates/**` was modified (they were read, and the SO
scripts imported read-only).

## Files (new)

- `docs/campaign/design/CERTIFIER-SHARPNESS.md`: the deliverable of task 5. It covers the inventory (§1), tighter
  majorants (§2), the optimizer (§3), kernel efficiency (§4), the ranked levers (§5), the package split for
  `KAM/CertificateSharp/` (§6), coordination with SHARP-PLUS (§7), caveats (§8) and reproduction (§9).
- `scripts/certifier/measure_residual.py`: rebuilds the exact R3/R4 invariance rows of the rotated lunar
  candidates (through `rot_build`) and the exp-witness data. It reports their ℓ¹, corner, ℓ² and sampled-sup
  norms.
- `scripts/certifier/smalldiv.py`: exact Diophantine infima of quadratic frequencies, certified by finite
  enumeration plus the norm tail. Also S(ω, δ) and the Γ_spec/Γ_R ratios.
- `scripts/certifier/lunar_oracle.py`: norm oracle. It handles frames A ∈ GL(2, ℤ), action and time scaling, three
  majorant regimes (landed ℓ¹, corner, sampled sup), the H-majorant with either the landed disc trig bound or cosh,
  and the torsion. It reproduces SO-GEN2's enclosures exactly.
- `scripts/certifier/optimize.py`: the free-parameter optimizer (task 3), with modes `reproduce`, `ladder`, `search`
  and `v2opt`.
- `scripts/certifier/v2_adapter.py`: adapter to SHARP-PLUS's `thresholds_v2.py`, imported read-only from the
  `sharp-plus` worktree, which was work in progress.
- `scripts/certifier/v2_majorants.py`: measured |Lᵀ|, |N|, |Nᵀ|, sup|T| and |ω| against what v1 derives.
- `scripts/certifier/step0_coh.py`: the actual cohomological solve of the residual against the a-priori bounds
  (evidence for L6).
- `scripts/certifier/rho_retrunc.py`: T/e against ρ for candidates re-truncated to the v1 support (L = 28–36).
- `scripts/certifier/v2_support.py`: the truncation SHARP-PLUS's v2 mirror needs (L = 16–24).
- `docs/campaign/handoffs/SHARP-CERTSIDE.md`: this handoff.

## Approach

- **Inventory.** A read-only subagent mapped every sub-check to its `G1Hyps` fields and bound (§1.1). I measured
  each bound against the true value on R1 with my own scripts (§1.2), and the toys from `certificates/so-toys/` and
  SO-TOYGEN (§1.3).
- **Majorants.**
  - The corner (vertex) bound, the maximum principle plus grid bound, and the trig primitive were evaluated on the
    exact residual and frame data.
  - Diophantine constants: quadratic exact, and a cubic direction bound.
  - S(ω, δ): kernel-evaluable bound and numbers, cross-checked against SHARP-PLUS's `c_freq` to 0.7 %.
  - Sizes of the v2 objects and of the step-0 solve.
- **Optimizer.** A staged search over 13 frame classes and λ, c, ρ, μ, s, against v0, v1, an L2-emulated v1
  ("v1L2", an estimate, not a mirror) and SHARP-PLUS's v2 mirror.
  - Validated on CONSTANTS-STUDY's P0 (−99.874) and R1 (−74.509) and on the emitted R1 (−74.669; T/e +3.03).
  - The lever ladder at the fixed R1 package separates the majorant gains from the re-optimization gains.
- **Kernel.** A read-only subagent built the cost model from D34, SO-REPLAY/REPLAY2/ADVCOUNT/DATA-1/GEN2, the
  OVERNIGHT log of `main` and the Poly code, plus its own truncation scan. I integrated it in §4.

## Checks run and their output

- `python3 -I scripts/certifier/optimize.py --cache C reproduce`:
  - P0 −99.874;
  - R1 (CONSTANTS-STUDY) −74.509;
  - R1 emitted −74.669; oracle T/e +3.03;
  - R1 with the Lean `lunarR1` M = 2.03: −74.94.
- `lunar_oracle.py` at R1: σK−μ 1.3604, Gram 1.97994, M₁ 1.047601 (cosh) and 2.0205 (disc = the Lean D²H sum),
  torsion 1.022493, η₃ 1.0603e-78. All equal to `lower_rot.json` and `LunarParams.lean`. θ frame: torsion 2.718037
  and 2.849753, the pilot's values.
- `optimize.py ladder` (v1, R1, lower / upper): landed +52.80 / +52.51 → corner +53.62 / +53.26 → + cosh
  +53.65 / +53.29 → + γ* +53.71 / +53.35 → + P2 +53.91 / +53.36.
- `smalldiv.py`: γ* = 0.0246196 (rotated), 0.0492392 (θ), certified with K₀ = 2. Γ_R/Γ_spec = 107 at δ₀ = 0.0024.
- `step0_coh.py`: Γ_R/measured = 10^6.08–10^6.55; Γ_spec/measured = 10^4.05–10^4.52.
- `search` (lower and upper):
  - rotated frame optimal, by 3.2 orders;
  - v1, landed checker: +52.80 → +54.84 (lower) and +52.51 → +54.81 (upper) at L = 88; the gain is a small-ρ
    artefact of the over-resolved data;
  - v1 with corner bounds: +55.44 / +55.38;
  - v0 with corner bounds: +4.56 / +4.16, against +2.76 / +2.47 landed.
- `rho_retrunc.py` at L = 32: ρ = 1/70 is optimal (T/e +2.50 / +2.60 with corner bounds; +1.62 / +1.74 landed).
- `v2opt` (lower): log₁₀T −11.18 at the R1-like package, T/e +66.92 → +68.92.
- `v2_support.py`: v2 (log₁₀T −11.18 at ρ = 1/70) gives T/e +1.4 at L = 16, +3.0 at L = 18 and +4.9 at L = 20.
  v2 needs about 17–18 digits of truncation, against 32 under v1 and 88 under v0.
- `sh scripts/lint_sources.sh` (exit 1, nothing from this branch, which adds no Lean file):
  - Lean lines over 100 characters in `KAM/Sharp/TorsionBound.lean:25` and `KAM/Sharp/TorsionPoly.lean:25`
    (SHARP-A3, pre-existing);
  - `check_lean_modules: PASS (1427 Lean files)`;
  - `FROZEN-ANCHOR GUARD OK`;
  - `abi_hashes.py` failed with "unknown module prefix 'KAM'", because this worktree has no build (the known
    ABI-scratch failure).
- `#print axioms`: not applicable. No Lean declaration was added.

## Incident (please read)

This worktree had no `.lake` directory. The lint script's ABI step (`abi_hashes.py`, through `lake env lean`) made
Lake create `.lake/` and **fetch the dependency sources from GitHub into `.lake/packages`**. It cloned 198 MB of
mathlib, batteries, aesop, Qq, proofwidgets, plausible, importGraph, LeanSearchClient and Cli, at the pinned
revisions. Nothing was built.

I checked that every entry of `.lake` was created by that run (11:52–11:53, after the session started). Those were
fresh clones, not hard links, so no other checkout was affected. I removed the directory, which restores the
worktree to its prior state (no `.lake`). `lake-manifest.json` is unchanged.

Suggestion for the orchestrator: in worktrees without a build snapshot, `lint_sources.sh` should skip the ABI step,
for example when `.lake/build` is missing, rather than letting Lake materialize packages.

## Uncertainties

- Sampled sups are heuristic. The corner regime is evaluated in double precision from exact coefficients; a
  certificate would carry rigorous rationals.
- v1L2 is my emulation of L2 (c_R → c_R,eff at δ₀); SHARP-PLUS's staged mirror is the reference.
- The v2 numbers come from SHARP-PLUS's uncommitted mirror as of 30 October 2026.
- Lean line counts are estimates from the landed analogues.
- The witness part of e in non-rotated frames uses the base frame's witness bound (about 12 % of e).
- Kernel figures are the SO studies' measurements and their extrapolations. Post-D34 packing was still being
  re-measured.

## Suspected errata and deviations

- **Pinned sources:** no errata suspected.
- **Deviations:** none introduced. No Lean change; the theorems are used as frozen or as designed.
- **Remark, not a defect:** `KAM/SpinOrbit/LunarParams.lean` sets M = 203/100. That is above the checker's D²H
  sum (2.0205), so the one-size 𝔪 of v0 is 2.03 rather than the 1.987 of `lower_rot.json`. The v0 threshold becomes
  10^−74.94 instead of 10^−74.67, which leaves 2.2–2.5 orders of slack against the certified errors.
- **Study discrepancy** (kernel subagent): SO-ADVCOUNT assumed that compose evaluates only the needed slots and that
  cfgLow factors are trimmed. The landed code does neither (`Expr/Compose.lean:171-187`, `Gram.lean:115-124`).

## What remains

- C1–C7 of §6 are proposals for new packages; none was started here.
- Rerun `optimize.py search --v2 …` once SHARP-PLUS's mirror is frozen.
- An SO-owned regeneration with the optimized parameters: a smaller ρ is optimal for the fixed 88-digit data, but
  after re-truncating to the v1 threshold (L ≈ 32), ρ is flat in [0.008, 0.02] (§3.4). That is a proposal for the SO
  track.
