# Handoff SO-GEN2: lunar candidates in the rotated frame with enclosed norms (track SO, owner ruling O5)

Branch `inp-sogen2`, worktree `/root/code/KAM-inp-sogen2`. Python and data only: no Lean file was touched or built.
Commits: `2c519944` (library, builder, norms, R1 mirror) and `2076fc34` (emitted data, tables, emitter, verifier).

## Verdict

**Package R1 works, with checked numbers.** I regenerated both candidates in the rotated frame and enclosed every
quantity the checker will certify. Every `g1_explicit` parameter constraint passes in exact rationals.

| | Lower | Upper |
|---|---|---|
| Exact threshold (R1, c = 237/125, 𝔪 = 1987/1000) | 2.1425e-75 (10^−74.669) | same |
| Enclosed invariance error at scale c, c·η | 2.010e-78 | 3.919e-78 |
| Chosen e (3 digits, meets the G-J splits) | 4.03e-78 | 7.84e-78 |
| c·η / threshold | 9.4e-4 | 1.8e-3 |
| Smallness C₁e/(γ⁴ρ⁴) (must be ≤ 1/2) | 1.9e-3 | 3.7e-3 |
| Truncation L / bits | 88 / 318 | 88 / 318 |
| v terms (half / full lattice) | 4237 / 8474 | 4233 / 8466 |
| E terms (full lattice) | 8307 | 8322 |
| p terms (half), J terms (half) | 4237, 4373 | 4233, 4357 |

- **The projection held.** The study projected about 1e-75, L ≈ 87 and about 8.3k / 8.1k terms. The enclosed result
  is 10^−74.67, L = 88 with 2 orders of headroom (minimum feasible L = 86), and 8.47k / 8.31k terms.
- **One number misses its projection: the Gram inverse.**
  - The checker as designed bounds sup‖B‖ by weighted ℓ¹ norms. That gives **‖G⁻¹‖ ≤ 1.9799** (upper torus
    1.9801), not the study's sup ×1.05 ≈ 1.925. This one bound is what sets 𝔪 = 1.987, against the study's 39/20.
  - A rigorous sharper enclosure gives **1.8347** (upper 1.8347; sampled sup 1.8330), which meets the brief's ~1.83
    target. It uses the maximum principle on the distinguished boundary plus a 4096×1024 grid with a Lipschitz
    remainder. The designed checker has no such sub-check.
  - With it, package **"R1grid"** (c = 1757/1000, 𝔪 = 1841/1000) has threshold **10^−73.588**, 1.08 orders better.
    Both packages pass on the same data, and both are recorded in the JSON (`package` and `package_alternative`).
  - **Owner/design decision:** add a grid-sup sub-check for the Gram witness row sums. It is worth about one order
    of threshold, or about 1.2 digits of truncation (≈ 3 % fewer terms).
- **R2 is not needed:** R1 itself passes.

## Files

- `scripts/spin_orbit/rotlib.py` (new): exact sparse Fourier models.
  - Coefficients are dyadic integers with a parity phase, plus a sup radius on T_ρ.
  - Products are exact convolutions with outward radius propagation; truncation and rounding mass goes into the
    radius.
  - Norms are weighted ℓ¹ against a rigorous integer table W(n) ≥ e^{2πρn} (interval upper end).
  - This mirrors the design's `CertModel` semantics.
- `scripts/spin_orbit/rot_build.py` (new): builds the candidate and its exact residual rows, the exp-witness error
  and the G-J budgets.
- `scripts/spin_orbit/rot_norms.py` (new): DK, the domain D, the H′ majorant, the Gram inverse (plus the grid
  alternative) and the bordered torsion inverse.
- `scripts/spin_orbit/rot_scan.py`, `rot_table.py`, `rot_emit.py`, `rot_verify.py` (new): truncation scan, tables,
  emitter, and an independent round-trip check.
- `scripts/spin_orbit/exact_constants.py`: adds the R1 package as exact rationals (`package_R1`, `threshold_of`, CLI
  `R1 c m [out]`). The pilot output is unchanged; I re-ran it and it is identical.
- `scripts/spin_orbit/README.md`: new SO-GEN2 section.
- `certificates/lunar-spin-orbit/`:
  - `lower_rot.json`, `upper_rot.json`: about 1.05 MB each.
  - `schema/candidate_rot.schema.json`: schema_version 2, extended for the frame, the package, the domain,
    witnesses, enclosures, checks and G-J.
  - `lower_rot_truncation.json`, `upper_rot_truncation.json`: L = 80–92.
  - `exact_constants_R1.json`, `exact_constants_R1grid.json`.
  - `logs/`: emit, verify and table logs, and every scan record (`rot_scan_all.jsonl`).
  - New data in total is about 2.2 MB, well under the 300 MB cap. Scratch files are in `.drafts/scratch` (ignored).

Reproduce (about 1 min per torus): `cd scripts/spin_orbit; python3 rot_emit.py lower 88 88 88 318 237/125 1987/1000
OUT.json 1757/1000 1841/1000`, then `python3 rot_verify.py OUT.json`.

## Method

**Frame and candidate.**
- Q1 = q − φ, Q2 = φ, P1 = p, P2 = p + J, with H′ = c(P1²/2 − P1 + P2 + V(Q1+Q2, Q2)). The modes become the keys
  (2, 2−m).
- K′(ψ, φ) = (ψ + v/2π, φ, p̃, p̃ + J̃), and s·ω* = c(ν−1, 1).
- The SO-GEN 440-bit solution v is frame-independent, so I did not re-solve. I truncated it at |b| ≥ 10^−L and
  rounded to S bits.
- p̃ = round(ν + D_t v): its coefficients are b·λ with λ = (ν−1)k + l ∈ ℚ(√5).
- E is the SO-GEN witness of exp(2iv), truncated and rounded.
- J̃ = round(−p̃²/2 + Σ εA_m Re(e_{s_m}E)), truncated at 10^−L. This needs the exact p̃² product.
- **One character witness serves all seven keys** (normalized index k·U = 2U₁). Its pin exp(2iv(0)) = 1 exactly,
  because v is odd: pinHalvings = 0, pinOrder = 1, ε₀ = |E(0) − 1| = 6.0e-88 / 2.9e-87.

**Invariance error rows**, computed exactly (integers, with ℚ(√5) as integer pairs and √5 enclosed to 600 bits),
then weighted-ℓ¹ summed. The ρ = 1/70 strip weights are taken in θ units.

| Row | Content | Lower | Upper |
|---|---|---|---|
| Q1 | p̃ − (ν + D_t v): rounding only | 2.29e-88 | 4.68e-88 |
| Q2 | 0 exactly | 0 | 0 |
| P1 | 2π(‖D_t p̃ + 2εΣA Im(e_m E)‖ + 2εΣ\|A_m\|w^{\|s\|}Δ) | **1.060e-78** | **2.067e-78** |
| P2 | 2π(‖εΣA(2−m)Im(e_m E) + D_t(p̃ + J̃)‖ + εΣ\|A\|\|2−m\|w^{\|s\|}Δ) | 2.94e-79 | 5.11e-79 |
| Energy | \|avg H′(K̃)\| | 3.9e-81 | 7.6e-81 |

These are unscaled; multiply by c.

**Exp-witness error.** Δ ≤ e^{2B}(ε₀ + (½+ρ)(r_ψ + r_φ)), the design's witness theorem with η = 0. The defects
d_jE − 2i(d_j v)E are exact products of about 8k × 8k terms at 636 bits.

| | Lower | Upper |
|---|---|---|
| B | 0.3448 | 0.3448 |
| r_ψ | 1.73e-77 | 3.32e-77 |
| r_φ | 5.4e-79 | 1.42e-78 |
| Δ | 1.82e-77 | 3.55e-77 |

**Cross-check.** At L = 30, R3 equals the SO-GEN reference evaluator (`exact_residual.py`) to 10 digits.
`rot_verify.py` recomputes R3 and R4 from the emitted JSON alone with plain Fractions; they agree with the emitter
to 7 digits (log in `logs/rot_verify.log`).

**Norm enclosures.** All are on T_{1/70} at c = 1, as checker-style models with 72-bit coefficients and tails below
2⁻⁵⁶ moved into the radius. No sampled maxima enter any bound. Lower torus values; upper agrees to 1e-4.

| Quantity | Enclosure | Method |
|---|---|---|
| ‖DK‖ (row sums) | 1.36036 (rows: 1.36036, 1.0, 0.12411, 0.00143) | Weighted ℓ¹ of the exact derivative polynomials. Sampled sup in the study: 1.303. |
| ι₁ | 0.005148 | Mean-value form; ι₂ = 0 |
| ρ_H | 257/10000 | |
| P1 disc | 48769/50000 ± 191/12500 (upper 51231/50000 ± 1529/100000) | |
| P2 disc | 24983/50000 ± 127/20000 | |
| H′ majorant M₁ | **1.047601** (binding term D²H) | Each term is a bound on D with \|sin\|, \|cos\| ≤ cosh(2π(2 + \|2−m\|)ρ_H): ‖DH‖ 1.04312, ‖X_H‖ 1, ‖DX_H‖ 1, ‖D²X_H‖ 0.59817, ‖D²H‖ 1.04760. |
| ‖G⁻¹‖ (row sum) | **1.979943** (checker ℓ¹); alternative 1.834651 | B is a Fourier approximate inverse (345/315/291 terms, 48 bits). Neumann check δ = ‖I − BG‖ = 2.48e-12, β = 1.979942, ‖G⁻¹‖ ≤ β/(1−δ), ‖G⁻¹ − B‖ ≤ 4.9e-12. |
| Torsion inverse ‖avg⁻¹‖ (c = 1) | **1.022493** | Literal `extendedTorsion` entry models through N = Ω₀DK·G⁻¹, DN[ω] and DX_H∘K via the E witness. Average = zero mode ± radius (radii ≤ 5.3e-11). Witness S (2⁻⁴⁰ rationals): δ_T = 5.7e-11 / 8.0e-11. Average ≈ [[1.12148, 0, −0.02462], [0, 0, 1], [−0.02462, 1, 0]]. |

**Package and checks.** All checks are in exact rationals, written to `checks` in the JSON, and all are true:
- M ≥ c·M₁ (1.98625 ≤ 1.987);
- σK − μ ≥ 1.3604;
- σB − μ ≥ 1.97994;
- σT − μ ≥ 1.0225/c;
- 1 < s < σω;
- both ray margins;
- e ≥ c·η and e ≥ c·energy;
- C₁e/(γ⁴ρ⁴) ≤ 1/2.

The binding constraint is σB. The time scale c is chosen so that c·M₁ just fits under the same 𝔪.

## Truncation table (abs threshold 10^−L on v, E, J; η_c/threshold for R1)

| L | bits | v half (lo/up) | E (lo/up) | η_c/thr (lower) | η_c/thr (upper) |
|---|---|---|---|---|---|
| 84 | 304 | 3824/3841 | 7515/7547 | 4.5 | 8.3 |
| 85 | 308 | 3936/3950 | 7705/7752 | 0.52 | 1.05 |
| 86 | 311 | 4030/4046 | 7907/7928 | 6.7e-2 | 0.11 |
| 87 | 314 | 4135/4142 | 8092/8131 | 7.7e-3 | 1.2e-2 |
| **88** | **318** | **4237/4233** | **8307/8322** | **9.4e-4** | **1.8e-3** |
| 90 | 324 | 4438/4426 | 8700/8712 | 1.3e-5 | 2.6e-5 |

- η falls by about 0.9 orders per digit.
- **Minimum feasible:** L = 86 (with e ≈ 2.1·c·η the ratio is about 0.23 ≤ 1/2). L = 88 is the 2-order-headroom
  choice.
- **Under R1grid:** L = 86 has headroom and L = 85 is the minimum.
- **Bits per coefficient:** S = ⌈3.33L⌉ + 24 (318 at L = 88). Rounding enters only through the Q1 row (2e-88) and
  the exact residual.
- **Product pairs** (v full × E) = 70.4M. The study's R1 projection was 67.3M; the emitted 1e-130 data had 357M.
- **Tested with no gain:**
  - An importance-weighted truncation (|c|·λ²·w^{|κ|} and similar) gives the same counts at equal η, within 1 %.
  - Recomputing E = exp(2iv) from the truncated v lowers Δ by about 30 % but leaves η unchanged.
  - Truncating E or J one or two digits looser than v makes η worse (J at L−2 raises the P2 row 100×).
  - So all three share one L.

## Gate G-J (rotated frame: the P2 = p + J row; budgets B₁ and B_r carry the factor c)

| | Lower | Upper | Target | Met |
|---|---|---|---|---|
| B₀ = sup\|ΔJ\| | 1.25e-80 | 2.29e-80 | ≤ e/4 | yes |
| B₁ = sup\|D_{sω*}ΔJ\| | 5.22e-79 | 8.62e-79 | | |
| B_r (≤ sup\|p−1\|·c·η_P1 + sup\|V_q\|·c·η_Q1) | 6.8e-80 | 1.3e-79 | | |
| B_c = c·η_Q1 | 4.3e-88 | 8.9e-88 | | |
| B_r + B₁ + B_c | | | ≤ e/2 | yes |
| q, φ, p rows + B_c | | | ≤ e/2 | yes; this is why e ≈ 2·c·η |
| B₂ = max(sup\|∂ΔJ\|, sup\|∂²ΔJ\|) | 8.1e-75 | 1.6e-74 | ≤ 1e-90 | **no** |

- The direct P2-row enclosure is c·η₄ = 5.6e-79 / 9.7e-79.
- **The B₂ ≤ 1e-90 target cannot be met** at any useful L: B₂ falls about 0.9 orders per digit, so it would need
  L ≈ 105.
  - The target dates from the pilot (e ≈ 1e-103). It is dominated by second derivatives of the dropped J tail and
    of the witness defect, at |κ| ≈ 200.
  - In this package it is not needed: every norm (DK, Gram, torsion) is enclosed on the actual K̃ including J̃.
  - Propose withdrawing it, or restating it as "norms recomputed on K̃".

## Checks run

- `rot_verify.py` on both files: OK. R3/R4 match, the energy bound holds, and all package checks are true (log in
  `certificates/lunar-spin-orbit/logs/rot_verify.log`).
- `exact_constants.py`:
  - pilot output unchanged;
  - R1 at (7/4, 39/20) reproduces the study's −74.509;
  - R1 at (237/125, 1987/1000) gives −74.669;
  - R1grid at (1757/1000, 1841/1000) gives −73.588.
- `sh scripts/lint_sources.sh` exits 1:
  - `check_lean_modules: PASS (1303 Lean files)` and `FROZEN-ANCHOR GUARD OK`;
  - the following ABI step fails with "unknown module prefix 'KAM'", because this worktree has no KAM build and I
    may not build in it;
  - no Lean file is changed (Python and data only).
- No Lean build applies; `#print axioms` does not apply.

## Uncertainties, deviations, suspected errata

1. **Rigor caveats.**
   - Float radii are rounded up after every operation.
   - The bounds on e^x and cosh use libm with a relative 1e-14 guard; 2π in floats uses a 1e-15 guard.
   - The grid alternative uses a 1e-9 guard on its double-precision FFT evaluation.
   - Everything else is exact integers, or intervals from mpmath.
   - All of this is untrusted tooling: the Lean checker recomputes everything.
2. **The study's R1 projection was optimistic for σB** (the ℓ¹ versus sup issue above). This is a deviation from the
   projected 39/20, not an erratum.
3. **Design §6 still describes the θ-frame pilot package** (ρ = 1/200, σ = 4, s = 2, γ = 1/42, D_{T_{1/200}}) and
   B₂ ≤ 1e-90. Revision 5 should take:
   - the rotated K′/H′ and key set (2, 2−m);
   - a single character witness with pinHalvings = 0;
   - package R1 or R1grid;
   - the domain values above;
   - the G-J split, which forces e ≈ 2·c·η.
4. **Diophantine input for the rotated vector.** ω* = c(ν−1, 1)/s with γ = c/(42s). This relies on
   γ((ν−1, 1)) ≥ 1/42, obtained from SO-DIO's (ν/2, 1/2) ∈ Dio(1/42, 1) by the unimodular change k′ = (k₁, k₂ − k₁)
   with |k′|₁ ≤ 2|k|₁. A small Lean transfer lemma is needed; it is not proved here.
5. **The torsion average's T-block is nearly singular** (T₁₁ ≈ 0, T₀₁ ≈ 1e-15). It is invertible only through the
   border. Its inverse bound is solid (δ_T ≈ 6e-11), but the checker's 3×3 witness must be computed in exactly this
   bordered form.
6. **No pinned-source errata suspected.**
