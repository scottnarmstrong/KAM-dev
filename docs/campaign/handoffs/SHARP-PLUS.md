# Handoff SHARP-PLUS: the least crude explicit a-posteriori KAM theorem (v2 design)

30 October 2026. Branch `sharp-plus`. No Lean proof, no Lean module added, no tracked file outside my new files modified
(`thresholds.py`, the v1 blueprints and design doc are untouched). Main document: `docs/campaign/design/APOST-SHARP-V2.md`.

## Files (new)

| File | Content |
|---|---|
| `docs/campaign/design/APOST-SHARP-V2.md` | benchmark, competitors, loss inventory L1–L9, v2 design, dominance, thresholds, honest comparison, errata |
| `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt` | copy of the probe `.drafts/sharp2/Signatures.lean` (612 lines, elaborates) |
| `blueprint/parts/p2s2-smalldiv.tex` | small-divisor constants at a bite: full-strip Bessel, ordered divisors, Abel, classical and frequency-specific constants, Rüssmann–Cauchy, full-bite averages |
| `blueprint/parts/p2s2-modified.tex` | refined data, geometry from ηᴺ, the modified step (all constants), stage engine, route A deltas, G1♯♯, frozen form, hybrid, register, errata |
| `blueprint-I/parts/p2s2-iso-modified.tex` | the bordered modified step, I-G1♯♯ concluding `IG1Body` |
| `blueprint/sharp2.tex`, `blueprint-I/sharp2.tex` | top files |
| `scripts/apost_sharp/r1_norms.py` | measured R1 norms (\|X_h\|, \|DX_h\|, \|D²X_h\|, \|Lᵀ\|, \|N\|, \|Nᵀ\|, sup\|T\|, ⟨T⟩) |
| `scripts/apost_sharp/smalldiv.py` | c_v1, the classical constant c♮, frequency-specific c(δ), the ℓ¹ constant Γ_∞ (L9) |
| `scripts/apost_sharp/benchmark_hl19.py` | HL19 Thm 3.1/3.6 on R1, every constant cited by equation number |
| `scripts/apost_sharp/benchmark_fh24.py` | FH24 Thm 2.18 on R1 (helper-written, cross-checked), erratum switch |
| `scripts/apost_sharp/h50_package.py` | the harder package H50 (ν = 1 − 1/(50+g)), torus solver and norms (helper-written) |
| `scripts/apost_sharp/step0_actual.py` | measured step-0 objects of the R1 candidate (helper-written) |
| `scripts/apost_sharp/thresholds_v2.py` | v2 mirror: route A (v1 + levers), route B (modified step), engine, hybrid, cumulative tables R1/H50 |
| `scripts/apost_sharp/dominance.py` | 108-point grid vs HL19 and FH24 (printed/corrected); `--plasmalean`; `--fh25` |

Downloaded papers (untrusted, not committed): `/home/scott/kam-tools/papers/{hl19-1711.05515, fhl17-1601.00084,
fhl18-1703.06809, villanueva17-param, villanueva-maps, fh24-2304.10205, fh25-2403.10152, …}`.

## Approach

1. **Benchmark (task 1).**
   - HL19 and FH24 were transcribed exactly and evaluated on R1 with identical inputs: the same c_R, two margin readings, and their
     free parameters optimised.
   - v1 beats HL19 on v1's data (−24.7 vs −29.5). HL19 wins on finer data (−23.5). FH24 is far ahead of both: −19.6 on v1's data
     and −14.7 on finer data.
2. **Competitors and L5.**
   - Literature search (two helper agents; §2 of the design doc).
   - FH24 is the decisive competitor: an explicit flow theorem with the γ²-structure, obtained by a composition (tangential)
     correction.
3. **Measurements.**
   - R1 norms and the frequency-specific small-divisor sums: c(δ_s) ≈ 0.0030 for every bite.
   - The H50 torus.
   - The actual step-0 objects of the R1 candidate: its new error is 10⁻²⁷ of the derived bound.
4. **v2 = route B (FH24's modified step) plus levers, with route A (v1 + levers) as a second disjunct.** The levers:
   - L1 refined data, including c_Th;
   - L2 small divisors (full-strip, classical 0.0814, frequency-specific per bite);
   - L3 δ powers kept, and the anisotropic stage-0 weight (ours);
   - L8 free budgets and caps for barred factors;
   - L6 hybrid corollary.

   The stage engine has an exact prefix and a δ-restricted tail. The frozen form takes C₁ = min{C₁^♯, C₁^B}, so v2 is never worse
   than v1.
5. **Owner directives.**
   - Dominance grid (§5).
   - Harvested tricks: FH24's composition step, Ω_K from ηᴺ, E recovered from η, averages at the full bite; FHL17's full-strip
     Bessel and ordered divisors.
   - PlasmaLean and FH25 benchmarks (§5, §10 of the design doc).

## Checks and their output

- `python3 -I scripts/apost_sharp/thresholds_v2.py`: A0 reproduces v1 exactly. Results (R1 / H50):

  | Variant | R1 fixed | R1 iso | H50 iso |
  |---|---:|---:|---:|
  | v1 (A0) | −24.72 | −24.98 | −27.37 |
  | route A | −11.18 | −11.37 | −12.44 |
  | route B | −12.25 | −12.39 | −13.17 |
  | hybrid | about −4.4 to −5.0 (R1) | | |

- `python3 -I scripts/apost_sharp/benchmark_hl19.py`: HL19 −29.46 (v1 data); −23.49 / −23.74 (finer data, fixed / iso).
- `python3 -I scripts/apost_sharp/benchmark_fh24.py`: FH24 −19.62 (v1 data), −15.38 (finer, c_R = 0.316), −14.58 (finer, 0.0814).
- `python3 -I scripts/apost_sharp/dominance.py` (273 s): 108 points, **0** wins for HL19 or corrected FH24 (minimum margin
  +0.03, median +0.61); printed FH24 leads at 48 points by ≤ 0.87 orders, all from its erratum (3.72).
- `dominance.py --fh25`: on Figueras–Haro 2025's Sun–Jupiter–Saturn data, v2 route B is −5.98 (δ = ρ/6) / −5.56 (prefix ratio 4)
  relative to their claimed (10⁻³⁸, 10⁻⁴⁴). FH24's own closed form gives −6.18 / −5.53 there. Neither reproduces their numerical
  closure (§10 of the design doc).
- `dominance.py --plasmalean`: see §10 of the design doc (result recorded there).
- `nice -n 5 lake env lean .drafts/sharp2/Signatures.lean`: 12 warnings "declaration uses `sorry`", no error (built
  `KAM.Iso.Sharp.Constants` once, niced, for `sharpIsoC1`).
- `latexmk -pdf` on `blueprint/sharp2.tex` and `blueprint-I/sharp2.tex`: exit 0, no undefined reference (PDFs not committed).
- `sh scripts/lint_sources.sh`: `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`. The only items are pre-existing: two long
  lines in `KAM/Sharp/TorsionBound.lean:25`, `TorsionPoly.lean:25`, and the known ABI-scratch missing `.olean`.

## Axioms

No Lean result was proved. `c1V2_le_sharpC1` is proved in the probe by `min_le_left`, and the probe is not a module.

## Uncertainties

- **The numbers are design mirrors.**
  - Measured norms are sampled sups (×1.05).
  - The H50 torus is double-precision.
  - Route B's constants are my derivation following FH24 (Definition `bp:p2s2:constantsB`), not yet proved in Lean.
  - The blueprint proofs of the modified step are complete in structure but compressed. The iso modified step is new mathematics
    (no source) and needs an independent audit before any package is assigned.
- **The hybrid threshold (−4.5) is candidate-specific:** high-frequency truncation residual. Its certificate cost is SHARP-CERTSIDE's
  estimate.
- **Dominance is numerical** (grid + packages). The analytic term-by-term argument holds only where v2's constants are FH24's with
  smaller inputs; norm conventions differ (FH24 use entrywise sups).
- **L9 (ℓ¹ Newton) is quantified as an estimate only** (constant swap and the ℓ¹/sup penalty on E). It is not designed in the
  blueprint.

## Suspected errata (for `docs/errata/ledger.json`)

Full table: design doc §8.
- **FH24.**
  - Lemma 2.14: the printed ĉ_R is twice its route's constant.
  - Table 3 (3.72): σ_L and C_ΔL̄̄ are printed where σ_Lᵀ and C_ΔL̄̄ᵀ are needed (an underestimate).
  - (3.10): typo "C_E" for C_{Eᵀ}.
  - p. 19: "Corollary 2.14" for 2.16.
- **HL19.**
  - (3.16) vs (6.51): γ²ρ^{2τ} vs γρ^τ for the frequency closeness.
  - §5.3: constants at "the worst δ₀" while Lemma 4.1 allows c_R(δ).
- **FHL17.** The same δ₀ gap (p. 16); "6 orders" at τ = 1 (p. 37).
- **dLGJV 2005.** Thms 3, 6: γ^{+2} for γ⁻².
- **`docs/explorations/lunar-band-2p8-2p9.md`.** Items 1 and 3: the binding mode in the rotated frame; the Gram inverse grows 41 %
  at N = 50.
- **FH25.** The claimed numerical closure at (10⁻³⁸, 10⁻⁴⁴) is not reproduced by FH24's own closed-form constants on the published
  data (twist-margin entry, 10^5.5 short). Unreported constants (c_Th, c_DTh) or larger margins must be involved. Not an erratum
  claim; a reproducibility note.

**Deviations introduced.** See Remarks `bp:p2s2sd:errata`, `bp:p2s2:register`, `bpI:p2s2:dev`:
- small-divisor constants per bite;
- the frozen torsion in the modified step (E^{LN}_red = 0);
- caps for the intermediate frame;
- the anisotropic weight;
- the stage engine;
- the isoenergetic modified step.

## What remains

- **Lean.** Packages B1–B8 (about 5.8k lines) and the optional B9; split and order in design doc §4.5.
- **Audit.** An independent audit of `p2s2-modified.tex` and `p2s2-iso-modified.tex` (especially the composition step and the iso
  identities) before assignment.
- **SHARP-CERTSIDE.**
  - Certify (R1)–(R4) (and (R5) for the hybrid).
  - Rational mirrors of `stepConsts`.
  - A certified X⋆.
- **L9.** If the ℓ¹ estimate pays (PlasmaLean section), design an ℓ¹/sup hybrid: ℓ¹ for the cohomological step and the error, with
  sup conclusions. Its Lean cost is a parallel norm layer, about 2k lines.
