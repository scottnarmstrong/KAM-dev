# Handoff SHARP2-FIX: v2 repaired after the two design audits; fair dominance restored

30 October 2026, branch `sharp-fix`.
- Base: `sharp-v2` at 148f9c79, then `sharp-v2` merged three times: B1/B2, then B9, then B10D. The B10D merge had conflicts in
  `thresholds_v2.py`, `dominance.py`; both sides were kept.
- No Lean module was added or edited. The Lean work is a signature probe in `.drafts`.
- Main documents:
  - `docs/campaign/design/APOST-SHARP-V2.md` §11 (dispositions, corrected tables, fair dominance, rechecks);
  - `docs/campaign/design/APOST-SHARP-V2-DELTA.md` (per-package signature deltas to relay).

## Outcome
- **Every audit finding is repaired** (fixed F1–F9, iso F1–F8), as are the B2, B3, B5, B9 and B10D signals. One-line dispositions are
  in design §11.1. The table below summarises them.
- **Structural repair of F8.**
  - The torsion is compared with the *initial* torus. Only the frame part 𝒯_ab is telescoped; 𝒯_F + 𝒯_c is bounded at each stage
    by its own data.
  - No new-torus estimate or next-bite certificate is needed, and the local contraction premise becomes unnecessary (dropped
    everywhere).
  - The repair costs nothing on R1 and H50; it gains up to 0.26 orders on route B's intermediate rows and 0.47 on route A (L8′).
- **Fair dominance.**
  - Every competitor gets c♮ at its own bites, optimised free parameters and corrected errata.
  - Under that fair data, v2 *as designed before* loses to corrected FH24 at 53 of the 108 old grid points (worst −0.47 orders).
  - Diagnosis: v2 lacked three of FH24's free parameters (schedule ratio a, optimal Rüssmann–Cauchy split, decay bound κ), and one
    lever of our own (L10) was still missing.
  - With the four levers v2 wins **all 720 points** of the extended grid (n ≤ 6, τ ≤ 5, γ ∈ [10⁻⁶, 10⁻¹], ρ ∈ [10⁻³, 0.3], sizes
    1–30). Minimum margin **+0.80**, median **+3.36** orders.
- **L10 (ours): the self-consistent tangential error.** The term (N̄−N)ᵀΩ₀Ē dominates FH24's (3.86) and the old v2 constant; it was
  bounded with the crude linear |Ē| ≤ C_Ē·μ.
  - The recovery lemma applied to the new torus, with its Lagrangian defect obtained as a pullback (Ω_{K̃∘φ} = Dφᵀ(Ω_K̃∘φ)Dφ, no
    new certificate), makes that term cubic.
  - It is worth +3.7 orders at size-10 grid points.
- **PlasmaLean target**: its tolerance is 10^{−18.24}.
  - v2 route A: 10^{−17.27} as proved by B9 (+0.97), 10^{−17.02} with L8′ (+1.22).
  - B10's ℓ¹ entry step: up to 10^{−15.20} (+3.04).

## Findings table (dispositions; full text in design §11.1)

| Finding | Disposition |
|---|---|
| F1 `g1_v2` counterexample | fixed: `NumB.Wf`, `StepInB.Ok`, `InitB.Wf`, `check_data` |
| F2 oscillating engine | fixed: `converge_checked` adopted; `converge_ratio` keeps hnn, hcondT, hball; J1t, strict J4 |
| F3 certificates, caps, quantifiers | fixed: `NumB.Cert γ Ω` inside the body (ω ∈ Ω), J3 over 7 caps with initial values, literal `G1Body` wrappers |
| F4 h periodic/real, κ, n | fixed: standing hypotheses in `modified_stepB`, `p.Ok` |
| F5 route A recursion | fixed: engine with ratio a and exponent p; route A = B9's `SchemeA` (2^{4κ}) |
| F6 closeness γ̄² | fixed: `c2B` without γ̄², min/max by cases |
| F7 unfair dominance | fixed: `dominance.py` rewritten; 720 points, 0 wins, min +0.80 |
| F8 new-torus torsion, contraction | fixed: torsion against the initial torus (`bp:p2s2:torsion-local`, `-ref`); contraction premise dropped |
| F9 tail averages | fixed: certified c̄_∞ at every full bite r_j ≤ r_k with (δ_k/min(r_k,1))^κ |
| iso F1 prefix constants unbound | fixed: `NumB.Cert`, `SDConst.of_le_gamma` |
| iso F2 J3 incomplete, kp = 0 | fixed: 7 caps, `kp_pos`, tail weights 1 |
| iso F3 closeness γ̄² | fixed: `c2B`, `c3B` |
| iso F4 weights > 1 | fixed: clipped p = max{σ_Nᵀ, σ_Lᵀ/(γδ₀^κ), 1}; `NumB.Fits` |
| iso F5 moving-frequency factors | fixed: condition C₀g₁X ≤ ϑ_ω, factor a_ω in C_Ē, Q′_L, Q̄_N |
| iso F6 / fixed hybrid | labelled heuristic extrapolation assuming certified first-step transfer |
| iso F7 "0.2 orders" | fixed: measured fair margin |
| iso F8 sign | fixed: ∂_ωΩ_K = −(Dηᴺ − (Dηᴺ)ᵀ) |
| B3 iso Q̄_N not monotone | option (b): polynomial Q̄_N; `stepConstsB_mono` covers iso |
| B5 `converge` false | `converge_checked` adopted |
| B2 Lagrange lemma unprovable | `norm_lagrangeMat_le_etaN_of_standing` adopted |
| B9 c(min(r,1)) with (δ/r)^κ | fixed: full bite min(r,1) in constant and factor |
| B10D flags | contraction: intentional (F8); c_Th, c_DTh: in `StepInB`, `RefHypB` |
| own bugs | `c_stages` tail index (k = 6 vs 5); route B's Q and tail factors for ratios ≠ 2 (old FH25 "ratio 3/4") |

## Corrected tables (log₁₀ of the largest admissible e; old → new)

| Package | Variant | Fixed | Iso |
|---|---|---|---|
| R1 | v1 | −24.72 → −24.72 | −24.98 → −24.98 |
| R1 | route A as proved (B9) | −11.18 → −11.18 | −11.37 → −11.37 |
| R1 | route A + L8′ | — → **−10.71** | — → **−10.95** |
| R1 | route B (B6) | −12.25 → **−12.25** | −12.39 → **−12.33** |
| R1 | route B B7 (new levers) | — → −12.24 | — → −12.31 |
| R1 | hybrid A / B (heuristic extrapolation assuming certified first-step transfer) | −4.42 / −4.97 → −4.18 / −4.96 | −4.52 / −5.04 → −4.42 / −5.00 |
| H50 | v1 | −27.19 | −27.37 |
| H50 | route A as proved / + L8′ | −12.29 / −11.73 | −12.44 / −11.90 |
| H50 | route B (B6) | −13.05 → −13.05 | −13.17 → −13.12 |

The intermediate route-B rows (B0–B5) are in design §11.2.

## Fair dominance (design §11.3)

| Grid | Points | Corrected-competitor wins | Min margin | Median |
|---|---:|---:|---:|---:|
| extended (with the levers) | 720 | **0** | **+0.80** | +3.36 |
| old 108 (with the levers) | 108 | 0 | +0.84 | +1.95 |
| old 108, ablation (no ratio, split 1/2, ȳ = 1/2, no L10) | 108 | **53** | −0.47 | +0.07 |

- The worst points are (2,1), size 1, ρ = 0.3 (+0.80, independent of γ). Route B is chosen at every point.
- No region was found that cannot be won.
- Not covered: n > 6, τ > 5, ρ > 0.3, and closeness constants (thresholds only).

**FH25** (corrected factors): the admissible scale of (10⁻³⁸, 10⁻⁴⁴) is 10^{−6.20} with FH24's weight, 10^{−5.95} anisotropic,
and 10^{−5.53} at ratio 4. FH24's closed form gives −6.18 / −5.53. Neither closes FH25's claim; this remains a reproducibility note.

## Files

| File | Change |
|---|---|
| `blueprint/parts/p2s2-modified.tex` | rewritten (labels kept). New: Definition `bp:p2s2:data-ok`; Lemmas `bp:p2s2:torsion-local`, `bp:p2s2:torsion-ref`; option L10 (`step:p2s2:selfcons`); engine with a, p, ȳ, (J0)–(J4); route A (L8′); theorem with clipped weights and caps list; frozen form by cases without γ̄²; register |
| `blueprint/parts/p2s2-smalldiv.tex` | real-points clause; `bp:p2s2sd:gamma-mono`; optimal split; `bp:p2s2sd:avg-tail`; FH24/HL19 wording |
| `blueprint-I/parts/p2s2-iso-modified.tex` | constants (a_ω, polynomial Q̄_N, bordered torsion maxima), step proof, clipped weights, frozen form without γ̄² |
| `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt` | replaced (copy of `.drafts/sharp2fix/Signatures.lean`, 818 lines) |
| `docs/campaign/design/APOST-SHARP-V2-DELTA.md` | new: per-package deltas |
| `docs/campaign/design/APOST-SHARP-V2.md` | superseding notes (§0, §5), new §11 |
| `scripts/apost_sharp/thresholds_v2.py` | route B (`stageB`, `engine_B`, `thresholdB`); route A torsion and engine; data check; B7 row; full-bite fix; `c_stages` fix; B10D merged |
| `scripts/apost_sharp/dominance.py` | fair grid (`best_fh24_fair`, `best_hl19_fair`, v2 parameter search, `--grid ext`, `--jobs`, `--point`, `--ablate`); PlasmaLean tail and L10 choice; B10D merged |
| `scripts/apost_sharp/benchmark_fh24.py` | optional input `cRrho` (default unchanged), needed to give FH24 a legal c_R(ρ) |

Route B in `thresholds_v2.py`:
- torsion against the initial torus (`Tab`, `B_loc`, `torsion_budget`);
- iso a_ω and polynomial Q̄_N;
- L10 (`selfcons`);
- schedule ratio in Q and the tail;
- decay bound `ymax`;
- optimal split;
- certified tail average;
- conditions with powers.

## Checks and their output
- `python3 -I scripts/apost_sharp/thresholds_v2.py --json …`: exit 0; table above (log in the design doc §11.2).
- `python3 -I scripts/apost_sharp/dominance.py --grid ext --jobs 6 --json …`: exit 0, 638 s, "points 720 (skipped 0),
  corrected-competitor wins: 0, printed-FH24 wins: 0"; "min 0.796, median 3.364, max 5.427".
- `… dominance.py --grid old --ablate --jobs 4`: exit 0, 56 s, "corrected-competitor wins: 53 … min −0.468".
- `… dominance.py --point 4 3 1/1000 1/10 10` (the audit's F7 point): v2 −44.07, corrected FH24 (fair) −47.85, margin +3.78.
- `… dominance.py --plasmalean`, `--fh25`: exit 0; numbers above.
- `nice -n 5 lake env lean .drafts/sharp2fix/Signatures.lean`: exit 0, 17 "declaration uses `sorry`", no error.
  - Built first (niced, sequentially): `KAM.Sharp2.Engine`, `ModConstantsMono`, `Data`, `Geometry`, `SmallDiv.Instances`,
    `KAM.Sharp2.RouteA.Frozen`, `KAM.Iso.Sharp2.RouteA.Frozen`, all successful.
- `latexmk -pdf` on `blueprint/sharp2.tex` and `blueprint-I/sharp2.tex` (out-of-tree): exit 0, no undefined reference, no error.
- `sh scripts/lint_sources.sh`: exit 1. `check_lean_modules: PASS (1526 Lean files)`, `FROZEN-ANCHOR GUARD OK`. The rest is
  pre-existing: the known ABI-scratch missing `FixedSunPlanetaryKAM.olean`, and long lines in merged B2/B3 files.

## Axioms
No Lean result was proved. Every new declaration in the probe has a `sorry` body; the probe is not a module.

## Uncertainties
- **L10 is new mathematics** (no source). The derivation in `step:p2s2:selfcons` was re-checked step by step:
  - the recovery lemma is pointwise algebra;
  - K̄'s frames are within the caps by the step's room hypothesis;
  - the pullback identity holds since D(K̃∘φ) = (DK̃∘φ)Dφ;
  - A = sup|η̄ᴸ| is finite.

  It needs the fresh audit. It is the source of the large margins.
- **The torsion against the initial torus** (`bp:p2s2:torsion-ref`) changes the admissibility predicate of the scheme. The state
  carries the reference ⟨T₀⟩ and the 𝒯_ab drift. The concrete `StageScheme` instance (B6) must be written that way.
- **Floating point.** The fair grid and the B7 rows evaluate route B in floating point; the route-B search uses a finite set of free
  parameters. The competitors' searches are grids (not proved optimal).
- **The comparison is a parameter study** with assigned inverse-twist numbers. FH24's torsion is not the frozen torsion, and
  closeness constants were not compared.
- The iso bordered modified step has no separate Lean signature in the probe. Its constants are the `StepInB` iso fields, and its
  frozen consumer is `iso_g1_v2B_frozen`.
- The route-A improvement L8′ is a proposal; B9's proved route A stands as is.

## Suspected errata (for `docs/errata/ledger.json`)
- No new pinned-source erratum.
- Wording qualifications requested by the audit, now in the blueprint:
  - FH24 Lemma 2.14: the printed ĉ_R is "twice the δ → 0 leading coefficient" of its own route; the halved value is not claimed as
    uniform.
  - HL19 §5.3: a bite-dependent c_R(δ) "may fail to be bounded by its value at δ₀"; use a proved uniform bound or stage-specific
    constants.
- FH25 stays a reproducibility note.
- Repairs of our own blueprint are not errata. Our own script bugs (the `c_stages` index; the ratio factors) are listed under the
  findings above.

## Deviations introduced
- The torsion against the initial torus.
- Option L10.
- The free schedule ratio and decay bound (as FH24).
- The split bite τ/(τ+1)·δ_s.
- The certified tail full-bite constant.
- The iso ratio ϑ_ω.
- Route B's literal wrappers require c_Th ≥ 2M and c_DTh ≥ 2M (implied by the frozen |DX_h|, |D²X_h| ≤ M).

All are recorded in the blueprint register `bp:p2s2:register` and `bpI:p2s2:dev`.
