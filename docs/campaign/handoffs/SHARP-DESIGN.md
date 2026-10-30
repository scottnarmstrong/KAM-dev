# Handoff SHARP-DESIGN

30 October 2026. Branch `sharp-design`. `apost-sharp` was merged in at the orchestrator's request (it brought
`KAM.cohomological_parseval`/`_russmann`, `cohConstP`/`cohConstR` and SHARP-BOX).

## Files (all new)

- `blueprint/parts/p2s-sharp.tex`: the sharp fixed-frequency theorem, labels `bp:p2s:*`.
  - Small-divisor data and its three instances (Rüssmann, Parseval, crude).
  - Separate-size constants, absorption, the Neumann ratio, the telescoping product.
  - Frame bounds, geometry, the torsion polynomial identity and the torsion bound.
  - Correction, new error, perturbation through the torsion polynomial, the step.
  - **The abstract Newton engine** (schedule, decay, induction, limit), the fixed scheme, G1♯ and its instances, the
    ρ-uniform remark, the register and the deviations.
  - `blueprint/sharp.tex` is the new top file: the preamble, Parts 0–4 and `p2s`.
- `blueprint-I/parts/p2s-iso-sharp.tex`: the isoenergetic instance, labels `bpI:p2s:*`.
  - Constants, bordered system, correction, new errors, bordered twist through the torsion polynomial, the step.
  - The iso scheme, I-G1♯, the instances, the certificate remark, register and deviations.
  - `blueprint-I/sharp.tex` is the new top file: the preamble, Parts 0–2 and `p2s-iso`.
- `docs/campaign/design/APOST-SHARP-LEAN-DESIGN.md`: the Lean design.
  - Reused declarations with file:line, and the generic copies needed.
  - Modules and their declarations; final theorems; how `checkSmallness` would change.
  - Package split A1–A8; the threshold table; risks.
- `docs/campaign/design/APOST-SHARP-SIGNATURES.lean.txt`: a copy of the probe `.drafts/sharp/Signatures.lean` (1050
  lines, 40 declarations with bodies).
- `scripts/apost_sharp/thresholds.py`: the exact (`fractions`) threshold mirror for package R1, with variants V0–V8,
  instances and sensitivity.

## Approach

1. **Mathematics first.** Re-derived HL19's torsion route in the canonical case:
   - `T = BLᵀ(AΩ₀LB − Ω₀ALB + Ω₀FB) + BΩ_KB(Lᵀ(Aᵀ+A)L − FᵀL − LᵀF)B`, with `F = DE`, from `∂_ωL = AL − DE` and
     `NᵀΩ₀ = BLᵀ`.
   - This bounds `T` without `1/δ`, with its Lagrangian part small through `Ω_K` (loss δ/2). Then `a = 2κ`.
   - The twist change is estimated with the same polynomial at real points, using the errors of both tori: one Cauchy
     loss each, so the loss per step is 3δ.
   - In the iso case it also absorbs the frequency change, so no separate Cauchy estimate in the frequency direction is
     needed.
2. **Choices were made by the numbers** (`thresholds.py`):
   - separate sizes;
   - absorption through `γ ≤ γ̄` (this matters a lot: Θ-absorption made the summed-margin branch dominant);
   - `c_R` without a floor at 1;
   - Neumann ratio 1/8 in the perturbation (0.5 orders better than 1/2);
   - Taylor's M/2;
   - splitting the step smallness into `𝔠_step X ≤ 1` and `2d ≤ β`. This removed a spurious `2/μ` factor and gained
     1.3 orders.
3. **Rüssmann's data are the headline** (orchestrator update): κ = τ, so a = 2τ, as in HL19.
4. **The engine:** an abstract `Scheme n k α` (`tor`, `par`, `Adm r β ε m x`, `step r δ x`) with constants `Consts k`
   (λ, a, C_E, C_Δ, C_p, 𝔠_step, caps, rates, exponents), and the hypotheses (N1), (N2) as `Scheme.IsNewton`.
   - The engine proves the schedule, the decay, the stage induction and the limit.
   - **Fixed instance:** states are tori, k = 3.
   - **Iso instance:** states are (torus, s), k = 4. The ray margin is the fourth rate, and `par = s‖ω*‖` gives (O6).

## Checks and their output

- **Signature probe.** `nice -n 5 lake env lean .drafts/sharp/Signatures.lean` gives 40 diagnostics, all
  `warning: declaration uses 'sorry'`, and no error.
  - The probe imports `KAM.Iso.Apost.G1`.
  - It carries verbatim copies of `KAM.cohConstR` and `KAM.cohConstP`: their modules, merged from `apost-sharp`, are not
    in this worktree's build snapshot, and the brief allows no build. They only appear as constants in statements.
- **LaTeX.** `latexmk -pdf blueprint/sharp.tex` and `blueprint-I/sharp.tex`: both exit 0, with no undefined reference.
  - The only warnings are overfull hboxes, as in the existing parts.
- **Thresholds.** `python3 -I scripts/apost_sharp/thresholds.py`: V0 reproduces −74.51 (iso, R1), as in
  CONSTANTS-STUDY and `scripts/spin_orbit/exact_constants.py`. Design results:

  | Theorem | log₁₀ threshold, iso | log₁₀ threshold, fixed |
  |---|---:|---:|
  | Current | −74.51 | −76.55 |
  | Rüssmann | **−24.98** | −24.71 |
  | Parseval | −36.99 | −36.73 |
  | Crude | −49.09 | −48.85 |

  The target was about 10⁻⁴⁰.
- **Lint.** `sh scripts/lint_sources.sh`: `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`. The ABI-scratch step
  fails with the known `KAM/Frozen/Iso/Defs/BorderedHessian.olean ... does not exist` (missing from the snapshot,
  unrelated; the same as SHARP-BOX and SHARP-RUSSMANN-COH).
- **Axioms.** No Lean result was proved (design only), so there is no `#print axioms` to report.

## Uncertainties

- **`torsion_identity` (Lean)** needs the Fréchet derivative of `θ ↦ (gramMatrix K θ)⁻¹`. The repo has only its
  differentiability; Mathlib's `hasFDerivAt_ring_inverse`, or differentiating `B G = 1`, should do it. This is the
  main new analytic Lean ingredient.
- **The iso identity helpers** `sumVec_error_eq`, `energyAverage_sub_eq` and `sMat_bounds` carry hypotheses in the old
  constants. They need copies with pointwise hypotheses (listed in the design §2.2). Their proofs should transfer
  verbatim, but this is not checked.
- **Line estimates** (about 6.6k in total, design §3) are engineering estimates.
  - `perturbation_poly` is the largest proof.
  - The `max` chains in `ConstantsArith` are the elaboration risk under the no-heartbeat rule.
- **The Parseval lemma** (`bp:p2s:cohdata-parseval`) gives its lattice step through the package's bound
  `(8n/(πδ))ⁿ`. I did not re-read the package proof line by line. The statement is that of
  `KAM.cohomological_parseval` with `κ = τ + n/2`.
- **The step constants now depend on γ̄** (deviation S5). This is allowed:
  - the frozen G1 and I-G1 choose `C₁, C₂ (, C₃)` after `γ̄`;
  - so the sharp theorems would also serve as providers of the frozen statements, though that is not proposed here.

## Suspected errata and deviations

- **Errata of HL19:** none new. The PDF is not on this machine; the citations reuse those already checked in Part 2.
  The errata E1–E5 of the track-I blueprint stand.
- **Defects in the existing blueprint or Lean:** none found. Remark `bp:p2:torsion-route` is the deliberate choice
  revisited here.
- **Deviations** (blueprint `bp:p2s:deviations` S1–S7, `bpI:p2s:register` W1♯–W4♯):
  - general small-divisor data, with δ ≤ 1 in the definition;
  - the torsion route, its Lagrangian part through `Ω_K` with loss δ/2 (our choice);
  - twist perturbation at real points only, 3δ per step, `δ₀ = min{1, (ρ−ρ∞)/6}`;
  - separate sizes with factor 2n and `|Aᵀ| = |A|`;
  - absorption via γ̄ (the constants depend on γ̄);
  - Neumann ratio 1/8, Taylor M/2, split step smallness;
  - margin budgets μ/2 (μ/4 for the ball);
  - iso: the frequency change carried by `DĒ_ω̄`, the energy row through `Y = ωᵀ − (ηᴸ)ᵀ`, `|∂_ωP| ≤ C_P` without
    `1/δ`, and the ray margin as an engine rate.

## What remains

- **Design:** nothing. Both forms are designed: the blueprint, exact signatures, the package split and the numbers.
- **Next:** the Lean packages A1–A7 (design §5), then SHARP-CERT, a second `checkSmallness` with rational mirrors of
  `sharpIsoC1/2/3` (design §4).
