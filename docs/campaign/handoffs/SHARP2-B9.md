# SHARP2-B9 handoff: route A of the v2 sharp a-posteriori theorem

Branch `sharp-b9`, from `sharp-v2` (b52d6b71), with `sharp-b1` merged twice (the only merge used; `sharp-b3` was
not needed). No file outside my new ones was edited, except `KAM.lean` (generated).

## Status

Route A is proved at fixed frequency and in the isoenergetic form, in the refined form and in the literal frozen
form. Axioms: `propext, Classical.choice, Quot.sound` for every target. **Read "Needs a decision" first**: the
statements below have had no independent audit.

| Result | Declaration | File |
|---|---|---|
| Additive step, fixed frequency | `KAM.Sharp2.RouteA.step_A` | `KAM/Sharp2/RouteA/Step.lean` |
| Stage engine, normalisation of F5 | `SchemeA.run`, `SchemeA.limit` | `KAM/Sharp2/RouteA/Engine.lean` |
| `bp:p2s2:g1`, route A | `g1_core_A`, `g1_branch_A` | `KAM/Sharp2/RouteA/G1.lean` |
| `bp:p2s2:frozen-form`, route A | `g1_v2A` (refined), `g1_v2A_frozen` (literal `G1Body`) | `G1.lean`, `Frozen.lean` |
| Bordered additive step | `KAM.Iso.Sharp2.RouteA.step_IA` | `KAM/Iso/Sharp2/RouteA/Step.lean` |
| `bpI:p2s2:g1`, route A | `iso_g1_core_A`, `iso_g1_branch_A` | `KAM/Iso/Sharp2/RouteA/G1.lean` |
| `bpI:p2s2:frozen`, route A | `iso_g1_v2A` (refined), `iso_g1_v2A_frozen` (literal `IG1Body`) | `G1.lean`, `Frozen.lean` |
| Certificates | `NumA.cert_classical`, `NumA.cert_freq` | `KAM/Sharp2/RouteA/Frozen.lean` |

## Needs a decision

1. **The signature file has no route-A declaration.** `APOST-SHARP-V2-SIGNATURES.lean.txt` lists route B only, so
   there was nothing to copy verbatim. I wrote the statements from `bp:p2s2:constantsA`, `bp:p2s2:g1`, the function
   `stageA` and the findings of the two audits. They need the audit the verbatim signatures would otherwise have had.
   The names are mine; `routeAOk` follows `routeBOk`.
2. **Lint exits 1**, for two reasons. One is the accepted ABI-scratch failure. The other is not covered by the brief:
   `KAM.lean` is over 1500 lines. It was already 1501 at the base commit and is generated; it is now 1528 (my 19
   imports, 8 from B1). Someone must split the root or exempt it.
3. **Overlaps with B2 and B5**, whose branches I could not merge. Each is a deliberate duplicate, for the integrator:
   - `RefHypA`, `InitA` against B2's `RefData`, `RefHyp`. Mine carry initial values and the torsion bound, as F3 asks.
   - `norm_lagrangeMat_le` against B2's `norm_lagrangeMat_le_etaN`: same identity, different bite pattern.
   - `SchemeA` against B5's `StageScheme`. F5 allows separate engines.

## What the numbers do and do not show

`scripts/apost_sharp/route_a_lean_mirror.py` evaluates `routeAOk`/`routeAOkI` from the Lean definitions, in double
precision. It is untrusted design tooling that I transcribed by hand: nothing links it mechanically to Lean.

| Package | Design (`thresholdA`) | Lean `routeAOk` |
|---|---:|---:|
| R1 fixed | -11.18 | -11.18 |
| R1 iso | -11.37 | -11.37 |
| H50 fixed | -12.29 | -12.29 |
| H50 iso | -12.44 | -12.44 |
| PlasmaLean cA-like norms, frequency-specific | -17.27 | -17.27 |
| PlasmaLean R1-like norms, frequency-specific | -13.87 | -13.87 |

Default data, no refined hypothesis, classical constants (`g1_v2A_frozen`, `iso_g1_v2A_frozen`): R1 -21.07 fixed,
-21.09 iso, against v1's -24.72 and -24.98. `TorsionOk` does not bind (it allows about -10.5).

**PlasmaLean.** The +0.97 margin over its -18.24 holds for these numbers only:
- no Lean statement mentions PlasmaLean, and the theorem is not applied to its field, which has a non-canonical area
  form and no closed-form canonical chart (design §10.1);
- the norms are the design's guesses ("cA-like"), and transposes use the conservative defaults;
- the frequency-specific constant is a floating-point value, not a certified `sdFinite` bound.

What Lean does prove is the wiring: the third example of `.drafts/b9_sig.lean` runs refined data and `NumA.cert_freq`
through `g1_v2A`. With only the classical constant the design number stays at -20.01, which is -1.77 behind.

The constants have no Lean-level cross-check against `stageA` of the kind B3 did: the table above is the only
comparison.

## Approach

- `NumA` (numbers), `RefHypA` (object bounds with initial values), `NumA.Cert` (Fourier certificates) are separate
  packages, as F3 asks; certificates are bound to a set `Ω ∋ ω`.
- `StepInA.δ` is the value of the bite in the constants and the actual bite is any `δ ≤ p.δ`, so one record covers a
  prefix stage or the whole tail without a monotonicity proof.
- The engine uses `x_s = ε_s/(γ⁴δ_s^{2a})`, recurrence `2^{4κ} C_E,s` (F5); `RunData` has the tail conditions at
  entry and downward closure (F2). All eight caps, nine in the iso form, are in (J3) with initial values (F3).
- The barred frame uses caps (L8); `torsion_sub_le` takes two frequencies and serves both forms. No small-divisor
  constant at a later bite enters, so F8 of the fixed audit does not reach route A.
- Closeness is proportional to `e` by `xA_scale`, `sumA_scale`. `c2A = ρ^{2τ} S/(X⋆ δ₀^{4τ})`, with `S` at `γ̄ = 1`:
  no `γ̄²`, as F6 requires.
- `g1_v2A_frozen` splits on the branch of the minimum itself, since the initial torsion bound needs route A's
  smallness and cannot be built in the v1 branch.

## Checks

- `nice -n 5 lake build KAM.Sharp2.RouteA.Frozen KAM.Iso.Sharp2.RouteA.Frozen`: `Build completed successfully (3345
  jobs)`. `lake build KAM` was not run: forbidden in this side campaign. The modules are in `KAM.lean`.
- `python3 -I scripts/gen_root_imports.py`: run, `KAM.lean` committed.
- `sh scripts/lint_sources.sh`: exit 1, see item 2. Otherwise no forbidden construct, no line over 100 characters in
  my files, `check_lean_modules: PASS (1514 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`.
- No heartbeat or recursion override. One default-heartbeat timeout (`triple_sub_le`) was fixed by restructuring.
- Largest file: 642+ lines (`Engine.lean`), under the 800 limit. About 5.3k lines in 19 files.
- Signature check: `.drafts/b9_sig.lean` closes `∃ C₁ C₂, … G1Body …` and `∃ C₁ C₂ C₃, … IG1Body …`, stated
  independently of my theorems' names, and the end-to-end example. No errors.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]` for `g1_core_A`, `g1_v2A`, `g1_branch_A`,
  `g1_v2A_frozen`, `step_A`, `SchemeA.run`, `SchemeA.limit`, `norm_lagrangeMat_le`, `iso_g1_core_A`, `iso_g1_v2A`,
  `iso_g1_branch_A`, `iso_g1_v2A_frozen`, `step_IA`, `iso_energy_limit_A`, `NumA.cert_classical`, `NumA.cert_freq`,
  `torsion_default`, `sdConst_mono`.

## Deviations

- (R3) is optional in the blueprint and required in `RefHypA`: route A has no derived-torsion branch at stage constants.
  The default wrappers derive it, under `TorsionOk`.
- The tail keeps `δ_kp` in the constants; `stageA` absorbs it into `γ̄`. This can only help.
- The cap of `|DK|` is `σ_K - μ/2`, where `stageA` uses `σ_K`. This can only help.
- `iso_energy_limit_A` applies `tendsto_energyAverage_of_uniform` from a late iterate: that lemma needs closeness
  `≤ μ/4`, and route A spends the free ball budget `μ/2`.
- `cert_classical` assumes `ρ ≤ 1`, because `sdConst_classical` needs a bite `≤ 1`.
- `ϑ` is a free input; `q_S = 1/2` and `η = 1` are fixed, as in the mirror's route-A rows.

## Suspected errata and defects

Our own material, no pinned-source erratum is new here.
- `blueprint/parts/p2s2-modified.tex:69,79` (`bp:p2s2:omega`): "`\partial_\omega\Omega_K=D\eta^N-(D\eta^N)^\top`".
  With `(Dη)_{ij} = ∂_jη_i`, the sign is minus: `(∂_ωΩ_K)_{ij} = ∂_iη_j - ∂_jη_i` is what is proved
  (`fderiv_lagrange_eq`). Harmless to the norm. Same as iso audit F8; independently confirmed here.
- `docs/campaign/design/APOST-SHARP-V2.md` §0, §4.4 still call B9 optional and say route A's levers add "about one
  more order"; superseded by the brief.
- `scripts/apost_sharp/thresholds_v2.py`, `c_stages`: `ccl(min(r, F(1)))` is paired with `(delta/r)^kappa` in
  `stageA`. For `r > 1` that is the constant at bite `1` with the power of `r`, which `NumA.Cert.bar` does not give.
  It does not affect any package here, all with `r < 1`.

## Uncertainties and what remains

- Whether (R3) should stay a required field of the refined form, and whether `Cert.bar` should allow a bite `≤ r`
  for `ρ > 1`, are design calls for the audit.
- Not done: the hybrid (B8), any certifier change (`checkSmallness` for route A), Lean cross-checks of the constants.
- `min`/`max` with route B: the final `C₁ = min {C₁♯, route A, route B}` belongs to the integration.
