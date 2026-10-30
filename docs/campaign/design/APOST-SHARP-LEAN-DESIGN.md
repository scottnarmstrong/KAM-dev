# Lean design of the sharp a-posteriori theorems (SHARP-DESIGN)

30 October 2026. Branch `sharp-design` (side campaign `apost-sharp`). Blueprint:
- `blueprint/parts/p2s-sharp.tex` (fixed frequency, labels `bp:p2s:*`; top file `blueprint/sharp.tex`);
- `blueprint-I/parts/p2s-iso-sharp.tex` (isoenergetic, labels `bpI:p2s:*`; top file `blueprint-I/sharp.tex`).

Exact signatures: `docs/campaign/design/APOST-SHARP-SIGNATURES.lean.txt`, a copy of the probe
`.drafts/sharp/Signatures.lean`. The probe elaborates with `sorry` bodies: 40 declarations with bodies, every
diagnostic `declaration uses 'sorry'`, no error.

## 0. Summary

- **Scope.** Two new theorems, `KAM.Sharp.g1_sharp` (fixed frequency) and `KAM.Iso.Sharp.g1_sharp` (isoenergetic).
  - Their hypotheses are, verbatim, those of `KAM.Apost.g1_explicit` and `KAM.Iso.Apost.g1_explicit`; the iso one
    concludes the frozen body `IG1Body`. Only the explicit constants change.
  - No existing declaration changes.
- **What the design changes:**
  1. The small-divisor estimate is data (`KAM.Sharp.CohData`), a theorem about `cohR`.
     - The headline instance is Rüssmann's: κ = τ, `cohConstR`.
     - The other instances are Parseval (κ = τ + n/2, `cohConstP`) and the crude one (κ = τ + n, `cohConst`).
  2. The torsion route of HL19 Lemma 4.8.
     - `torsion = 𝒯(A, L, B, DE)` (`KAM.Sharp.torsion_identity`), bounded without `1/δ`, so `a = 2κ`.
     - The averaged twist is perturbed through the same polynomial and the errors of both tori, with a loss of 3δ per
       step.
  3. Separate sizes M, σ_K, σ_B, σ_T, with the exact transposition factor `2n` and `|Aᵀ| = |A|`.
  4. Absorption through `γ ≤ γ̄`.
  5. `c_R` enters as itself, with no floor at 1.
  6. A Neumann ratio of 1/8 in the perturbation lemmas, and Taylor's `M/2`.
  7. The step smallness is split into `𝔠_step X ≤ 1` and `2d ≤ β`.
  8. **One Newton engine** (`KAM/Sharp/Engine/*`): the schedule, decay, sums, induction and limit are proved once for an
     abstract scheme. Both theorems are instances.
- **Numbers** (lunar package R1, exact mirror `scripts/apost_sharp/thresholds.py`, §6):

  | Theorem | log₁₀ threshold, iso | log₁₀ threshold, fixed |
  |---|---:|---:|
  | Current | −74.51 | −76.55 |
  | Sharp, Rüssmann data | **−24.98** | −24.72 |
  | Sharp, Parseval data | −36.99 | −36.73 |
  | Sharp, crude data | −49.10 | −48.85 |

  The target in the brief was about 10⁻⁴⁰.

## 1. The mathematics in one page (blueprint labels)

| Step | Statement | Label |
|---|---|---|
| data | `|𝓡g| ≤ c_R γ⁻¹ δ^{-κ} H` and the a-priori bound, `0 < δ ≤ 1` | `bp:p2s:cohdata` |
| instances | `(τ, cohConstR)`, `(τ+n/2, cohConstP)`, `(τ+n, cohConst)` | `bp:p2s:cohdata-russmann`, `-parseval`, `-crude` |
| frame | `|L| ≤ σ_K`, `|Lᵀ| ≤ 2nσ_K`, `NᵀΩ₀ = BLᵀ`, `|N| ≤ σ_Kσ_B`, `Aᵀ = Ω₀AΩ₀`, `|Pξ| ≤ σ_K|ξᴸ| + σ_Kσ_B|ξᴺ|` | `bp:p2s:frame-bounds` |
| geometry | `C_Ω = 2n(n+1)c_Rσ_K`, no `⟨T⟩` hypothesis | `bp:p2s:geometry` |
| torsion identity | `∂_ωB = -B(∂_ωG)B`, `∂_ωN = Ω₀(AL-F)B - N((AL-F)ᵀL + Lᵀ(AL-F))B`, `T = 𝒯(A,L,B,F)`, `F = DE`, any `ω` | `bp:p2s:torsion-identity` |
| torsion bound | `|T| ≤ C_T0 + C_T1 ε/δ + C_T2 ε/(γδ^{κ+1})` on `T_{r-δ}` (Lagrangian part through `Ω_K` with loss δ/2) | `bp:p2s:torsion-bound` |
| correction | `|ΔK| ≤ C_ΔK ε/(γ²δ^{2κ})` | `bp:p2s:correction` |
| new error | `|Ē| ≤ C_E ε²/(γ⁴δ^{4κ})`, `C_E ≈ (M/2)C_ΔK²` | `bp:p2s:newton-error` |
| perturbation | at real points `|T̃_{ω̃} - T_ω| ≤ (C_Δab + C_Δc) d/δ + O(ε/δ) + O(ε/(γδ^{κ+1}))`, any `ω̃`; Neumann ratio 1/8 | `bp:p2s:perturbation` |
| step | loss `3δ`; rates `ϱ_D, ϱ_B, ϱ_T` per unit `U = ε/(γ²δ^{a+1})` | `bp:p2s:step` |
| engine | abstract scheme (N1), (N2); induction (I1)–(I4); limit | `bp:p2s:scheme`, `bp:p2s:engine-iteration`, `bp:p2s:engine-limit` |
| G1♯ | `C₁♯ = ρ^{4τ} max{γ̄⁴, 𝔠_* δ₀^{-2a}}`, `C₂♯ = 2C_ΔK ρ^{2τ} δ₀^{-a}`, `δ₀ = min{1, (ρ-ρ∞)/6}` | `bp:p2s:g1` |
| iso | the same with `S_*`, `C_Δω = Θγ̄C_S`, bordered twist through `𝒯` at `(K̄, ω̄)` and `Y = ωᵀ - (ηᴸ)ᵀ`; I-G1♯ with `C₃♯ = 2C_Δω ρ^{2τ} δ₀^{-a}` | `bpI:p2s:*` |

## 2. Existing declarations

### 2.1 Reused unchanged

Statements as they are; for some, only the qualitative conjuncts are used.

**Data and standing.**

| Declaration | Location | Use |
|---|---|---|
| `KAM.Apost.Params`, `Standing`, `Admissible` | `KAM/Apost/Standing.lean:41, 50, 67` | standing data; the fixed scheme's `Adm` is `Admissible (m 0) (m 1) (m 2) …` |
| `KAM.Apost.cohR` | `KAM/Apost/Tools.lean:283` | the operator `𝓡` (definitionally `cohSolutionPi`) |
| `KAM.cohomological`, `KAM.cohomological_operator` | `KAM/Strip/CohomologicalNodes.lean:57, 119` | qualitative clauses; the instance `cohData_crude` |
| `KAM.cohomological_russmann`, `…_operator_russmann` | `KAM/Strip/CohomologicalRussmann.lean:182, 243` | `cohData_russmann` |
| `KAM.cohomological_parseval`, `…_operator_parseval` | `KAM/Strip/CohomologicalParseval.lean:184, 245` | `cohData_parseval` |

**Matrices and Hamiltonian.**

| Declaration | Location | Use |
|---|---|---|
| `matrix_facts`, `averages` | `KAM/Apost/Tools.lean:219, 249` | matrix norms, Ω₀, averages |
| `hamiltonian`, `ham_symplectic`, `ham_mvt` | `KAM/Apost/Hamiltonian.lean:371, 323, 345` | `Aᵀ = Ω₀AΩ₀`, `|Ã - A| ≤ Md` |
| `KAM.taylor_of_differentiableOn_fderiv` | `KAM/Strip/Taylor.lean:125` | `|Δ²X| ≤ (M/2)|ΔK|²`, `|Δ²H| ≤ (M/2)|ΔK|²` |
| `KAM.neumann` | `KAM/Matrix/Bridges.lean:33` | `|S⁻¹| ≤ 2` (ratio 1/2) |

**Frame and geometry.**

| Declaration | Location | Use |
|---|---|---|
| `periodicity` | `KAM/Apost/Periodicity.lean:447` | periodicity and realness of all objects |
| `frequency` | `KAM/Apost/Frame.lean:423` | `|ω| ≤ 2nσ_Kσ_B(M+ε)` (iso only) |
| `frame_basic` (qualitative conjunct only) | `KAM/Apost/Frame.lean:438` | holomorphy of the frame objects |
| `frame_identities`, `fi_dL` | `KAM/Apost/Identities.lean:445, 269` | `∂_ωL = AL - DE` and the frame identities **at the standing Diophantine ω** only (both take `Standing … ω γ`); not reused for arbitrary ω′: the generic-frequency derivative helper is the new `KAM.Sharp.TorsionPoly.fderiv_tangentMat_eq` (it repeats the chain-rule computation of `fi_dL`, using the frequency-generic `fderiv_tangent_column_omega`, with no `Standing … ω′ γ` and no Diophantine hypothesis) |
| `exactness` | `KAM/Apost/Exactness.lean:292` | `⟨Ω_K⟩ = 0`, `⟨ηᴺ⟩ = 0` |
| `Geometry.geo_de` | `KAM/Apost/Geometry.lean:77` | `|DE| ≤ nε/δ`, `|(DE)ᵀ| ≤ 2nε/δ` |

**Correction and Newton error.**

| Declaration | Location | Use |
|---|---|---|
| `triU`, `triXi0`, `triXiN`, `triGL`, `triXiL` | `KAM/Apost/Triangular.lean:49–58` | the triangular solution |
| `triangular` (clauses (a), (b), (d)) | `KAM/Apost/Triangular.lean:270` | qualitative part |
| `Triangular.norm_triXi0_le`, `norm_triXiN_le`, `norm_triGL_le` (generic `Γ`) | `KAM/Apost/Triangular.lean:131, 193, 212` | proof of `triangular_bounds` |
| `xi`, `correction`, `correction_spec` (first conjunct) | `KAM/Apost/Correction.lean:52, 58, 398` | `ξ`, `ΔK`, qualitative part |
| `newtonMap`, `NewtonError.sMat_spec`, `newtonMap_mem`, `sumVec_invarianceError_newtonMap` | `KAM/Apost/NewtonError.lean:54, 116, 159, 187` | constant-free pieces of the error identity |
| `xi_equation` | `KAM/Apost/NewtonError.lean:221` | constant-free piece of the error identity |

**Perturbation, step and limit.**

| Declaration | Location | Use |
|---|---|---|
| `Perturbation.tangentMat_sub`, `gramMatrix_sub`, `normalMat_sub` | `KAM/Apost/Perturbation.lean:70, 80, 89` | perturbation algebra |
| `ball_subset_of_close`, `norm_fderiv_sub_le`, `norm_transpose_tangentMat_sub_le` | `KAM/Apost/Perturbation.lean:106, 128, 145` | perturbation bounds |
| `norm_torsionAverage_sub_le`, `differentiableOn_torsion_of` | `KAM/Apost/PerturbationTorsion.lean:276, 257` | average of the torsion change |
| `newtonMap_differentiableOn`, `_isPrimaryOnStrip`, `_isRealOnReals` | `KAM/Apost/Step.lean:56, 62, 73` | step (a) |
| `tendstoUniformlyOn_telescope`, `lim_k`, `lim_dk`, `lim_holo`, `lim_primary`, `lim_close` | `KAM/Apost/Limit.lean:57–133` | engine limit (generic already) |
| `lim_margins`, `lim_invariance` | `KAM/Apost/Limit.lean:232, 249` | margins and invariance of `K_∞` |
| `norm_le_of_rowSum_le`, `g1_closeness_eq` | `KAM/Apost/G1.lean:68`; `KAM/Apost/Constants.lean:930` | row sums ↔ norms; `C₂ e/(γ²ρ^{2τ})` |

**Isoenergetic: linear part.**

| Declaration | Location | Use |
|---|---|---|
| `Setting`, `AdmissibleNoTwist`, `BordData`, `bordSol`, `bordXi*`, `bordGL`, `bordAvg`, `bordMat` | `KAM/Iso/Linear/Defs.lean` | iso data; `AdmissibleNoTwist` is also the hypothesis of the K lemmas without `⟨T⟩` |
| `border_solve` (clauses (a), (b), (d), (e)) | `KAM/Iso/Linear/BorderSolve.lean:218` | qualitative part of the bordered system |
| `extended_basic`, `last_row` | `KAM/Iso/Linear/Extended.lean:274`, `LastRow.lean:95` | `⟨𝖳⟩ = bordMat`, `Y = ωᵀ - (ηᴸ)ᵀ` |
| `energy_approx`, `energy_conservation`, `reduced` | `KAM/Iso/Linear/Energy.lean:135, 210`, `Reduced.lean:181` | energy identities, (O3) |

**Isoenergetic: iteration.**

| Declaration | Location | Use |
|---|---|---|
| `IsoStanding`, `rayMargin`, `IsoAdmissible`, `isoBordData`, `isoXi`, `isoXiOmega`, `isoCorrection`, `isoNewS`, `isoNewtonMap`, `isoQuadX`, `isoQuadH` | `KAM/Iso/Apost/Defs.lean:45–170` | iso objects and step map |
| `correction_core` (first conjunct), `isoNewS_smul_sub`, `isoNewS_smul_eq` | `KAM/Iso/Apost/Correction.lean:168, 358, 366` | qualitative correction, `Δω` |
| `isoNewtonMap_*` | `KAM/Iso/Apost/Torsion.lean:50–72` | step (a) |
| `TorsionDiff.bordMat_sub`, `norm_bordMat_le`, `norm_extendedTorsionAverage_sub_le` | `KAM/Iso/Apost/TorsionDiff.lean:45, 54, 245` | bordered difference |
| `lim_invariance_moving`, `tendsto_energyAverage_of_uniform`, `exists_tendsto_of_dist_ray` | `KAM/Iso/Apost/Limit.lean:197, 232, 174` | iso limit (generic) |
| `margin_of_le`, `norm_le_of_rowSum_le_of_nonempty` | `KAM/Iso/Apost/G1.lean:78, 70` | hypotheses (I7)–(I9) |
| `KAM.Iso.Charts.IG1Body` | `KAM/Iso/Charts/Inputs.lean:45` | the frozen body |

### 2.2 Generic copies needed

These are stated with the old constants. The new ones replace them; the old ones stay as they are.

| Old | Why | New |
|---|---|---|
| `KAM.Apost.cohomological` (`Tools.lean:322`) | bound with `cR n τ`, `kappa n τ` | `KAM.Sharp.CohData` (fields `sol`, `apriori`) |
| `frame_basic` bounds (in 𝔪), `norm_torsion_le` (`C_T/δ`) | one size; Cauchy route | `KAM.Sharp.frame_bounds`, `torsion_identity`, `torsion_bound` |
| `geometry` (`Geometry.lean:298`), `Iso.Linear.geometry_noA5` | 𝔪, `kappa n τ`, needs `(A5)` | `KAM.Sharp.geometry_sep` (no torsion hypothesis) |
| `triangular` clause (c), `Iso.Linear.border_solve` clause (c) | `Γ` with `kappa n τ` | `KAM.Sharp.triangular_bounds`, `KAM.Iso.Sharp.border_bounds` |
| `correction_spec` bounds, `newton_error` (hypotheses in old constants) | constants | `correction_bounds`, `newton_error_bounds` (identity from the helpers of §2.1) |
| `Iso.Apost.NewtonError.sMat_bounds`, `sumVec_error_eq`, `energyAverage_sub_eq` (`:321, 331, 451`) | hypotheses `hsym`/`hβ` in old constants | copies with the pointwise hypotheses `‖symDefect K θ‖ ≤ 1/2`, `‖isoCorrection … θ‖ < β` (private helpers of `iso_newton_error_bounds`) |
| `perturbation`, `frame_items`, `twist_neumann`, `Iso.Apost.torsion_step` | `d/δ²` route, ratio 1/2 | `perturbation_poly`, `neumann_ratio`, `iso_twist` |
| `step`, `Schedule`, `Iteration` (`Stage`), `limit`, `Iso.Apost` iteration and limit, `energy_limit` | old constants and the `4δ` schedule | the engine; `fixedScheme`, `isoScheme`, `iso_energy_limit` |

`KAM.Apost.triangular` is generic in Γ only through its helpers. Its node statement fixes Γ through
`KAM.Apost.cohomological`. Hence `triangular_bounds` reproves clause (c) from the helpers plus `CohData.sol`, and
cites `triangular` for (a), (b), (d).

### 2.3 Exports that are deliberate projections of the blueprint lemma

The following signatures export less than the blueprint lemma states. No Lean signature changes; each
omission is deliberate and the final theorems do not need it.

| Export | Blueprint statement | Exported | Omitted, and why it is not needed |
|---|---|---|---|
| `Engine.error_decay` | `bp:p2s:decay`: `ε_s ≤ q^{2^s-1} 2^{-2as} e ≤ 2^{-2as} e` | `0 ≤ ε_s ≤ 2^{-2as} e`, the weighted bounds, the sums | the intermediate `q^{2^s-1}` factor; the proved bound is by direct induction from `q ≤ 1` (no `C_E > 0` needed), and the induction and limit use only `ε_s ≤ 2^{-2as}e` |
| `torsion_identity` | `bp:p2s:torsion-identity` (a)–(c) | `∂_ω'B`, `∂_ω'N`, `T = 𝒯(A,L,B,F)` | the identity `∂_ω'G = (AL-F)ᵀL + LᵀAL…` of (a); it is the internal step before `∂_ω'B = -B(∂_ω'G)B` (the helper `fderiv_gramMatrix_eq` of `KAM/Sharp/TorsionPoly.lean`) and nothing downstream uses `∂G` itself |
| `Engine.Scheme.iterate` | `bp:p2s:engine-iteration` (i)–(iv), incl. `m_{s,i} ≤ m_{0,i}+2ϱ_ie/(γ²δ₀^{a+j_i})` and `P_s ≤ 2C_pe/(γ²δ₀^a)` | (i)–(iv) with `m_s ≤ σ`, increments, `D_s` bound | the explicit upper bound on `m_s` (it is `Scheme.IsNewton.sums_le`, a named lemma, used inside the proof) and the partial sum `P_s` (the limit theorem bounds `|p_∞ - p_0|` directly by the full sum); neither enters `g1_sharp` |
| `perturbation_poly` | `bp:p2s:perturbation` (a), (b) | the torsion-polynomial perturbation and the frame bounds used by the step | `|Ã-A| ≤ Md` and the transpose estimates, which are intermediate facts, obtainable from the existing `ham_mvt` and `norm_transpose_tangentMat_sub_le` (to be proved as named helpers inside the perturbation modules, not exported); the step uses only the exported torsion and frame bounds |
| `geometry_sep` | `bp:p2s:geometry` | the bounds under `AdmissibleNoTwist` | none: `ε ≤ 1` is now stated in the blueprint lemma (it is a field of the bundle, and every application has `ε ≤ δ ≤ 1`) |

Constants: "none depends on `ρ, ρ∞, γ`" is read as "none of the constants preceding `δ₀`"; `δ₀` depends only on
`(ρ, ρ∞)` (blueprints corrected).

## 3. New modules

All modules are new and additive, and each stays at most 800 lines. Line counts are estimates.

### 3.1 Engine (`KAM/Sharp/Engine/*`, namespace `KAM.Sharp.Engine`)

| Module | Declarations | Lines |
|---|---|---:|
| `Schedule.lean` | `delta0 lam ρ ρinf`, `deltaSeq`, `rSeq`, `schedule` | 150 |
| `Decay.lean` | `epsSeq CE a lam ρ ρinf γ e`, `error_decay` (`2^{-2as}` decay, weighted bounds, sums for `i ≤ 2a-1`) | 250 |
| `Scheme.lean` | `structure Scheme n k α` (`tor`, `par`, `Adm`, `step`); `structure Consts k` (`lam a CE CD Cp cstep cap rate j`); `Scheme.IsNewton` ((N1), (N2)); `Scheme.iter`; `Consts.eps`, `.d`, `.sumD`, `.mSeq`; `Scheme.iterate` | 350 |
| `Limit.lean` | `Scheme.limTor`, `Scheme.limPar`, `Scheme.limit` | 250 |

- `IsNewton` is a `Prop` structure: (N1) regularity of admissible states, and (N2) the abstract step.
  - **It is never a hypothesis of a source result.** Each instance proves it (`fixedScheme_isNewton`,
    `isoScheme_isNewton`).
  - The engine theorems are conditional helpers whose hypothesis is that proof plus the arithmetic (I1)–(I4).
- The caps form a vector over `Fin k`:
  - fixed frequency: k = 3 (`|DK|`, `|B|`, `|⟨T⟩⁻¹|`);
  - isoenergetic: k = 4, adding the used part of the ray margin `ν`, with `j = 0`.

### 3.2 Fixed frequency (`KAM/Sharp/*`, namespace `KAM.Sharp`)

| Module | Declarations | Lines |
|---|---|---:|
| `CohData.lean` | `structure CohData n τ κ cR`; `cohData_russmann`, `cohData_parseval`, `cohData_crude` | 200 |
| `Constants.lean` | `vth`, `vthh`, `cOm`, `cSym`, `cRed`, `cT0`, `cT1`, `wT`, `cT2`, `hT`, `cXi0`, `cXiN`, `cG`, `cDXi`, `cXi`, `cDK`, `cLin`, `cE`, `cGram`, `cB`, `cDab`, `cDc`, `cDT`, `rateD`, `rateB`, `rateT`, `cStep`, `cSum`, `cStar`, `delta0s`, `twistD`, `sharpC1`, `sharpC2` | 150 |
| `ConstantsArith.lean` | `consts_pos`, `absorb`, `step_small` | 450 |
| `Tools.lean` | `neumann_ratio`, `norm_mul_sub_mul_le` | 150 |
| `Frame.lean` | `frame_bounds`, `geometry_sep` | 300 |
| `TorsionPoly.lean` | `torsionPoly`, `torsion_identity` | 400 |
| `TorsionBound.lean` | `torsion_bound` | 200 |
| `Correction.lean` | `triangular_bounds`, `correction_bounds` | 350 |
| `NewtonError.lean` | `newton_error_bounds` | 350 |
| `Perturbation.lean` (split if needed: `PerturbationFrame`, `PerturbationTorsion`) | `perturbation_poly` | 700 |
| `Step.lean` | `step_spec` | 250 |
| `Scheme.lean` | `fixedScheme`, `fixedConsts`, `fixedScheme_isNewton`, `engine_hyps` | 300 |
| `G1.lean` | `G1Body`, `g1_gen`, `g1_sharp`, `g1_sharp_parseval`, `g1_sharp_crude`, `g1_sharp_uniform` | 300 |

Name clashes are avoided:
- The sharp `δ₀` is `KAM.Sharp.delta0s`, because `KAM.Apost.delta0` is `(ρ-ρ∞)/8`.
- The theorems are `geometry_sep`, `correction_bounds`, `newton_error_bounds`, `perturbation_poly` and `step_spec`,
  so they do not shadow the Apost names when `open KAM.Apost` is used.
- `KAM/Sharp/Box*` already exists (SHARP-BOX) and nothing here collides with it.

### 3.3 Isoenergetic (`KAM/Iso/Sharp/*`, namespace `KAM.Iso.Sharp`)

| Module | Declarations | Lines |
|---|---|---:|
| `Constants.lean` | `thetaS`, `iCS`, `iCXiN`, `iCG`, `iCDXi`, `iCXi`, `iCDK`, `iCDw`, `iCP`, `iCdK`, `iCLin`, `iCE1`, `iCE2`, `iCE`, `iCDT`, `iCDTb`, `iRateD`, `iRateB`, `iRateT`, `iCStep`, `iCSum`, `iCStar`, `sharpIsoC1`, `sharpIsoC2`, `sharpIsoC3` | 150 |
| `ConstantsArith.lean` | `iso_step_small` (+ positivity, engine hypotheses) | 450 |
| `BorderBounds.lean` | `border_bounds` | 250 |
| `Correction.lean` | `iso_correction_bounds` | 400 |
| `NewtonError.lean` | `iso_newton_error_bounds` (+ the three generic copies of §2.2 as private helpers) | 500 |
| `Twist.lean` | `iso_twist` | 350 |
| `Step.lean` | `iso_step_spec` | 250 |
| `Scheme.lean` | `IsoState`, `isoScheme`, `isoConsts`, `isoScheme_isNewton`, `iso_energy_limit` | 450 |
| `G1.lean` | `g1_gen`, `g1_sharp`, `g1_sharp_parseval`, `g1_sharp_crude` | 300 |

The total is about 3.5k lines for the engine and fixed frequency, and about 3.1k for the isoenergetic part.

## 4. The final theorems

### 4.1 `KAM.Sharp.g1_sharp`

- **Binders.** Those of `KAM.Apost.g1_explicit`, verbatim: `hn, hτ, hρinf, hρinfρ, hM, hσK, hσB, hσT, hμ, hγbar`.
- **Conclusion.** `0 < C₁♯ ∧ 0 < C₂♯ ∧ G1Body n τ ρ ρinf M σK σB σT μ γbar C₁♯ C₂♯`, where:
  - `G1Body` is the frozen body copied verbatim from `g1_explicit`;
  - `C₁♯ = sharpC1 n τ (cohConstR n τ) M σK σB σT γbar μ τ ρ ρinf`;
  - `C₂♯ = sharpC2 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf`.
- **Variants.**
  - `g1_sharp_parseval` and `g1_sharp_crude` are the same with `(τ + n/2, cohConstP n τ)` and `(τ + n, cohConst n τ)`.
  - `g1_sharp_uniform` takes the ρ-uniform smallness `max {γ̄⁴, 𝔠_*} e/(γ⁴ δ₀^{2a}) < 1`.

### 4.2 `KAM.Iso.Sharp.g1_sharp`

- **Binders.** Those of `KAM.Iso.Apost.g1_explicit`, verbatim.
- **Conclusion.** `0 < C₁♯ ∧ 0 < C₂♯ ∧ 0 < C₃♯ ∧ IG1Body … C₁♯ C₂♯ C₃♯`, with:
  - `C₁♯ = sharpIsoC1 n τ (cohConstR n τ) M σK σB σT γbar μ ν τ ρ ρinf`;
  - `C₂♯ = sharpIsoC2 …`;
  - `C₃♯ = sharpIsoC3 …`.

### 4.3 How `checkSmallness` would change

This would be package SHARP-CERT, in new files only.

- **Unchanged sub-checks.** `checkSmallness` (`KAM/Certificate/Defs.lean:285`) tests
  `isoC1Q · err < γ⁴ ρ^{4τ}` and `isoC2Q · err ≤ disp · γ² ρ^{2τ}`.
  - Every other sub-check (static, H-bounds, embedding, invariance, energy, Gram, torsion) checks hypotheses of
    `IG1Body`.
  - Those hypotheses are identical for `KAM.Iso.Sharp.g1_sharp`, so all those sub-checks and their soundness lemmas
    transfer as they are.
- **The new check.** A sharp checker replaces only `checkSmallness`:
  - `sharpIsoC1Q · err < γ⁴ ρ^{4τ}`;
  - `max(sharpIsoC2Q, sharpIsoC3Q) · err ≤ disp · γ² ρ^{2τ}`.
  - `sharpIsoC*Q` are rational mirrors of Definition `bpI:p2s:constants`.
- **The mirrors.** They are monotone in their inputs.
  - Every sharp constant is a polynomial with rational coefficients in `(c_R, M, σ_K, σ_B, σ_T, γ̄)`, maxima of such,
    and the powers `2^{κ+1}`, `2^{2a}`.
  - `c_R = cohConstR n τ` enters through a rational upper bound `cRQ` (for (2,1): `0.31629`), proved like `cRUpQ`.
  - With `τ ∈ ℕ`, `a = 2τ` and the exponents `2a = 4τ` and `a` of `δ₀` are natural numbers; `2^{κ+1} = 2^{τ+1}`.
  - `δ₀ = min {1, (ρ-ρ∞)/6}`.
- **Soundness.** The soundness lemma is the old one with `g1_explicit` replaced by `KAM.Iso.Sharp.g1_sharp` and the
  mirror inequalities `sharpIsoC1 ≤ sharpIsoC1Q`, `sharpIsoC2 ≤ sharpIsoC2Q`, `sharpIsoC3 ≤ sharpIsoC3Q`.
- **The ρ-uniform form.** Equivalently, test `max(γ̄⁴, iCStarQ) · err < γ⁴ δ₀^{4τ}`; the ρ-uniform corollary would then
  be the iso analogue of `g1_sharp_uniform`.
- **Effect.** For R1 the admissible error rises from 3·10⁻⁷⁵ to 1.05·10⁻²⁵.
  - CONSTANTS-STUDY §2.3 fits log₁₀ η ≈ −0.94 L + 3 and N_E ≈ 1.1 L². With 2 orders of headroom, the truncation would
    be L ≈ 32 digits instead of 87, and the E-support about 1.1k terms instead of 8.1k (about 7× fewer).
  - This is extrapolated from the study's fits; it was not measured.

## 5. Package split (dependency order)

| Package | Owned files | Targets | Depends on | Lines |
|---|---|---|---|---:|
| **A1 SHARP-ENGINE** | `KAM/Sharp/Engine/{Schedule,Decay,Scheme,Limit}.lean` | `Engine.schedule`, `Engine.error_decay`, `Engine.Scheme.iterate`, `Engine.Scheme.limit` | `KAM.Apost.Limit` (generic lemmas) | 1000 |
| **A2 SHARP-DATA** | `KAM/Sharp/{CohData,Constants,ConstantsArith,Tools}.lean` | `CohData`, `cohData_russmann`, `cohData_parseval`, `cohData_crude`, all `def`s, `consts_pos`, `absorb`, `step_small`, `neumann_ratio`, `norm_mul_sub_mul_le` | `KAM.Strip.Cohomological{Russmann,Parseval}`, `KAM.Apost.Tools`, `KAM.Matrix.Bridges` | 950 |
| **A3 SHARP-TORSION** | `KAM/Sharp/{Frame,TorsionPoly,TorsionBound}.lean` | `frame_bounds`, `geometry_sep`, `torsionPoly`, `torsion_identity`, `torsion_bound` | A2; `KAM.Apost.{Identities,Exactness,Geometry,Hamiltonian}` | 900 |
| **A4 SHARP-K-STEP** | `KAM/Sharp/{Correction,NewtonError,Perturbation,Step}.lean` | `triangular_bounds`, `correction_bounds`, `newton_error_bounds`, `perturbation_poly`, `step_spec` | A2, A3; `KAM.Apost.{Triangular,Correction,NewtonError,Perturbation,PerturbationTorsion,Step}` | 1650 |
| **A5 SHARP-K-G1** | `KAM/Sharp/{Scheme,G1}.lean` | `fixedScheme_isNewton`, `engine_hyps`, `G1Body`, `g1_gen`, `g1_sharp`, `g1_sharp_parseval`, `g1_sharp_crude`, `g1_sharp_uniform` | A1, A4 | 600 |
| **A6 SHARP-ISO-STEP** | `KAM/Iso/Sharp/{Constants,ConstantsArith,BorderBounds,Correction,NewtonError,Twist,Step}.lean` | `iso_step_small`, `border_bounds`, `iso_correction_bounds`, `iso_newton_error_bounds`, `iso_twist`, `iso_step_spec` | A2–A4; `KAM.Iso.Linear.*`, `KAM.Iso.Apost.{Defs,Correction,NewtonError,Torsion,TorsionDiff}` | 2350 |
| **A7 SHARP-ISO-G1** | `KAM/Iso/Sharp/{Scheme,G1}.lean` | `isoScheme_isNewton`, `iso_energy_limit`, `KAM.Iso.Sharp.g1_gen`, `g1_sharp`, `g1_sharp_parseval`, `g1_sharp_crude` | A1, A6; `KAM.Iso.Apost.Limit` (generic lemmas) | 750 |
| A8 SHARP-CERT (later) | new `KAM/Certificate/Sharp/*` | rational mirrors, the sharp `checkSmallness`, soundness | A7 | – |

- A1, A2 and A3 (A3 after A2's `Constants.lean`) can run in parallel.
- A4 then A5 (fixed); A6 then A7 (iso), in parallel with A5 once A4 has landed.
- Every package proves exactly the signatures of `APOST-SHARP-SIGNATURES.lean.txt`; changing a statement is a design
  change and needs a ruling.

## 6. Thresholds (output of `python3 -I scripts/apost_sharp/thresholds.py`)

### 6.1 Inputs and conventions

- **Package R1** (CONSTANTS-STUDY §2.2):
  - n = 2, τ = 1, ρ′ = 1/70, ρ∞ = ρ′/1000, μ = 1/160, ν = 10⁻⁶;
  - time scale c = 7/4, s = 1 + 10⁻⁶, γ = γ̄ = c/(42s);
  - majorants: sampled sup × 1.05 (plus μ where the hypothesis carries the margin), giving M ≥ 153909/80000 = 1.9238625 (taken as 1.924), σK = 1.374,
    σB = 1.931, σT = 0.619.
  - The one-size rows use 𝔪 = 39/20.
- **Arithmetic.** All of it is exact (`fractions`); `c_R` enters as rational upper bounds.
  - `cohConstR 2 1 = 0.31628`, `cohConstP 2 1 = 0.37967`, `cohConst 2 1 = 0.48341`.
  - The best constant of the Parseval route itself would be 0.0397; this is not used.

### 6.2 Cumulative path to the design (rows V1–V8)

V0 is checked against `scripts/spin_orbit/exact_constants.py` (−74.51 iso, matching CONSTANTS-STUDY).

| Variant | log₁₀ threshold, fixed | log₁₀ threshold, iso | a | Active branch (iso) |
|---|---:|---:|---:|---|
| V0 current theorem | −76.55 | −74.51 | 8 | E |
| V1 torsion route only (κ = τ+n, one size, Θ-absorption, 4δ) | −58.14 | −58.20 | 6 | sum |
| V2 + Parseval (κ = τ+n/2, `cohConstP`) | −47.14 | −47.20 | 4 | sum |
| V3 + Rüssmann instead (κ = τ, `cohConstR`) | −36.15 | −36.21 | 2 | sum |
| V4 + 3δ schedule | −35.65 | −35.71 | 2 | sum |
| V5 + separate norms | −32.55 | −32.62 | 2 | sum |
| V6 + γ̄-absorption | −28.32 | −28.54 | 2 | step |
| V7 + `c_R` itself | −26.32 | −26.56 | 2 | step |
| **V8 = design (Rüssmann)**: ratio 1/8, M/2, split step smallness | **−24.72** | **−24.98** | 2 | E |

### 6.3 Other instances of the design

| Instance | log₁₀ threshold, fixed | log₁₀ threshold, iso | a | Active branch (iso) |
|---|---:|---:|---:|---|
| Parseval | −36.73 | −36.99 | 4 | E |
| Crude | −48.85 | −49.10 | 6 | E |

### 6.4 The design's c_* branches (log₁₀, Rüssmann, iso)

| Branch | log₁₀ |
|---|---:|
| 2^{2a}C_E | 8.97 |
| 𝔠_step | 7.76 |
| 𝔠_sum/μ | 7.97 |
| 4γ̄²C_Δω/ν | 6.03 |

### 6.5 Sensitivity (Rüssmann, iso)

| Input | Value | log₁₀ threshold |
|---|---|---|
| `c_R` | 0.1 | −23.08 |
| `c_R` | 1 | −26.94 |
| μ | 1/320 | −24.96 |
| μ | 1/80 | −25.02 |
| μ | 1/20 | −25.27 |
| ϑ | 1/16 | −24.98 |
| ϑ | 1/4 | −24.98 |
| ϑ | 1/2 | −25.54 |

Larger μ raises σ_K, σ_B, σ_T in this package. ϑ only matters once it reaches 1/2.

### 6.6 Reading

- **Each step's gain.** The torsion route gains about 18 orders, the exponent about 22 (Rüssmann: a = 2τ = 2), the
  schedule 0.5, separate norms 3, γ̄-absorption 4, `c_R` 2, and the rest 1.6.
- **Active branch.** For the design it is the quadratic one, `2^{2a}C_E` with `C_E ≈ (M/2)C_ΔK²`:
  - C_ΔK ≈ 5.7·10³ (iso: 7.3·10³);
  - it is driven by the torsion bound `H_T = 4nMσ_K²σ_B² + 1 ≈ 109`, entering squared through `C_g` and `C_ξN`.
- **The next lever** would be an actual-norm torsion majorant as a new hypothesis, which this design does not add
  (hypotheses must keep the old form).

## 7. Notes for the provers (risks)

- **`torsion_identity`** needs the derivative of `θ ↦ (gramMatrix K θ)⁻¹`.
  - `frame_basic` gives only differentiability.
  - Use `hasFDerivAt_ring_inverse` in the normed ring of matrices (local instance `Matrix.linftyOpNormedRing`, as in
    `KAM/Matrix/Neumann.lean`), or differentiate `B * G = 1` directly with the product rule.
  - The identity holds for every `ω'`, so `torsion_identity` takes `ω'` separately from the standing `ω`.
- **Exponents** are real (`κ : ℝ`): `δ ^ (2 * (2 * κ))` is `rpow`. Keep the absorption arithmetic in `absorb` and use
  `Real.rpow_add`, `Real.rpow_le_rpow_of_exponent_ge` (base ≤ 1).
- **Constants** are long `max` chains.
  - Prove the comparison lemmas (`le_cStep_*`, `le_cSum_*`) once in `ConstantsArith` and keep the defs folded
    elsewhere.
  - Under the no-heartbeat rule, a slow `positivity`/`nlinarith` there is a signal to split.
- **`Fin k` vectors** `![…]`: use `Matrix.cons_val_zero` / `Fin.cases` simp lemmas. Do not `decide` over reals.
- **`perturbation_poly`** is the largest proof.
  - Split the torsion polynomial into `𝒯_ab`, `𝒯_F`, `𝒯_c` (private defs), prove the three bounds separately, and
    assemble.
  - The telescoping uses `norm_mul_sub_mul_le` five or eight times; `vthh` absorbs the barred norms.
- **The iso twist** uses `perturbation_poly` at `ω' = s̄ω*`, and at `(K̄, s̄ω*)` on `T_{r-3δ}` the unconditional helpers, not `last_row`/`extended_basic` (whose `Setting`, Diophantine, primary and real hypotheses are not available for the new pair; `s̄ > 1` is not used, the ray is certified by the engine cap):
    - `KAM.Iso.Linear.LastRowAux.energyRow_eq_sub_etaL` (`LastRow.lean:46`), `Y = ωᵀ - (ηᴸ)ᵀ`, only premise: Gram invertible;
    - `KAM.Iso.Linear.extended_regular` (`Extended.lean:255`), continuity/holomorphy of the energy row at an arbitrary new real frequency;
    - `KAM.Iso.Linear.ExtendedAux.extendedTorsionAverage_eq_bordMat` (`Extended.lean:178`), the average of the bordered matrix.
  - No Cauchy estimate in the frequency direction is needed. The old `torsion_sub_freq` and `energyRow_sub` are not
    used.
- **Modules not in this worktree's snapshot.** `KAM.Strip.CohomologicalRussmann` and `KAM.Strip.CohomologicalParseval`
  (merged from `apost-sharp`) were not built here.
  - The probe therefore carries verbatim copies of the two constant definitions.
  - The real modules import them; `CohData.lean` is the only module that needs the two theorems.
