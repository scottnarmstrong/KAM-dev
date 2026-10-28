# P11A-C6 prover handoff (branch inp-p11ac6, 3049422; off inp (P11A-C0 on inp); offloaded package run by the main orchestrator; prover on claude-12)


Branch `inp-p11ac6` (worktree /root/code/KAM-inp-p11ac6), off `inp`. Nothing merged or pushed; `KAM.lean` untouched.

## Files (all new, under KAM/Planetary/MaximalStep/)
| file | lines | content |
|---|---|---|
| `AffineFlowBasic.lean` | 198 | `p11Affine`, `p11Flow`, `p11GaugeBound`, `P11AffineHyp` (verbatim); explicit field components, Cauchy bounds (`af-field`), `SmallField` for gauge `scaleCLE (s/2) σ`, `ε = κ` |
| `AffineFlowGauge.lean` | 184 | gauge-interior inclusions `U ⊆ Ω^{1/2}`, `V ⊆ Ω^1`, `V ⊆ U`; integer-lattice periodicity of `p0,p1`, their derivatives and the field; translation invariance of `Ω` |
| `AffineFlowSimple.lean` | 309 | `af-simple`: angle flow independent of action (`gen_uniqueness` for `θ' = p1 θ`); affine combinations of trajectories are trajectories (`flow_a` uniqueness); `affTheta/affM/affV`; `D Φ(0,b) = (0, M b)`; duality `(DΘ a)·(M b) = a·b` (from `flow_symplFormC`) |
| `AffineFlow.lean` | 223 | `affine_flow` (verbatim signature), `flow_displacement` (af-flow), `fderiv_flow_sub_id` (af-deriv), `field_real` |
| `ParameterFlow.lean` | 176 | `affine_flow_param` (verbatim); `paramField`, `paramGauge` |

`AffineFlow` and `ParameterFlow` are the design-table facades (they `public import` the helper modules). Statements of `p11Affine`, `p11Flow`, `p11GaugeBound`, `P11AffineHyp`, `affine_flow`, `affine_flow_param` were whitespace-normalised and compared programmatically against `.drafts/design/P11ASignatures.lean`: identical (only docstrings differ).

## Approach
- (a)(b): `SmallField (scaleCLE (s/2) σ) Ω X_φ κ`, `κ = 2(n+1)A/σ ≤ 1/2`, bound from `cauchy_strip` on `T_r` with `δ = σ`. Displacements `≤ A`, `≤ (n+1)sA/σ` by the mean-value inequality along the trajectory (the gauge bound alone would only give `2(n+1)A`).
- (c): `Θ(θ) = (Φ(θ,0)).1`, `v(θ) = (Φ(θ,0)).2`, `M(θ) = D_η (Φ.2)(θ,0)`. Angle part independent of `η`: `KAM.ODE.gen_uniqueness` on the strip. Affine in `η`: for `c ∈ [0,1]`, `(θ(t), (1-c)η₀(t) + cη_η(t))` is a trajectory from `(θ, cη)`, so `f(cη)` is affine in `c`; the one-sided derivative at 0 gives `M η = f η - f 0`. `ω`-duality from `flow_symplFormC` applied to `((a,0),(0,b))`.
- (d): `Canonical.flow_c` in the gauge; the `D Φ` operator-norm bound `2κ + κ s/σ` uses the block structure (`(DΦ u).1 = DΘ u.1`, no `θη` block).
- (e): `flow_symplFormC`, `flow_d` (translation by `(k,0)`), `flow_c` (inverse), `flow_e` + `KAM.hamiltonianVectorField_eq_of_real` (reality).
- (f): augmented field `(b,z) ↦ (0, X_{φ_b}(z))` on `B × Ω` in the gauge `diag(δ₀⁻¹, W)` where `ball(b₀,δ₀) ⊆ B` (no uniform margin needed); uniqueness identifies its flow with `(b, X_{φ_b}^t z)` on `ball(b₀,δ₀/2) × U`; `flow_b` gives holomorphy there.

## Checks
- Gate build `inp_lake_build.sh /root/code/KAM-inp-p11ac6 KAM.Planetary.MaximalStep.ParameterFlow KAM.Planetary.MaximalStep.AffineFlow`: `Build completed successfully (9103 jobs)`; no warnings in my files after cleanup. Each of the five modules was also built individually through the gate in dependency order.
- `grep` for `sorry|axiom|maxHeartbeats` in the five files: none. No `set_option` at all. Largest file 309 lines.
- `#print axioms KAM.Planetary.affine_flow` and `... affine_flow_param`: `[propext, Classical.choice, Quot.sound]`.
- `sh scripts/lint_sources.sh`: only remaining complaint is `KAM.lean is out of date; run scripts/gen_root_imports.py` (exit 1, expected: new modules; root file is generated and I did not touch it). Module check PASS, frozen-anchor guard OK, ABI hashes OK; no over-100-column lines in my files.
- No imports of providers, `Frozen` theorems or W/measure modules (imports: Mathlib, `KAM.Canonical.*`, `KAM.Head.HamiltonianField`, `KAM.Planetary.MaximalStep.Basic`).

## Uncertainties / design signals
- None on heartbeats (all default; slowest module ~40 s).
- `affineGauge H` depends on `H` only through proofs; `ParameterFlow` uses `smallField (H b)` against the gauge of `H b₀`, which is defeq by proof irrelevance (compiles).
- `U_sub_half`/`V_sub_one` use strict-inequality bookkeeping of the open strip; no off-by-closure issue.

## Suspected errata / deviations
- None. All signatures are as in the design; no hypothesis added. (Source remark: the unscaled bound `‖Φ_θ - θ‖ ≤ A` cannot come from the gauge bound alone, which gives `2(n+1)A`; it needs the trajectory/MVT argument used here. Not an error in the statement.)

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-C6 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements and definitions = signature file exactly (p11Affine, p11Flow, p11GaugeBound, P11AffineHyp, affine_flow, affine_flow_param, ...); (2) proofs sound (Canonical.flow_a/b/c/d/e, flow_symplFormC consumed as designed; no W/measure dependency); no added premises; P11AffineHyp is a hypothesis package: check it contains only source premises, not a conclusion or hard step; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/MaximalStep/AffineFlow*.lean and ParameterFlow.lean.
