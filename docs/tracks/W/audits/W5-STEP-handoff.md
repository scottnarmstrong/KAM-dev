# W5-STEP handoff — PARTIAL (not ready for audit as a whole)

Branch `inp-wpj`, stacked on W4-HOMOLOGICAL (audit-target commit `82d8325d`). Source:
`blueprint-W/parts/w5-kamstep.tex`. All modules below build at default heartbeats (`w_build.sh`), no `sorry`, no
axioms, `w_lint.sh` exit 0; `#print axioms` of every main result listed: propext, Classical.choice, Quot.sound only.

## Landed (modules under `KAM/Wave/`)

| Module | Content | Blueprint label |
|---|---|---|
| `KamStep/Phase.lean` | `StepPhase r`: Banach carrier on `KamPhase` with norm `kamNorm r` | setting |
| `KamStep/Omega.lean` | symplectic form `stepSymp`, bound `(4π+1) r²` (sharper than `(4π+2) r²`), antisymmetry, nondegeneracy | `omega` |
| `KamStep/Class.lean` | `IsSmoothing`, uniqueness of the field, `FamBound` (λ-norm as a conjunction), `FamBound.mono`, `lamProd_bound` | `class`, `lambda-product` (arithmetic core) |
| `Homological/*` (W4 refactor) | W4 with general `p_+` (`pb`), `j^{1/2}` tail; general declarations carry `_gen`; `PPlusOne.lean` restores the old names at `p_+ = p+1` | `w4-general` |
| `KamStep/LatticeBN.lean` | `waveBN` (`B^♮_σ`), `waveBNconst` (`b^♮(τ) = 4(C_0+C_2+C_{2τ}+C_{2τ+2})`), `waveBW_le_waveBN`, `waveBN_le : B^♮_σ ≤ b^♮ σ^{-(2τ+4)}` | `w4-modified` (iii), step `m-const` |
| `KamStep/Data.lean` | step constants `stepC1, stepT, stepCF, stepC0, stepC2` and modified `stepTn, stepCFn, stepC0n, stepC2n`, `stepMF`; positivity; `stepMF_le_of_small` (smallness ⇒ `M_F ≤ ση²/16`); `stepMF_margins` (`M_F ≤ σ/1024`, `M_F/(σ/4) ≤ 1/256`, `16M_F/σ ≤ η²`); `stepSolve_bound`, `stepSolve_bound_mod` (`3C₁B_σ/α · 3ε ≤ M_F`, both cases); `stepEstimate_arith` (`896ηε + 168 c ε²/(ασ^tη²) ≤ C₂(...)`) | `data`, `solve` (arithmetic), `step` (st-1/st-2 arithmetic) |
| `KamStep/Divisors.lean` | `stepDivisors` (divisor lower bounds after the step, `HomMelnikov` data), `stepFreqHyp` (the frequency hypothesis `bpW:w5:freq` is stable with `M₀+3ε`, `M_ω+6πε/λ`, `M_Ω+3ε/λ`), helper `homPairL_sub_le`, `waveA_le_of_modeSize_le` | `step` (iii), (iv) |
| `KamStep/Flow.lean` | `stepDomain ρ s r'`, openness, `stepDomain_margin` (ball `B(w,σ/2) ⊂ D(s-σ,r)` for `w ∈ D(s-2σ,r/2)`), **`stepFlowHyp`**: `FlowHyp X V U M (σ/4)` on `StepPhase r` with the concrete A.4 margins (so all landed `KAM/Wave/Analytic/Flow` lemmas apply), `stepImage_mem` (`φ^t(D(s-5σ,ηr)) ⊂ D(s-4σ,2ηr)`) | `flow` (margins, image, hypotheses) |
| `KamStep/Pullback.lean` | abstract core of the pull-back: `stepInv_sub`, `stepPullback_diff` (`λ‖B_ξy₁-B_ζy₂‖ ≤ (9/2 Y₀+2λY_L)d`), `stepPullback_const` (`2Y₀+(9/2Y₀+2λY_L) ≤ 7(Y₀+λY_L)`), `stepCommutator_arith` (`24εM_F/(ση²)`) | `pullback` (operator core, step `p-ass`), `commutator` (arithmetic) |
| `KamStep/SymplecticFlow.lean` | `stepSymp_const`: `B(a(t),b(t))` is constant along `a'=K a` when each `K(t)` is `B`-skew (derivative lemma `stepSymp_hasDerivWithinAt`) | `flow-calc` (ii), step `c-symp` (abstract core) |
| `KamStep/Triangle.lean` | `stepTriangle`, `stepTriangle_on`: `∫₀¹∫₀ᵗ g = ∫₀¹(1-τ)g` | external `W5-E5` |
| `KamStep/FlowSmooth.lean` | abstract smoothing flow (`F` carrier, `G` target of norm `p_+`, `ι : G →L F`): `φ^t w = w + ι Ψ^t w`, `‖Ψ^t‖ ≤ M|t|`, parameter dependence `‖ΔΨ‖ ≤ |t|N(1+Le^L)` | `flow` (i), step `f-flow`, `f-par` |
| `KamStep/FlowVariational.lean` | `fderiv_holoFlow_eq` (`Dφ^t = I + ∫DX(φ^σ)Dφ^σ`), `continuousOn_fderiv_holoFlow_time` | `flow-calc` (i), steps `c-cont`, `c-var` (abstract) |
| `KamStep/FlowSymplectic.lean` | `holoFlow_preserves_form`: `Dφ^t` preserves a bilinear form skewed by every `DX(z)` (abstract) | `flow-calc` (ii), step `c-symp` (the skewness `c-skew` for the concrete `X_F` is open) |
| `KamStep/FlowSmoothDeriv.lean` | `Ψ^t` is `G`-holomorphic (`hasFDerivAt_smoothDisp`), Cauchy bounds `‖DΨ^t‖ ≤ M|t|/ρ`, differences, `Dφ^t = I + ι DΨ^t` | `flow` (i), (ii), step `f-der` |
| `KamStep/FlowStepBounds.lean` | the same with `L ≤ 1/64`: `‖Ψ‖ ≤ M`, `‖ΔΨ‖ ≤ 2N`, `‖DΨ‖ ≤ M/ρ`, `‖ΔDΨ‖ ≤ 2N/ρ` (`ρ = σ/8`) | `flow` (i), (ii) (numerical form) |
| `KamStep/FlowEquivariant.lean` | `holoFlow_translate`: `φ^t(w+a) = φ^t w + a` for translation-invariant fields (reality is `holoFlow_mem_range` of W1) | `flow` (iv), step `f-real` (abstract) |
| `KamStep/TaylorOneVar.lean` | `norm_taylorCoeff_le`, `norm_taylor_remainder_le` (Banach-valued, one variable) | external `W5-E1` |
| `KamStep/TaylorScale.lean`, `TaylorEst.lean` | `S_t`, `T_t` (`scaleS`, `scaleT`), `scaleS_mem`, `kamNorm_scaleT_le`; `taylorXR` (sum of the Taylor coefficients of `t ↦ T_t X(S_t w)`), `taylorXR_bound` (`≤ 3ε`), `taylorXR_remainder` and `taylorXR_remainder_128` (`|X-X_R|_{ηr} ≤ 128ηε` on `D(s,4ηr)`) for any field `X` holomorphic on `D(s,r)` with `|X|_r ≤ ε` | `taylor` (iii), (iv), steps `t-disc`, `t-est` (the identification of `taylorXR` with the field of the Taylor polynomial `R`, parts (i), (ii), is open) |
| `KamStep/FlowInverse.lean`, `FlowTransport.lean`, `FlowTime.lean`, `FlowSkew.lean` | `isUnit_fderiv_holoFlow` (`‖Dφ^t-I‖ ≤ 1/8`, Neumann), `hasFDerivAt_comp_hamiltonian` (transport: field of `G∘φ` is `A⁻¹ X_G∘φ`), `hasDerivWithinAt_comp_holoFlow` (time derivative), `skew_of_hamiltonian` (`DX_F` is `B`-skew from symmetry of `D²F`, external E3), `hasFDerivAt_bracket` (`D{G,F} = B([X_G,X_F],·)`) | `flow-calc` (iii)–(v), step `c-skew`, `new-ham` step `n-br` (all abstract in `F`, `B`) |
| `KamStep/NewHamExp.lean` | `stepFTC`, `stepIntegral_eq`, `stepExpansion`, `stepExpansion_H`: `H(Φw) = N + N̂ + â₀ + (P-R)(Φw) + ∫₀¹((1-τ){N̂,F}+τ{R,F})` along a trajectory (scalar core) | `new-ham` (i), step `n-exp` (scalar core) |
| `KamStep/StepCLM.lean` | `stepSympCLM` (`ϖ` as `StepPhase r →L StepPhase r →L ℂ`, `‖·‖ ≤ (4π+1) r²`, antisymmetric for `q=q'`), `stepEmbedCLM` (`homEmbed_gen` on the normal components, `‖ι W‖ ≤ ‖W‖`): the concrete `B` and `ι` for the abstract flow calculus | `omega`, `flow` (instantiation data) |
| `KamStep/TaylorFun.lean`, `TaylorFunSym.lean`, `TaylorFunDeriv.lean`, `TaylorField.lean` | `stepZ, stepZb` (`z=(u+iv)/√2`), `stepFun T` (the polynomial `F` of a W4 `HomTaylor_gen`), `stepPr` (weighted pairing), `stepPr_swap` (transposed matrices pair transposed), `stepFun_hasFDerivAt`, `stepField T` (`(b/2π, -F_θ/2π, F_v, -F_u)`), **`stepFun_field`**: `D(stepFun T)(w) W = ϖ_{p,p_+}(stepField T w, W)` for `θ∈T_s` | `solve` step `s-class` (field of `F`, `DF=ϖ(X_F,·)`) |
| `KamStep/TaylorFieldDiff.lean`, `StepSympEmbed.lean` | `differentiableOn_homPartial`, `stepField_differentiableAt` (holomorphy of `X_F`), `stepSymp_embed` (`ϖ_{p,p}(ιX,W)=ϖ_{p,p_+}(X,W)`) | `solve` `s-class`, `flow-calc` `c-skew` |
| `KamStep/StepFlowConcrete.lean`, `StepFieldBound.lean` | `stepToKCLM/stepOfKCLM`, `stepFieldS` (`Z`), `stepFS`, `stepFS_hasFDerivAt` (`DF=B(ιZ,·)`), **`stepFieldS_skew`** (`DX_F` is `B`-skew, concrete), `kamNorm_stepField` (= W4's `homXnorm_gen`), `homDomain_stepZ`, `stepFieldS_bound` (W4 `HomFieldBound_gen` ⇒ `‖Z‖≤ε` on `D(s',r)`), **`stepFlowHyp_concrete`**: `FlowHyp (ι∘Z) D(s-σ,r) D(s-2σ,r/2) M (σ/4)` | `flow` (hypotheses), `flow-calc` `c-skew` (concrete) |
| `KamStep/StepNfun.lean`, `StepSolve.lean` | `stepToHom`, `stepNfun` (`N` on `KamPhase`), `stepNfun_hasFDerivAt`, **`stepNfun_lie`** (`DN(w)(ιX_F(w)) = -L_NF(w)`, from W4 `homLemma_lie_iv_gen`); `stepField_sub`; **`stepSolve_fam`** (`|X_F|^λ_{r,D(s-σ,r)} ≤ (3C₁B^W_σ/α)(ε+λε^L)` as a `FamBound`, from W4 `homLemma1_fieldBound_gen`/`homLemma1_lipschitz_gen`/`homLemma2`); **`stepSolve_equation`** (`R + DN·ιX_F = N̂ + â₀` on `θ∈T_{s-σ}`); `stepNhat_fam` (`|X_{N̂}|^λ ≤ 2(ε+λε^L)`); `stepSymp_comm_weights`; **`stepFun_isSmoothing`** (`stepFun T ∈ 𝒮_{p_+}(D(s',r))` with field `stepField T`) | `solve` (unmodified case, concrete), `flow-calc` (v) |
| `KamStep/NewHamFlow.lean` | **`stepNewHam_flow_H`**: `N(Φw)+P(Φw) = N(w)+N̂(w)+â₀+(P-R)(Φw)+∫₀¹((1-τ)DN̂·X+τDR·X)(φ^τ w)dτ` for any `FlowHyp` flow and `C¹` `N,N̂,R` with `DN·X = N̂+â₀-R` on `V` (abstract in the phase space; instantiate with `stepNfun_hasFDerivAt`, `stepFS_hasFDerivAt`-type derivatives and `stepSolve_equation`) | `new-ham` (i), step `n-exp` (along the flow) |
| `KamStep/HoloFderiv.lean` | **`differentiableOn_fderiv_of_holomorphic`**: for `f` holomorphic on an open subset of a complex normed space with Banach target, `Df` is holomorphic (operator norm); `hasFDerivAt_fderiv_of_holomorphic`; `holoD2` (slice second derivative), bounds | infrastructure (the infinite-dimensional Cauchy/analyticity fact used by Taylor (i), new-ham (ii), flow-calc) |
| `KamStep/TaylorCommute.lean`, `TaylorRv.lean`, `TaylorFieldRv.lean` | Taylor coefficients of order ≤ 2 commute with a parameter derivative (`hasDerivAt_taylorSum_param`); `taylorRv` (value of `R`), `hasDerivAt_taylorRv`; scaling identity `stepSymp_scale`, `sympK`, `sum_taylorCoeff_symp` (Gateaux `DR = ϖ(X_R,·)`) | `taylor` (ii), steps `t-scale`, `t-field` |
| `KamStep/TaylorSmoothing.lean`, `TaylorBlocks.lean`, `TaylorData.lean`, `TaylorBound.lean`, `TaylorBoundA0.lean`, `TaylorAssemble.lean`, `TaylorValue.lean`, `TaylorFieldBound.lean` | Hessian symmetry (`stepSymp_dX_symm`), angle periodicity of `X`, `DX`; the blocks `P,P',Q,Q^T` of `DX(w₀)` (`blockP…`), `stepSymp_z` (`ϖ` in `(z,z̄)` coordinates), entry symmetry; components `tA0,tB,tCp,tCm,tP,…` with holomorphy, periodicity, boundedness (Cauchy in the normal directions; `P(θ,0,0,0)` bounded by periodicity + gradient bound); **`stepTaylorOf`** (`R ∈ 𝒯_s` = `HomTaylor_gen a p pb s`); `taylorRv_eq`, **`stepFun_taylorOf_eq`** (`R = stepFun T`), **`stepField_taylorOf_eq`** (`X_R = taylorXR X` on `D(s,r)`), **`stepTaylor_fieldBound`** (`HomFieldBound_gen r (3ε) T`) | `taylor` (i), (ii), (iii) (iv from `taylorXR_remainder_128` + `stepField_taylorOf_eq`) |
| `KamStep/NewHamTransport.lean`, `ParamIntegral.lean`, `NewHamLip.lean`, `NewHamIntegral.lean` | **`hasFDerivAt_comp_flow_smooth`** (the field of `Gf∘φ^t` is `y` with `y + N_t(w) y = Zg(φ^t w)`, `N_t = DΨ^t∘ι`, lies in the `p_+` target `G`); `transSolve`, `transSolve_spec/unique`, `differentiableAt_transSolve_apply`; `riemannSum`, `tendstoUniformlyOn_riemann`, **`smoothing_integral`** (integral of a holomorphic smoothing family, Lipschitz in `t`, is holomorphic with field the integral of the fields; via `holomorphic_of_tendstoUniformlyOn`); time-Lipschitz bounds `norm_smoothDisp_time_sub_le`, `norm_flow_time_sub_le`, `norm_fderiv_smoothDisp_time_sub_le`, `norm_transSolve_le`, `norm_transSolve_sub_le`, `norm_yfam_time_sub_le`; **`newHam_integral_smoothing`** (`w ↦ ∫₀¹ g_t(φ^t w)dt` is a smoothing Hamiltonian with field `∫₀¹ (1+N_t)⁻¹ Zg_t(φ^t w) dt`) | `new-ham` (ii), steps `n-field`, `flow-calc` (iv) |
| `KamStep/StepMargin.lean`, `StepBracket.lean`, `StepPlusClass.lean`, `StepPlusFinal.lean`, `StepPlusA.lean`, `StepPlusAssemble.lean` | `stepDomain_U_margin` (`B(w,σ/8) ⊆ D(s-2σ,r/2)` for `w ∈ D(s-3σ,r/4)`); concrete `stepN_bound` (`‖N_t(w)‖ ≤ 1/128`); bracket `stepBrG/stepBrZ` on `U` (derivative `B(ι stepBrZ,·)`, holomorphy, Cauchy bounds `‖stepBrZ‖ ≤ 4eM/σ`, `|stepBrG| ≤ (4π+1)r²eM`); commutator family `stepGfam/stepZgfam` with all hypotheses of the engine; **`stepPlus_integral_smoothing`**; `stepPS`, `stepPS_hasFDerivAt`, **`stepPlusA_smoothing`** (`(P-R)∘Φ`); `stepPplusS`, `stepXplusS` and **`stepPlus_isSmoothing`**: `(P_+,X_+) ∈ 𝒮_{p_+}(D(s-5σ, ηr))` with `P_+ = (P-R)∘Φ + ∫₀¹{R(t),F}∘φ^t dt`, `X_+ = (1+N_1)⁻¹(X_P-X_R)(Φ w) + ∫₀¹(1+N_t)⁻¹ Zg_t(φ^t w)dt` | `new-ham` (ii) (class membership), `commutator` (Cauchy), `pullback` (class) |
| `KamStep/PullbackAbstract.lean`, `PullbackNu.lean`, `StepLip.lean`, `StepPullbackBound.lean`, `StepNuIntegral.lean`, `StepCtx.lean`, `TaylorLinear.lean`, `StepPlusBound.lean`, `StepPlusArith.lean` | inverse-free seminorm pull-back estimates (`seminorm_solve_le/_sub_le`); `stepNu`, `stepNu_transNop_le/_sub_le`, `stepPullback_sup/_sub`; `kamNorm_lipschitz_small` (Cauchy at scale `ηr`); **`stepPullback_bounds`** (`ν(y₁) ≤ 2Y₀`, `ν(y₁-y₂) ≤ 2(Y_d + (2Y₀/σ)η⁻²2N₁) + 4η⁻²(16N₁/σ)Y₀`); `stepNu_integral_sub_le`; `StepCtx`; `taylorXR_sub`; `stepXplusA_bounds`, `stepXplusB_time_bounds`, `stepYfam_time_lip`, `stepXplusB_bounds`, **`stepXplus_pair_bound`** (sup and two-parameter bound of `X_+ = y_A + ∫y_t`); `stepBrZ_sub_norm_le` (two-parameter commutator); **`stepXplus_arith`** (`S + λD ≤ 896ηε + 168 ε M_F/(ση²)`, the blueprint constants `7·128`, `7·24`) | `pullback`, `commutator`, `new-ham` (ii) bound, step `st-1`, `st-2` |

## Session 2 summary
Landed: the abstract flow calculus (smoothing, variational equation, symplecticity, Cauchy bounds with the step
constants, equivariance) and external W5-E1; the W4 audit fixes F1/F2 (see `W4-HOMOLOGICAL-handoff.md`, Round 2; commit
`7155ce2c`). The flow results are abstract (`ι : G →L F`, `Z : F → G`); instantiating `F = StepPhase r`,
`G` = the `p_+` representatives with `ι = kamEmbed` and `Z = X_F` needs the concrete `F` (open, below).

## Not done
* `w4-modified` (i), (ii), m-act (operator estimate for `∂_θ Q_F : ℓ_p → ℓ_{p_+}`), the modified `Q`-division; only the
  lattice constant (iii) is done. Design: the `p_+`-weighted matrix of `Q_F` is the Hadamard image of the `p+1`-matrix
  with multiplier `d'_{ij} = I^{-c} d_{ij}` (`c = p+1-p_+`, `I = i+2`); `HomHadamardBound` applies with
  `|d'_{ij}| ≤ A_k/(α̂|i-j|)` since `β ≤ c`.
* `taylor` (Lemma Taylor: components of `R`, scaling `S_t`, Cauchy estimates, constants 3 and 128).
* `solve` proper (the objects `F, N̂, â₀` for the Taylor polynomial and the field/λ-bounds; only constants done),
  `flow` (ii): `|φ^t - id|^λ ≤ 2M_F` and derivative bounds (Cauchy on balls); the existence/holomorphy/Lipschitz-in-ξ
  conclusions follow from the landed lemmas applied through `stepFlowHyp` but the `p_+`-smoothing and the λ-norm
  statements are not written; reality/equivariance (iv).
* `flow-calc`: all items are done abstractly (continuity, variational equation, symplecticity, inverse, transport, time derivative, skewness). Open: the instantiation on `StepPhase r` (`B = stepSymp` between the `p_+` and `p` weights, `ι = kamEmbed`, `Z = X_F` with `F ∈ C²` from its polynomial form), holomorphy of `w ↦ Dφ^t(w)⁻¹ X_G(φ^t w)` into the `p_+` target, and the time derivative for `N` via W4 Lie (iv).
* `taylor`: the estimates (iii), (iv) are done for `taylorXR`; open: parts (i), (ii) (that `taylorXR` is the field of the Taylor polynomial `R` and `R ∈ 𝒯_s`, with the `z,\bar z` component formulas, `H` symmetry via E3), reality/periodicity.
* `new-ham`: only the scalar expansion core is done; the bracket field `[X_G,X_F]`, the field of `P_+` and the weak conjugacy (iii) are open. `pullback`/`commutator`: only the abstract cores/arithmetic; applying them needs the flow derivative bounds (Cauchy on balls). The step theorem `bpW:w5:step` (i)–(v). No Lean statement of `bpW:w5:step` exists.
  The arithmetic closing it is `stepEstimate_arith`; the analytic content of (i), (ii), (v) is missing.
* Action–angle and initial perturbation were out of scope (need W3).

## Design notes
* `FamBound`/`IsSmoothing` in `Class.lean` are the setting for λ-norms and smoothing Hamiltonians.
* Carrier of the flow: `StepPhase r` with fields at weight `p` (norm `|·|_{p,r}`); smoothing is expressed by the
  weight of the representative.
* Lean pitfalls: `Π`, `α₊`, `ω₊` are not valid identifiers; `U` must live in `StepPhase r` (use
  `stepDomain r (s-2σ) (r/2)`, not `stepDomain (r/2) …`); `nlinarith` in big contexts needs split-out facts.

## Blueprint defects / deviations
* Omega bound: `(4π+1)r²` proved (stronger than the blueprint's `(4π+2)r²`).
* `stepImage_mem` needs `σ ≤ 1` (the blueprint step `f-image` uses the numerical smallness only); harmless since
  `σ ≤ 1/4` in step data.

## Session 4 (partial)
Landed `KamStep/StepCLM.lean` (builds with `w_build.sh`, default heartbeats; `w_lint.sh` not re-run). It gives the
concrete `B = stepSympCLM` and `ι = stepEmbedCLM` on `F = G = StepPhase r` (the weight lives in the representatives, so
one carrier serves both). Still needed for step 1 (instantiation): a function `taylorFun T : KamPhase → ℂ` and field
`taylorField T : KamPhase → KamPhase` for `T : HomTaylor_gen`, via `u=(z+z̄)/√2`, `v=(z-z̄)/(i√2)` (`homU`, `homV`,
`homRu_gen`, `homRv_gen`), with `DF·W = ϖ(X_F, W)` and holomorphy of `X_F` into the `p_+` target; only then do the
abstract flow results specialise. Steps 2-6 of the order above are untouched; `bpW:w5:step` is NOT proved and
`.drafts/READY-W5-STEP` was deliberately NOT written (not done, not blocked).

## Session 4, item 1 (concrete instantiation on `StepPhase r`) — DONE
Deviation: `ι` is `stepEmbedCLM` built from W4's `homEmbed_gen` (Dirichlet labels `j+2`), NOT W1's `kamEmbed`
(label `j`): the W1 embedding would not satisfy `ϖ_{p,p}(ιX,W)=ϖ_{p,p_+}(X,W)`. `StepPhase r` carries both `F` and `G`.
The abstract flow results (`holoFlow_smooth_eq`, Cauchy bounds, `isUnit_fderiv_holoFlow`, transport, bracket) now
apply to `X = smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb T r)` via `stepFlowHyp_concrete` and
`stepFieldS_skew`, with `B = stepSympCLM (q:=p) (q':=p)`.

## Session 4, item 3 (solve proper, UNMODIFIED case) — DONE except the Taylor identification
`stepSolve_fam`/`stepNhat_fam`/`stepSolve_equation`/`stepFun_isSmoothing` give, for any family `R_ξ ∈ 𝒯_s` with
`HomFieldBound` (the output of the Taylor lemma), the solve outputs of `bpW:w5:solve`. The family `F_ξ` is a parameter with
the specification `F ξ = homSolveTaylor_gen … (R ξ)`. Not yet done: the identification of `R = Taylor polynomial of P`
(`bpW:w5:taylor` (i),(ii): an `R : HomTaylor_gen` with `stepField R = taylorXR X_P`), and the frequency-hat bounds
`|ω̂| ≤ 6πε`, `Ω̂` from `homNhat_coeff_bounds_gen` (available in W4, assembled in the step theorem).
Order deviation: items 2 (w4-modified) was NOT started; the unmodified chain is being completed first because the
core analytic argument (new-ham, pullback, step) is shared and `w4-modified` only changes the supplier of the solve outputs.
Design note for w4-modified: `F` is `homSolve` of `R`'s `(p+1)`-representatives with the multipliers `ratio_i * d_ij`
(`ratio_i = ω_{p_+}(i)/ω_{p+1}(i)`), cp/cm/P/P' with `ratio_i`-twisted multipliers; bounds need a modified copy of
`LemmaOneBounds/LemmaOneLipBounds` (dQ from the operator norm, `m-act`).

## Session 4, new-ham (i) along the flow — DONE (abstract in `F`); instantiation pending
`stepNewHam_flow_H` closes `new-ham` (i) at the level of functions. To instantiate on `StepPhase r`: functions
`N := stepNfun ∘ toK` (derivative `stepNfun_hasFDerivAt`), `R := stepFS R`, `N̂ := stepFS (homNhatTaylor_gen R)` (derivative
from `stepFS_hasFDerivAt`: `ϖ(ι X_·, ·)`), `heq` from `stepSolve_equation` with `V = D(s-σ,r)`; continuity of the brackets along
the trajectory from continuity of the fields (`continuousOn_holoFlow_time`).
## State at the end of session 4 (bpW:w5:step NOT proved; READY file NOT written)
Done: item 1 (instantiation), unmodified solve outputs, `N` and the Lie identity, `H∘Φ` expansion along the flow.
NOT done: `w4-modified` (item 2), `taylor` (i),(ii) (the `R ∈ 𝒯_s` identification `stepField R = taylorXR X_P`),
`new-ham` (ii) (field of `P_+`: transport of `P-R` and of the brackets `{R(t),F}` with holomorphy of
`w ↦ Dφ^t(w)⁻¹X_G(φ^t w)` into the `p_+` target) and (iii) (weak conjugacy), the concrete application of
`stepPullback_*` and `stepCommutator_arith` (Cauchy bounds on balls `D(s-3σ,4ηr)`), and the statement and proof of
`bpW:w5:step` (i)-(v). No blueprint defect and no default-heartbeat failure was found, so neither stop condition
(a) nor (b) of the owner's instruction holds; the work stopped for lack of capacity in this session, not on a blocker.
Lint: `w_lint.sh` run after the first three modules of this session (exit 0, only line-length notices for lines
> 100 chars in TaylorFun*.lean, StepFlowConcrete.lean, StepFieldBound.lean, StepCLM.lean, to be wrapped); `KAM.lean`
is regenerated at landing.

## Session 4, Taylor (i),(ii) — DONE (reality of R not yet derived)
`stepTaylorOf` builds `R ∈ 𝒯_s` from a smoothing pair `(P,X)` on `D(s,r)` with `P` angle-periodic and `|X|_r ≤ ε`; it satisfies
`stepFun R = taylorRv P`, `stepField R = taylorXR X` on `D(s,r)` and W4's field bound `3ε`. Key new infrastructure:
`differentiableOn_fderiv_of_holomorphic` (the derivative of a holomorphic map on a Banach space is holomorphic; proved by
slice analyticity in finitely many variables plus Cauchy remainder estimates; no such lemma existed in W1/Mathlib).
Open for `taylor`: reality (`P` real ⇒ `R` real; needed only for the reality clauses of the step theorem).

## Design plan for new-ham (ii),(iii) + pullback/commutator application (recorded before implementation)
Setting: `F = G = StepPhase r`, `ι = stepEmbedCLM`, `Z = stepFieldS T`, `X = smoothField ι Z`, `Dφ^t(w) = I + ι∘DΨ^t(w)`
(`fderiv_holoFlow_smooth`). Transport is formulated through `N_t(w) := DΨ^t(w)∘ι : G →L G` (`‖N‖ ≤ 1/8`-type bounds, holomorphic in `w`
by `differentiableOn_fderiv_of_holomorphic`): the field of `Gf∘φ^t` is `y` with `(1+N_t(w)) y = Zg(φ^t w)` (then `A⁻¹(ιZg)=ιy`).
Estimates need no inverse series: `‖y‖_{ηr} ≤ 2‖u‖_{ηr}` from `‖N y‖_{ηr} ≤ ½‖y‖_{ηr}` (`kamNorm_le_ratio_sq`, monotonicity of
`kamNorm` in the radius), and for two parameters `(1+N_ζ)(y_ξ-y_ζ) = u_ξ-u_ζ-(N_ξ-N_ζ)y_ξ`. P_+ := (P-R)∘Φ + ∫₀¹{R(t),F}∘φ^t dt as a function;
its field is `y_1(P-R)` plus the `t`-integral of `y_t([X_{R(t)},X_F])`, differentiation under the integral as in `hasFDerivAt_smoothDisp`.
The bracket field uses `hasFDerivAt_bracket` with `DZ` (G-valued) so the bracket lies in the `p_+` target.

## Session 4, new-ham (ii): abstract engine DONE; instantiation and estimates pending
Done in the abstract setting (`F, G, ι, Z, B`): transport of smoothing Hamiltonians by the flow, with the field in the `p_+` target;
the `t`-integral of a Lipschitz-in-`t` family (`newHam_integral_smoothing`). Remaining for new-ham (ii): (1) the bracket family
`g_t = B(ιZ_{R(t)}, ιZ)`, `Zg_t = DZ_{R(t)}(ιZ) - DZ(ιZ_{R(t)})` from `hasFDerivAt_bracket` and the skewness of `X_{N̂}`, `X_R`
(both are `stepFun` of Taylor elements: `stepFieldS_skew`); (2) the margins `‖N_t(w)‖ ≤ q` from the Cauchy bound `norm_fderiv_smoothDisp_le`
on `D(s-3σ, r/4)`; (3) `P_+ := (P-R)∘Φ + ∫…` class membership; (4) the `λ`-bounds (pullback/commutator, seminorm version of
`norm_transSolve_sub_le` at the scale `ηr`); (5) (iii) weak conjugacy.

## Session 4, new-ham (ii) class membership — DONE (`stepPlus_isSmoothing`)
Statement: for a smoothing pair `(P,X)` on `D(s,r)`, `R = T ∈ 𝒯_s`, `F = FT ∈ 𝒯_{s-σ}` with `HomFieldBound` constants
`e₁` (T), `2e₁` (N̂), `Mf ≤ σ/1024` (F), `5σ < s`, `0 < η ≤ 1/8`: `(P_+, X_+)` is a smoothing pair on `D(s-5σ, ηr)` in the
weights `(p_+, p)`. Still open: the `λ`-bounds for `X_+` (pull-back and commutator estimates at the scale `ηr`, two-parameter
Lipschitz parts), periodicity/reality of `P_+`, (iii) weak conjugacy, and the concrete instantiation of `stepNewHam_flow_H`.

## Session 4, pullback/commutator on the concrete flow — pair bounds DONE; wiring into the step theorem pending
`stepXplus_pair_bound` + `stepXplus_arith` give the `λ`-bound `|X_{P_+}|^λ_{ηr,D_+} ≤ 896ηε + 168 ε M_F/(ση²)` once
the inputs are fed: `Mf := M₀` (sup of `X_F`), `N₁ := M₁ d` (Lipschitz of `X_F`, `M₀ + λM₁ ≤ M_F`), `e₁ := 3ε₀`, `Δ₁ := 3ε₁ d`,
`Y₀ := 128ηε₀`, `Y_d := 128ηε₁ d` (Taylor (iv) for `X_P` and for the difference via `taylorXR_sub`).
Coordination: `w4-modified` (i)-(iii) incl. `m-act` is being done by a second prover (branch `inp-wpq`, files `KamStep/Modified*.lean`);
this session does NOT touch it. The step theorem is proved first for the non-modified case; the modified case will consume the
`w4-modified` result by its blueprint statement once merged.

## Session 4, λ-bound of X_+ for a pair — DONE (e57b9d44), `zeroTaylor` (5459435c)
`StepPlusLam.lean`: `stepSplus`, `stepDplus`, `stepPlus_pair_lamBound` (sup bound `stepSplus ε₀ M₀ η σ`, difference bound
`stepDplus ε₀ ε₁ M₀ M₁ η σ · d` for `ν_{ηr}(X_+)`), with `stepSplus + λ·stepDplus ≤ 896ηε + 168εM_F/(ση²)`.
`ZeroTaylor.lean`: `zeroTaylor` (the element `0 ∈ 𝒯_s`, value of parameter families outside `Π`).
Next: package with the F-family data (`FamBound`), concretize new-ham (i), (iii), then clauses (iii)-(v) of the step theorem.

## Session 4, `stepPlus_famBound` (StepPlusFam) and new-ham (i) concrete (NewHamConcrete) — DONE
`stepPlus_famBound`: `FamBound` of `X_+` on `D(s-5σ,ηr)` at scale `ηr` with constant `896ηε + 168εM_F/(ση²)`; the family of
Taylor elements is `stepTaylorFam` (`stepTaylorOf` on `Π`, `zeroTaylor` off it). `stepNewHam_concrete`: for `w ∈ D(s-5σ,ηr)`,
`N(Φw)+P(Φw) = N w + N̂ w + â₀ + P_+(w)` with `P_+ = stepPplusS`-integrand form; hypotheses: the homological equation on the strip
`T_{s-σ}` in the form of `stepSolve_equation`, `Mf ≤ σ/1024`. `N_+ = N + N̂` stays a sum of functions (identification with
`ω+ω̂, Ω+Ω̂` is part of clause (iii), pending).
Pending: weak conjugacy (iii), reality/periodicity of `P_+`, clauses (iii)–(v) of the step theorem, `bpW:w5:step` statement.
