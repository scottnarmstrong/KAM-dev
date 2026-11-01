# W5-AA handoff (in progress)

Branch `inp-w5aa` (worktree `/root/code/KAM-inp-wpj`), from the integrated W5 head `a7414cf7`. Package W5-AA:
blueprint `bpW:w5:action-angle`, `bpW:w5:initial` (`blueprint-W/parts/w5-kamstep.tex`), plus the added item
W5-STEP-A-FIX (below). No existing KamStep file was edited.

Build note: the worktree lacked the oleans of `KAM/Wave/Birkhoff` (and other unchanged directories); they were
copied (no-clobber) from main's build snapshot `/root/code/KAM/.lake/build` (identical sources; the traces differ
only in absolute paths), instead of rebuilding them.

## Progress (W5-AA proper)

Done (each module builds with `w_build.sh`, default heartbeats, no `sorry`):
- `KAM/Wave/KamStep/ActionAngle.lean`: `aaSqrt`, `aaShift`, `aaNormal`, `aaTanCoord`, `aaMap a p ξ w` (= `𝒜_ξ(w)` in
  weighted coordinates of `𝔚_{a,p}`), `aaDomJ`; (i): `aaMap_differentiableOn` (joint in `(ξ,w)`), `isOpen_aaDomJ`,
  `aaMap_add_tau`, `aaMap_real`, `aaMap_linearTorus` (`birkZinv (aaMap 1 1 ξ (θ,0,0,0)) = birkReal (linearTorus ξ hξ θ)`).
- `ActionAngleDomain.lean`: (ii) `aaCA = 2200`, `aaMap_domain`, `aaMap_mem_ball`, `aaMap_mem_birkBall1`; (vi)
  `aaNormal_norm_le`, `aaNormal_norm_ge`, `norm_sq_aaMap`.
- `ActionAngleDeriv.lean`: (iii) `aaDer a q ξ w`, `hasFDerivAt_aaMap`, `aaDerInv`, `aaDerInv_aaDer`, `aaDer_aaDerInv`.
- `ActionAngleSymp.lean`: (iii) `birkOmegaMix`, `aaDer_symp` (`Ω(D𝒜W, D𝒜W') = ϖ_{q,q'}(W,W')`, `q+q' ≥ 0`),
  `birk_tsum_tan_nor`.
- `ActionAngleNormal.lean`: (iv) `aaEnergy`, `aaOmega0`, `aaOmegaN0` (= `waveFreqTan`, `waveFreqNor` for real `ξ`),
  `aaZZ`, `aaNfun`, `aaQt`, `aaKext`, `aaXKext`, `aaPfun`, `aaMap_normalForm`.
- `ActionAngleQt.lean`: (v) the field of `Q̃`: `aaSfun`, `aaBq`, `aaXQt`, `aaQt_hasFDerivAt`.
- `ActionAngleField.lean`: (v) `aaXP` (`X_{P_ξ}`), `hasFDerivAt_comp_aaMap` (chain rule, step `a-field`),
  `aaP_isSmoothing_of` (helper, any open `V`), **`aaP_isSmoothing`** (`a=p=1`, `D(s,r)`), `aaPfun_real`, `aaPfun_add_tau`.
- `InitialBound.lean`: `aaEpsIn`, `kamNorm_aaXQt_le` (i-q), `kamNorm_aaDerInv_normal_le` (i-g), `kamNorm_aaDerInv_le`
  (i-k), `kamNorm_aaXP_le`.
- `Initial.lean`: `differentiableAt_aaXP_param`, `aaXP_lipschitz` (i-par), **`initialPerturbation`** (`bpW:w5:initial`).

Open (in progress): (v) the conjugacy identity `X_{H'}(𝒜w) = D𝒜(w)(X_N + X_P)` in `𝔚^{p-1}`.

## W5-STEP-A-FIX (findings F1, F2 of `W5-STEP-A-audit-1.md`)

New modules (no existing file edited): `KAM/Wave/KamStep/FlowCalcJoint.lean`, `KAM/Wave/KamStep/FlowCalcOnto.lean`.

### AUDIT FOCUS

**F1 (`bpW:w5:flow-calc` (i), `w5-kamstep.tex:431`, step `c-cont`): joint continuity.** For
`h : FlowHyp X V U M δ` (`[CompleteSpace F]`), no further premise:
- `FlowCalcJoint.lean:79` `continuousOn_holoFlow_joint :
  ContinuousOn (fun x : ℝ × F => holoFlow X x.1 x.2) (Icc (-1 : ℝ) 1 ×ˢ U)`.
- `FlowCalcJoint.lean:96` `continuousOn_fderiv_holoFlow_joint :
  ContinuousOn (fun x : ℝ × F => fderiv ℂ (holoFlow X x.1) x.2) (Icc (-1 : ℝ) 1 ×ˢ U)`.
- Helper `FlowCalcJoint.lean:40` `continuousOn_jointOfLocLip`: continuity on `I ×ˢ U` from continuity in `t` at each
  `w ∈ U` and a local Lipschitz bound in `w` uniform in `t ∈ I` (both are proved, not assumed, for the flow).
  The uniform Lipschitz bounds: mean value inequality with `‖Dφ^t‖ ≤ e^{M/δ}` (`norm_fderiv_holoFlow_le`) for
  `φ^t`; the Cauchy estimate `norm_fderiv_sub_le_holoMargin` with `‖φ^t z‖ ≤ ‖w₀‖ + 2ρ + M` on `ball w₀ (2ρ) ⊆ U`
  for `Dφ^t`. Time continuity: `continuousOn_holoFlow_time` (W1), `continuousOn_fderiv_holoFlow_time`.

**F2 (`bpW:w5:flow-calc` (iii), `w5-kamstep.tex:434`): `Dφ^t(w)` maps `𝒫^{p_+}` onto `𝒫^{p_+}`.** The target is
kept as the representative space `G` with inclusion `ι` (concretely `stepEmbedCLM a p pb hpb r`), never identified
with `𝒫`.
- Abstract (`FlowHyp (smoothField ι Z) V U M δ`, `Z` holomorphic and `‖Z‖ ≤ M` on `V`, `‖ι g‖ ≤ ‖g‖`,
  `‖DΨ^t(w)‖ < 1`, `w ∈ U`, `t ∈ [-1,1]`):
  `FlowCalcOnto.lean:51` `fderiv_holoFlow_smooth_targetUnit : ∃ T : (G →L[ℂ] G)ˣ, ∀ g,
  fderiv ℂ (holoFlow (smoothField ι Z) t) w (ι g) = ι (T g)` (target inverse; both inverse identities are those of
  the unit `T = I + DΨ^t(w) ∘ ι`, Neumann series);
  `FlowCalcOnto.lean:70` `fderiv_holoFlow_smooth_image_range :
  fderiv ℂ (holoFlow (smoothField ι Z) t) w '' range ι = range ι`.
- Concrete, flow of `X_F` on the small domain `w ∈ D(s-3σ, r/4)`, every `t ∈ [-1, 1]` (hypotheses those of
  W5-REAL's `stepFlow_dPhi_smooth_onto`: `0 ≤ a`, `0 ≤ p`, `p ≤ pb`, `0 < σ ≤ 1`, `3σ < s`, `FT ∈ 𝒯_{s-σ}`,
  `HomFieldBound_gen … r Mf FT`, `0 < Mf ≤ σ/1024`):
  `FlowCalcOnto.lean:119` `stepFlow_dPhi_targetUnit` (the unit `T` on `StepPhase r`, `ι = stepEmbedCLM`),
  `FlowCalcOnto.lean:134` `stepFlow_dPhi_image_range : fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
  (stepFieldS ha hp hpb FT r)) t) w '' range (stepEmbedCLM a p pb hpb r) = range (stepEmbedCLM a p pb hpb r)`.
  `FlowCalcOnto.lean:88` `stepFlow_dPhi_data` packages the hypotheses (the same derivation as in
  `stepFlow_dPhi_smooth_onto`, which already held for all `t ∈ [-1,1]`; the W5-REAL `t = 1` instances
  `StepCore.dPhi_smooth_onto` are special cases, not duplicated).
- `#print axioms` (all four main declarations above): `[propext, Classical.choice, Quot.sound]`.
- Checks: `w_build.sh … KAM.Wave.KamStep.FlowCalcJoint KAM.Wave.KamStep.FlowCalcOnto`: `Build completed
  successfully`.

## W5-STEP-B-FIX (findings F1, F2, notes, rulings D2/D3 of `W5-STEP-B-audit-1.md`)

New modules: `KamStep/StepPsi.lean`, `KamStep/StepDivisorsW.lean`, `KamStep/StepOmegaBridge.lean`. Edited
(allowed by the orchestrator for this item): `KamStep/StepTheoremSrc.lean` (source-facing theorems extended; the old
statements kept as helpers `stepTheorem_clauses`, `stepTheoremMod_clauses`), `KamStep/StepTheorem.lean` (stale
docstring only). Source-facing names `stepTheorem`, `stepTheoremMod` are unchanged; their statements now END with six
new conjuncts (all previous conjuncts unchanged, same order): consumers destructuring with exactly 17 components must
add the new ones.

### AUDIT FOCUS

**F1 (clause (v) in `p_+` norms, `w5-kamstep.tex:585-586`).** `StepPsi.lean`:
- `StepCore.Psi` (:145) `= smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS … (FT ξ) r) 1` (values in the
  `p_+`-representatives; no inclusion applied);
- `StepCore.phi_eq_add_Psi` (:162) `Φ ξ w = w + ι (Ψ ξ w)` on `D_+`; `StepCore.fderiv_phi_eq` (:169)
  `DΦ = id + ι ∘L DΨ`; `StepCore.psi_differentiableOn` (:177);
- `stepFlow_bounds_smooth` (:84) and `StepCore.flow_pair_smooth` (:189): `‖Ψ ξ w‖ ≤ M₀`,
  `‖Ψ ξ w - Ψ ζ w‖ ≤ 2(M₁‖ξ-ζ‖)`, `‖DΨ ξ w‖ ≤ 8M₀/σ`, `‖DΨ ξ w - DΨ ζ w‖ ≤ 16M₁‖ξ-ζ‖/σ` (norms of
  `StepPhase r` = `|·|_{p_+,r}` on `p_+`-representatives, and the operator norm `|·|_{p→p_+,r}`), from
  `flowII_disp`, `flowII_disp_sub`, `flowII_deriv`, `flowII_deriv_sub` without `‖ι g‖ ≤ ‖g‖`;
- `StepCore.smooth_clause_v` (:215): `∃ A₀ A₁ B₀ B₁ ≥ 0, A₀+λA₁ ≤ 2M_F, B₀+λB₁ ≤ 16M_F/σ` with the four bounds on `Ψ`.
- In `stepTheorem`/`stepTheoremMod` (`StepTheoremSrc.lean`, new conjunct 5 of the appended six).

**F2 (clause (iv), Dirichlet weight, `w5-kamstep.tex:581-584`).** `StepDivisorsW.lean`: `stepDivisorsW` (:32) (the
subtraction argument of `stepDivisors` with `HomMelnikovW`/`homJapW`; only `homJapW l ≥ 1` is used, no factor 3);
`StepCore.divisorsW` (:100). In the source theorems: appended conjunct 4,
`HomMelnikovW τ α Par ω Ω → … → α' * homJapW l / waveA τ k ≤ |homPairZ k ω_+ + homPairL l Ω_+|`.

**Notes.** Holomorphy of `Φ`: `StepCore.phi_differentiableOn` (`StepPsi.lean:183`), appended conjunct 1. Integer
translations: `shift_int_law` (:43), `kamDomain_sub_tau` (:66), `stepDomain_sub_tauS` (:76),
`StepCore.phi_translate_int` (:201): `Φ(w + (k 0 • τ₀ + k 1 • τ₁)) = Φ w + (k 0 • τ₀ + k 1 • τ₁)` for
`k : Fin 2 → ℤ`, appended conjunct 2. `Ψ` data (holomorphy, `Φ = id + ιΨ`, `DΦ = I + ι DΨ`): appended conjunct 3.
Stale `StepTheorem.lean` docstring fixed.

**D3.** `StepCore.psi_le_MF` (`StepPsi.lean:237`): `‖Ψ ξ w‖ ≤ M_F` on `D_+` (from `‖Ψ‖ ≤ M₀` and
`M₀ + λM₁ ≤ M_F`); appended conjunct 6. The `λ`-clause keeps `2M_F`.

**D2.** `StepOmegaBridge.lean` (not imported by `StepTheoremSrc`; for W6): `stepOmegaTail_reweight` (:47),
`stepOmegaTail_taylorRho` (:57), `StepHypMod.core_R_eq` (:79), `StepHypMod.R1_eq` (:84),
**`StepHypMod.core_OmegaPlus_eq`** (:89) `H.core.OmegaPlus ξ j = Ω ξ j + stepOmegaTail (H.R1 ξ) j`,
`StepHypMod.core_omegaPlus_eq` (:95) `ω_+ = ω + stepOmegaHat (R1 ξ)`, and the `J`-weighted consequences
`StepHypMod.OmegaPlus_tail_bound_J` (:102) `(j+2)^((p+1)-p) |Ω_{+,j}-Ω_j| ≤ 3ε₀`,
`StepHypMod.OmegaPlus_tail_lip_J` (:108) `≤ 3ε₁‖ξ-ζ‖` (from `R1_field`, `R1_sub`). Here `H.core` is the step core
of the `StepHypMod` passed (for the source theorem, `H.hyp`, whose `ε₀, ε₁` are the split `stepE0/stepE1`).

`#print axioms` of `stepTheorem`, `stepTheoremMod`, `StepCore.smooth_clause_v`, `StepCore.divisorsW`,
`StepHypMod.core_OmegaPlus_eq`, `StepHypMod.OmegaPlus_tail_lip_J`: `[propext, Classical.choice, Quot.sound]`.
Builds: `w_build.sh … StepPsi StepDivisorsW StepOmegaBridge StepTheorem StepTheoremSrc`: `Build completed successfully`.
