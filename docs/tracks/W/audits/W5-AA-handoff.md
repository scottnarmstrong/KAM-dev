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
