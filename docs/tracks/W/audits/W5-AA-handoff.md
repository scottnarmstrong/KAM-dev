# W5-AA handoff

Branch `inp-w5aa` (worktree `/root/code/KAM-inp-wpj`), from the integrated W5 head `a7414cf7`. Package W5-AA:
blueprint `bpW:w5:action-angle`, `bpW:w5:initial` (`blueprint-W/parts/w5-kamstep.tex`), plus the added item
W5-STEP-A-FIX (below). No existing KamStep file was edited.

Build note: the worktree lacked the oleans of `KAM/Wave/Birkhoff` (and other unchanged directories); they were
copied (no-clobber) from main's build snapshot `/root/code/KAM/.lake/build` (identical sources; the traces differ
only in absolute paths), instead of rebuilding them.

## Status: COMPLETE (both labels proved; W5-STEP-A-FIX and W5-STEP-B-FIX done)

Labels: `bpW:w5:action-angle` (i)-(vi), `bpW:w5:initial`. 11 new modules under `KAM/Wave/KamStep/`
(`ActionAngle*`, `Initial*`), each < 450 lines, default heartbeats, no `sorry`/axiom/option override.

### AUDIT FOCUS (W5-AA proper)

Conventions. `𝒫 = KamPhase` (normal components: representatives at weight `p`, Dirichlet labels `j+2`);
`𝔚 = BirkSpace` in weighted coordinates at `(a,p)`; `ξ : Fin 2 → ℂ` (real parameters enter as
`aaOfReal ξ = fun i => (ξ i : ℂ)`); `√ = aaSqrt` (`ζ^(1/2)`, principal `cpow`). Total maps (`aaMap`, `aaDer`, …)
are only *used* on `Re(ξ_i + y_i) > 0` (and `𝒜_ξ(w) ∈ B_{ρ₁}`), as hypotheses of every theorem.

- **(i)** `ActionAngle.lean`: `aaMap a p ξ w` (:172, `= aaTan + aaNormal`; coordinates `birkCoord_aaMap_tan`,
  `aaMap_nor_true/false`); `aaMap_differentiableOn` (:264, joint in `(ξ,w)` on `aaDomJ`, `isOpen_aaDomJ` :177);
  `aaMap_add_tau` (:299); `aaMap_real` (:326, real `ξ`, `StepReal w`, `ξ_i + Re y_i > 0` ⇒ `ϱ𝒜w = 𝒜w`);
  `aaMap_linearTorus` (:373, `a=p=1`: `birkZinv (aaMap 1 1 ξ (θ,0,0,0)) = birkReal (linearTorus ξ hξ θ)`).
- **(ii)** `ActionAngleDomain.lean`: `aaCA = 2200` (:41); `aaMap_domain` (:174): `s ≤ 1/8, r>0, t>0, ‖ξ‖ ≤ t,
  2r² ≤ Re ξ_i, w ∈ D(s,r)` ⇒ `r² < Re(ξ_i+y_i)` and `‖𝒜w‖² < c_A(t+r²)`; `aaMap_mem_ball` (:216),
  `aaMap_mem_birkBall1` (:223, under `c_A(t+r²) < ρ₁(m)²`). Numerics: `2(e²+4e⁴)e^{π/2} ≤ 2199` (`aaTan_const_le`).
  The blueprint premise `0 < s` is not needed and omitted.
- **(iii)** `ActionAngleDeriv.lean`: `aaDer a q ξ w` (:100) = `D𝒜_ξ(w)` on `q`-representatives;
  `hasFDerivAt_aaMap` (:188, at `q = p`); `aaDerInv` (:249, the blueprint's inverse formulas);
  `aaDerInv_aaDer` (:278), `aaDer_aaDerInv` (:315) (bijection `𝒫^q → 𝔚^q` for every `q`).
  `ActionAngleSymp.lean`: `birkOmegaMix a q q'` (:36, `Ω` between weights; `= birkOmega` for `q=q'`,
  `birkOmegaPlus_eq_birkOmegaMix`), `aaDer_symp` (:167): `Ω(D𝒜W, D𝒜W') = stepSymp (q) (q') W W'`, `q+q' ≥ 0`.
- **(iv)** `ActionAngleNormal.lean`: `aaEnergy` (:48), `aaNfun` (:64) (`aaOmega0`, `aaOmegaN0`, `aaZZ = z_j z̄_j`),
  `aaQt` (:68), `aaKext` (:78, W3's `K` extended by 0), `aaPfun` (:93); `aaMap_normalForm` (:215):
  `birkLambda + birkHamBar + birkHamNor + birkK ⟨𝒜w,h⟩ = aaEnergy ξ + aaNfun ξ w + aaPfun ξ w`.
  `aaOmega0_ofReal` (:104), `aaOmegaN0_ofReal` (:113): `= waveFreqTan`, `waveFreqNor` for real `ξ`.
- **(v)** `ActionAngleQt.lean`: `aaXQt` (:100), `aaQt_hasFDerivAt` (:210). `ActionAngleField.lean`:
  `hasFDerivAt_comp_aaMap` (:99, step `a-field`), `aaXP` (:117) `= X_{Q̃} + aaDerInv a (p+1) ξ w (X_{G^nor}(𝒜w) +
  X_K(𝒜w))`; `aaP_isSmoothing_of` (:162, helper on any open `V` with the domain conditions);
  **`aaP_isSmoothing`** (:209, `a=p=1`, `IsSmoothing (p:=1) (pb:=1+1) … (kamDomain s r) (aaPfun ξ) (aaXP ξ)`);
  `aaPfun_add_tau` (:227), `aaPfun_real` (:236). `ActionAngleGbar.lean`: `birkCoord_birkHamBarX_tan` (:217),
  `_nor` (:226) (coordinates of `X_Ḡ`, via `DḠ(w')e_{-l}` along complex lines). `ActionAngleConj.lean`:
  `aaXN` (:81, `X_N` in `(p-1)`-representatives), **`aaConjugacy`** (:125):
  `birkXLam (𝒜w) + birkEmbed a (p+1) (p-1) (X_Ḡ + X_{G^nor} + X_K)(𝒜w) = aaDer a (p-1) ξ w (aaXN ξ w +
  kamHomEmbed a (p-1) (p+1) (aaXP ξ w))`. Deviation (proof route only): the identity is proved coordinatewise
  instead of through derivatives and nondegeneracy; the statement is the blueprint's.
- **(vi)** `aaNormal_norm_le` (`ActionAngleDomain.lean`:70), `aaNormal_norm_ge` (:77) (`‖ŵ‖ ≤ ‖u‖+‖v‖ ≤ √2‖ŵ‖`);
  `‖x‖_E ≤ ‖𝒵x‖ ≤ √2‖x‖_E` is W3's `norm_le_norm_birkZ`, `norm_birkZ_le`. The "no weight conversion" remark is
  structural (`homWt a q j = ellWeight a q (j+2)`; `aaNormal` is weight-free).
- **`bpW:w5:initial`** `InitialBound.lean`: `aaEpsIn m r t` (:38) `= (1+2C_*)r² + 66C_*C_F(c_A(t+r²))^{5/2}(3/r +
  2√(t+r²)/r²)`, `C_* = waveCubicConst 1`, `C_F = birkCF m 1`; `kamNorm_aaXQt_le` (:263, i-q `≤ r²`),
  `kamNorm_aaDerInv_normal_le` (:103, i-g), `kamNorm_aaDerInv_le` (:119, i-k), `kamNorm_aaXP_le` (:374,
  `|X_{P_ζ}(w)|_{2,r} ≤ ε_in`). `Initial.lean`: `differentiableAt_aaXP_param` (:103), `aaXP_lipschitz` (:158,
  `4ε_in/ρ_ξ`), **`initialPerturbation`** (:219): hypotheses `s ≤ 1/8, 0<r, 0<t, 0<ρ_ξ`, the `ρ_ξ`-neighbourhood
  condition `hPar`, `c_A(t+r²) < ρ₁²`; conclusions: `IsSmoothing` on `D(s,r)` for `ξ ∈ Π`, periodicity, reality,
  `∀ λ ≥ 0, FamBound Π D(s,r) r λ (ε_in(1+4λ/ρ_ξ)) X_P`, `HomFreqHyp1` with the constants of `homFreqHyp1_wave`
  (for any `B ≥ |⟨b,ξ⟩|` on `Π`), `dist (waveFreqTan ξ) (waveFreqTan ξ') ≤ N_A dist ξ ξ'`. The blueprint premises
  `0 < s` and `r ≤ 1` are not needed and omitted (stronger statement).

### Not done
Nothing of the package. Interfaces left to consumers: the step theorem's `N` (`stepNfun`, real frequencies) is
identified with `aaNfun` only through the frequencies (`aaOmega0_ofReal`, `aaOmegaN0_ofReal`), not as a function
identity; `aaXN` is stated with complex `Ω⁰` (W3/W4's `stepXN` uses real `Ω`).

### Checks
- Builds (all via `w_build.sh`, one module per call): `FlowCalcJoint`, `FlowCalcOnto`, `ActionAngleConj` (pulls all
  `ActionAngle*`), `Initial`, `StepOmegaBridge`, `StepTheoremSrc`: each `Build completed successfully`.
- `w_lint.sh /root/code/KAM-inp-wpj`: exit 0 (`check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`).
- `main_shortname_check.py` on all 16 new modules: `short-name check OK` (after renaming two flagged helpers).
- `KAM/Root/Wave.lean` regenerated by `scripts/gen_root_imports.py`.
- `#print axioms`: `initialPerturbation`, `aaConjugacy`, `aaMap_normalForm`, `aaDer_symp`, `aaP_isSmoothing`,
  `aaMap_linearTorus`, `aaMap_differentiableOn`, `aaMap_real`, `aaMap_add_tau`, `aaMap_domain`,
  `aaMap_mem_birkBall1`, `hasFDerivAt_aaMap`, `aaDerInv_aaDer`, `aaDer_aaDerInv`, `aaPfun_real`, `aaPfun_add_tau`,
  `aaQt_hasFDerivAt`, `kamNorm_aaXP_le`, `aaXP_lipschitz`, `aaNormal_norm_le/ge`, `birkCoord_birkHamBarX_tan/nor`:
  all `[propext, Classical.choice, Quot.sound]`.

### Blueprint defects / deviations
- No blueprint defect found. Omitted unneeded premises: (ii) `0 < s`; initial `0 < s`, `r ≤ 1`.
- (v) conjugacy proved coordinatewise (route deviation; same statement).
- Build note: Birkhoff (and other unchanged) oleans were copied no-clobber from main's build snapshot.

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
- In `stepTheorem` (`StepTheoremSrc.lean`:357) / `stepTheoremMod` (:687): new conjunct 5 of the appended six.

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
