# W5-R2A independent audit 2

Verdict: **PASS WITH NOTES**, restricted to round-2 items 1–2 and the seven named modules. The requested repairs satisfy the available blueprint and round-2 handoff; no new mathematical failure found. Hygiene qualification: prescribed lint exited 1 at its ABI stage because its generated wrapper referenced the parallel wpja5b overlay; ABI verification is not green in this run. This is not a W5-AA audit, a frozen-anchor seal audit, or an acceptance of the full `inp...HEAD` branch.

## Identity, authority, scope

- Worktree: `/root/code/KAM-inp-wpja5` (the supplied `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpja5` resolves here).
- Audited HEAD: `7185220102d1fbbee3c11b78b2f19569818d8a3e`.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, `docs/tracks/W/audits/W5-R2-handoff.md`, and the STEP-A-FIX/STEP-B-FIX sections of `W5-AA-handoff.md`.
- Compared `git diff inp...HEAD`; substantive review restricted to `git diff a7414cf7..HEAD --` the seven modules below, as directed. ActionAngle*, Initial*, and the substantive StepTheoremMod implementation are excluded.
- **Documentation limitation:** `docs/tracks/W/audits/W5-R2A-handoff.md`, `W5-STEP-A-audit-1.md`, and `W5-STEP-B-audit-1.md` are absent here and at the corresponding main-worktree paths. A filename search under `/root/code` also found none. Thus closure of the original findings is assessed against their explicit descriptions in the available R2/producer handoffs and the blueprint, not against unavailable first-round reports. Their unquoted notes cannot independently be certified.
- Controlling focus: `blueprint-W/parts/w5-kamstep.tex`, `bpW:w5:flow-calc` (i),(iii), `bpW:w5:step` (i),(iv),(v), and the D2/D3 requirements as quoted in the producer handoff. D53/D60 authority is the current user instruction; local DECISIONS ends at D51.
- No frozen provider or anchor is supplied by this delta. Frozen-type/seal-body equivalence probes are inapplicable. No claim that `nlw2` is seal-ready.

## Findings and fidelity

### STEP-A F1: joint continuity — PASS

`FlowCalcJoint.lean:80,97` exports continuity on the full product `Icc (-1) 1 ×ˢ U`, including both time endpoints, with values in the original Banach space and its operator space respectively. The only flow premise is `FlowHyp` with completeness. The auxiliary local Lipschitz premise is discharged: the flow uses the uniform derivative bound and a convex ball in U; its derivative uses a uniform bound on the flow on a doubled ball and the Cauchy derivative-difference estimate. Separate time continuity is upgraded to joint continuity, rather than left as the final result. No compactness of U or extra uniformity premise is inserted.

### STEP-A F2: onto the smoothing space — PASS

`FlowCalcOnto.lean:51,70,119,134` keeps the target G and its inclusion ι explicit. The unit is `I + DΨ ∘ ι` in `G →L[ℂ] G`, constructed by the Neumann lemma; its inverse is two-sided in G. The image statement is literally `Dφ '' range ι = range ι`. The concrete theorems discharge the small-derivative premise from the existing field/smallness/margin assumptions on `D(s-3σ,r/4)`, for every `t ∈ [-1,1]`. The abstract helper's norm and derivative premises are explicit helper assumptions, not new source-level premises. Identical representative types are never used to erase ι.

### STEP-B F1: clause (v) in the required norms — PASS

`StepCore.Psi` is the target-valued integral displacement. `phi_eq_add_Psi` and `fderiv_phi_eq` identify the ambient transformation and derivative through the inclusion. Thus `‖Ψ‖` measures `p_+` representatives and `‖DΨ‖` measures the operator from p representatives to `p_+` representatives, despite both being implemented with `StepPhase r`.

`stepFlow_bounds_smooth` obtains the four target bounds directly from `flowII_disp`, `flowII_disp_sub`, `flowII_deriv`, and `flowII_deriv_sub`. The inclusion contraction is used in the flow comparison estimates, but is not used to replace the output target norms by weaker ambient norms. `smooth_clause_v` chooses `(A₀,A₁,B₀,B₁) = (M₀,2M₁,8M₀/σ,16M₁/σ)`; nonnegativity and `M₀+λM₁ ≤ M_F` give exactly `2M_F` and `16M_F/σ`. `psi_le_MF` separately exports the sharper sup bound `M_F`. The λ clause remains `2M_F`.

### STEP-B F2: Dirichlet-weight divisors — PASS

`stepDivisorsW` starts with `HomMelnikovW`, retains `homJapW` in the conclusion, and subtracts the frequency perturbation with the blueprint loss `6π(1+K)(1+K^τ)ε`. It only needs `homJapW ≥ 1`; it never converts from the unweighted Melnikov assumption and loses no factor 3. The core wrapper discharges the frequency sup estimates from its source data. Allowing arbitrary α′ satisfying the loss, rather than additionally requiring positive α′, is a stronger statement.

### STEP-B notes, D2/D3, source-facing assembly — PASS within available focus

- `phi_differentiableOn` supplies complex differentiability on the open D₊; `phi_translate_int` proves the full ℤ² law by positive and negative shifts, with domain invariance proved in both directions.
- `StepOmegaBridge.lean:48–115` identifies the modified core correction with the actual `R1` family at p+1, using coefficient agreement and `homNormalEntry_rho`. The frequency equalities apply to the same `H.core`, not an independently chosen normal form. The J-weighted sup/Lipschitz bounds follow from `R1_field`/`R1_sub`. These exports are on `StepHypMod`; for a source-facing input use `H.hyp`, including its split error bounds. This bridge is not imported into StepTheoremSrc; consumers must import it explicitly.
- `stepTheorem` and `stepTheoremMod` each retain their original 17 conjuncts and append six: holomorphy; integer equivariance; holomorphic Ψ with both identification formulas; weighted divisors; target-norm clause (v); sharp sup bound. A whitespace-normalized comparison against a7414cf7 verified that the renamed `_clauses` helper statements are unchanged. The assembly explicitly reuses all 17 components in their original order.
- `StepTheorem.lean` correctly describes its conditional helpers and points to the source-facing extended results. `WaveStepHyp.Conclusion` becoming protected changes short-name lookup only; its full name and proposition body are retained. The analogous StepHypMod protection is outside the seven-file review and is not reaudited here.
- API note: consumers destructuring exactly 17 components must account for the six appended components, or use the `_clauses` helpers. This is a deliberate strengthening, not a weakening.

## Declaration coverage

Names below are in `KAM.Wave`. Unchanged declarations are listed only to delimit the axiom probe coverage; their mathematics was not reopened.

| Node / area | Declaration | Verdict | Reason |
|---|---|---|---|
| flow-calc (i) | `continuousOn_jointOfLocLip` | PASS | Local uniform Lipschitz helper; discharged in applications. |
| flow-calc (i) | `continuousOn_holoFlow_joint` | PASS | Full joint continuity on [-1,1] × U. |
| flow-calc (i) | `continuousOn_fderiv_holoFlow_joint` | PASS | Joint continuity in the operator norm. |
| flow-calc (iii) | `fderiv_holoFlow_smooth_targetUnit` | PASS | Two-sided unit on the target G. |
| flow-calc (iii) | `fderiv_holoFlow_smooth_image_range` | PASS | Exact image equality for range ι. |
| flow-calc (iii) | `stepFlow_dPhi_data` | PASS | Derives hypotheses and strict derivative smallness. |
| flow-calc (iii) | `stepFlow_dPhi_targetUnit` | PASS | Concrete target inverse for every allowed t. |
| flow-calc (iii) | `stepFlow_dPhi_image_range` | PASS | Concrete image equality for every allowed t. |
| step (i) | `shift_int_law` | PASS | Both integer directions; invariant domain. |
| step (i) | `kamDomain_sub_tau` | PASS | Negative unit shift preserves domain. |
| step (i) | `stepDomain_sub_tauS` | PASS | Representative-space domain preservation. |
| step (v) | `stepFlow_bounds_smooth` | PASS | Four bounds in the target and mixed operator norms. |
| step (i),(v) | `StepCore.flow_data` | PASS | Discharges flow and target holomorphy/bound hypotheses. |
| step (v) | `StepCore.phi_eq_add_Psi` | PASS | Identifies the target displacement via ι. |
| step (v) | `StepCore.fderiv_phi_eq` | PASS | Identifies target derivative via ι. |
| step (v) | `StepCore.psi_differentiableOn` | PASS | Complex differentiability into the target. |
| step (i) | `StepCore.phi_differentiableOn` | PASS | Complex differentiability of Φ on D₊. |
| step (v) | `StepCore.flow_pair_smooth` | PASS | Pairwise parameter estimates in target norms. |
| step (i) | `StepCore.phi_translate_int` | PASS | Full ℤ² translation law. |
| step (v) | `StepCore.smooth_clause_v` | PASS | Totals 2M_F and 16M_F/σ. |
| D3 | `StepCore.psi_le_MF` | PASS | Separate sharp sup bound M_F. |
| step (iv) | `stepDivisorsW` | PASS | Retains homJapW and the exact loss. |
| step (iv) | `StepCore.divisorsW` | PASS | Core instance; frequency bounds discharged. |
| D2 | `stepOmegaTail_reweight` | PASS | Target reweighting preserves the frequency diagonal. |
| D2 | `stepOmegaTail_taylorRho` | PASS | Matches the concrete Taylor extractions. |
| D2 | `StepHypMod.core_R_eq` | PASS | Core extraction identified on Par. |
| D2 | `StepHypMod.R1_eq` | PASS | Original p+1 extraction identified on Par. |
| D2 | `StepHypMod.core_OmegaPlus_eq` | PASS | Actual modified core normal frequency equals Ω + tail(R1). |
| D2 | `StepHypMod.core_omegaPlus_eq` | PASS | Actual modified core tangential frequency equals ω + hat(R1). |
| D2 | `StepHypMod.OmegaPlus_tail_bound_J` | PASS | J-weighted 3ε₀ sup bound. |
| D2 | `StepHypMod.OmegaPlus_tail_lip_J` | PASS | J-weighted 3ε₁ Lipschitz bound. |
| Inherited | `stepTheoremCore` | Scope note | Unchanged in the audited delta; axioms checked only. |
| Inherited | `stepTheorem_of_eps0_pos` | Scope note | Unchanged in the audited delta; axioms checked only. |
| Inherited | `kamNorm_sub_le` | Scope note | Unchanged in the audited delta; axioms checked only. |
| Inherited | `eps_split_spec` | Scope note | Unchanged in the audited delta; axioms checked only. |
| Inherited | `StepHypSrc.split_spec` | Scope note | Unchanged in the audited delta; axioms checked only. |
| Inherited | `StepHypSrc.hyp` | Scope note | Unchanged in the audited delta; axioms checked only. |
| step helper | `stepTheorem_clauses` | PASS | Original non-modified statement preserved. |
| step (i),(iv),(v) | `stepTheorem` | PASS | Original 17 clauses plus six stronger clauses. |
| Inherited | `StepHypModSrc.split_spec` | Scope note | Unchanged in the audited delta; axioms checked only. |
| Inherited | `StepHypModSrc.hyp` | Scope note | Unchanged in the audited delta; axioms checked only. |
| step helper | `stepTheoremMod_clauses` | PASS | Original modified statement preserved. |
| step (i),(iv),(v) | `stepTheoremMod` | PASS | Same extension in the modified case. |

## Definitions and hypothesis classification

- **New `StepCore.Psi` (`StepPsi.lean:146`): intended object**, the Bochner integral of the target field along the ambient flow at time one. It is total by the underlying integral convention, and has no new ad hoc branch or fallback. Flow/domain assumptions establish the claimed integral, holomorphy, and displacement interpretation where used; no theorem relies on an out-of-domain fallback.
- **Changed `WaveStepHyp.Conclusion` (`StepTheorem.lean:132`): unchanged proposition body**, now protected. It is a conclusion definition, not a newly assumed hypothesis; the helper theorem proves it.
- No new `abbrev` or `structure` in the seven-file delta. Existing `stepE0`, `stepE1`, `StepHypSrc`, `StepHypModSrc` and their constructors were not changed or reaudited. No added conclusion-shaped source premise: the two extended theorem inputs are unchanged, and the abstract calculation helper assumptions are discharged by the concrete instances.

## Hygiene and validation

All Lean/Lake commands below were serial and under
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
Builds used the existing compile gate in the W driver, one module per Lake invocation:

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpja5 \
  KAM.Wave.KamStep.FlowCalcJoint KAM.Wave.KamStep.FlowCalcOnto \
  KAM.Wave.KamStep.StepPsi KAM.Wave.KamStep.StepDivisorsW \
  KAM.Wave.KamStep.StepOmegaBridge KAM.Wave.KamStep.StepTheorem \
  KAM.Wave.KamStep.StepTheoremSrc
```

Exit **0**. All seven targeted builds completed successfully. Output included inherited unused-variable, unused-tactic, style and deprecation warnings; no elaboration or memory failure. No budget override was used. Lake's cached-task word “Replayed” here is not a separate `leanchecker` run.

Axiom probe command (scratch imports the seven modules and issues `#print axioms` for every theorem in the declaration table):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 \
  lake env lean .lake/abi-scratch/W5R2AAudit.lean
```

Exit **0**, 43 theorem results. Exact output:

```text
'KAM.Wave.continuousOn_jointOfLocLip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.continuousOn_holoFlow_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.continuousOn_fderiv_holoFlow_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fderiv_holoFlow_smooth_targetUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fderiv_holoFlow_smooth_image_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlow_dPhi_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlow_dPhi_targetUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlow_dPhi_image_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.shift_int_law' depends on axioms: [propext]
'KAM.Wave.kamDomain_sub_tau' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepDomain_sub_tauS' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlow_bounds_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.flow_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phi_eq_add_Psi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.fderiv_phi_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.psi_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phi_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.flow_pair_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phi_translate_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.smooth_clause_v' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.psi_le_MF' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepDivisorsW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.divisorsW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepOmegaTail_reweight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepOmegaTail_taylorRho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.core_R_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.R1_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.core_OmegaPlus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.core_omegaPlus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.OmegaPlus_tail_bound_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypMod.OmegaPlus_tail_lip_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTheoremCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTheorem_of_eps0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamNorm_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.eps_split_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypSrc.split_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypSrc.hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTheorem_clauses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypModSrc.split_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepHypModSrc.hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTheoremMod_clauses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepTheoremMod' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay and short-name checks: not rerun. The user states the launcher already ran both; their exact output/exit codes are unavailable in this session. This report does not invent or independently attest those results. The fresh builds and axiom probe above are independent checks, not a substitute claim of fresh leanchecker replay.

Static checks: all seven files have the copyright comment, `module`, public imports, module docstring, exposed public noncomputable section. Line counts: FlowCalcJoint 123; FlowCalcOnto 149; StepPsi 248; StepDivisorsW 122; StepOmegaBridge 121; StepTheorem 205; StepTheoremSrc 824. No forbidden declaration, proof placeholder, heartbeat/depth override, or EuclideanSpace use was found in them. No direct provider or frozen import in these seven modules; the successful axiom probes contain no `sorryAx` or extra axiom. No changed hypotheses or new bundled conclusion assumptions appear in the scoped delta.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output, exit 0. The full branch comparison includes generated KAM/Root/Wave changes; these were pre-existing branch content and were not edited or audited here. A separate targeted comparison confirms the only Conclusion change in StepTheorem is `def` → `protected def`.

Lint command (the required wrapper only; the outer D53 scope also caps any ABI-check Lean subprocesses):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 \
  /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpja5
```

Exit **1**. Exact output:

```text
check_lean_modules: PASS (3964 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpja5/.lake/abi-scratch/tmpra7d1yto.lean:1:0: error: object file '/root/code/KAM-inp-wpja5b/.lake/w-overlay/KAM/Frozen/Defs/ActionNbhd.olean' of module KAM.Frozen.Defs.ActionNbhd does not exist

```

The source-module check and frozen-anchor guard passed. The ABI hash stage did **not** complete successfully. Afterward, reading `.lake/w-bin/lake` showed that its generated LEAN_PATH entry was `/root/code/KAM-inp-wpja5b/.lake/w-overlay`, rather than this worktree's overlay. This is direct evidence of wrapper-path interference with the parallel audit, consistent with a shared generated wrapper; the precise filesystem alias/race was not investigated or repaired outside scope. No `ABI HASHES OK` claim is made. The 43-theorem direct axiom probe, which completed before lint and did not use this generated wrapper, remains valid. The wrapper failure is recorded as an environment/verification note, not as a Lean theorem refutation. A clean ABI lint rerun remains outstanding for the orchestrator after isolating the parallel wrappers.

## Errata, deviations, residual scope

No new suspected pinned-source or blueprint mathematical defect found in this tight delta. The reviewer introduced no source or statement deviation. The previously described proof routes are source-compatible; independent continuity and target-unit helpers are stronger/general infrastructure with concretely discharged premises.

Residual notes: original first-round reports and R2A handoff unavailable; launcher replay/name-check output unavailable; fresh lint ABI stage failed as recorded; consumers must handle the extended conjunct list and import the D2 bridge. Acceptance is limited to the visible descriptions of STEP-A F1/F2 and STEP-B F1/F2 plus the explicitly quoted notes/D2/D3. No inference about unquoted first-round notes, action-angle/initial proofs, W6 assembly, frozen-anchor sealing, or full-branch hygiene.

Only this report was added to tracked repository content. Temporary axiom-probe source and logs were removed after incorporating their results. No state-changing git command, source edit, generated-root regeneration, or replay rerun was performed.
