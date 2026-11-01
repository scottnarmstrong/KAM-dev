# W5-STEP-B independent package audit 1

**Verdict: FAIL for the claimed complete source-facing W5 step interface.** Both `KAM.Wave.stepTheorem` and `KAM.Wave.stepTheoremMod` omit the smoothing-norm content of clause (v) (F1) and the wave/Dirichlet-weight version of clause (iv) (F2). This is a statement-fidelity verdict, not a claim of a false proved Lean proposition. The modified solve, reality, step-map onto property, and field-form weak conjugacy pass the scoped source review. D2 and D3 are consumer interface requests, not those missing W5 conclusions.

## Scope and authority

Audited checkout `/root/code/KAM-inp-wpja5`, HEAD `27c7667814940c3b07c651288476a2be011c8d59`; comparison `inp = 51be245691bc21c0cf789b0c5b6bb9a4d3a7972a`, using `git diff inp...HEAD`. The 61 modules in `W5-STEP-B-handoff.md` contain 10,761 lines (largest: ModifiedDivisors, 571). The complete comparison has 118 changed files; only the named run-B modules receive substantive verdicts below. Run-A declarations are inputs, including their flow and Taylor constructions; its two notified repairs are not re-audited or counted as findings here. F1 concerns their consumption by **run-B** StepFlowFam and step theorem statements.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the track W statement draft, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the run-B focus, W5-STEP/MODIFIED/REAL handoffs, and the local W5 blueprint, with the W4 weight definitions where consumed. Applied the refute-first KAM package audit workflow. User's run-B focus replaces the generic focus; D53 overrides the generic nice/build/lint recipes; the requested package-worktree report path overrides the generic main-worktree destination. No provider or frozen anchor is assigned or sealed by these modules; provider/frozen exact-type and seal-body probes are therefore not applicable. No claim about `nlw2` closure is made.

## Findings

| Blueprint node / export | Verdict | Reason |
|---|---|---|
| `bpW:w5:step` / `stepTheorem` | FAIL | F1 smoothing target norms; F2 Dirichlet-weight divisor conclusion. |
| `bpW:w5:step` / `stepTheoremMod` | FAIL | Same F1/F2; ε₀ splitting, modified premises and reality clauses themselves pass. |
| `bpW:w5:new-ham` (i)–(iii) | PASS | Actual scalar expansion, smoothing field and field-form weak conjugacy. |
| `bpW:w5:w4-modified` (i)–(iii) | PASS | Twisted multipliers, correct 2β Lipschitz loss and B^♮ exponent. |
| `bpW:w5:step` reality / onto clauses | PASS | Real input data prove outgoing reality; Neumann argument on smoothing range. |
| `bpW:w5:step` (iii) | PASS | Correct p₊−p exponent and λ-frequency bounds; D2 is a stronger consumer need. |
| `bpW:w5:step` (iv) | FAIL complete coverage | Ordinary bracket variant passes; wave bracket variant missing. |
| `bpW:w5:step` (v) | FAIL | Correct numeric constants in a weaker ambient target norm. D3's sharper sup constant is separate. |
| Source ε₀=0 case | PASS | Positive ε majorant and proved `stepE0/stepE1` split; helpers distinctly named. |
| Source opening holomorphy / all integer shifts | NOTE | Available underlying facts are not explicitly aggregated into the source-facing conjunctions. |

### F1 — FAIL: clause (v) exports ambient norms instead of smoothing norms

Blueprint `blueprint-W/parts/w5-kamstep.tex:585–586` requires

```
|Φ-id|^λ_{p₊,r,D₊} ≤ 2 M_F
|DΦ-I|^λ_{p→p₊,r,D₊} ≤ 16 M_F/σ.
```

`StepTheoremSrc.lean:306–314` and `:493–501` instead bound `‖H.hyp.core.Phi ξ w - w‖` and the operator norm of `fderiv ℂ (H.hyp.core.Phi ξ) w - id`, both on `StepPhase r` representing the **ambient p coordinates**. The Lipschitz versions use those same ambient targets. `StepCore.Phi` (`StepConj.lean:55`) is the flow of `smoothField (stepEmbedCLM ... p pb ...) Z`; this is an ambient map, not its displacement in p₊ representatives.

The precise loss occurs in scoped `StepFlowFam.lean:77–110`: after rewriting the flow as `w + ι Ψ`, the proof applies `‖ι g‖ ≤ ‖g‖` (lines 80 and 90), and composes the derivative with `ι` (lines 93–110). Thus it discards the stronger estimates already available for `smoothDisp` and its derivative. `StepCore.flow_pair` (`StepFlowClauses.lean:54`) and both helper/source-facing theorems propagate the weaker result. This is not a harmless change of representative: on normal mode j, the inclusion scales by `(j+2)^(p-pb)`, with unbounded reciprocal when pb>p. A bound on the embedded vector cannot recover its p₊ norm. The onto clause establishes invariance of the smoothing subspace, not this quantitative estimate.

Required interface: expose the actual smoothing displacement Ψ with `Φ w = w + ι Ψ w`, and estimates on Ψ, parameter differences, `DΨ`, and derivative differences (or equivalent explicitly typed p→p₊ operators), then aggregate them with the stated constants. No new premise is needed and no run-A declaration needs to be refuted to identify this run-B omission.

### F2 — FAIL: clause (iv) omits the Dirichlet-weight version

Blueprint `w5-kamstep.tex:581–584` says: “this holds for the Dirichlet weight … as well as for” the unshifted bracket. `StepTheoremSrc.lean:300–305` and `:487–492`, and `StepCore.divisors` (`StepClauses.lean:131–149`), only accept `HomMelnikov` and conclude the bound with `homJap`. They have no corresponding implication from `HomMelnikovW` to a lower bound with `homJapW` at the same α′.

The two weights differ: the consumed W4 definitions are `homJap l = max(1, |Σ j l_j|)` and `homJapW l = max(1, |Σ (j+2) l_j|)` (`Homological/WaveReindex.lean:30–36`). For `l=e₁` they are 1 and 3. W4's comparison allows a factor-three loss, which does not prove the blueprint's same-α′ conclusion. Instantiating the existing theorem under the stronger old wave condition yields only the unshifted-weight new bound. The missing result must use the old **wave-weight** lower bound directly in the subtraction argument (the blueprint's “whenever the same holds” applies separately to that variant). Do not strengthen the unshifted premise into an unrequested wave conclusion.

### Interface notes under the literal aggregation requirement

The source-facing conjunctions do not explicitly assert holomorphy of Φ (the theorem's opening sentence), nor the full `k : ℤ²` translation law: they state the law for `k : Fin 2`, i.e. the two unit shifts. The existing flow holomorphy theorem, applied to the concrete flow hypothesis, supplies holomorphy, and domain invariance plus iteration/inverses of unit shifts supplies the integer law. These are straightforward export/aggregation omissions, not evidence of a false map or a new analytic gap. They should be included if “clauses verbatim” is the acceptance standard. Merely mentioning totalized `fderiv` is not an explicit holomorphy assertion. The old `StepTheorem.lean` module docstring still calls the now separately supplied reality/onto/Riesz clauses “open”; this is stale documentation.

## D2 and D3 rulings

| Request | Ruling against the W5 blueprint | What remains for the W6 consumer |
|---|---|---|
| D2: J-weighted normal-frequency shift in the modified preparatory step | **Consumer mismatch, not an omitted conclusion of W5 step (iii).** Its literal exponent is p₊−p; at p₊=p+1/2 it is J^(1/2). Both source theorems state that exponent. | W6's J bound uses the p+1 Taylor family `StepHypMod.R1`. W5 modified lemma (i) preserves W4's N̂ bounds for that family. `StepReweightTaylor.homNhat_taylorRho` preserves the scalar N̂ polynomial, and `homNormalEntry_rho` preserves true entries under reweighting; the step interface does not directly export the corresponding `stepOmegaTail`/core-`OmegaPlus` equality. Extract and expose that bridge before using the p+1 bound for the actual new frequency. No inference J^(1/2)→J is valid. |
| D3: sup displacement ≤ M_F rather than the λ bound ≤2M_F | **Consumer mismatch, not an omitted conclusion of W5 step (v).** The blueprint theorem explicitly states ≤2M_F. The sharper sup bound occurs in `stepW:w5:f-flow` (`w5-kamstep.tex:400–402`). | A separate sharp sup export can use the existing pointwise M₀ estimate and `M₀+λM₁≤M_F`; StepCore.flow_pair already exposes the ambient estimate ≤M₀. For a p₊-norm sup bound, retain Ψ as in F1. Changing 2M_F to M_F for the whole λ norm would be unjustified. |

D2/D3 do not excuse F1: **the constant** in W5 clause (v) is correct, while **the target norm** is not the blueprint's target.

## Hypotheses and construction review

`StepHypSrc` / `StepHypModSrc` assume ε₀≥0, ε₁≥0, ε>0 and ε₀+λε₁≤ε. `eps_split_spec` proves the bounds for `(stepE0 ε ε₀, stepE1 ε₀ ε₁)`: when ε₀>0 it is the original pair; when ε₀=0, the field-difference norm is ≤0 by the triangle inequality and both zero bounds, so `(ε,0)` works. This does not discard a nonzero field. The source-facing theorems use `H.hyp`, while the strictly positive forms have the distinct `*_of_eps0_pos` names. **PASS:** no ε₀>0 premise reaches either source-facing theorem. ε>0 is the blueprint's explicit positive majorant, including P=0.

The Lean assumptions σ≤1 and 5σ<s are weaker than the source's σ≤min(1/4,s/6), σ>0; the latter implies 5σ<s strictly. Omitting s≤1 and the unmodified pb≤p+1 restriction generalizes these results. At the standing a=p=1, the nonnegative weights, `1≤p+pb`, `HomGuard`, and pairing evidence are available; these are not extra analytic conclusions assumed of the step. The modified β≥0 range generalizes β>0; `2β≤p+1-pb` supplies both pb≤p+1 and β≤p+1-pb. A `Fact (0<r)` instance duplicates the supplied hr and is typing data.

`WaveStepHyp` and `StepHypMod` contain source smoothing/periodicity/reality, frequency, divisor, bound and smallness data. `StepCore` deliberately abstracts the solved family, its bounds and homological equation; it is an internal conditional interface, not the source theorem. `WaveStepHyp.core` proves its F bounds/equation from the ordinary solve; `StepHypMod.core` proves them from the modified solve and reweights the actual input field. No hard step remains as a source-facing premise. The extra `HomMelnikov` in modified clause (iv) is legitimate: line 583 says “whenever the same holds with α”. A modified lower bound alone is not asserted to propagate as an ordinary Melnikov bound.

## Modified and reality proof chains

Modified multipliers are `homModRatio_i * homDQ_{ij}` and `homModRatio_i * homDQ_{ji}`. `homModRatio_eq` identifies ρ_i=I^(pb-p-1); the off-diagonal bounds absorb `min(I,J)^β` with β≤p+1-pb, and the Lipschitz product absorbs `min(I,J)^(2β)` using 2β≤p+1-pb. The diagonal resonances are separately handled. `homModSolve_entry` cancels the output weight ratio and recovers the scalar inverse divisor on true entries; symmetry/transposition are proved for those entries. The c±/P/P′ solves are the ordinary solves read through Dρ.

`ModifiedAct` differentiates the solved Fourier series; Q's angle derivative is bounded in the operator target and then paired, rather than assuming the unavailable bounded unweighted multiplier in the bilinear norm. `ModifiedBounds`, `ModifiedLip*` and `homModLemma2` preserve C₁=7+10K_S, B^W for the sup part, B^♮ for the Lipschitz part and exponent 2τ+4. The all-carrier equation in `ModifiedEquation` is established first on finite support, then by continuity and truncation; it is not merely a finite-sequence equation. `ModifiedStepSolve` transfers its sign to `R+DN·X_F=N̂+â₀`. `StepReweightTaylor` relates the actual reweighted Taylor family to the p+1 data; `StepHypMod.equation` consumes the value and N̂ identities, and `core` discharges the abstraction. **PASS** for this modified-case chain, subject to the separate source-interface findings above.

Reality is proved from real P, not assumed of the outgoing family: real Taylor coefficients → real ordinary/modified solve → real Hamiltonian/field → real Picard iterates and limit. P₊ reality follows from the scalar conjugacy and real N,N₊,â₀. `RealSmoothOnto` uses `DΦ∘ι = ι∘(I+DΨ∘ι)` and a genuine Neumann unit with norm<1, both into and onto the smoothing range. Its step-map use has M₀≤ση²/16≤σ/1024 from source smallness. No run-A general-flow onto defect is asserted to be resolved by this narrower valid use.

`stepXN` is the affine field `(ω/(2π),0,Ωv,−Ωu)` in p−1 representatives, using Ω_j/(j+2), not a bounded p→p field. `stepDN_eq_symp_XN` proves its Riesz identity against embedded p₊ directions. `StepCore.weakConj_field` rewrites the differentiated Hamiltonian identity with `DΦ(ιW′)=ιW″`; `stepEmbedCLM_injective` and the onto/into result make this exactly the field-form weak conjugacy. Modified `X′=DρX` is a representative change preserving the physical pairings, not a replacement physical perturbation. These clauses occur in both source-facing theorems. **PASS.**

The new-Hamiltonian chain constructs `(P−R)∘Φ + ∫{(1−t)N̂+tR,F}∘φᵗ`, proves its derivative and field formula by bracket skewness/transport, and derives the scalar conjugacy by FTC/triangle integration. NewHamIntegral/StepPlusFinal supply actual holomorphy and integrability of the field integral from time bounds; they do not assume the desired outgoing error estimate. StepPlus* and StepPullbackBound assemble the 7, 24, 896 and 168c_F constants with the η/σ losses. No additional source-fidelity defect identified there.

## Definitions and totalized operations

All scoped definitions are classified individually in the inventory below. They are mathematical constructions or conditional interfaces, with these carrier boundaries:

* `homModRatio`, twisted multipliers, diagonal reweighting and solution CLMs use positive nonzero wave weights. Inverse divisors are nonzero under the ordinary/modified Melnikov conditions on Π, except the deliberately removed average/diagonal resonant terms. Those terms are paid by N̂ and â₀.
* `homReweight` is the same Hamiltonian on its whole Taylor carrier, with changed gradient representatives; true entries, pairings, values and N̂ are proved invariant. `StepHypMod.X′` is the matching field representative. The p+1 and reweighted Taylor constructions agree on their intended strip; no off-strip identity is silently needed.
* `transSolve N = Ring.inverse (1+N)` is total, but all its inverse equations and uses in P₊'s field are restricted by norm<1 (`newHam_isUnit_one_add`, `stepN_bound`). NewHamIntegral uses q<1, and StepPlusFinal supplies q=1/128. No nonunit fallback is used to prove conjugacy or smoothing.
* `fderiv` occurs only where holomorphy/differentiability is supplied for the relevant open domain before derivative identities are used. `transNop` differentiates `smoothDisp`, whose differentiability comes from the flow hypothesis. Off-domain totalizations are not certified as dynamics. F1 is a norm/export defect, not misuse of the zero fallback of fderiv.
* Fourier `tsum`s have summability/termwise-derivative receipts on the reduced strip; the all-carrier pairings use bounded diagonals and ℓ² pairings. Interval integrals have continuity/time-Lipschitz receipts before differentiation or FTC. No nonsummable tsum fallback pays a claimed bound.
* `stepFTfam`, `stepFTfamMod` and `stepTaylorFam` use zero outside Π; every source conclusion is restricted to ξ∈Π and the corresponding membership lemmas select the intended branch. These extensions are harmless. `stepE0/stepE1` implement the proved positive splitting, not a changed perturbation. Real/imaginary coordinate maps are genuine bounded coordinate functionals.
* `WaveStepHyp.Conclusion` and `StepHypMod.Conclusion` are explicitly conditional proposition bundles; their content inherits F1/F2 when advertised as the complete blueprint theorem. `StepHypSrc`/`StepHypModSrc` and the other Prop structures are source/typing or internal conditional interfaces as distinguished above.

No new frozen definition, manifest entry, axiom, or provider is introduced by run B. There is no discovered junk-value reliance in source-facing objects on their asserted domains.

## Validation receipts

All Lean/Lake processes started by this audit, including those inherited by the lint process, ran in the D53 systemd scope with MemoryMax=4G, MemorySwapMax=0, nice 10 and LEAN_NUM_THREADS=1; checks were serialized. No heartbeat, recursion or synthesis overrides were set. No library-wide or application build was requested.

1. **Targeted build**, using the inspected D53 gated driver (one module per Lake invocation):

   ```sh
   /root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpja5 KAM.Wave.KamStep.StepTheoremSrc
   ```

   Its actual build invocation is:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build KAM.Wave.KamStep.StepTheoremSrc
   ```

   Exit **0**; exact completion: `Build completed successfully (3437 jobs).` All 61 scoped modules are in this target's import closure (checked against source imports). Warnings include deprecated `if_pos`/`if_neg` and an unused `hlam` binder in StepTheoremSrc; they do not change the statement-fidelity verdict. Retained log: `/tmp/w5b-build.log`.

2. **Every scoped public theorem's axioms.** A temporary `.lake/abi-scratch/W5BAudit.lean` imported precisely the 61 scope modules and issued `#print axioms` for the 396 public theorem/lemma declarations in the inventory. Invocation:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean .lake/abi-scratch/W5BAudit.lean'
   ```

   Exit **0**; **396 axiom reports, 0 errors**, exactly one distinct list: `[propext, Classical.choice, Quot.sound]`. In particular:

   ```text
   'KAM.Wave.stepTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.stepTheoremMod' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.stepTheorem_of_eps0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.stepTheoremMod_of_eps0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.homModLemma_fieldBound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.homModLemma_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.homModLemma_equation_all' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.stepTheorem_reality_of_eps0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.stepTheoremMod_dPhi_smooth_onto_of_eps0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Wave.stepTheoremMod_weakConj_field_of_eps0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Retained full output: `/tmp/w5b-axioms.log`. The package's own build artifacts came first in LEAN_PATH. The scratch probe was deleted after successful checking. No `sorryAx` or project axiom was reported.

3. **Required lint**, only through the user-prescribed wrapper, with a retained full rerun:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpja5
   ```

   Exit **0**. Exact output:

   ```text
   check_lean_modules: PASS (3899 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

   The application anchors in that ABI message were checked by file hash, not rebuilt or kernel-replayed in this audit; no stronger receipt is claimed. No stale-root exception was needed. Retained output: `/tmp/w5b-lint.log`.

4. **Diff, module and hygiene scope.** `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` returned no output (exit 0). The broader diff does include the producer's generated `KAM/Root/Wave.lean` update (113 additions); it is recorded as an inherited generated integration change, not an auditor edit or a run-B analytic result. Lint found no forbidden proof escapes, resource overrides, module-format failures or line-cap violations. Scoped maximum is 571 lines. Direct scoped imports contain no provider or frozen module; the combined axiom check establishes no frozen sorry dependency in any scoped public theorem. The report is the only intended repository change.

5. **Kernel replay and short-name checks.** Per the user's explicit instruction, these were already run by the launcher. Their actual logs/exit codes were not available in this turn; they were **not rerun**, and no independently observed replay exit code or short-name receipt is invented here. The independent checks in this turn are the targeted build, complete theorem-axiom probe, required lint and source/diff review. The source-interface counterevidence F1/F2 does not require another kernel replay. Provider type/seal probes are not applicable to this helper-only package.


## Suspected errata, deviations, and limits

No new mathematical defect in P96-K is claimed. The existing local blueprint warning at `w5-kamstep.tex:244–252` remains: P96-K p.140 asserts the parameter-Lipschitz estimate with a weight loss β, while the termwise product of two modified divisors needs loss at least 2β; the angle-derivative argument also uses B^♮ rather than B^W. The scoped Lean package implements the adopted repaired premise and exponent. This audit does not independently re-audit that pinned-source gap or provide a counterexample to the original source.

F1/F2 and the aggregation/doc notes are implementation deviations from the current local blueprint, with locations and literal requirements given above; they should be returned to the producer. Run-A repairs, W5 action-angle/initial lemmas, W6 proof packages, and eventual W8/nlw2 closure remain outside this verdict. Only this report is an intended repository edit; scratch probes are removed after validation. No state-changing git command, source repair, root regeneration, or frozen/manifest edit was made.

## Declaration inventory

Every listed theorem was included in the combined axiom probe. PASS means no additional source or definition defect was identified for that declaration's own stated/conditional role; it does not promote a helper to the full source result. F1/F2 identify incomplete source-node coverage even when the weaker Lean proposition is valid. Fully qualified names below are in namespace `KAM.Wave` unless explicitly shown otherwise.


### KAM.Wave.KamStep.ModifiedStepSolve

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepSolveMod_fieldBound` (46) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `stepSolveMod_fam` (62) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `stepSolveMod_equation` (113) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.KamStep.NewHamBracket

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `fderiv_smoothField` (30) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `hasFDerivAt_bracket_smooth` (35) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |

### KAM.Wave.KamStep.NewHamConcrete

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepNewHam_concrete` (37) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |

### KAM.Wave.KamStep.NewHamConj

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepWeakConj` (34) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |

### KAM.Wave.KamStep.NewHamExp

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepFTC` (32) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `stepContOn` (42) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `stepIntegral_eq` (47) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `stepExpansion` (64) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `stepExpansion_H` (103) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |

### KAM.Wave.KamStep.NewHamFlow

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepNewHam_flow_H` (36) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |

### KAM.Wave.KamStep.NewHamIntegral

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `differentiableOn_transNop` (33) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `newHam_integral_smoothing` (41) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |

### KAM.Wave.KamStep.NewHamLip

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `norm_smoothDisp_time_sub_le` (37) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `norm_flow_time_sub_le` (53) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `norm_fderiv_smoothDisp_time_sub_le` (63) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `yfam` (90) | def | **PASS** — Transported target field through transSolve; validity restricted by the proved unit bound. |
| `norm_transSolve_le` (95) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `norm_transSolve_sub_le` (111) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `norm_yfam_time_sub_le` (142) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |

### KAM.Wave.KamStep.NewHamTransport

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `transNop` (37) | def | **PASS** — Derivative of the smoothing displacement composed with the inclusion; genuine operator on its carrier. |
| `fderiv_flow_comp_iota` (40) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `hasFDerivAt_comp_flow_smooth` (47) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `newHam_isUnit_one_add` (67) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `transSolve` (73) | def | **PASS** — Total Ring.inverse(1+N); used as an inverse only under norm<1. |
| `transSolve_spec` (75) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `transSolve_unique` (80) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |
| `differentiableAt_transSolve_apply` (100) | theorem | **PASS** — new-ham expansion, differentiation, transport or integral helper; source premises supplied concretely. |

### KAM.Wave.KamStep.RealFlowPicard

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `wavePicard_real_of_field_real` (45) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `holoFlow_real_of_field_real` (64) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepRealIdx` (80) | abbrev | **PASS** — Coordinate index type for the real locus. |
| `stepCoordCLM` (83) | def | **PASS** — Bounded complex coordinate functional on the full representative space. |
| `stepRealFun` (95) | def | **PASS** — Imaginary part of the coordinate functional, restricted to real scalars. |
| `stepRealFun_apply` (98) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepReal_iff_stepRealFun` (102) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepReal_kamHomEmbed` (116) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepFlow_real` (131) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |

### KAM.Wave.KamStep.RealNField

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homWt_pred_div` (39) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepXNcoef` (47) | def | **PASS** — Ω times the positive ratio of p−1 and p weights; equals Ω/(j+2). |
| `norm_stepXNcoef_le` (50) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepXNdiag` (59) | def | **PASS** — Bounded diagonal from the supplied frequency bound. |
| `stepXN` (65) | def | **PASS** — Physical affine X_N stored in p−1 representatives. |
| `homNOmega_embed_eq_stepPair` (72) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `homNOmega_zbook` (92) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepDN_eq_symp_XN` (105) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `homEmbed_gen_self` (131) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepPair_embed_eq_true` (138) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepSymp_embed_eq` (157) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |

### KAM.Wave.KamStep.RealSmoothOnto

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `fderiv_holoFlow_smooth_mapsTo` (54) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `fderiv_holoFlow_smooth_onto` (62) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepEmbedCLM_injective` (89) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepFlow_dPhi_smooth_mapsTo` (114) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepFlow_dPhi_smooth_onto` (137) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.dPhi_smooth_mapsTo` (181) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.dPhi_smooth_onto` (189) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepTheorem_dPhi_smooth_onto_of_eps0_pos` (201) | theorem | **PASS** — Distinct positive-ε₀ helper; source-facing usage discharges positivity with the split. |
| `stepTheoremMod_dPhi_smooth_onto_of_eps0_pos` (215) | theorem | **PASS** — Distinct positive-ε₀ helper; source-facing usage discharges positivity with the split. |

### KAM.Wave.KamStep.RealStep

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `kamDomain_star_mem` (51) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepNfun_real` (60) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.R_isRealTaylor` (89) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.a0_im` (95) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.phi_real_of_FT_real` (104) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.Pplus_real_of_FT_real` (114) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `WaveStepHyp.FT_isRealTaylor` (138) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepHypMod.R1_isRealTaylor` (151) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepHypMod.FT_isRealTaylor` (159) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepTheorem_reality_of_eps0_pos` (171) | theorem | **PASS** — Distinct positive-ε₀ helper; source-facing usage discharges positivity with the split. |
| `stepTheoremMod_reality_of_eps0_pos` (182) | theorem | **PASS** — Distinct positive-ε₀ helper; source-facing usage discharges positivity with the split. |

### KAM.Wave.KamStep.RealTaylorFun

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepPr_star` (44) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `homOp_star_of_entries` (55) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `kamEntry_conj_of_normal` (65) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepZb_eq_star` (75) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepFun_real` (89) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepReal_of_symp` (137) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepField_real` (163) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |

### KAM.Wave.KamStep.RealTaylorOf

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepPairCLM_kamBasis` (44) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `im_stepWinv_mul` (49) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `complex_eq_ofReal_re` (55) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepNormal_real_of_symp` (60) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `conj_homSqrt2_inv` (80) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepCm_eq_conj_cp` (85) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepBilin_iota_conj` (102) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepIotaZ_eq` (115) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepIotaZb_eq` (120) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepX_w0_normal_real` (134) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `tCm_eq_conj_tCp` (142) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepDXForm_real` (149) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `tP'_entry_eq_conj` (156) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `tQt_entry_eq_conj` (176) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepTaylorOf_isRealTaylor` (198) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |

### KAM.Wave.KamStep.RealWeakConj

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `StepCore.hqq1` (50) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.hpm` (52) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.dNplus_eq` (57) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `StepCore.weakConj_field` (82) | theorem | **PASS** — reality, Riesz representation or smoothing-range derivative helper; see reality proof chain. |
| `stepTheorem_weakConj_field_of_eps0_pos` (140) | theorem | **PASS** — Distinct positive-ε₀ helper; source-facing usage discharges positivity with the split. |
| `stepTheoremMod_weakConj_field_of_eps0_pos` (163) | theorem | **PASS** — Distinct positive-ε₀ helper; source-facing usage discharges positivity with the split. |

### KAM.Wave.KamStep.StepBracket

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepBrG` (41) | def | **PASS** — Scalar bracket with the ambient symplectic form and embedded fields. |
| `stepBrZ` (47) | def | **PASS** — Target-valued commutator DZ_G(ιZ_F)−DZ_F(ιZ_G). |
| `stepSkew_embedded` (53) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepBrG_hasFDerivAt` (64) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFieldS_cauchy` (82) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepDomain_mono'` (98) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepBrZ_norm_le` (102) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFieldS_differentiableOn_theta` (130) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `isOpen_theta_strip` (136) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepBrZ_differentiableOn` (140) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `norm_stepBrG_le` (163) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFieldS_sub` (192) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `fderiv_stepFieldS_sub` (201) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepBrZ_sub_norm_le` (215) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepN_le'` (297) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepClauses

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `StepCore.Pplus_smoothing` (46) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.Pplus_periodic` (56) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.Xplus_fam` (65) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.omegaPlus_sub` (83) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.OmegaPlus_sub` (86) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.freq_sup` (91) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.freq_lip` (97) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.tail_sup` (103) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.tail_lip` (108) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.freq_hyp` (115) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.divisors` (132) | theorem | **FAIL full clause (iv) coverage** — F2: valid unshifted result only; missing wave-weight variant. |

### KAM.Wave.KamStep.StepConj

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `StepCore.omegaPlus` (44) | def | **PASS** — Original real angle frequency plus Re of the zero-mode b coefficient. |
| `StepCore.OmegaPlus` (47) | def | **PASS** — Original normal frequency plus the true diagonal zero-mode Q entry. |
| `StepCore.a0` (50) | def | **PASS** — Zero Fourier coefficient of the scalar Taylor component. |
| `StepCore.Phi` (55) | def | **PASS** — Time-one flow of the embedded field in ambient p representatives; F1 concerns exported norms. |
| `StepCore.Pplus` (59) | def | **PASS** — Constructed new Hamiltonian via stepPplusS, not a chosen witness. |
| `StepCore.Xplus` (63) | def | **PASS** — Constructed pullback-plus-integral field via stepXplusS. |
| `StepCore.hK0` (68) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.hKp` (70) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.ε₀_le` (72) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.tail_bound` (76) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.omegaPlus_bound` (90) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.mf_le_sigma` (101) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.nplus_eq` (107) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.conj_eq` (123) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepCore

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepM₀` (34) | def | **PASS** — Explicit uniform solve bound with B^W. |
| `stepM₁` (36) | def | **PASS** — Explicit parameter solve bound with B^W. |
| `stepTaylorFam_field` (44) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepTaylorFam_sub` (54) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore` (75) | structure | **PASS** — Internal conditional abstraction; solved bounds/equation discharged by both concrete core suppliers. |
| `StepCore.ε_pos` (133) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.hσs'` (137) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.pb_pos` (139) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.mf_small` (142) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.R` (146) | def | **PASS** — Taylor family of the actual perturbation on Π; harmless zero extension outside Π. |
| `StepCore.R_eq` (149) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.R_field` (154) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.R_sub` (157) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepCtx

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `StepCtx` (32) | structure | **PASS** — Internal flow/holomorphy/skewness interface instantiated by StepCtx.mk′. |
| `StepCtx.mk'` (44) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepFlowClauses

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `StepCore.mf_lt` (44) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.Dplus_sub_small` (48) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.Dplus_sub_U` (52) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.flow_pair` (57) | theorem | **FAIL smoothing-node coverage** — F1: target inclusion applied, so exported four bounds are ambient. |
| `StepCore.phi_mem` (70) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.two_p` (85) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.weakConj` (88) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.phi_symplectic` (109) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepCore.phi_translate` (118) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepFlowConcrete

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepToKCLM` (36) | def | **PASS** — Bounded linear identification from scaled representatives; r>0 instance. |
| `stepOfKCLM` (44) | def | **PASS** — Inverse bounded linear identification into scaled representatives; r>0 instance. |
| `stepToKCLM_apply` (51) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepOfKCLM_apply` (54) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFieldS` (58) | def | **PASS** — Taylor field read in p₊ representatives, on the fixed scaled model. |
| `stepDomain_theta_mem` (62) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFieldS_differentiableAt` (67) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFS` (76) | def | **PASS** — Taylor scalar function pulled to the scaled model. |
| `stepFS_hasFDerivAt` (81) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFieldS_skew` (97) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepFlowFam

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepFlow_bounds` (36) | theorem | **FAIL smoothing-node coverage** — F1: target inclusion applied, so exported four bounds are ambient. |

### KAM.Wave.KamStep.StepFreqBound

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepOmegaHat` (36) | def | **PASS** — Real part of the zero Fourier b coefficient. |
| `stepOmegaTail` (39) | def | **PASS** — Real part of the true diagonal zero Fourier Q coefficient. |
| `stepOmegaHat_bound` (42) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepOmegaTail_bound` (52) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepOmegaHat_sub` (60) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepOmegaTail_sub` (69) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepHyp

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `WaveStepHyp` (30) | structure | **PASS** — Source data plus positive ε₀ for the distinctly named conditional helper. |
| `WaveStepHyp.ε_pos` (72) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.hσs'` (76) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.pb_pos` (78) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.mf_small` (81) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.R` (85) | def | **PASS** — Taylor family of the actual perturbation on Π; harmless zero extension outside Π. |
| `WaveStepHyp.FT` (89) | def | **PASS** — Ordinary or modified solved Taylor family on Π, as specified by its enclosing hypothesis. |
| `WaveStepHyp.R_eq` (92) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.FT_eq` (97) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.R_field` (101) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.R_sub` (104) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.F_field` (108) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.F_sub` (114) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.M₀_pos` (127) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.M₁_nonneg` (135) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.M_sum` (145) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `WaveStepHyp.core` (164) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepHypMod

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepM₁n` (33) | def | **PASS** — Explicit Lipschitz solve bound with B^♮. |
| `stepFTfamMod` (38) | def | **PASS** — Modified solve on Π and zero off Π; correct membership branch selected. |
| `stepFTfamMod_of_mem` (47) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod` (59) | structure | **PASS** — Source modified data, 2β loss condition and positive ε₀ for helper only. |
| `StepHypMod.hc` (104) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.hβ` (106) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.hσs'` (108) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.X'` (111) | def | **PASS** — Dρ applied to the actual p+1 field; matching p₊ representative of that field. |
| `StepHypMod.R1` (114) | def | **PASS** — Taylor family of the original p+1 smoothing perturbation. |
| `StepHypMod.FT` (118) | def | **PASS** — Ordinary or modified solved Taylor family on Π, as specified by its enclosing hypothesis. |
| `StepHypMod.R1_field` (121) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.R1_sub` (124) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.hP'` (128) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.hb'` (132) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.M₀_pos` (135) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.M₁_nonneg` (143) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.M_sum` (153) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.F_field` (178) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.F_sub` (185) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.equation` (199) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `StepHypMod.core` (230) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepLip

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `kamNorm_ball_mem` (31) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `kamNorm_lipschitz_small` (48) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepMargin

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepDomain_U_margin` (29) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepNplus

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homNOmegaCLM_add` (32) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepNfun_add_Nhat` (53) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepNuIntegral

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepKappa` (35) | def | **PASS** — Continuous scaling operator for the small-radius field integral estimate. |
| `norm_stepKappa` (38) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepNu_integral_sub_le` (41) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepPeriodicFlow

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepTauS` (34) | def | **PASS** — Unit angle translation in scaled representatives. |
| `toK_add_tauS` (36) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepDomain_add_tauS` (39) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFieldS_add_tau` (43) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFS_add_tau` (49) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepBrG_add_tau` (55) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFlow_translate` (64) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepPplusS_periodic` (80) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepPeriodic

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepZ_add_tau` (31) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepZb_add_tau` (35) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepField_add_tau` (40) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFun_add_tau` (65) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepPlusA

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepSympCLM_embed_apply` (33) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepPS` (40) | def | **PASS** — Input Hamiltonian composed with the scaled-space identification. |
| `stepXPS` (43) | def | **PASS** — Input smoothing field in the scaled target representatives. |
| `stepPS_hasFDerivAt` (46) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepPlusA_smoothing` (63) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPlusArith

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepXplus_arith` (28) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPlusAssemble

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepPplusS` (33) | def | **PASS** — (P−R)∘Φ plus the bracket integral: the intended scalar new Hamiltonian. |
| `stepXplusS` (43) | def | **PASS** — Transported X_P−X_R plus transported commutator integral in p₊ representatives. |
| `stepPplusS_hasFDerivAt` (55) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepPlus_isSmoothing` (78) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPlusBound

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepXplusA_bounds` (34) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepXplusB_time_bounds` (98) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepYfam_time_lip` (224) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepXplusB_bounds` (277) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepXplus_pair_bound` (323) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPlusClass

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepGfam` (39) | def | **PASS** — (1−t){N̂,F}+t{R,F}; linearity gives the stated bracket family. |
| `stepZgfam` (43) | def | **PASS** — Corresponding linear combination of target-valued commutators. |
| `stepGfam_hasFDerivAt` (48) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepZgfam_differentiableOn` (70) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `norm_stepZgfam_le` (76) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `norm_stepZgfam_sub_le` (99) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `norm_stepGfam_le` (123) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `norm_stepGfam_sub_le` (145) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPlusFam

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepTaylorFam` (36) | def | **PASS** — Actual Taylor polynomial on Π; zero outside the asserted parameter set. |
| `stepTaylorFam_of_mem` (46) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepPlus_famBound` (59) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPlusFinal

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepPlus_integral_smoothing` (28) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPlusLam

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepSplus` (39) | def | **PASS** — Explicit sup majorant for the outgoing field estimate. |
| `stepDplus` (43) | def | **PASS** — Explicit Lipschitz majorant for the outgoing field estimate. |
| `stepSplus_stepDplus_le` (50) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |
| `stepPlus_pair_lamBound` (58) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPlus

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepZF` (34) | abbrev | **PASS** — Abbreviation for the solved Taylor field in scaled representatives. |
| `stepN_bound` (37) | theorem | **PASS** — outgoing smoothing field/error assembly with explicit bounds. |

### KAM.Wave.KamStep.StepPullbackBound

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepPullback_bounds` (38) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepReweight

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepRhoK` (37) | def | **PASS** — Identity on angle/actions, Dρ on both normal components. |
| `stepRhoK_apply` (41) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepRhoK_fst` (44) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepRhoK_snd_fst` (46) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `kamNorm_stepRhoK_le` (49) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepZ_stepRhoK` (61) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepZb_stepRhoK` (66) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepZ_comp_stepRhoK` (71) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepZb_comp_stepRhoK` (75) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepWinv_mul_ratio` (80) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepPairCLM_rho` (90) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepSymp_stepRhoK` (104) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `IsSmoothing.rhoK` (116) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepReweightTaylor

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `kamNorm_stepRhoK_sub_le` (37) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepRhoK_fderiv` (42) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `blockP_rhoK` (48) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `blockP'_rhoK` (55) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `blockQ_rhoK` (62) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `blockQt_rhoK` (69) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepPr_rho` (76) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `homCoeff_congr_real` (81) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `realTheta_mem_strip` (89) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `tCp_rhoK` (97) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `tCm_rhoK` (102) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `tDX_rhoK` (110) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `tP_rhoK` (115) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `tP'_rhoK` (120) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `tQ_rhoK` (125) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `tQt_rhoK` (130) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepRhoK_bound` (138) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepRho_nn1` (143) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepRho_nn2` (145) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepTaylorRho` (157) | def | **PASS** — Actual Taylor polynomial of the reweighted field, retaining the same scalar P. |
| `stepTaylorP1` (163) | def | **PASS** — Actual Taylor polynomial before gradient reweighting. |
| `stepTaylorRho_b` (166) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepTaylorRho_a0` (169) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFun_taylorRho` (173) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `homNhat_taylorRho` (197) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFun_nhat_taylorRho` (209) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepSetup

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `waveBW_pos` (31) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepFTfam` (50) | def | **PASS** — Ordinary solve on Π; zero extension outside Π. |
| `stepFTfam_of_mem` (58) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepSymplectic

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepFlow_symplectic` (33) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |

### KAM.Wave.KamStep.StepTheorem

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `stepTheoremCore` (50) | theorem | **FAIL full blueprint coverage** — F1 ambient transformation norms; F2 missing wave-weight divisors. Existing weaker proposition not refuted. |
| `WaveStepHyp.Conclusion` (127) | def | **FAIL coverage F1/F2** — Conditional result bundle; incomplete as full source coverage because of F1/F2. |
| `stepTheorem_of_eps0_pos` (195) | theorem | **FAIL full blueprint coverage** — F1 ambient transformation norms; F2 missing wave-weight divisors. Existing weaker proposition not refuted. |

### KAM.Wave.KamStep.StepTheoremMod

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `StepHypMod.Conclusion` (42) | def | **FAIL coverage F1/F2** — Conditional result bundle; incomplete as full source coverage because of F1/F2. |
| `stepTheoremMod_of_eps0_pos` (111) | theorem | **FAIL full blueprint coverage** — F1 ambient transformation norms; F2 missing wave-weight divisors. Existing weaker proposition not refuted. |

### KAM.Wave.KamStep.StepTheoremSrc

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `kamNorm_sub_le` (42) | theorem | **PASS** — Stated infrastructure/conditional role; no additional defect identified. |
| `stepE0` (50) | def | **PASS** — Positive replacement bound ε₀ if positive, ε otherwise. |
| `stepE1` (53) | def | **PASS** — Original ε₁ if ε₀ positive, zero otherwise; justified by eps_split_spec. |
| `eps_split_spec` (56) | theorem | **PASS** — Source-compatible ε₀≥0 split; no outgoing analytic conclusion assumed. |
| `StepHypSrc` (87) | structure | **PASS** — Source data with ε₀≥0 and the blueprint positive ε majorant. |
| `StepHypModSrc` (122) | structure | **PASS** — Modified source data with ε₀≥0, ε>0 and 2β≤p+1−pb. |
| `StepHypSrc.split_spec` (168) | theorem | **PASS** — Source-compatible ε₀≥0 split; no outgoing analytic conclusion assumed. |
| `StepHypSrc.hyp` (176) | theorem | **PASS** — Source-compatible ε₀≥0 split; no outgoing analytic conclusion assumed. |
| `stepTheorem` (217) | theorem | **FAIL full blueprint coverage** — F1 ambient transformation norms; F2 missing wave-weight divisors. Existing weaker proposition not refuted. |
| `StepHypModSrc.split_spec` (353) | theorem | **PASS** — Source-compatible ε₀≥0 split; no outgoing analytic conclusion assumed. |
| `StepHypModSrc.hyp` (361) | theorem | **PASS** — Source-compatible ε₀≥0 split; no outgoing analytic conclusion assumed. |
| `stepTheoremMod` (403) | theorem | **FAIL full blueprint coverage** — F1 ambient transformation norms; F2 missing wave-weight divisors. Existing weaker proposition not refuted. |

### KAM.Wave.Homological.ModifiedAct

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `norm_two_pi_I_coord` (41) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `modeSize_mul_waveA_le` (54) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homPartial_fourierSumVec` (65) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homPartial_homSolve_le` (75) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homPartial_homSolve_sub_le` (124) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedBounds

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homLamDiag_comm_homModTdp` (37) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homLamDiag_comm_homModTdm` (46) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModF_compBounds` (56) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLemma_fieldBound_of_gates` (216) | theorem | **PASS** — Distinct conditional helper; gate supplied from source premises by the corresponding export. |
| `homModLemma_fieldBound` (234) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedDivisors

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `HomMelnikovMod` (42) | structure | **PASS** — Explicit original divisor bounds except the specified modified off-diagonal Q divisors. |
| `homModPP1` (58) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homMod_pb_le` (60) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homMod_beta_le` (62) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModRatio` (66) | def | **PASS** — Positive weight quotient on every normal index; algebraically I^(pb−p−1). |
| `homModRatio_eq` (68) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModRatio_pos` (75) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModRatio_mul_rpow_le` (79) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModRatio_le_one` (92) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModRatio_le` (99) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModDQ` (105) | def | **PASS** — Twisted Q divisor multiplier ρ_i d_ij. |
| `homModDQt` (109) | def | **PASS** — Twisted transposed divisor multiplier ρ_i d_ji. |
| `HomModMultBounds` (115) | structure | **PASS** — Conditional multiplier/nonvanishing gate; derived by homModMultBounds_of. |
| `HomModMultLip` (131) | structure | **PASS** — Conditional Lipschitz multiplier gate; derived by homModMultLip_of. |
| `norm_homInv_sub_le_of_lower` (146) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homOmega_sub_le` (164) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homPairZ_omega_sub_le` (172) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homDiv_sub_le` (180) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homLipC_div_sq_le` (212) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homMelnikovMod_pos_of` (229) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `ne_zero_of_lower` (234) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homInv_le_div` (237) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `one_le_natCast_pnat` (243) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `min_add_two_pos` (245) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModQ_lower` (252) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `abs_sub_pnat_pos` (260) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `one_le_abs_sub_pnat` (263) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModDQ_off_le` (271) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModDQ_diag_le` (302) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homDP_bound_mod` (317) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homDP'_bound_mod` (330) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModMultBounds_of` (345) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homInv_sub_le_weight` (399) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModDQ_sub_off_le` (408) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homMultA0_sub_le_mod` (461) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModDQ_sub_diag_le` (480) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModMultLip_of` (507) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedEq

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homSolve_image_eq_two` (41) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homSolve_partial_image_eq_two` (53) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homFamily_eq_two` (80) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModEq_a` (119) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModEq_b` (135) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModEq_cp` (167) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModEq_cm` (199) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModEq_P` (231) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModEq_P'` (262) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModEq_Q` (295) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedEquation

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homModLemma_equation_fin` (49) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLemma_equation_all_of_gates` (149) | theorem | **PASS** — Distinct conditional helper; gate supplied from source premises by the corresponding export. |
| `homModLemma_equation_all` (210) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedLipDeriv

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homModLip_dcp` (44) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_dcm` (88) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_dP` (132) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_dP'` (176) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_dQ` (221) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `HomCompBounds_gen.mono_scale` (258) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedLipField

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homModF_sub_compBounds` (39) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLemma_lipschitz_of_gates` (123) | theorem | **PASS** — Distinct conditional helper; gate supplied from source premises by the corresponding export. |
| `homModLemma_lipschitz` (151) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLemma2` (177) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedLip

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homModLip_b` (44) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_cp` (67) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_cm` (90) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_P` (113) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_P'` (143) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_Q` (174) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_Qt` (199) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_da` (225) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLip_db` (263) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedReal

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homModRhoL_comm_hadamard` (37) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModSolveTaylor_cp` (53) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModSolveTaylor_cm` (64) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModSolveTaylor_P` (75) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModSolveTaylor_P'` (82) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModLemma_zero_modes` (93) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homReweight_isReal` (115) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModSolveTaylor_isReal` (130) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homMelnikovMod_of_melnikov` (230) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedReweight

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homModRho` (39) | def | **PASS** — Bounded diagonal inclusion of p+1 normal representatives into pb representatives. |
| `homModRho_apply` (42) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModRho_le` (45) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModRho_apply_le` (48) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModRhoL` (53) | def | **PASS** — Bounded operator postcomposition with Dρ. |
| `homModRhoL_apply` (56) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModRhoL_apply_le` (59) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `kamEntry_homModRho_comp` (64) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homNormalEntry_rho` (69) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homLamD_rho` (80) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homLamDiag_rho` (89) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homLamCLM_rho` (95) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homPairRep_rho` (102) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homDualNorm_rho` (108) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `IsHomComp.clm` (114) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homReweight` (124) | def | **PASS** — Same Taylor Hamiltonian with Dρ applied to gradient components; true values/entries preserved. |
| `homRz_reweight` (152) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homRzb_reweight` (156) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homRu_reweight` (166) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homRv_reweight` (171) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homPartial_rho` (176) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homPartial_rhoL` (181) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homRtheta_reweight` (195) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homXnorm_reweight_le` (211) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homFieldBound_reweight` (229) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homRval_reweight` (235) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homNhat_reweight` (244) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homReweight_homSub` (256) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |

### KAM.Wave.Homological.ModifiedSolve

| Declaration (source line) | Kind | Verdict / classification |
|---|---|---|
| `homModTdp` (42) | def | **PASS** — Ordinary plus-divisor diagonal on the reweighted cp component. |
| `homModTdm` (46) | def | **PASS** — Ordinary minus-divisor diagonal on the reweighted cm component. |
| `homModTP` (50) | def | **PASS** — Ordinary P Hadamard solve CLM on reweighted operators. |
| `homModTP'` (54) | def | **PASS** — Ordinary P′ Hadamard solve CLM on reweighted operators. |
| `homModTQ` (58) | def | **PASS** — Twisted Q Hadamard solve CLM on original p+1 operators. |
| `homModTQt` (62) | def | **PASS** — Twisted transposed Q Hadamard solve CLM on original p+1 operators. |
| `norm_homModTdp_le` (69) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTdm_le` (71) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTP_le` (73) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTP'_le` (76) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTQ_le` (79) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTQt_le` (82) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTscal_le` (86) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTvec_le` (92) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTscal_sub_le` (106) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTvec_sub_le` (120) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTdp_sub_le` (135) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTdm_sub_le` (149) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTP_sub_le` (163) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTP'_sub_le` (169) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTQ_sub_le` (175) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `norm_homModTQt_sub_le` (181) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModSolve_entry` (192) | theorem | **PASS** — modified-divisor, solve, reweighting or bound helper; see modified proof chain. |
| `homModSolveTaylor` (223) | def | **PASS** — Fourier solution with twisted Q/Qt and reweighted ordinary other components; true entries proved. |

## Audited source hashes

SHA-256 of each scoped module; paths are the module name with dots replaced by slashes and `.lean` appended.

| Module | SHA-256 |
|---|---|
| `KAM.Wave.KamStep.ModifiedStepSolve` | `90710198f964abd89570508f809cf073d6b1c2b5e422a18a92ff3347e8e7d7f4` |
| `KAM.Wave.KamStep.NewHamBracket` | `cccf144f2d9f153635a93b82624ee17ec9d34f01fd6d984bd8c4eff3bb5268b4` |
| `KAM.Wave.KamStep.NewHamConcrete` | `acd8f8fe18d62dca468d7c69f8672ddcc4856412e962764918bd533aec54a9a9` |
| `KAM.Wave.KamStep.NewHamConj` | `89341d7196715664b9056951151f22f720f05e30693ce8e1a3ccb667daefc7b8` |
| `KAM.Wave.KamStep.NewHamExp` | `0259a6b6e69adf6eba7b6993566c560687085ea467f46c53fcad41900b8e81bb` |
| `KAM.Wave.KamStep.NewHamFlow` | `24e4c6c743186852776af3a23cc7a514d55ae01dee75063394a8bdce40baf6e1` |
| `KAM.Wave.KamStep.NewHamIntegral` | `3459c4fa85e8190a9340277a439b7b463966b089eb1e7a39a5ccb14a74fc6c63` |
| `KAM.Wave.KamStep.NewHamLip` | `9819d1f60c6adfb9ffec798e2b2710c376ed913e64642e8d1e7ef619052c7eda` |
| `KAM.Wave.KamStep.NewHamTransport` | `6919731486855336710196e09b9d06713293e62a9d380111614c2ec9ab93cb71` |
| `KAM.Wave.KamStep.RealFlowPicard` | `edd103370fe6c5377182d06a2a19d7e64ae767af6441f8bdd6dd5f10febcc61b` |
| `KAM.Wave.KamStep.RealNField` | `abcebd36c3dd1f84b23d0988de6406dc8e5ad9a30c3faa2b0b5f5740d6cf82b0` |
| `KAM.Wave.KamStep.RealSmoothOnto` | `7b958e28916146944e27687c88cfd994339b1c7cefd25ecdfc109567659ec63f` |
| `KAM.Wave.KamStep.RealStep` | `3daa1cc36a65330eaef43f401e8c365e0052d92b06fe34e80d73c386e1ed9d82` |
| `KAM.Wave.KamStep.RealTaylorFun` | `8c1d1f605e118f77a1421d6c353cc6fec6325f0b0a89d28baef1fb71d9622167` |
| `KAM.Wave.KamStep.RealTaylorOf` | `abe96529b678ce02e4f267908390c6a4d4eed7b636f69afcf275b75646905513` |
| `KAM.Wave.KamStep.RealWeakConj` | `8c904bcbe2f4f2c0e20cae0f1427dee0b572c339f3e69886bf6ded5056b7f805` |
| `KAM.Wave.KamStep.StepBracket` | `672afd791e507fe847d2d13dbd8e39f35b921682ae0feb23e03f27a5cdf05e5f` |
| `KAM.Wave.KamStep.StepClauses` | `170e44ae22bfe595bdb7d8f4582630311953066a1dd772ff669247c0b7f40cc1` |
| `KAM.Wave.KamStep.StepConj` | `8e624a10914666e69f7a539f1003f37262b23a0f04e203255008179c20595562` |
| `KAM.Wave.KamStep.StepCore` | `77b1de2d3505ad9b30960bd7057a6cf0d9de7a93387d2aab7f3610c0a972d138` |
| `KAM.Wave.KamStep.StepCtx` | `acf74c9663b30c8eecaca159425f7ddce526b61f161bd3cd832a6c441dd2bead` |
| `KAM.Wave.KamStep.StepFlowClauses` | `e43e2a03596d3a5b0073117c2a03ec07efef059fbce3d516f9538d387ac6e131` |
| `KAM.Wave.KamStep.StepFlowConcrete` | `3f425714202c8b0c583d9c642860ec2be4bab0d187faf980b82516483a247a0e` |
| `KAM.Wave.KamStep.StepFlowFam` | `93296fc367ad92986a30aa3c75eda09dabefdcc572e27153384e73ac25cef59c` |
| `KAM.Wave.KamStep.StepFreqBound` | `6b1f28eef39d965fe76787043d9f73e4590f8904e633d110e1832bcce9068e8b` |
| `KAM.Wave.KamStep.StepHyp` | `f3fde5e2dd025b997fcaaa62830c2c11e4165887b7603a0506a4000e30de3d33` |
| `KAM.Wave.KamStep.StepHypMod` | `ea20f598f277d50072d2edb64e7750dfca07c2479dc34049c7ac75241d4601eb` |
| `KAM.Wave.KamStep.StepLip` | `9a5df8a2b43720b2876ed33751ec323bfd3488c09dda85041b6c182455faf2b5` |
| `KAM.Wave.KamStep.StepMargin` | `1d0b349ba0cde177dbe4c73df05748a39d54e920e457e5464c87ea3cf856524d` |
| `KAM.Wave.KamStep.StepNplus` | `f113e3b622a9aebc977ffad471d748fafda2a73bfc936d73f9f65f3d805d50fa` |
| `KAM.Wave.KamStep.StepNuIntegral` | `6f5528af1a44edb29ea8e1178296c98a62c5543afaba03a807850ebfca360a77` |
| `KAM.Wave.KamStep.StepPeriodicFlow` | `db991b66c532214973fb335117eb6bef9231d53f51d73492bce75f8a83fd933d` |
| `KAM.Wave.KamStep.StepPeriodic` | `629e9ab63484ac9a01e9205809ea925d12585f0df2c1d611683b96c30f3e24d0` |
| `KAM.Wave.KamStep.StepPlusA` | `d220bbc4d5f25c5e39f40a16c60e161e43ccd5e35473ca87ebac4175b788b438` |
| `KAM.Wave.KamStep.StepPlusArith` | `7cf317cd8c73bd0298ff970a58afe3f3c980abdd55e23a7fbb53e3ad665f39af` |
| `KAM.Wave.KamStep.StepPlusAssemble` | `f09c3f4170e300eac8f659820a4025695d790fe82b6a396c2e18ae09584e1be7` |
| `KAM.Wave.KamStep.StepPlusBound` | `242453870f8b9f274b47ba82f8764aa8a362a4b61e8cb1ecad4023ab13de32a7` |
| `KAM.Wave.KamStep.StepPlusClass` | `14275e4f00a2645fff79958504d52446bf0476e97cc8a2fc9e6ad2213c4c65db` |
| `KAM.Wave.KamStep.StepPlusFam` | `a6a36f6963febf7f32d29386a1fa8fc2c79c52cab308eb5a8b3bb55e15aa085e` |
| `KAM.Wave.KamStep.StepPlusFinal` | `ed23813defba0113789a58af760bbcd6177caabcb5c79fab4c1482a4cb38a816` |
| `KAM.Wave.KamStep.StepPlusLam` | `f89a0f7eca97b90c7dd548a5c0a1437e79760262403ef8f54c583509a70b1ad2` |
| `KAM.Wave.KamStep.StepPlus` | `0a943dca873a92fd54a2aa0ae343b1e1a51398170a2bb626e151025768015a61` |
| `KAM.Wave.KamStep.StepPullbackBound` | `0df64ec69651d9832909a7a36218f86b3a324a8574a4e90110e60a7940f70684` |
| `KAM.Wave.KamStep.StepReweight` | `e78b0127d7846d70299ed273798ddeb3ab573815c89ffd6193a68e8bc5b1439a` |
| `KAM.Wave.KamStep.StepReweightTaylor` | `e44faac00c4bb9bdde515b1f1a67bb51ff9d53c8dcda01eddd8fa4e18ce3def3` |
| `KAM.Wave.KamStep.StepSetup` | `ae563b84af21c810662fceade5290a5c95a6fbd1b4ef96210dc81a15d427a9a1` |
| `KAM.Wave.KamStep.StepSymplectic` | `4826557c7f2729bf31f6f178c37b5977d5bfcbad2bc1a25deb759fa6490d46d8` |
| `KAM.Wave.KamStep.StepTheorem` | `25804cf1735ae466fe0aabfd220d31ca67522cb630f97bb093cea3fc1825595e` |
| `KAM.Wave.KamStep.StepTheoremMod` | `f1b1b618f45aabf6847059a50a4a193f0ceccc67ded5b2740b7331da098dfbf3` |
| `KAM.Wave.KamStep.StepTheoremSrc` | `c6b5d837be2b34be54914469fe375dcbce6ef2846dc486ab7f227465573c50fa` |
| `KAM.Wave.Homological.ModifiedAct` | `669793363951678148165627b538ecf3e96e54bbf2607e664937b39010ee3308` |
| `KAM.Wave.Homological.ModifiedBounds` | `56a91348ffc0f4e86178495744d301c8245613ad30434787803add831e59f424` |
| `KAM.Wave.Homological.ModifiedDivisors` | `99d6127cbc4f2961cbe1245f0d2ac3de504bbdc0e1b014b525d0e1f06c85654f` |
| `KAM.Wave.Homological.ModifiedEq` | `5c00fb79b6a3b479729f991e5a259b0a77486b963b6e7a79868f3cdedcc0c2d1` |
| `KAM.Wave.Homological.ModifiedEquation` | `9a17f3d6ac3d825a5e9994cdbe862deef0aed3232f3d8b6435c1cda507a7241c` |
| `KAM.Wave.Homological.ModifiedLipDeriv` | `6a9b5679c07447f06d87388aba25c82b1452dd17159027a44bdfee8a00029042` |
| `KAM.Wave.Homological.ModifiedLipField` | `3274bab1934032eacdd9c6b939caf7886b305701404d8c408907987cad76e2ad` |
| `KAM.Wave.Homological.ModifiedLip` | `efa7ddfe530f00f91997bed66a9252abb769013805400f0886c528827876936a` |
| `KAM.Wave.Homological.ModifiedReal` | `793f8331575b61b081e5bc4393eaebef69594fa5587764daea886fee62fb82fb` |
| `KAM.Wave.Homological.ModifiedReweight` | `50b15c95bb570279730adf8feab99abf3368a0ea3bce728a5190d8ff440b4883` |
| `KAM.Wave.Homological.ModifiedSolve` | `b6ca27819924fa73fe043a3911bcade3e4b015d9a5dd1d701e9e1fac7e2f6959` |
