# W-GRAPH-CLOSE independent package audit 1

Auditor: `maud-wpj-1`. Date: 2026-11-01. **Overall: FAIL for complete ten-node closure; nine PROVED-OK, one NOT.** No frozen anchor is being sealed by this package.

Audited HEAD: `d986d53c2767de387c096e075e3559c111ef9fd5`; comparison branch `inp`: `fc55b79512be84ee028470d409482b30fc434a71`. Scope is exactly the ten KEEP nodes of D27's `BYPASS-audit-1.md`, read with `git -C /root/code/KAM-inp-wgraph show inp-wgraph-byp:docs/graph/W/reviews/BYPASS-audit-1.md`. Read the package audit brief, AGENTS.md, PLAN.md, DECISIONS.md, producer handoff, relevant blueprint paragraphs, packet blocks, and declaration types and bodies. The handoff has no separately titled AUDIT FOCUS section; its node table and uncertainties supply the focus. The generic brief's `docs/tracks/W/statement.md` does not exist; the available track statement document is `docs/tracks/W/W-STATEMENTS.md` (historical draft). Current node statements, not that historical draft status, control this audit.

The owner's D53 command wrapper and lint route in the task override the generic brief's older invocation instructions. This is a report-only audit. No implementation, graph packet, frozen file, manifest, or root was edited.

## Per-node decisions and exact LEAN_REF records

Names below are fully qualified. Lists are the records recommended for this audit; old inaccurate or redundant lists should be replaced, not silently retained. PROVED-OK allows stronger statements and the existing weighted-coordinate representation. It does not allow a conditional `StepCore` helper to stand in for a source-facing export.

| Node | Verdict | Exact LEAN_REF list to record | Statement comparison |
|---|---|---|---|
| `bpW:w5:flow` | **PROVED-OK** | `KAM.Wave.stepFlowLemma, KAM.Wave.stepFlowLemmaMod` | `ExportFlow.lean:66,189`: both regimes, every time in `[-1,1]`; concrete `FlowHyp`, `M_F ≤ σ/256`, `M_F/(σ/4) ≤ 1/64`, and all four clauses. Holomorphic smoothing displacement, both derivative bounds and `≤ η²`, nested image domains, reality, and all integer translations are present. |
| `stepW:w5:f-flow` | **PROVED-OK** | `KAM.Wave.stepFlow_fFlow, KAM.Wave.stepFlowMod_fFlow` | `ExportFlow.lean:126,249`: all-time image inclusion, integral identity for the embedded field, holomorphic smoothing lift and `‖Ψᵗ‖ ≤ |t| M_F`. The lift identity identifies the displacement in the source carrier. |
| `stepW:w5:f-par` | **PROVED-OK** | `KAM.Wave.stepFlow_fPar, KAM.Wave.stepFlowMod_fPar` | `ExportFlow.lean:147,270`: nonnegative uniform sup/Lipschitz witnesses with total `≤ 2M_F`, for every permitted time and all parameter pairs. Exactly the norm interpretation prescribed at `w5-kamstep.tex:114–118`. |
| `stepW:w5:f-der` | **PROVED-OK** | `KAM.Wave.stepFlow_fDer, KAM.Wave.stepFlowMod_fDer` | `ExportFlow.lean:160,283`: on precisely `D(s−3σ,r/4)`, derivative decomposition through the smoothing inclusion, `8M_F/σ`, parameter total `16M_F/σ`, and `16M_F/σ ≤ η²`. The core proof uses the `σ/8` ball margin. |
| `bpW:w7:shell-geom` | **PROVED-OK** | `KAM.Wave.shellGeom` | `ExportShells.lean:108`: disjointness, Borel measurability, equality of the union with the open box, exact volume, boundary-layer constant 7, lower max-norm bound, and diameter. Only `t₀>0` is required, a strengthening of the source's `0<t₀≤1/2`. |
| `stepW:w7:partition` | **PROVED-OK** | `KAM.Wave.shellSet_partition, KAM.Wave.shellGeom` | `ExportShells.lean:80,108`: unique shell index `l≥k`, the exact half-open max characterization and volume difference. The second reference also covers the packet's broader `SOURCE_CONCLUSION: (i)`, including Borel/disjoint/union assertions. |
| `bpW:w0n:algebra` | **PROVED-OK** | `KAM.Wave.wave_algebra_w0n` | `ExportW0n.lean:74`: absolute summability, membership and norm bound with the actual `waveAlgConst s`, plus the exact `K_(3/2)²` identity. Equivalent older two-reference mapping: `KAM.Wave.wave_algebra, KAM.Wave.waveAlgConst_three_halves_sq`. |
| `stepW:w0n:weight` | **PROVED-OK** | `KAM.Wave.wave_weight_step` | `ExportW0n.lean:36`: all three packet conclusions, with the intermediate exponential-weight inequality as well. Integer indices, `max 1 |l|` bracket, hypotheses and constants match. |
| `bpW:w5:solve` | **NOT** | **No complete PROVED LEAN_REF list.** For a retained PARTIAL record: `KAM.Wave.stepSolveLemma, KAM.Wave.stepSolveLemmaMod`. | `ExportSolve.lean:194,239` covers the packet's displayed conclusion, but omits the blueprint's “(indeed p′)” in the modified case. See F1. The non-modified case passes; the modified export states only `S_(p_+)`, while `p′=p+1`. |
| `bpW:w0:basis#lambda-facts` | **PROVED-OK** | `KAM.Wave.lamBasis_facts` | `ExportLamFacts.lean:161`: all bounds for `j:ℕ+`, strict increase, strict convexity on all real arguments, derivative formula via `HasDerivAt`, positive derivative less than 1 on positive arguments, strictly increasing derivative, and the exact successive-difference identity and bound. No W6-specific frequency names are substituted. |

## F1: solve remains incomplete against the blueprint

`blueprint-W/parts/w5-kamstep.tex:355–356` states:

> `F∈T_(s−σ)∩S_(p_+)(D(s−σ,r)), N̂∈S_(p_+)(𝒫) (indeed p′), both real`.

Step data at lines 335–336 specify `p′=p+1` in the modified case. `stepSolveLemmaMod` asserts global smoothing with `pb=p_+` only (`ExportSolve.lean:245–247`); none of its other conjuncts supplies global `p+1` smoothing. The handoff explicitly acknowledges this omission in uncertainty 4. A theorem true at `p_+` does not state the stronger conclusion at `p+1`, especially when `p_+<p+1`.

The packet `W-w5a.nodes.md:909` transcribes only `N̂∈S_(p_+)(𝒫)` and drops the parenthetical. Thus the packet-only verdict would pass, but the requested simultaneous blueprint/packet exact-statement verdict is NOT. This is a packet omission / missing export, not evidence that the source assertion is false.

I checked the modified `R` representation rather than treating its changed weight as a second defect: `StepHypMod.R1` is the `p+1` Taylor input; `StepHypMod.core` uses `(P,D_ρ∘X)` at `p_+`. Existing `stepFun_taylorRho` and `stepFun_nhat_taylorRho` (`StepReweightTaylor.lean:173,209`) identify the Hamiltonian functions with those from the original Taylor input; `StepHypMod.equation` uses these bridges. Therefore the core's reweighted `R` is not a substituted Hamiltonian. Those identities do not add the missing global `p+1` smoothing conjunct to the cited source-facing theorem.

Required closure is an explicit source-facing export for the modified normal correction in `S_(p+1)(𝒫)`, identifying it with this same `N̂`. No implementation repair or source weakening is made in this audit. Do not promote the whole solve node to PROVED using only the two partial references.

## Premise and public-helper audit

`StepHypSrc` and `StepHypModSrc` in `StepTheoremSrc.lean:95–160` contain source input data, not the conclusions of these ten nodes. In particular they assume smoothing/periodicity/reality of the input `P`, frequency and divisor conditions, explicit sup/Lipschitz majorants, and the smallness condition. They do not assume solved `F`, flow bounds, a homological identity or the desired derivative estimates. The modified hypothesis includes the source's `2β≤p+1−p_+` condition. At the W5 standing weights `a=p=1`, the guards `ha`, `hp`, `hp1` and `HomGuard` are standing/typing conditions. The exported hypotheses weaken several strip restrictions (`σ≤1`, `5σ<s`), which contain the blueprint's case. `[Fact (0<r)]` repeats the source radius positivity solely to supply the Banach-space instances.

`StepHypSrc.hyp` and its modified analogue discharge the positive-majorant splitting, including `ε₀=0`; no extra `ε₀>0` premise leaks into the exports. `StepCore` itself does bundle `F_field`, `F_sub`, `M_sum` and `equation`. Its 25 new core-layer theorems are distinctly named helpers, not independent proofs of a source node from source premises. The source-facing theorems instantiate those helpers through the constructed core. `StepCore.phiT_real_of_FT_real` is explicitly conditional on real `FT`; both final cases discharge that premise using the actual `WaveStepHyp.FT_isRealTaylor` / `StepHypMod.FT_isRealTaylor` declarations. No rule-6 violation was found in the accepted exports.

The remaining public helpers were checked in their advertised roles: elementary lambda identities and calculus; max characterization, union and disjointness for shells; monotonicity of `FlowHyp` under a larger permitted bound; integer-domain invariance; an arbitrary complex argument lying in a sufficiently wide strip; global constant-coefficient normal-form smoothing. None is substituted for a source-facing result with an unproved source obligation.

The smoothing target of `Ψᵗ` is encoded by representatives: `StepPhase r` has the same weighted-coordinate carrier for the two exponents, `stepFieldS` returns `p_+` representatives, and `stepEmbedCLM` embeds them into the `p` representatives. Its norm is `kamNorm r`. Thus `Dφᵗ=I+ι∘DΨᵗ` with a bound on `DΨᵗ` is the stated `p→p_+` bound, not a weaker `p→p` bound. The construction is the existing Picard flow of this concrete field; it is not a newly chosen map satisfying only an unrelated estimate. All uses are on `U`, for parameter members and `|t|≤1`.

## Definition fidelity and file scope

There are exactly four new definitions and no new structures, abbreviations or instances:

| Definition | Classification |
|---|---|
| `KAM.Wave.lamFun` (`ExportLamFacts.lean:39`) | Literal `sqrt(s²+m)` on its whole real carrier; all frequency/convexity/calculus claims use `m>0`. It does not claim a frequency interpretation for nonpositive mass. |
| `KAM.Wave.StepCore.phiT` (`ExportFlowCore.lean:79`) | Literal alias of existing `holoFlow` for `ι∘stepFieldS(FT ξ)` at time `t`; time one is definitionally `Phi`. As with the existing totalized flow, a dynamical interpretation is asserted only on the proved parameter/time/domain range. No global existence outside that range is certified. |
| `KAM.Wave.StepCore.PsiT` (`ExportFlowCore.lean:84`) | Literal existing `smoothDisp`, the interval integral of `stepFieldS` along the same flow, into the smoothing representatives; time one is definitionally `Psi`. Integration and displacement claims are made on the valid flow range, with bounded holomorphic integrand; no nonintegrable fallback is used by the proofs. |
| `KAM.Wave.homNhatTaylorWide` (`ExportSolve.lean:51`) | Same constant coefficients as `homNhatTaylor_gen R` at an arbitrary strip width: average `b`, diagonal average `Q`, remaining nonconstant terms zero. These are the intended normal-form coefficients, not junk values. The coefficients are genuinely constant at every angle and hence define the same polynomial everywhere; both Hamiltonian and field equalities in `stepNhat_isSmoothing_univ` are `rfl`. |

No new definition manufactures a theorem by fallback on a valid input. `ExportFlow`, `ExportShells`, and `ExportW0n` introduce theorems only.

`git diff --name-status inp...HEAD` gives six added Lean modules, the added producer handoff, and exactly one modified existing file, `KAM/Root/Wave.lean`. The root diff is precisely six new `public import` lines. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. No provider or frozen theorem is introduced or sealed. A recursive read-only import scan of all six modules found 238 local modules, no provider, and only ten frozen definition modules (ComplexStrip, OmegaZero, and eight Wave definitions), with no frozen theorem dependency. No generated file was regenerated by this auditor.

Line counts (`wc -l`), in module order: `ExportW0n` 81, `ExportLamFacts` 177, `ExportShells` 127, `ExportFlowCore` 310, `ExportFlow` 303, `ExportSolve` 278. All have copyright, `module`, interface `public import`, module documentation, and `@[expose] public ... section`. The 1500-line cap is respected.

## Verification

All auditor Lean/Lake invocations ran serially under the D53 scope; no heartbeat, recursion or synthesis override was set. Lint ran only through the specified wrapper, under the same outer cap (including its child ABI process).

Exact lint command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpj
```

Exit **0**, complete stdout:

```text
check_lean_modules: PASS (4059 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

A scratch probe imported all six new modules and issued `#print axioms` for **all 67 new public theorems**, including the helpers (14 lambda, 6 shells, 27 flow-core, 8 source-facing flow, 10 solve, 2 algebra). Exact command, from this worktree:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/WGraphCloseAudit.lean' > .lake/abi-scratch/WGraphCloseAudit.log 2>&1
```

Exit **0**, complete axiom output:

```text
'KAM.Wave.lam_eq_lamFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamFun_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamFun_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamBasis_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamBasis_div_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamBasis_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamFun_mul_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamFun_strictConvexOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamFun_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamFun_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamFun_deriv_pos_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamFun_deriv_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamBasis_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamBasis_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.mem_shellSet_iff_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.iUnion_shellSet_subset_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.iUnion_shellSet_eq_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.shellSet_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.shellSet_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.shellGeom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.FlowHyp.weakenFieldBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepDomain_U_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phiT_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.M₀_le_MF' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.MF_margins' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.M₀_div_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.MF_flow_margins' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.flowT_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phiT_mem_V' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phiT_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phiT_eq_add_PsiT' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_norm_le_M₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_lam_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.small_sub_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.fderiv_phiT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_deriv_le_M₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_deriv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_deriv_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.PsiT_deriv_lam_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.image_sub_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phiT_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phiT_translate_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.phiT_real_of_FT_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlowLemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlow_fFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlow_fPar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlow_fDer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlowLemmaMod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlowMod_fFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlowMod_fPar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepFlowMod_fDer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.mem_complexStrip_sum_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepNhat_isSmoothing_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.solve_F_isSmoothing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.solve_F_famBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.solve_Nhat_famBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.solve_omegaHat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.solve_OmegaTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.StepCore.solve_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolveLemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.stepSolveLemmaMod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.wave_weight_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.wave_algebra_w0n' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every axiom set is a subset of `{propext, Classical.choice, Quot.sound}`. In particular both solve exports and all eight source-facing flow exports have exactly those three axioms. The probe also successfully resolves every new public theorem name. Probe and log are removed after copying this evidence into the report.

`git diff --check inp...HEAD` and `git diff --check` both exit 0 with no output. The protected-file diff listed above has no output. Source inspection and lint found no forbidden constructs, option overrides, module-format or line-cap violation in the six new files.

No fresh build or kernel replay was run by this auditor: no Lean module was edited, the task explicitly reports launcher replay and name checks already completed, and the axiom probe imports the existing built artifacts for all six modules successfully. The launcher's replay stdout and exit code are not visible in this session and are **not independently claimed here**. Producer build/replay evidence and this auditor's source-fidelity decisions remain separate. This report does not certify an independently rerun kernel replay; it records the authorized reuse boundary rather than inventing unseen output.


## Errata, deviations and audit boundary

F1 is a blueprint-to-packet/export omission. No suspected error in a pinned published source was established: this audit compares the repository blueprint and packets, not independently reopens the cited PDFs. Old nonexistent `KAM.Wave.FT_isRealTaylor` and mismapped lambda names should not survive the reference replacement. The new solve exports already include the correctly namespaced reality results in their proofs; separate reality references are unnecessary in the recommended partial list.

No proof, hypothesis, normalizer, source statement or consumer was repaired. No claim is made about the other 44 D27 rows or about re-auditing the sealed headline. The sole repository addition by this auditor is this report; transient axiom probes are removed before handoff.
