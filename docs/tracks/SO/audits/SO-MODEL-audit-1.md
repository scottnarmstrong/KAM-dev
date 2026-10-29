# SO-MODEL independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-somodel`.
Audited HEAD: `1b08d8b1c5550bd399124c69bd964b47bbe6ba94`.
Comparison ref `inp`: `836e8efe03c1f2e23422a12dd35058c9bc7101a6`.

## Verdict and scope

**PASS WITH NOTES for SO-MODEL (unfrozen helper package).** All four requested slices are complete against
`/root/code/KAM-inp/.drafts/briefs/offload-main/SO-MODEL.md` and proposal §§2, 5, with the clarifications below.
No frozen theorem is proved or proposed for sealing by this package. Accordingly the per-anchor verdict and
provider/frozen-type and copied seal-body probes are **not applicable**, rather than evidence of a seal.
There is no SO signature file or blueprint graph; the handoff expressly assigns the brief and proposal as the
statement authorities. Tracks I/N/P statements are context, not additional obligations of this SO slice.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the audit/prover briefs, SO-MODEL handoff and AUDIT FOCUS,
external local SO plan, proposal and feasibility report, relevant frozen definitions, and the IG1Body interface.
Inspected the entire `git -C /root/code/KAM-inp-somodel diff inp...HEAD`: exactly four new Lean files,
960 lines total; no other committed change. User's exact worktree report destination overrides the generic
brief's main-inp destination. No repository file was edited except this report; temporary probes/logs were
confined to `.lake/abi-scratch/` and removed after incorporating their output. No state-changing git operation.

| Slice | Verdict | Reason |
| --- | --- | --- |
| Model / proposal §2.3 | PASS | Every rational coefficient, parameter, phase, derivative sign, and mode matches. |
| PeriodOne / §2.2 | PASS | Both changes of variables and both solution implications; correct 2π force factor. |
| Hamiltonian / §2.4 | PASS | Actual frozen fields and bordered Hessian, with determinant −1. |
| ScalarEmbedding / §§5.1–5.2 | PASS WITH NOTES | Full identities and uniform norm bound for general holomorphic u; phase rescaling explicit; candidate reality remains unproved as allowed by AUDIT FOCUS. |
| Hygiene | PASS WITH NOTES | Build, axiom audit and kernel replay pass; lint's sole failure is the expressly permitted stale generated root. |

## Semantic review

The coefficient comparison is literal, not a numerical comparison at e*. `Model.lean:64–72` contains:

| m | Proposal §2.3 and Lean expression (identical rational polynomial) |
| --- | --- |
| 1 | −e/4 + e³/32 |
| 2 | 1/2 − 5e²/4 + 13e⁴/32 |
| 3 | 7e/4 − 123e³/32 |
| 4 | 17e²/4 − 115e⁴/12 |
| 5 | 845e³/96 − 32525e⁵/1536 |
| 6 | 533e⁴/32 |
| 7 | 228347e⁵/7680 |

`soModes = Icc 1 7`; the default coefficient branch is zero only outside that range. Parameters are exactly
549/10000 and 69/200000 in ℚ and ℝ, with proved cast equalities. The potential is −εΣA_m cos(2π(2q−mφ));
its q derivative is +4πεΣA_m sin and the physical acceleration is its negative. The φ derivative has the
correct negative sign and mode multiplier. Complex coefficients are casts of the same real coefficients.

`PeriodOne.lean:76–82` rescales angles and time together, leaving momentum unchanged.
`soVq_eq_two_pi_mul_soVradx` and the two solution implications prove dp/ds=−Vrad_x after dividing the
period-one acceleration by 2π. Round trips are equalities of arbitrary triples of real functions.

`Hamiltonian.lean:62–70,128–138` uses frozen angle/action order ((q,φ),(p,J)) and X_H=(∂I H,−∂θ H).
The actual frozen real gradient and its derivative are computed before identifying the frozen bordered
Hessian by reindexing; the determinant proof is not merely for an unrelated literal matrix. The ordinary
Hessian block is singular. This says nothing about the later approximate torus's averaged bordered torsion.

`ScalarEmbedding.lean:74–82,137–190`: the only regularity premise of the differentiated error identity is
`ContDiffAt ℂ 2 u θ`. It is legitimate local smoothness, not a conclusion-shaped premise; open-domain
holomorphy implies it by the proved helper using existing multivariable analyticity. No polynomial restriction,
frequency bound, residual smallness, or periodicity is hidden in the error formula. Periodicity is used only
for the separate primary-winding theorem. The energy identity is unconditional. Deriving J's directional
derivative gives −p Dν²u−Vq p−Vφ, so subtracting DKω from X_H gives (−r,pr), with zero angle components.

The norm uses existing Pi and product maximum norms. `norm_invarianceError_soK_le_strip` is a bound on every
point of an arbitrary set S, specialized to `complexStrip 2 ρ`; this matches the bound-based interface
`KAM/Iso/Charts/Inputs.lean:66`. It does not define a new supremum or assume a nonexistent strip norm.
Bounds Bp, Br remain arbitrary inputs; no positivity is improperly omitted (norm bounds imply what is needed
at any member of S, and the empty-set case is vacuous). Primary winding is proved for every ρ, stronger than
the positive-width analytic use case; translation invariance of fderiv also holds off differentiability.

**π-free coordinate clarification:** the brief's shorthand “v=2πu; r=2πR(v)” requires a phase-coordinate
change as well. Lean correctly states u(θ)=w(2πθ)/(2π), x=2πθ and
r(θ)=2π[Dν²w+2εΣA_m sin(2w+2x₀−mx₁)](2πθ). There is no hidden π in soRW or soDnu.
Interpreting v=2πu with the same θ coordinates would leave a 1/(2π) second-derivative coefficient in R.
The implementation and handoff explicitly state the correct coordinates; no repair is required.

## Declaration-by-declaration review

All names below have namespace `KAM.SpinOrbit`. Locators are relative to the worktree. Every new public
declaration is listed, including helpers omitted from the handoff's overview. PASS assesses this package's
scoped statement; it does not assert later certificate applicability.

| Node / locator | Lean declaration | Verdict | Reason / note |
| --- | --- | --- | --- |
| Model:44 | `soEccQ` | PASS | Exact rational eccentricity 549/10000. |
| Model:47 | `soEpsQ` | PASS | Exact rational perturbation 69/200000. |
| Model:50 | `soEcc` | PASS | Exact real eccentricity 549/10000. |
| Model:53 | `soEps` | PASS | Exact real perturbation 69/200000. |
| Model:55 | `soEcc_eq_ratCast` | PASS | Exact compatibility with the rational data. |
| Model:58 | `soEps_eq_ratCast` | PASS | Exact compatibility with the rational data. |
| Model:61 | `soEps_pos` | PASS | Direct proof of the displayed scoped statement; no added source premise. |
| Model:64 | `soCoeffPoly` | PASS | All seven branches match proposal §2.3; zero outside 1..7 is intentional. |
| Model:75 | `soA` | PASS | Evaluation of the table at the fixed real eccentricity. |
| Model:78 | `soAQ` | PASS | Evaluation of the same table in ℚ. |
| Model:80 | `soA_eq_ratCast` | PASS | Exact compatibility with the rational data. |
| Model:95 | `soModes` | PASS | Finset.Icc 1 7 includes each required mode once. |
| Model:100 | `soV` | PASS | Exact real seven-mode period-one potential. |
| Model:104 | `soVC` | PASS | Same formula and coefficients over ℂ. |
| Model:108 | `soVq` | PASS | Correct positive 4πε sine derivative. |
| Model:112 | `soVφ` | PASS | Correct negative 2πε weighted sine derivative. |
| Model:116 | `soVqC` | PASS | Complexification of the q derivative. |
| Model:120 | `soVφC` | PASS | Complexification of the φ derivative. |
| Model:126 | `soVC_ofReal` | PASS | Correct real-to-complex compatibility. |
| Model:129 | `soVqC_ofReal` | PASS | Correct real-to-complex compatibility. |
| Model:132 | `soVφC_ofReal` | PASS | Correct real-to-complex compatibility. |
| Model:136 | `soVC_add_int` | PASS | Exact integer-shift periodicity of the defined potential. |
| Model:146 | `soV_add_int` | PASS | Exact integer-shift periodicity of the defined potential. |
| Model:152 | `soV_periodic_q` | PASS | Exact integer-shift periodicity of the defined potential. |
| Model:155 | `soV_periodic_φ` | PASS | Exact integer-shift periodicity of the defined potential. |
| Model:158 | `soVC_periodic_q` | PASS | Exact integer-shift periodicity of the defined potential. |
| Model:161 | `soVC_periodic_φ` | PASS | Exact integer-shift periodicity of the defined potential. |
| Model:164 | `soVC_differentiable` | PASS | Joint complex differentiability on all ℂ×ℂ: entireness. |
| Model:168 | `soVC_differentiable_pi` | PASS | Joint entireness in the required Fin 2 carrier. |
| Model:172 | `soVC_analyticOnNhd_q` | PASS | One-variable analytic packaging; joint holomorphy is separately proved. |
| Model:176 | `soV_differentiable` | PASS | Direct proof of the displayed scoped statement; no added source premise. |
| Model:184 | `hasDerivAt_soV_comp` | PASS | Chain-rule computation of the stated actual derivative. |
| Model:202 | `hasDerivAt_soVC_comp` | PASS | Chain-rule computation of the stated actual derivative. |
| Model:222 | `hasDerivAt_soV_q` | PASS | Chain-rule computation of the stated actual derivative. |
| Model:225 | `hasDerivAt_soV_φ` | PASS | Chain-rule computation of the stated actual derivative. |
| Model:228 | `hasDerivAt_soVC_q` | PASS | Chain-rule computation of the stated actual derivative. |
| Model:231 | `hasDerivAt_soVC_φ` | PASS | Chain-rule computation of the stated actual derivative. |
| Model:234 | `deriv_soV_q` | PASS | Chain-rule computation of the stated actual derivative. |
| Model:237 | `deriv_soV_φ` | PASS | Chain-rule computation of the stated actual derivative. |
| Model:244 | `soField` | PASS | Physical field defined using the actual deriv of V. |
| Model:248 | `soField_eq` | PASS | Direct proof of the displayed scoped statement; no added source premise. |
| Model:252 | `soVq_explicit` | PASS | Direct proof of the displayed scoped statement; no added source premise. |
| Model:258 | `IsSoSolution` | PASS | Global real-time HasDerivAt solution predicate; no existence assumed. |
| Model:262 | `isSoSolution_iff` | PASS | Solution predicate unfolded to the intended equations. |
| PeriodOne:32 | `soVrad` | PASS | Exact radian potential, phases 2x−mf. |
| PeriodOne:36 | `soVradx` | PASS | Actual x derivative, factor 2ε. |
| PeriodOne:39 | `soV_eq_soVrad` | PASS | Exact potential equality under angle conversion. |
| PeriodOne:45 | `soVq_eq_two_pi_mul_soVradx` | PASS | Period-one force is exactly 2π times radian force. |
| PeriodOne:52 | `soVrad_eq_soV` | PASS | Exact potential equality under angle conversion. |
| PeriodOne:57 | `hasDerivAt_soVrad_x` | PASS | Chain-rule computation of the stated actual derivative. |
| PeriodOne:71 | `IsSoRadSolution` | PASS | Global real-time radian-system solution predicate. |
| PeriodOne:76 | `soToRad` | PASS | x=2πq(s/2π), y=p(s/2π), f=2πφ(s/2π). |
| PeriodOne:81 | `soFromRad` | PASS | q=x(2πt)/2π, p=y(2πt), φ=f(2πt)/2π. |
| PeriodOne:84 | `soFromRad_soToRad` | PASS | Exact function rescaling or solution transport, including all 2π factors. |
| PeriodOne:90 | `soToRad_soFromRad` | PASS | Exact function rescaling or solution transport, including all 2π factors. |
| PeriodOne:96 | `hasDerivAt_comp_div` | PASS | Generic time-division chain rule; valid even for c=0. |
| PeriodOne:101 | `hasDerivAt_comp_mul` | PASS | Generic time-multiplication chain rule. |
| PeriodOne:106 | `isSoRadSolution_soToRad` | PASS | Exact function rescaling or solution transport, including all 2π factors. |
| PeriodOne:120 | `isSoSolution_soFromRad` | PASS | Exact function rescaling or solution transport, including all 2π factors. |
| PeriodOne:138 | `isSoRadSolution_iff` | PASS | Both directions proved, including time change and force scaling. |
| Hamiltonian:45 | `soHasDerivAt_line` | PASS | General line-chain-rule helper; renamed collision is resolved. |
| Hamiltonian:53 | `fderiv_apply_eq_deriv_line` | PASS | Differential recovered from derivative along the line. |
| Hamiltonian:62 | `soHR` | PASS | J+p²/2+V with angles first and actions second. |
| Hamiltonian:66 | `soHC` | PASS | Same Hamiltonian over ℂ. |
| Hamiltonian:70 | `soH0` | PASS | Integrable action Hamiltonian J+p²/2. |
| Hamiltonian:72 | `soHC_ofReal` | PASS | Correct real-to-complex compatibility. |
| Hamiltonian:76 | `soHR_differentiable` | PASS | Direct proof of the displayed scoped statement; no added source premise. |
| Hamiltonian:79 | `soHC_differentiable` | PASS | Direct proof of the displayed scoped statement; no added source premise. |
| Hamiltonian:83 | `fderiv_soHR_apply` | PASS | Chain-rule computation of the stated actual derivative. |
| Hamiltonian:99 | `fderiv_soHC_apply` | PASS | Chain-rule computation of the stated actual derivative. |
| Hamiltonian:118 | `soExtField` | PASS | Real autonomous physical extension with Jdot=−Vφ. |
| Hamiltonian:123 | `soExtFieldC` | PASS | Complex autonomous extension with correct signs. |
| Hamiltonian:128 | `hamiltonianVectorField_soHR` | PASS | Equality to frozen real vector field at every point. |
| Hamiltonian:134 | `hamiltonianVectorFieldℂ_soHC` | PASS | Equality to frozen complex vector field at every point. |
| Hamiltonian:141 | `soExtFieldC_ofReal` | PASS | Correct real-to-complex compatibility. |
| Hamiltonian:152 | `soBordered` | PASS | Literal proposal 3×3 bordered matrix over any commutative ring. |
| Hamiltonian:155 | `det_soBordered` | PASS | Literal bordered determinant −1, generalized to any commutative ring. |
| Hamiltonian:159 | `det_soHessian0` | PASS | Literal 2×2 Hessian block determinant zero; derivative bridge proved separately. |
| Hamiltonian:164 | `soBorderEquiv` | PASS | Genuine two-sided index equivalence; border is last. |
| Hamiltonian:170 | `fderiv_soH0Re_apply` | PASS | Chain-rule computation of the stated actual derivative. |
| Hamiltonian:182 | `frequencyMap_soH0` | PASS | Frozen real-restriction gradient is (p,1). |
| Hamiltonian:188 | `fderiv_frequencyMap_soH0` | PASS | Actual derivative of frozen frequencyMap is (v₀,0). |
| Hamiltonian:208 | `borderedHessian_soH0` | PASS | Actual frozen bordered Hessian equals the reindexed literal matrix. |
| Hamiltonian:221 | `det_borderedHessian_soH0` | PASS | Actual frozen bordered determinant is −1. |
| ScalarEmbedding:46 | `soDir` | PASS | Complex direction (ν,1). |
| ScalarEmbedding:49 | `soOmega` | PASS | Real frequency (ν,1). |
| ScalarEmbedding:51 | `soOmega_cast` | PASS | Direct proof of the displayed scoped statement; no added source premise. |
| ScalarEmbedding:55 | `soDnu` | PASS | Directional fderiv; derivative identities are guarded by regularity. |
| ScalarEmbedding:58 | `soP` | PASS | Momentum ν+Dνu. |
| ScalarEmbedding:61 | `soJ` | PASS | Energy-zero auxiliary action −p²/2−V. |
| ScalarEmbedding:65 | `soK` | PASS | Candidate map ((θ₀+u,θ₁),(p,J)); no injectivity claim. |
| ScalarEmbedding:69 | `soResidual` | PASS | Dν²u+Vq with the actual complex force derivative. |
| ScalarEmbedding:74 | `differentiableAt_soDnu` | PASS | Local C² suffices for differentiating Dνu. |
| ScalarEmbedding:79 | `contDiffAt_of_differentiableOn` | PASS | Open-domain holomorphy implies the local C² premise; no circular input. |
| ScalarEmbedding:84 | `differentiableAt_soK` | PASS | Local C² suffices for differentiability of the entire candidate map. |
| ScalarEmbedding:108 | `soHC_soK` | PASS | Unconditional energy identity; stronger than analytic-only scope. |
| ScalarEmbedding:113 | `soDnu_q` | PASS | Dν(θ₀+u)=p under local C². |
| ScalarEmbedding:128 | `soDnu_φ` | PASS | Dνθ₁=1 without assumptions on u. |
| ScalarEmbedding:137 | `fderiv_soK_dir` | PASS | All four differentiated candidate coordinates; only local C². |
| ScalarEmbedding:183 | `invarianceError_soK` | PASS | Exact frozen error ((0,0),(−r,pr)); only local C². |
| ScalarEmbedding:193 | `norm_error_form_le` | PASS | Pi and product max norms give the exact requested factor. |
| ScalarEmbedding:206 | `norm_invarianceError_soK_le` | PASS | Pointwise norm inequality with local C². |
| ScalarEmbedding:214 | `norm_invarianceError_soK_le_strip` | PASS | Uniform-bound form on arbitrary S; specializes to complexStrip 2 ρ. |
| ScalarEmbedding:223 | `soK_primary` | PASS | Global integer periodicity implies frozen primary winding for any ρ; no regularity needed. |
| ScalarEmbedding:249 | `soUofW` | PASS | u(θ)=w(2πθ)/(2π), including phase-coordinate change. |
| ScalarEmbedding:252 | `soRW` | PASS | Explicit π-free phase-coordinate residual Dν²w+2εΣ A_m sin(2w+2x₀−mx₁). |
| ScalarEmbedding:256 | `soDnu_comp_smul` | PASS | Directional chain rule for scalar phase rescaling. |
| ScalarEmbedding:265 | `soDnu_soUofW` | PASS | First derivative rescaling cancels 2π. |
| ScalarEmbedding:280 | `soDnu_soDnu_soUofW` | PASS | Second derivative contributes exactly 2π; uses local eventual equality. |
| ScalarEmbedding:298 | `soResidual_soUofW` | PASS | r(θ)=2π R(w)(2πθ), local C² at 2πθ. |

## Definition classification (all 37 definitions)

All are exposed public definitions; no new abbrev, structure, instance, or bundled hypothesis is introduced.

| Definitions | Classification and whole-carrier behavior |
| --- | --- |
| soEccQ, soEpsQ, soEcc, soEps | Exact fixed rational/real constants. |
| soCoeffPoly, soA, soAQ | Explicit table expressions and specializations, with intentional zero extension on ℕ. Generic Field generalization is literal field arithmetic; rational-model interpretation uses characteristic-zero ℚ/ℝ/ℂ only. |
| soModes | Exact finite support 1..7. |
| soV, soVC, soVq, soVφ, soVqC, soVφC | Entire finite trigonometric expressions; derivatives verified, no truncated tail omitted. |
| soField, IsSoSolution | Actual derivative-based field and global HasDerivAt solution predicate. |
| soVrad, soVradx, IsSoRadSolution, soToRad, soFromRad | Explicit radian expressions, global solution predicate, and mutually inverse function transforms. |
| soHR, soHC, soH0, soExtField, soExtFieldC | Explicit Hamiltonians and autonomous fields on the full finite-dimensional carriers. |
| soBordered, soBorderEquiv | Literal matrix and genuine index equivalence. The if-branch partitions Fin 3; no junk case. |
| soDir, soOmega | Real/complex versions of (ν,1). |
| soDnu, soP, soJ, soK, soResidual | Actual directional derivative, momentum, energy-zero action, candidate map, scalar residual. Mathlib fderiv is total and zero off differentiability; differentiated identities have the C² premise, so no proof exploits that fallback. The unconditional energy identity and primary winding remain valid for arbitrary functions. |
| soUofW, soRW | Explicit phase-coordinate transform and π-free residual; 2π≠0 is proved where cancellation is needed. |

## Independent validation

All Lean/Lake commands used `LEAN_NUM_THREADS=1` and `nice -n 5` (the compile gate itself applies nice).
They were run sequentially: gate build, axiom probe, one kernel-replay invocation, then lint (which runs ABI
probes). No overlapping Lean checks, cache downloads, package updates, clean builds, or source repairs.

Targeted build, exit 0:

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-somodel KAM.SpinOrbit.Model KAM.SpinOrbit.PeriodOne KAM.SpinOrbit.Hamiltonian KAM.SpinOrbit.ScalarEmbedding
[inp-gate] slot 1 acquired 11:04:55 for KAM.SpinOrbit.Model KAM.SpinOrbit.PeriodOne KAM.SpinOrbit.Hamiltonian KAM.SpinOrbit.ScalarEmbedding
Build completed successfully (2874 jobs).
```

Axiom probe, exit 0:

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOModelAudit.lean
```

Probe imported `KAM.SpinOrbit.PeriodOne` and `KAM.SpinOrbit.ScalarEmbedding` and issued `#print axioms` for
**every one of the 73 new public theorems**, generated from the four source files. Exact output:

```text
'KAM.SpinOrbit.soHasDerivAt_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.fderiv_apply_eq_deriv_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soHC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soHR_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soHC_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.fderiv_soHR_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.fderiv_soHC_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hamiltonianVectorField_soHR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hamiltonianVectorFieldℂ_soHC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soExtFieldC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.det_soBordered' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.det_soHessian0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.fderiv_soH0Re_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.frequencyMap_soH0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.fderiv_frequencyMap_soH0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.borderedHessian_soH0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.det_borderedHessian_soH0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soEcc_eq_ratCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soEps_eq_ratCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soEps_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soA_eq_ratCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVqC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVφC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVC_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soV_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soV_periodic_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soV_periodic_φ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVC_periodic_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVC_periodic_φ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVC_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVC_differentiable_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVC_analyticOnNhd_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soV_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_soV_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_soVC_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_soV_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_soV_φ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_soVC_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_soVC_φ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.deriv_soV_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.deriv_soV_φ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soField_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVq_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.isSoSolution_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soV_eq_soVrad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVq_eq_two_pi_mul_soVradx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soVrad_eq_soV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_soVrad_x' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soFromRad_soToRad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soToRad_soFromRad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_comp_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hasDerivAt_comp_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.isSoRadSolution_soToRad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.isSoSolution_soFromRad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.isSoRadSolution_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soOmega_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.differentiableAt_soDnu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.contDiffAt_of_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.differentiableAt_soK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soHC_soK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soDnu_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soDnu_φ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.fderiv_soK_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.invarianceError_soK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.norm_error_form_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.norm_invarianceError_soK_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.norm_invarianceError_soK_le_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soK_primary' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soDnu_comp_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soDnu_soUofW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soDnu_soDnu_soUofW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soResidual_soUofW' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, exit 0:

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Model KAM.SpinOrbit.PeriodOne KAM.SpinOrbit.Hamiltonian KAM.SpinOrbit.ScalarEmbedding
replaying KAM.SpinOrbit.ScalarEmbedding
replaying KAM.SpinOrbit.Hamiltonian
replaying KAM.SpinOrbit.PeriodOne
replaying KAM.SpinOrbit.Model
```

Lint, exit 1 solely for the generated-root exception explicitly allowed by the audit brief:

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1285 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No root regeneration was attempted. Module, frozen-anchor, and elaborated ABI checks passed.


Additional read-only checks:

- `git -C /root/code/KAM-inp-somodel diff --check inp...HEAD`: exit 0, no output.
- `git -C /root/code/KAM-inp-somodel diff --check`: exit 0, no output.
- `git -C /root/code/KAM-inp-somodel diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
- All 110 public declarations have unique short names across KAM (declaration scan); generic helper names
  also searched in Mathlib, with no collision. The line helper is now `soHasDerivAt_line`; the obsolete handoff
  spelling is corrected by its appended orchestrator note. No new root declarations or harmful shadowing.
- Forbidden-token/override/native_decide/Lean.ofReduceBool scan of KAM/SpinOrbit: no matches.
- All four files have copyright, module, public imports, module docstring, exposed public section.
  Sizes / maximum Unicode line widths: Model 270 / 99; PeriodOne 147 / 98; Hamiltonian 226 / 99;
  ScalarEmbedding 317 / 99. All fit 1500 lines and 100 columns.
- Recursive local KAM import inspection: 26 modules, including 17 frozen definition modules; no provider or
  frozen theorem anchor in the closure. Relevant frozen vector-field, invariance-error and bordered-Hessian
  definitions are manifest SEALED; there is no imported DRAFT_SORRY theorem to justify.

## Uncertainties, source defects, and deviations

No defect found in the controlling proposal coefficient table, model units, or §§5.1–5.2 identities. This audit
compares the pinned local proposal exactly; it does not independently authenticate its coefficient table
against Celletti's original book. No new external-source erratum is claimed.

The older proposal's §1, §3 target `3/100` is superseded by the SO plan's explicit owner D30 target `33/1000`,
following the feasibility report. This preexisting documented scope change does not affect any identity here;
SO-MODEL proves no confinement statement. No new deviation was introduced by the auditor.

Two scope notes for downstream consumers:

1. `IsRealOnReals (soK ν u)` is not proved. AUDIT FOCUS explicitly says this is not a failure unless required
   by the brief; the brief requests potential reality, which is proved. A later IG1Body application still needs
   the candidate's reality, analytic-domain, derivative/inverse/torsion, and smallness inputs.
2. `soK` is a candidate map, not a proved injective embedding or an exact invariant torus. No certificate,
   numerical bound, clock bridge, or lunar confinement theorem is certified by this audit. Global periodicity
   in `soK_primary` is satisfied by entire periodic Fourier candidates; a strip-only periodicity API could be
   added later, but is not needed to complete this slice.

## Audited source SHA-256

```text
586af68ee2cc4d5bdefbabc9d40aa7950d24c2970ea026d3d9d69e63e6bb295e  KAM/SpinOrbit/Hamiltonian.lean
d9b99918c48809dd7713fcd0560a58b0c347a99bb603bea05d316aef22f8d46f  KAM/SpinOrbit/Model.lean
030741ad22fdd2ef31b4e7e192cb72190c53e8a60fda9fdc35ec9abf3e26b0d4  KAM/SpinOrbit/PeriodOne.lean
b3b95325afa0da17a1c5c7fab124aff41e7cdcbbc914bf6d0ccfeec5cb13c75b  KAM/SpinOrbit/ScalarEmbedding.lean
```
