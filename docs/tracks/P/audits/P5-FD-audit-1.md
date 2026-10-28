# P5-FD independent package audit 1

Overall verdict: **PASS WITH NOTES**, for the P5-FD infrastructure package and its exact revision-4 signature contract. `freq_data` and `pgAnalytic_spec` are complete, unconditional in the fixed source data, and nonvacuous. This package contains no frozen anchor or provider to seal; no verdict of seal-readiness for P-G or downstream frequency inversion is implied.

## Scope and pinned inputs

Audited HEAD `7ca93505e7b604705329abb055e95f1c2fe9ae21` in `/root/code/KAM-inp-p5fd`, dated 2026-10-28. Read AGENTS.md, PLAN, DECISIONS, the shared package-audit brief, P5-FD handoff, Track P statement, P45 design/proof plan/Revision 4, design audits 1–4, blueprint Part 5 lines 95–125, the P-G frozen telescope and relevant frozen definitions. Applied the lean-statement-audit workflow to the source-facing contract; this is not a frozen-declaration promotion.

The user's exact report destination supersedes the brief's generic main-worktree destination. Only `KAM/Planetary/PGAssembly/Frequency*.lean` is independently audited here. The imported Jets/Remainder/FastComplex/OneScale implementations are dependencies, inspected at the consumed interfaces rather than re-audited as whole packages.

`git diff inp...HEAD` was inspected. `inp` resolved to `686d56cfb012dd62ac088abd79a6dd17cb22eb98`; Git reported multiple merge bases and selected `69266082262afe2a00d98e20ee9b34e9e75880be` (the other is `6ea225e3dd432b780011f07228316a24ae4b4c46`). That diff includes 19 files: five Frequency files plus inherited Jets/Remainder files. The handoff's requested `git diff inp-p5rem...HEAD -- 'KAM/Planetary/PGAssembly/Frequency*.lean'` independently shows exactly the same five new Frequency files; current `inp-p5rem` is `27821a78dba73e87bd879b1e8462e5146349d002`, merge base `6ea225e3dd432b780011f07228316a24ae4b4c46`. Its unrelated history is excluded from the package verdict.

Shared signature source: `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, SHA256 `6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402` (the revision-4 audited hash). Independent declaration extraction, comment removal and whitespace normalization produced **True** for all nine comparisons: `PGAnalytic`, `analyticDomain`, `analyticBoundDomain`, `complexIntegrable`, `complexFrequency`, `PGAnalyticSpec`, the complete `freq_data` type, `pgAnalytic`, and `pgCU`. Only the theorem proof body is excluded from its comparison. Definition bodies and structure fields are included.

## Mathematical checks and findings

**Bounds (`stepP:p5:fd-bd`): PASS.** FrequencyJets:33–73 bounds the actual average jets via the upstream multilinear Cauchy estimate. `jpPoly` bounds the actual quadratic polynomial, retaining the factor 1/2 harmlessly below 1. For a center with fast action in the delta/16 tube and slow norm <2, the closed ball of radius delta/8 stays in `jpDom` (fast radius <delta/2) and has slow norm ≤3, using 0<delta<1. FrequencyJets:215–272 applies the Cauchy estimates for orders 1 and 2 on that ball. The operator norm identities relating `fderiv (fderiv ...)` and `iteratedFDeriv 2` are explicitly proved. No default derivative outside the differentiability domain supplies the estimates. The final polynomial/first/second derivative bounds are on the required slow-radius-2 domain, independently of the radius-1 inverse domain.

**Lipschitz (`stepP:p5:fd-lip`): PASS.** `embFast` and `embSlow` are the actual append embeddings, with norm ≤1. `jpGrad_eq` proves the chain-rule identification with the full jet derivative. The fast-action estimates call `lip_complex d.ha` on the doubled tube, with radius delta/32 and verified holomorphy and sup bounds on radius delta/16. Thus no convexity of V is assumed. The slow-action estimate differentiates along the slow embedding, controls the mixed second derivative by `jpBound`, and applies the mean-value theorem on the convex closed unit ball. It is stronger than the exported `lipConst` estimate since `jpBound ≤ lipConst`.

**Torsion (`stepP:p5:fd-beta`): PASS WITH NOTES.** `continuousOn_jetBeta_real` supplies joint parameter/action continuity. `jetBeta_lower` uses the compact set `[0,mu0] × closure V × sphere(0,1)` and the strictly positive norm of beta times a nonzero unit vector. Positivity uses the actual `jetBeta_det_closure` and source `B>0`; no arbitrary boundary value of `d.beta` is identified with the extension. Rescaling proves the homogeneous lower bound for every complex v, with v=0 handled separately. Subtracting the Theta estimates at xi=w and xi=0 yields the matrix Lipschitz constant `2*lipConst`. At distance ≤m/(4*lipConst), the perturbation is ≤m/2, giving the inverse bound with `LB=max 1 (2/m)`.

This replaces the blueprint's adjugate/Cramer route by compactness plus perturbation. It retains the required data-only LB and full complex-vector carrier. No Cramer theorem or explicit source Cramer formula is exported. The auxiliary entry bound requested as M_beta in the source is available as `jetK4 d` (or `max 1 (jetK4 d)` to ensure ≥1), uniformly even on the larger delta/2 tube. Neither an additional input nor a missing inverse estimate is hidden here.

**Assembly (`bpP:p5:freq-data`): PASS.** FrequencyBounds:104–159 actually consumes `bilip d`, `jetBeta_lower d`, `uniform_remainder d`, and `dio_one d` with tau=(a+b)+1. It chooses rho=min(rhob,betaRadius), AN=LN=lipConst, LB=max 1 (2/m), the explicit one-scale `dioConstant`, LP=max 1 (MP*coth(delta/4)^a), and the positive threshold

```text
muStar = min (min 1 mu0) (min (c0/(2*LN)) (c0/(4*LN^2*LB))).
```

The proof checks all 28 top-level conjuncts, including rho>0, rho<delta/16, muStar≤mu0, the two weak and one strict smallness inequalities, all domain guards, and the unchanged fifth-order remainder. Strictness follows from the factor 2 versus 4 and c0>0; equality at a weak endpoint cannot invalidate it. Every constant is chosen before the later mu, gamma, I, xi, J, x and v. FrequencyBounds has no placeholder, `True`, empty-domain replacement, or supplied analytic-spec premise. `pgAnalytic_spec` immediately characterizes the selected witness by the full proved specification.

## Binder audit

The only logical input to `freq_data` and `pgAnalytic_spec` is `d : PGData a b`; a,b are implicit typing indices. The following expands its fields against `PG/Setting.lean:47–79` and the exact frozen `ProperlyDegenerateKAM.lean:54–75`. Here SOURCE means the source context as fixed by frozen P-G, including its openly adopted corrected-contract premises; it does not mean these were all verbatim hypotheses of CP10.

| Expanded input | Bin | Authority / meaning |
|---|---|---|
| a | TYPING | frozen natural dimension index |
| b | TYPING | frozen natural dimension index |
| d.ha | SOURCE | positive fast dimension |
| d.hb | SOURCE | positive slow dimension |
| d.V | TYPING | real action set |
| d.hV | SOURCE | V open |
| d.hVc | SOURCE | V connected/nonempty |
| d.hVb | SOURCE | V bounded |
| d.W | TYPING | real action neighbourhood |
| d.hW | SOURCE | W open |
| d.hVW | SOURCE | closure V contained in W |
| d.hboundary | SOURCE | exists A,d>0; for every 0<t<d, two-sided frontier collar volume ≤ofReal(A*t) |
| d.r0 | TYPING | real source oscillator radius |
| d.mu0 | TYPING | real source parameter endpoint |
| d.B | TYPING | real source determinant bound |
| d.hr0 | SOURCE | r0 positive |
| d.hmu0 | SOURCE | mu0 positive |
| d.hB | SOURCE | B positive |
| d.H0 | TYPING | real integrable Hamiltonian |
| d.P | TYPING | real perturbation family |
| d.P0 | TYPING | real constant coefficient family |
| d.Omega | TYPING | real linear coefficient family |
| d.beta | TYPING | real matrix coefficient family |
| d.hP | SOURCE | joint real analyticity on [0,mu0] × closure of the disc cylinder |
| d.hperiod | SOURCE | all parameter values in [0,mu0], cylinder points and integer fast shifts; literal 2*pi period |
| d.hfreq: analytic clause | SOURCE | HasFastDiffeomorphism: H0 analytic on W |
| d.hfreq: open-image clause | SOURCE | fastFrequency image of W open |
| d.hfreq: inverse clause | SOURCE | exists g, C1 on image, g(fastFrequency I)=I on W, and g(y)∈W with fastFrequency(g(y))=y on image |
| d.hBNF: integral clause | SOURCE | all mu∈[0,mu0], I∈V and oscillator-disc p,q; angular integrability |
| d.hBNF: remainder clause | SOURCE | all eps>0, exists 0<delta≤r0, all smaller-disc p,q; literal normalized averaged expansion error ≤eps*norm(p,q)^4 |
| d.htorsion | SOURCE | all mu∈[0,mu0], I∈V: B≤abs(det beta) |
| d.hsymm | SOURCE | all mu∈[0,mu0], I∈V: beta symmetric |

Counts at the displayed expanded-field level: SOURCE=20, TYPING=12, STANDING=0, RULED=0, EXCESS=0. The inverse and epsilon-delta witnesses remain inside their source existential scopes; none is replaced by a globally supplied proof result. `HasSecularBirkhoffForm`, `HasFastDiffeomorphism`, `secularAverage`, `cylinder`, `fastFrequency`, `IsDiophantine` and `actionNbhd` were inspected to exclude concealed conclusions or changed carriers/normalizations.

Auxiliary estimate lemmas have their explicit local variable/domain/radius hypotheses. Two helpers, `jetBeta_lower_nbhd` and `spec_beta_inverse`, explicitly accept a previously obtained real lower bound `hlow`; these are distinctly named conditional perturbation helpers, not replacements for the source node. `freq_data` supplies that bound from the unconditional `jetBeta_lower d`. The final theorem has no such binder. Other helpers similarly propagate produced radius inequalities; no extra premise survives assembly.

## Declaration inventory

All names below are in `KAM.Planetary`. D=FrequencyDefs, J=FrequencyJets, L=FrequencyLip, B=FrequencyBeta, F=FrequencyBounds. Each row is one declaration, with its actual source line. The 55 theorem rows were checked for full statements, domain guards and constant dependence; all 77 declarations were included in the axiom probe.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| fd-beta | `continuousOn_jetBeta_real` (B:32) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-beta | `jetBeta_lower` (B:46) | PASS WITH NOTES | Compactness replaces Cramer; full complex-vector bound. |
| fd-beta | `jetBeta_lip_mulVec` (B:103) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-beta | `betaRadius` (B:138) | PASS | Literal formula / coordinate carrier. |
| fd-beta | `betaRadius_pos` (B:141) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-beta | `jetBeta_lower_nbhd` (B:147) | PASS | Conditional perturbation helper; lower bound supplied in assembly. |
| freq-data assembly | `spec_poly_bounds` (F:40) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| freq-data assembly | `jpBound_le_lipConst` (F:56) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| freq-data assembly | `spec_lip_fast` (F:65) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| freq-data assembly | `spec_lip_slow` (F:79) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| freq-data assembly | `spec_beta_inverse` (F:90) | PASS | Conditional helper; LB=max 1 (2/m); consumed with produced bound. |
| freq-data assembly | `freq_data` (F:104) | PASS | Source data alone; all existence/specification clauses supplied. |
| freq-data assembly | `pgAnalytic` (F:162) | PASS | Choice from proved existence, followed by full specification. |
| freq-data assembly | `pgCU` (F:165) | PASS | Exact signature max formula. |
| freq-data assembly | `pgAnalytic_spec` (F:168) | PASS | Complete specification of the selected constants. |
| freq-data definition | `PGAnalytic` (D:33) | PASS | Eleven numeric fields; no assumed estimates. |
| freq-data definition | `analyticDomain` (D:46) | PASS | Literal fast tube times slow ball <1. |
| freq-data definition | `analyticBoundDomain` (D:49) | PASS | Literal fast tube times slow ball <2 (F3). |
| freq-data definition | `complexIntegrable` (D:55) | PASS | Literal H0 extension plus mu times actual jet polynomial. |
| freq-data definition | `complexFrequency` (D:58) | PASS | Literal coordinate Frechet gradient. |
| freq-data definition | `PGAnalyticSpec` (D:62) | PASS | Exact nine-way signature comparison; 28 proved conjuncts. |
| fd-bd | `jetK2` (J:33) | PASS | Literal formula / coordinate carrier. |
| fd-bd | `jetK4` (J:36) | PASS | Literal formula / coordinate carrier. |
| fd-bd | `jetK2_nonneg` (J:38) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jetK4_nonneg` (J:42) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jetP0_norm_le` (J:46) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jetOmega_norm_le` (J:51) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jetBeta_norm_le` (J:58) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jpPoly` (J:76) | PASS | Literal formula / coordinate carrier. |
| fd-bd | `jpPoly_mono` (J:79) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jpPoly_nonneg` (J:86) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `norm_blockSlow_le` (J:92) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jetPolynomial_norm_le` (J:95) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `differentiable_blockSlow_apply` (J:138) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `differentiable_blockFast` (J:142) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jpDom` (J:146) | PASS | Literal formula / coordinate carrier. |
| fd-bd | `isOpen_jpDom` (J:149) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jetPolynomial_differentiableOn` (J:152) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `norm_blockFast_sub_le` (J:174) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `norm_blockSlow_sub_le` (J:178) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `blockFast_mem_of_close` (J:182) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jpRadius` (J:194) | PASS | Literal formula / coordinate carrier. |
| fd-bd | `jpRadius_pos` (J:196) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jpSup` (J:201) | PASS | Literal formula / coordinate carrier. |
| fd-bd | `jpBound` (J:204) | PASS | Literal formula / coordinate carrier. |
| fd-bd | `jpBound_ge_one` (J:207) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-bd | `jetPolynomial_ball_bound` (J:215) | PASS | Positive delta/8 ball inside domain; slow norm ≤3. |
| fd-bd | `jetPolynomial_derivs_bound` (J:239) | PASS | Closed-ball Cauchy; actual polynomial, DN, D2N. |
| fd-lip | `embFast` (L:31) | PASS | Literal formula / coordinate carrier. |
| fd-lip | `embSlow` (L:40) | PASS | Literal formula / coordinate carrier. |
| fd-lip | `embFast_apply` (L:48) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `embSlow_apply` (L:50) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `append_eq_add` (L:52) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `norm_embFast_le` (L:57) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `norm_embSlow_le` (L:64) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `blockFast_append` (L:71) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `blockSlow_append` (L:75) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `norm_single_le_one_fin` (L:79) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `norm_embFast_single_le` (L:85) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `jpGrad` (L:89) | PASS | Literal formula / coordinate carrier. |
| fd-lip | `jpTheta` (L:93) | PASS | Literal formula / coordinate carrier. |
| fd-lip | `differentiableOn_fderiv_jp` (L:96) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `append_mem_jpDom` (L:103) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `hasFDerivAt_append` (L:110) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `jpGrad_eq` (L:117) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `norm_jpGrad_le` (L:132) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `differentiableOn_jpGrad` (L:154) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `differentiableOn_jpTheta` (L:169) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `norm_jpTheta_le` (L:179) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `lipRadius` (L:197) | PASS | Literal formula / coordinate carrier. |
| fd-lip | `lipRadius_pos` (L:199) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `lipConst` (L:204) | PASS | Literal formula / coordinate carrier. |
| fd-lip | `lipConst_ge_one` (L:207) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `actionNbhd_two_lipRadius` (L:217) | PASS | Valid local estimate, regularity, identity or domain inclusion; used with its guards. |
| fd-lip | `jpGrad_lip` (L:223) | PASS | lip_complex on doubled tube; no convex V premise. |
| fd-lip | `jpTheta_lip` (L:241) | PASS | lip_complex with coefficient bounds. |
| fd-lip | `jpGrad_lip_slow` (L:261) | PASS | Mean-value proof; stronger jpBound constant. |

## Definition classification

There are 21 definitions and one structure, no abbrev. All have BODY_MATCH=OK and PUBLIC_CARRIER=OK against their specified mathematical role.

| Definitions | Classification and body audit |
|---|---|
| PGAnalytic | Numeric output structure, eleven real fields; not a source hypothesis bundle. |
| PGAnalyticSpec | Literal output predicate packaging the audited bounds and domains; theorem-shaped as an output specification, never an assumed input. Its complete truth is proved by freq_data. |
| analyticDomain, analyticBoundDomain | Literal products of the frozen action tube with slow balls of radius 1 and 2. |
| complexIntegrable, complexFrequency | Literal integrable extension and coordinate Frechet gradient; gradient estimates are guarded by proved holomorphy. No branch inserted outside the source domain. |
| jetK2, jetK4, jpPoly, jpRadius, jpSup, jpBound | Literal numeric majorants/radius/polynomial formulas. Positivity/domain facts proved before division estimates are consumed. |
| jpDom | Literal delta/2 fast tube, unrestricted slow coordinates for the polynomial. |
| embFast, embSlow | Actual continuous linear coordinate embeddings, not selected approximations. |
| jpGrad, jpTheta | Actual partial gradient and affine slow frequency; chain rule identifies the partial gradient. |
| lipRadius, lipConst, betaRadius | Literal formulas; betaRadius depends on m only as an auxiliary radius and is used with produced m>0. |
| pgCU | Literal max formula; no claim of uniform inverse control for arbitrary unqualified p. |
| pgAnalytic | Choice of constants from proved freq_data, with full characterization pgAnalytic_spec. Constants are existential witnesses, not an object specified uniquely by the manuscript. Uniqueness of these arbitrary admissible constants is neither claimed nor required. |

For literal entries: WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS. For pgAnalytic: WELL_DEFINEDNESS=OK (proved existence), CHARACTERIZATION=OK (complete PGAnalyticSpec), CHOICE_INDEPENDENCE=N/A (nonunique admissible numeric witnesses, not a uniqueness-defined source object), DEFINITION_VERDICT=PASS. The construction introduces no default/fallback branches and does not claim uniqueness from mere existence.

## Independent validation

Every Lean/Lake invocation was serial, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean, update, cache fetch, package modification, resource-limit override, source repair, or state-changing git command was issued.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5fd KAM.Planetary.PGAssembly.FrequencyBounds
```

Exit **0**. Output: `[inp-gate] slot 2 acquired 12:39:02 for KAM.Planetary.PGAssembly.FrequencyBounds`; `Build completed successfully (9125 jobs).` All five scoped modules build. Replayed warnings occur only in CompactLipschitz:140, JetsPoly:213,215 and Jets:75,78,79 (unused variables/simp arguments); no scoped Frequency warning.

2. Axiom and direct-use probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5FDAudit.lean > /tmp/P5-FD-audit-1-probe.log 2>&1
```

Exit **0**, no errors/warnings. Probe generated from every top-level scoped declaration, with `#print axioms KAM.Planetary.<name>` for all **77** names (55 theorems, 21 defs, one structure). Every output row has exactly `[propext, Classical.choice, Quot.sound]`; zero sorryAx or project axioms. Main output:

```text
'KAM.Planetary.freq_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgAnalytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgCU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgAnalytic_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same probe elaborated `example (d : PGData a b) : ∃ p : PGAnalytic, PGAnalyticSpec d p := freq_data d`, the complete `pgAnalytic_spec` application, and rfl equations for pgAnalytic and the exact pgCU formula. Provider/frozen type-equivalence and seal-body probes are N/A: no provider or anchor is delivered by P5-FD, and no draft anchor was imported for these probes.

3. Kernel replay, one invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.FrequencyBounds KAM.Planetary.PGAssembly.FrequencyDefs KAM.Planetary.PGAssembly.FrequencyJets KAM.Planetary.PGAssembly.FrequencyLip KAM.Planetary.PGAssembly.FrequencyBeta > /tmp/P5-FD-audit-1-leanchecker.log 2>&1
```

Exit **0**. Complete output:

```text
replaying KAM.Planetary.PGAssembly.FrequencyBeta
replaying KAM.Planetary.PGAssembly.FrequencyLip
replaying KAM.Planetary.PGAssembly.FrequencyJets
replaying KAM.Planetary.PGAssembly.FrequencyDefs
replaying KAM.Planetary.PGAssembly.FrequencyBounds
```

4. Static import, hygiene and protected-path checks:

A recursive parser of project `public import`/`import` statements from FrequencyBounds found **79** project modules, **20** frozen imports, **zero** providers and **zero** frozen theorem imports. Each frozen import was matched by exact path to a unique manifest entry with state **SEALED**:

```text
KAM.Frozen.Defs.{ActionNbhd,ComplexStrip,HamiltonianVectorField,HamiltonianVectorFieldC,
 IsDiophantine,IsPrimaryOnStrip,IsRealOnReals,OmegaZero,SymplecticForm}
KAM.Frozen.Planetary.Defs.{Assemble,Cylinder,Fast,FastFrequency,FastShift,
 HasFastDiffeomorphism,HasSecularBirkhoffForm,OscillatorAction,Phase,SecularAverage,Slow}
```

`rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/PGAssembly/Frequency*.lean` returned no matches. All five files have copyright, `module`, public imports, module docstring and `@[expose] public noncomputable section`. Sizes are Beta=181, Bounds=173, Defs=98, Jets=276, Lip=323 lines; zero scoped lines exceed 100 characters.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (only Git's multiple-merge-base warning on stderr). `git diff --check` exits **0**. No protected file was edited. Initial status contained only the existing untracked P5-FD-handoff.md.

5. Repository source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > /tmp/P5-FD-audit-1-lint.log 2>&1
```

Exit **1**, solely for the audit brief's explicitly permitted stale generated root. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (651 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All other lint checks pass. No generated-root regeneration was attempted. The lint ABI subprocess ran after kernel replay, with the same single-thread environment and inherited nice priority. The scratch audit probe was deleted; lint's own temporary ABI probe was removed by its script.

## Source defects, deviations and limits

- **Existing blueprint F4, implemented repair verified:** `blueprint-P/parts/p5-pg-assembly.tex:116–118` says “For $\mu\in(0,\mu_*]$, where $\mu_*\le1$ is defined by” the three smallness inequalities. The preceding extension/bounds are controlled only for mu∈[0,mu0], so these inequalities alone do not guarantee that the entire inverse interval lies in the controlled parameter range. The existing design records the omission at lines 635–639; this package proves the required additional output `muStar≤mu0` (FrequencyDefs:64 and FrequencyBounds:126,150). No source premise is added.
- **Declared proof deviation:** blueprint Part 5:112 says “Cramer as in” the real inverse-bound lemma and specifies an adjugate constant. FrequencyBeta:46–99 and 147–177 instead prove the required uniform bound by compactness and perturbation, with a possibly different data-only LB. This is valid for the existential constant contract; the source's particular explicit Cramer formula is not claimed as an export.
- **Inherited revision-4 source imprecision:** the source extension lemma's “at real points” agreement must be restricted to the closed frozen cylinder, as documented by P45 design Revision 4:1986–2002 and design audit 4. The imported `PGExtension.agrees` has exactly that restriction. P5-FD uses bounds and constructed jets, not an identity for arbitrary off-cylinder total source values; no new defect is introduced here.

No new suspected defect in a pinned paper was found; this report audits the local blueprint/signature contract and does not re-adjudicate the inherited CP10/CP11 allegations. No mathematical/code repair was introduced. No independent implementation verdict is given for upstream packages or downstream `complexFrequency_real`, `freq_inj` or P-G. The handoff's historical “draft” label has no residual proof-hole counterpart in FrequencyBounds.

## Audited file hashes

| File under KAM/Planetary/PGAssembly | SHA256 |
|---|---|
| FrequencyBeta.lean | ffaf5d7978c02d21c68a8d2b0853cdf045a67a959a874e5fb28eece77a54b209 |
| FrequencyBounds.lean | 47301f7fcebc3d3e51e4deafe10d81832b4351186ff36264d2d5b567daf8e573 |
| FrequencyDefs.lean | 0765b4497da5bd52e9891e6a787079b0316819f4ad8fd001ace2e3c9829d673e |
| FrequencyJets.lean | bad0bd43444b5266fba9977fe38a5a0bfe86cc1971269f835c2cc3926c5c933e |
| FrequencyLip.lean | 7a88d6071fe970fdb0ff5bc7a72b731996e065801d077cffae7a3b3d492a842c |

## Closeout

P5-FD has no unresolved mathematical or implementation blocker against its exact signature contract. Package verdict **PASS WITH NOTES** reflects the declared Cramer-route substitution, the inherited blueprint parameter guard repaired by the output, and the permitted generated-root lint exception. No frozen theorem is sealed or declared proved by this report.

All five audited source hashes were rechecked unchanged. The 77/77 declaration inventory has no missing or duplicate rows; the binder-bin counts were independently recounted. Report fences balance, no trailing whitespace, terminal newline present. `git diff --check` exits 0; final status contains only the pre-existing untracked handoff and this new report. The only persistent audit change is `/root/code/KAM-inp-p5fd/docs/tracks/P/audits/P5-FD-audit-1.md`. All audit Lean probes were removed.
