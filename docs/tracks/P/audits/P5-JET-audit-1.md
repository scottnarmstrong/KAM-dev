# P5-JET independent package audit 1

Overall verdict: **PASS WITH NOTES** for P5-JET as an infrastructure package. The three main theorem types and five design definitions match Revision 4. No mathematical or statement-fidelity failure found. The root-import lint exception is explicitly allowed by the audit brief. One additional nonblocking formatting note is trailing whitespace in `JetsParam.lean:57`. This is not a seal of P-G.

## Scope and authority

Audited HEAD `ab33230b249764b8a8c2c77c76adeb278fc4a51d` in `/root/code/KAM-inp-p5jet`. Read AGENTS.md, PLAN, DECISIONS, the package-audit brief, the handoff/AUDIT FOCUS, P45 design including Revision 4, design audits 1–4, shared signatures, Track P statement, blueprint P5:49–61, frozen P-G and the definitions of secular average, Birkhoff form, oscillator action, assembly, phase and action neighbourhood. The older statement document's draft status is superseded by D20; no premise was inferred from its historical status text.

The user's exact report path and handoff's Jets-only scope supersede the generic brief's main-worktree destination and provider assumption. Only this report is a persistent repository edit. P5-EX and P5-ID are checked as consumed dependencies, not re-audited packages.

Commands `git diff inp...HEAD` and `git diff inp-p5ex...HEAD` were inspected. At inspection `inp` was `872a014af58890f96058190624e431a0ed0228a5`, `inp-p5ex` was `117d37238a3f0ac1e88dfcfe8718fee28b271823`. The former warns `multiple merge bases, using 05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2` and contains 23 new modules (10 Extension + 13 Jets). The latter contains unrelated branch-history changes; scoped to `KAM/Planetary/PGAssembly/Jets*.lean`, it adds exactly the same 13 audited files. Neither broader comparison expands this audit's ownership.

The shared signature file `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` has SHA256 `6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402`, matching design audit 4. Its Jets block equals the local design appendix. The theorem headers `fourth_jet_unique`, `birkhoff_ext`, `birkhoff_ext_parameter_regularity` are textually identical modulo whitespace.

## Anchor disposition and main proof review

| Anchor / target | Verdict | Meaning |
|---|---|---|
| `KAM.Planetary.properlyDegenerateKAM` (P-G) | Not submitted for sealing | Frozen body remains `by sorry`, manifest remains unchanged. P5-JET provides helpers only. Provider/frozen ABI and seal-body probes are inapplicable here. |
| `fourth_jet_unique` | PASS | Exact design signature; arbitrary real normed-space generalization is separately named. |
| `birkhoff_ext` | PASS | Exact four-clause signature, including all jets through order four and determinant on closure V. |
| `birkhoff_ext_parameter_regularity` | PASS | Exact F2 signature: joint continuity, not just separate continuity, and complex matrix symmetry. |

`PGData` repeats the frozen source inputs, including hBNF, htorsion and hsymm. No new structure, instance, witness assumption or conclusion-shaped provider premise was introduced. Conditional multilinear helpers have distinct names and their hypotheses are proved at each application.

The average is the actual normalized angular integral. `JetsParam:39` calls `KAM.Weighted.holomorphic_parametric_integral`, transporting along a continuous linear equivalence rather than changing norms or assuming product-domain holomorphy. `JetsAverage:112–180` supplies the integrand/derivative continuity and finite-box dominated convergence, with the produced extension bound MP. `JetsFamily:31–120` establishes joint continuity of derivatives by a local Cauchy estimate and induction; it does not assume this as a bundled field.

At real actions in V, `JetsIdent:101–124` uses the literal frozen little-o inequality, shrinking the disc radius to delta/2 for the product max norm. `fourth_jet_unique_gen` proves full multilinear jet uniqueness by analytic order along lines and polarization. It covers k=0 as well as k=4. `JetsPoly:200–258` retains both off-diagonal matrix entries until hsymm is used in `mixed_osc`; `JetsIdent:177–205` applies precisely `d.hsymm mu hmu I hI`. The diagonal fourth derivative is 3 beta_jj, canceled by the signature's 1/3. No antisymmetric torsion shortcut occurs.

The canonical carrier is `(q,p)` for jet vectors; the average explicitly swaps arguments into frozen `(phi,q;I,p)` assembly. The unit vector `(0,e_j)` is therefore the p_j direction. Oscillator actions and the product norm are invariant under the documented swap; there is no physical-coordinate change hidden in the notation.

`JetsVanish:66–100` derives zero real jets and then zero complex multilinear maps by a basis of real vectors. `JetsRegular:146–162` uses P5-ID's `connected_complex_tube d.hVc.closure` and `real_slice_identity` to extend each evaluated jet over the full half tube. The source's connected, nonempty V is used, not an unproved connectedness assumption. Complex beta symmetry follows independently by permutation of the analytic fourth derivative.

`Jets:45–58` obtains the determinant bound on closure V by continuity of the constructed beta and density of V. It does not equate the arbitrary original total beta with the constructed beta on the boundary. Real-average attachment stays on V and inside the oscillator radius, so Revision 4's closed-cylinder agreement restriction is respected.

## Every new public declaration

All names below have prefix `KAM.Planetary.`. File locators are relative to `KAM/Planetary/PGAssembly/`. The nodes are `bpP:p5:birkhoff-ext`, its `stepP:p5:be-*` children, and F2; helper rows refine those proof obligations rather than assert new source results. There are 93 declarations: 72 theorems, 19 definitions, 2 carrier abbreviations.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| be-det | `jetBeta_det_real` (Jets.lean:35) | PASS | Maps the real determinant into complex numbers; applies source htorsion on V. |
| be-det | `jetBeta_det_closure` (Jets.lean:45) | PASS | Continuous determinant on closure V and density of V; no boundary beta assumption. |
| birkhoff-ext | `birkhoff_ext` (Jets.lean:60) | PASS | Exact design telescope and all four clauses; includes k=0 and k=4. |
| F2 | `birkhoff_ext_parameter_regularity` (Jets.lean:81) | PASS | Exact F2 output: joint continuity of every coefficient and symmetry on the whole half tube. |
| be-an | `JetE` (JetsAverage.lean:33) | PASS | Type alias for the existing product carrier; unchanged max norm. |
| be-an | `isOpen_extensionDomain` (JetsAverage.lean:35) | PASS | Union of open balls; no positivity premise needed. |
| be-an | `avgDom` (JetsAverage.lean:43) | PASS | Actual half action tube times the open oscillator ball. |
| be-an | `isOpen_avgDom` (JetsAverage.lean:46) | PASS | Intersection of preimages of open sets. |
| be-an | `avgFun` (JetsAverage.lean:51) | PASS | Unchanged normalized complexAverage, uncurried. |
| be-an | `avgInt` (JetsAverage.lean:54) | PASS | Actual extension integrand with the q,p swap required by canonical ordering. |
| be-an | `assembleLin` (JetsAverage.lean:58) | PASS | Continuous complex linear part of assembly; fast angles set to zero. |
| be-an | `assembleComplex_eq_add` (JetsAverage.lean:69) | PASS | Coordinate equality proving the affine decomposition. |
| be-an | `avgInt_mem` (JetsAverage.lean:75) | PASS | P5-EX strip-domain inclusion; oscillator radius bounded by delta/4. |
| be-an | `continuous_assembleComplex_real` (JetsAverage.lean:95) | PASS | Continuity of the actual assembly map. |
| be-an | `avgInt_eq_comp` (JetsAverage.lean:105) | PASS | Exact affine pullback, not a replacement integrand. |
| be-an | `avgFun_differentiableOn` (JetsAverage.lean:112) | PASS | Supplies all N integral hypotheses, transports to product domain, preserves normalization. |
| be-an | `avgFun_continuousOn` (JetsAverage.lean:149) | PASS | Dominated convergence with extension MP on a finite angular box. |
| birkhoff-ext / definition | `jetP0` (JetsDefs.lean:30) | PASS | Value at zero of the actual average; exact design body. |
| birkhoff-ext / definition | `jetOmega` (JetsDefs.lean:32) | PASS | Second derivative at the p_j vector; exact design body. |
| birkhoff-ext / definition | `jetBeta` (JetsDefs.lean:35) | PASS | Diagonal fourth derivative divided by 3; mixed i,i,j,j elsewhere; exact design body. |
| birkhoff-ext / definition | `jetPolynomial` (JetsDefs.lean:41) | PASS | Exact P0 + Omega.R + (1/2) sum beta_ij R_i R_j. |
| birkhoff-ext / definition | `pgRemainder` (JetsDefs.lean:45) | PASS | Actual average minus that polynomial at oscillator actions. |
| be-an | `continuousOn_fderiv_family` (JetsFamily.lean:31) | PASS | Local Cauchy estimate for the difference; compact parameter times closed ball gives uniform continuity. |
| be-an | `continuousOn_iteratedFDeriv_family` (JetsFamily.lean:89) | PASS | Induction on derivative order; evaluates fixed multilinear directions. |
| be-coef | `iteratedDeriv_eq_zero_of_isLittleO` (JetsFourth.lean:27) | PASS | Analytic order at least 5 from the all-epsilon fourth-order bound. |
| be-coef | `fourth_jet_unique_gen` (JetsFourth.lean:67) | PASS | Stronger real normed-space form; line restriction plus polarization, including arity zero. |
| be-coef | `fourth_jet_unique` (JetsFourth.lean:106) | PASS | Exact Fin N design signature; specializes the general theorem. |
| be-coef | `pgOscRadius_pos` (JetsIdent.lean:35) | PASS | Positivity from r0>0 and extension delta>0. |
| be-coef | `mem_avgDom_zero` (JetsIdent.lean:38) | PASS | Zero oscillator vector is in the positive-radius ball. |
| be-coef | `realInclusion_mem_tube` (JetsIdent.lean:43) | PASS | Witness is I itself; works on closure V. |
| be-coef | `complexAverage_analyticAt` (JetsIdent.lean:52) | PASS | Finite-dimensional holomorphy on avgDom implies slice analyticity at zero. |
| be-coef | `realAvg` (JetsIdent.lean:60) | PASS | Frozen secularAverage in the stated q,p carrier. |
| be-coef | `birkPoly` (JetsIdent.lean:64) | PASS | Real oscillator polynomial using the original frozen coefficient functions. |
| be-coef | `birkRem` (JetsIdent.lean:68) | PASS | Real average minus real polynomial, with no truncation or fallback. |
| be-coef | `norm_swap_eq` (JetsIdent.lean:71) | PASS | Max product norm invariant under swapping factors. |
| be-coef | `complexAverage_realY` (JetsIdent.lean:74) | PASS | Uses P5-EX equality only on V and inside pgOscRadius. |
| be-coef | `complexAverage_realY_eventually` (JetsIdent.lean:81) | PASS | Positive oscillator radius gives a neighbourhood equality at zero. |
| be-coef | `realAvg_analyticAt` (JetsIdent.lean:88) | PASS | Real restriction of the complex average, composed with real part. |
| be-coef | `birkRem_isLittleO` (JetsIdent.lean:101) | PASS | Uses d.hBNF; shrinks the disc radius to delta/2 to control the product max ball. |
| be-coef | `iteratedFDeriv_realAvg_eq` (JetsIdent.lean:126) | PASS | Analytic remainder plus fourth_jet_unique_gen; no jet equality assumed. |
| be-coef | `realInclusion₂_yvec` (JetsIdent.lean:139) | PASS | Exact bridge from real p-direction to complex p-direction. |
| be-coef | `birkRem_zero` (JetsIdent.lean:144) | PASS | Little-o inequality evaluated at zero. |
| be-coef | `realAvg_zero` (JetsIdent.lean:151) | PASS | Subtracts polynomial value P0 at zero. |
| be-coef | `jetP0_real` (JetsIdent.lean:159) | PASS | Average equality and computed real value. |
| be-coef | `jetOmega_real` (JetsIdent.lean:165) | PASS | Real/complex jet bridge, degree-two polynomial coefficient. |
| be-coef | `jetBeta_real` (JetsIdent.lean:177) | PASS | Diagonal factor 1/3 checked; off diagonal invokes mixed_osc with source hsymm. |
| be-an | `holomorphic_parametric_integral_gen` (JetsParam.lean:28) | PASS | N theorem transported through a finite-dimensional continuous linear equivalence; derivative formula is not claimed. |
| be-coef | `iteratedFDeriv_comp_clm_of_isOpen` (JetsPolar.lean:34) | PASS | Local chain rule; explicit open-domain smoothness supplies derivative uniqueness. |
| be-coef | `curryLeft_symm` (JetsPolar.lean:49) | PASS | Symmetry inherited by fixing one multilinear argument. |
| be-coef | `hasDerivAt_diag_line` (JetsPolar.lean:62) | PASS | Derivative sums k+1 equal contributions using permutation symmetry. |
| be-coef | `diag_curryLeft` (JetsPolar.lean:94) | PASS | Derivative of an identically zero diagonal; cancels positive k+1. |
| be-coef | `eq_zero_of_diag_of_symm` (JetsPolar.lean:109) | PASS | Polarization by arity induction; conditional calculus helper, not a source substitute. |
| be-coef | `iteratedDeriv_quartic` (JetsPoly.lean:29) | PASS | Direct second and fourth one-variable derivatives: 2a and 24q. |
| be-coef | `RY` (JetsPoly.lean:68) | PASS | Real product carrier alias; no new norm instance. |
| be-coef | `oscS` (JetsPoly.lean:71) | PASS | (p_j^2+q_j^2)/2 for y=(q,p). |
| be-coef | `oscQ2` (JetsPoly.lean:73) | PASS | Full quadratic sum of oscillator actions. |
| be-coef | `oscQ4` (JetsPoly.lean:75) | PASS | Full ordered quartic sum, with coefficient 1/2. |
| be-coef | `oscPoly` (JetsPoly.lean:78) | PASS | Constant plus quadratic plus quartic pieces on the whole real carrier. |
| be-coef | `oscS_smul` (JetsPoly.lean:81) | PASS | Degree-two scaling by direct ring identity. |
| be-coef | `oscPoly_smul` (JetsPoly.lean:85) | PASS | Exact even quartic along every real line. |
| be-coef | `contDiff_oscPoly` (JetsPoly.lean:97) | PASS | Polynomial smoothness, with arbitrary coefficient matrix. |
| be-coef | `iteratedFDeriv_oscPoly_diag` (JetsPoly.lean:102) | PASS | Continuous linear line restriction equates scalar and diagonal Frechet derivatives. |
| be-coef | `iteratedFDeriv_two_oscPoly` (JetsPoly.lean:117) | PASS | Second jet is 2 Q2. |
| be-coef | `iteratedFDeriv_four_oscPoly` (JetsPoly.lean:123) | PASS | Fourth jet is 24 Q4. |
| be-coef | `mixed_value` (JetsPoly.lean:130) | PASS | Two derivatives of the symmetric diagonal identity yield e2/6; premises discharged by caller. |
| be-coef | `analyticAt_oscS` (JetsPoly.lean:175) | PASS | Polynomial analytic on the whole carrier. |
| be-coef | `analyticAt_oscPoly` (JetsPoly.lean:183) | PASS | Polynomial analytic on the whole carrier. |
| be-coef | `yvec` (JetsPoly.lean:190) | PASS | Actual unit p_i vector in the q,p carrier. |
| be-coef | `oscS_yvec` (JetsPoly.lean:192) | PASS | Action value is 1/2 in coordinate i, zero otherwise. |
| be-coef | `oscQ2_yvec` (JetsPoly.lean:195) | PASS | Quadratic value Omega_j/2. |
| be-coef | `oscQ4_line` (JetsPoly.lean:200) | PASS | Keeps both beta_ji and beta_ij before any symmetry assumption. |
| be-coef | `oscQ4_yvec` (JetsPoly.lean:233) | PASS | Quartic value beta_ii/8. |
| be-coef | `mixed_osc` (JetsPoly.lean:246) | PASS | Explicit matrix symmetry converts the symmetrized entry to beta_ij. |
| be-jet | `iteratedFDeriv_comp_clm_of_analyticAt` (JetsReal.lean:31) | PASS | Stronger pointwise analytic version of the local linear chain rule. |
| be-jet | `jet_real_restrict` (JetsReal.lean:42) | PASS | Proves real analyticity from germ equality; restriction of scalars preserves each iterated derivative. |
| be-jet | `multilinear_eq_zero_of_real` (JetsReal.lean:73) | PASS | Extensionality on a complex basis of real unit vectors, including zero arity. |
| be-an / F2 | `tube_eq_zero_slice` (JetsRegular.lean:32) | PASS | Exact equality of the slice domain with the half tube. |
| be-an / F2 | `jetP0_differentiableOn` (JetsRegular.lean:37) | PASS | Holomorphic average composed with I maps to (I,0). |
| be-an / F2 | `jetOmega_differentiableOn` (JetsRegular.lean:43) | PASS | Second partial jet is holomorphic in I. |
| be-an / F2 | `jetBeta_differentiableOn` (JetsRegular.lean:51) | PASS | Both conditional branches are holomorphic in I; diagonal scale retained. |
| be-an / F2 | `jet_continuousOn` (JetsRegular.lean:64) | PASS | Compact parameter-family derivative continuity, for each coefficient entry. |
| be-an / F2 | `jetBeta_isSymm` (JetsRegular.lean:90) | PASS | Complex fourth derivative permutation symmetry; no hsymm use is needed here. |
| be-an / F2 | `pgRemainder_differentiableOn` (JetsRegular.lean:111) | PASS | Holomorphic average minus the actual oscillator polynomial with holomorphic coefficients. |
| be-jet | `remainder_jet_tube` (JetsRegular.lean:146) | PASS | P5-ID connected_complex_tube and real_slice_identity extend every evaluated remainder jet from V. |
| be-an | `iteratedFDeriv_slice` (JetsSlice.lean:33) | PASS | Affine translation and inr chain rule; no global smoothness premise. |
| be-an | `differentiableOn_slice_jet` (JetsSlice.lean:61) | PASS | Holomorphic iterated derivative composed with inclusion and evaluation. |
| be-an | `continuousOn_slice_jet` (JetsSlice.lean:78) | PASS | Applies joint derivative continuity at (mu,I,0) to fixed directions. |
| be-jet | `cOsc` (JetsVanish.lean:31) | PASS | Complex oscillator polynomial action, not the real norm squared. |
| be-jet | `cPoly` (JetsVanish.lean:34) | PASS | Full complex Birkhoff polynomial with the same 1/2 ordered sum. |
| be-jet | `analyticAt_cOsc` (JetsVanish.lean:37) | PASS | Complex polynomial analyticity. |
| be-jet | `analyticAt_cPoly` (JetsVanish.lean:46) | PASS | Complex polynomial analyticity. |
| be-jet | `pgRemainder_real` (JetsVanish.lean:52) | PASS | On V only, constructed coefficients are replaced by the original real coefficients. |
| be-jet | `remainder_jet_real` (JetsVanish.lean:66) | PASS | Analytic little-o real remainder; real-to-complex jets and basis extensionality prove zero. |

## Definition classification

All 21 new definitions/abbreviations are classified in the table above. `JetE`, `RY` are aliases for standard product carriers, with no new norm instance. `avgDom` is the intended open domain; `avgFun` and `avgInt` are exact average/integrand wrappers; `assembleLin` is the coordinate linear map whose decomposition is proved. The five signature definitions are unchanged in meaning and body. `realAvg`, `birkPoly`, `birkRem`, `oscS`, `oscQ2`, `oscQ4`, `oscPoly`, `yvec`, `cOsc`, `cPoly` are total algebraic functions on their stated carriers. No junk branch is used in a theorem. Outside the analytic domain the jets retain the standard total iterated-derivative meaning; no claim of regularity or source equality there is made. `jetBeta`'s conditional is the intended diagonal/mixed formula, not a failure fallback. All definitions are exposed by the public exposed section.

## Suspected defects, deviations and limits

No new pinned-source erratum, blueprint contradiction or frozen-statement defect was found in the Jets scope. The pre-existing Revision 4 source imprecision is retained: blueprint `p5-pg-assembly.tex:30` says the extension agrees with P "at real points" without the necessary closed-cylinder restriction. Revision 4 of the design (lines 1986–2002) and design audit 4 explain why exterior total source values are unconstrained. This package consumes only the corrected on-V average identity; it does not revive the refuted exterior equality. This is an inherited blueprint clarification, not a new defect in a pinned CP paper. No external PDF claims are certified by this package audit.

The support-module split and real-normed-space/general-domain helper generalizations are justified implementation choices; the public target signatures and carriers do not change. `JetsPoly.lean` has 261 lines (the handoff describes supporting modules as at most 260); this is a harmless handoff count discrepancy, far below the 1500-line cap. `git diff --check` finds one trailing-whitespace line at `JetsParam.lean:57`; remove it during integration. Source edits are outside this auditor's authorization. No heartbeat or synthesis-budget workaround is used.

## Validation receipts

Validation receipts follow. All audit-owned Lean work is sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build uses the prescribed compile gate. Probe copies use fresh names and the original design text; no frozen declaration is edited or imported to manufacture a seal receipt.


### Design/type probes and axioms

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5JetAudit.lean
```

Final exit **0**; no errors or warnings. Fresh declarations copied from the shared signatures were discharged with `by exact fourth_jet_unique hf ho`, `by exact birkhoff_ext d`, and `by exact birkhoff_ext_parameter_regularity d`; additionally `example : type_of% @<target> := @audit_<target>` succeeded for each. All five copied design definitions satisfy `example : @audit_<def> = @<def> := rfl`. Thus the checks preserve binder order and the entire telescope, not just a downstream implication.

The first probe attempt exited 1 solely because the audit harness omitted the source's `noncomputable` section on its copied definitions (`lean.dependsOnNoncomputable`, five definitions). Restoring that section produced the clean receipt above; no package change or budget override was needed.

The probe issued `#print axioms KAM.Planetary.<name>` for every one of the 72 public theorems listed above. Complete output:

```text
'KAM.Planetary.jetBeta_det_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetBeta_det_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkhoff_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkhoff_ext_parameter_regularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_extensionDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_avgDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.assembleComplex_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avgInt_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_assembleComplex_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avgInt_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avgFun_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avgFun_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_fderiv_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_iteratedFDeriv_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedDeriv_eq_zero_of_isLittleO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fourth_jet_unique_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fourth_jet_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgOscRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_avgDom_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realInclusion_mem_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexAverage_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_swap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexAverage_realY' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexAverage_realY_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realAvg_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkRem_isLittleO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedFDeriv_realAvg_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realInclusion₂_yvec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkRem_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realAvg_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetP0_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetOmega_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetBeta_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.holomorphic_parametric_integral_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedFDeriv_comp_clm_of_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.curryLeft_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDerivAt_diag_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.diag_curryLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eq_zero_of_diag_of_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedDeriv_quartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscS_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscPoly_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.contDiff_oscPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedFDeriv_oscPoly_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedFDeriv_two_oscPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedFDeriv_four_oscPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mixed_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticAt_oscS' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticAt_oscPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscS_yvec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscQ2_yvec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscQ4_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscQ4_yvec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mixed_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedFDeriv_comp_clm_of_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jet_real_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multilinear_eq_zero_of_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tube_eq_zero_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetP0_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetOmega_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetBeta_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jet_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetBeta_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgRemainder_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.remainder_jet_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedFDeriv_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_slice_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_slice_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticAt_cOsc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticAt_cPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgRemainder_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.remainder_jet_real' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 72 have exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, provider axiom, or additional trust assumption appears.

### Import and static hygiene

A recursive scan of all KAM imports from the 13 audited files visits 66 KAM modules. It finds **no frozen theorem module and no provider module**, so no imported DRAFT_SORRY anchor or provider quarantine violation occurs. Frozen definition imports are ordinary definitions; the SEALED-theorem exception is not needed. No new instances are declared. All files have copyright, `module`, public imports, module documentation, exposed public noncomputable section. No forbidden token or resource override appears in the scoped sources.

The file lengths, including comments and blanks (a stronger size check than code lines), are:

```text
Jets.lean: 102
JetsAverage.lean: 186
JetsDefs.lean: 51
JetsFamily.lean: 124
JetsFourth.lean: 115
JetsIdent.lean: 209
JetsParam.lean: 60
JetsPolar.lean: 130
JetsPoly.lean: 261
JetsReal.lean: 101
JetsRegular.lean: 166
JetsSlice.lean: 98
JetsVanish.lean: 104
```

Command `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` prints only Git's multiple-merge-base warning, with no diff, exit **0**. These protected files were not changed by the package or auditor.

Command `git diff --check inp...HEAD -- 'KAM/Planetary/PGAssembly/Jets*.lean'` exits **2**:

```text
warning: inp...HEAD: multiple merge bases, using 05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2
KAM/Planetary/PGAssembly/JetsParam.lean:57: trailing whitespace.
+
```

The added source line shown by the final `+` contains two spaces (trailing spaces omitted from this report).

This is the nonblocking formatting note underlying PASS WITH NOTES, alongside the permitted generated-root lint exception. It is not concealed as a passing diff check.


### Kernel replay

Command (single invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Planetary.PGAssembly.Jets \
  KAM.Planetary.PGAssembly.JetsAverage \
  KAM.Planetary.PGAssembly.JetsDefs \
  KAM.Planetary.PGAssembly.JetsFamily \
  KAM.Planetary.PGAssembly.JetsFourth \
  KAM.Planetary.PGAssembly.JetsIdent \
  KAM.Planetary.PGAssembly.JetsParam \
  KAM.Planetary.PGAssembly.JetsPolar \
  KAM.Planetary.PGAssembly.JetsPoly \
  KAM.Planetary.PGAssembly.JetsReal \
  KAM.Planetary.PGAssembly.JetsRegular \
  KAM.Planetary.PGAssembly.JetsSlice \
  KAM.Planetary.PGAssembly.JetsVanish
```

Exit **0**. Complete output:

```text
replaying KAM.Planetary.PGAssembly.JetsVanish
replaying KAM.Planetary.PGAssembly.JetsSlice
replaying KAM.Planetary.PGAssembly.JetsRegular
replaying KAM.Planetary.PGAssembly.JetsReal
replaying KAM.Planetary.PGAssembly.JetsPoly
replaying KAM.Planetary.PGAssembly.JetsPolar
replaying KAM.Planetary.PGAssembly.JetsParam
replaying KAM.Planetary.PGAssembly.JetsIdent
replaying KAM.Planetary.PGAssembly.JetsFourth
replaying KAM.Planetary.PGAssembly.JetsFamily
replaying KAM.Planetary.PGAssembly.JetsDefs
replaying KAM.Planetary.PGAssembly.JetsAverage
replaying KAM.Planetary.PGAssembly.Jets
```


### Source lint and frozen checks

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the brief's explicitly allowed generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (574 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden proof escapes, resource overrides, overlong lines or oversize files were reported. The module check, frozen-anchor guard and all 144 ABI hashes pass. `KAM.lean` was deliberately not regenerated.


### Targeted build

Command:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-p5jet KAM.Planetary.PGAssembly.Jets
```

The gate invokes `nice -n 5 lake build KAM.Planetary.PGAssembly.Jets`. Final exit **0**. Complete output:

```text
[inp-gate] slot 1 acquired 11:59:21 for KAM.Planetary.PGAssembly.Jets
⚠ [9108/9112] Replayed KAM.Planetary.PGAssembly.JetsPoly
warning: KAM/Planetary/PGAssembly/JetsPoly.lean:213:17: This simp argument is unused:
  hki

Hint: Omit it from the simp argument list.
  [apply] simp [hkj, hij, Ne.symm hij]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: KAM/Planetary/PGAssembly/JetsPoly.lean:213:22: This simp argument is unused:
  hij

Hint: Omit it from the simp argument list.
  [apply] simp [hkj, hki, Ne.symm hij]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: KAM/Planetary/PGAssembly/JetsPoly.lean:215:14: This simp argument is unused:
  hkj

Hint: Omit it from the simp argument list.
  [apply] simp [hki, hij, Ne.symm hij]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: KAM/Planetary/PGAssembly/JetsPoly.lean:215:29: This simp argument is unused:
  Ne.symm hij

Hint: Omit it from the simp argument list.
  [apply] simp [hkj, hki, hij]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9112/9112] Replayed KAM.Planetary.PGAssembly.Jets
warning: KAM/Planetary/PGAssembly/Jets.lean:75:7: Variable name `mu` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _mu

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/PGAssembly/Jets.lean:75:14: Variable name `I` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _I

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/PGAssembly/Jets.lean:76:8: Variable name `mu` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _mu

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/PGAssembly/Jets.lean:78:8: Variable name `mu` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _mu

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/PGAssembly/Jets.lean:78:15: Variable name `I` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _I

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/PGAssembly/Jets.lean:79:8: Variable name `mu` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _mu

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/PGAssembly/Jets.lean:79:15: Variable name `I` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _I

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/PGAssembly/Jets.lean:98:8: Variable name `mu` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _mu

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/PGAssembly/Jets.lean:98:15: Variable name `I` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _I

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9112 jobs).
```

The first gate request was stopped while still waiting (exit 143, no Lean/Lake child) to run the independent probe and replay first. The resubmitted build above is the completed build receipt. Warnings are four unused simp arguments and nine unused binder names in the copied facade statements/proof lambdas; there is no sorry, elaboration error, heartbeat failure or raised budget.

## Handoff

Persistent file: `/root/code/KAM-inp-p5jet/docs/tracks/P/audits/P5-JET-audit-1.md` only. The pre-existing untracked handoff is unchanged. Audit probe, inventory and validation logs under this worktree's `.lake/abi-scratch/` were removed after their results were embedded here. No state-changing git command was used.

Final disposition: **PASS WITH NOTES** for the P5-JET helpers. Build, exact design-type/definition probes, all 72 axiom checks, and kernel replay pass. Lint has only its explicitly permitted root-generation exception. Integrator should remove the trailing whitespace at `JetsParam.lean:57` and regenerate the root through the normal integration workflow. No source-level hypothesis, mathematical conclusion or frozen declaration needs repair for this package. P-G remains unsealed and is outside this package's closure claim.
