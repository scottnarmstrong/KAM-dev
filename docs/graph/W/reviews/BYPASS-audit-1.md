# D27 track-W route-substitution audit 1

Auditor: `maud-wbyp-1`. Date: 2026-11-01. **Overall verdict: FAIL / RETURN the proposed sync as written.**

Scope: `/root/code/KAM-inp-wgraph`, branch `inp-wgraph-byp`, HEAD
`f04a53a7ddd309c34d6a87d3276015389442fc4c`. Read AGENTS.md, PLAN.md,
DECISIONS.md (D27 in full), W/SPEC.md, BYPASS-CANDIDATES.md, packet records,
the cited blueprint parts and relevant Lean suppliers/consumer bodies. This is a source audit:
no Lean, Lake, kernel replay, ABI check, lint wrapper or axiom probe was run. Only this report is written.

D27 says a bypass follows “another valid route” and its note records the route and the audit
confirming no proved consumer needs the step. I apply the requested exact-statement test to
proof dependencies, including bodies of intermediate declarations, not just the final theorem's
conclusion or the names of directly called lemmas. A recorded specialized/alternative component
form is allowed. Renaming, packaging differently, or specializing an existing theorem at time one
does not by itself show its original statement is unused. KEEP is a rejection of this proposed
status/note, not a mathematical counterexample or a claim that the sealed-route proof is broken.

There are **54 rows: 39 BYPASS-OK, 5 PROVED-OK, 10 KEEP**. Of the 48 proposed bypasses,
39 pass and 9 are retained pending correction. The tenth KEEP is the already PARTIAL lambda-facts
row. The complete direct-consumer inventory agrees with the packet DEPS/status records.

## Per-node rulings

Paths in the evidence column are relative to `KAM/Wave/` unless stated otherwise. All Lean names
there are in `KAM.Wave` except where a deeper namespace is explicitly given.

| Node | Verdict | Evidence / reason |
|---|---|---|
| `bpW:w0:twosided` | BYPASS-OK | Only the negative-s counterexample is omitted. TwoSided.lean:243–258 supplies square summability and absolute convolution for nonnegative a,s; Extension and the majorant consumers use those guards. |
| `bpW:w0:H` | PROVED-OK | HamHamiltonian.lean:73–78 defines Λ and H=Λ+G on transported coordinates; Gradient.lean:56 defines the integral G on arbitrary real sequences, hence also a>0 and arbitrary p. Lambda/MainQuart supply the complex forms. Definition acceptance does not assert new differentiability for every p. |
| `bpW:w0:eqmotion` | PROVED-OK | FrozenForm.lean:112–176 gives the field and the precise coefficient equations, in the lower-weight target. HamField and Seq/Diag supply the nonlinear field and the multiplier. The sign is −λq−Gq. |
| `bpW:w0:z` | PROVED-OK | Birkhoff/Coords and MainReal define birkZ, birkZinv and birkZR with 1/√2 and recover q,p with √2. The linear rotation and symplectic identities are provided in the W3 coordinate route; no P96 sign is substituted. |
| `bpW:w0:actions` | PROVED-OK | QuartBar defines birkAction; MainRealId.lean:83–114 defines (q²+p²)/2 and identifies Λ. Positive-action angles are the period-one chart (φ=2πθ), with negative sine and clockwise exponential, as in linearTorus and ActionAngle. |
| `bpW:w0:basis#lambda-facts` | KEEP (PARTIAL) | No PROVED consumer uses the full real strict-convexity/derivative statement. Discrete curvature is a valid replacement. However three cited names do not exist in the claimed namespace and lam_le/lam_facts do not have the advertised general bounds; see finding L. |
| `bpW:w0:ellap#spaces` | PROVED-OK | Transport.lean:75–112 defines coeffW, IsEll, ellTsumSq, tauLp and the membership-guarded ellNorm later in the file. Both RCLike carriers and the max product norm are represented; the raw tsum is not treated as a norm off IsEll. |
| `bpW:w0n:algebra` | KEEP (PARTIAL) | The allegedly replaced K_(3/2)² identity is explicitly proved by waveAlgConst_three_halves_sq and used by waveCubicConst_one (CubicHeadline.lean:46–58). This is exact use, not an alternative constant calculation. See A. |
| `stepW:w0n:weight` | KEEP (NOT_STARTED) | Contrary to “not separately formalized”, wave_weight_ineq is a separate theorem (Algebra.lean:48) used at :102 by wave_algebra, with the same weights and exponent. See A; reclassifying it PROVED requires the correct reference. |
| `stepW:w0n:young` | BYPASS-OK | The complete W0 step is not used as a theorem. Algebra.lean:92–170 assembles it from wave_expl1_le and the nonnegative, squared-sum wave_young_real (Young.lean:56), plus the local hpt estimate. These are the recorded component route; this does not bypass Young’s inequality itself. |
| `stepW:w0n:force` | BYPASS-OK | fcub cites reconWave_force_cub (Recon2/Force.lean:77), whose body uses wave_force_identity directly. It does not need U(λ²q) as a weighted-space object. PdeForward.lean:88–120 also proves the coefficientwise PDE identity. Correct the note’s attribution: fcub does not call wave_pde_identity. |
| `bpW:w0n:Qdef` | BYPASS-OK | Finite resonantQuarticPart is not the infinite object consumed by the root. QuartPaired, QuartBarAlg and MainQuart construct the two-sided birkCoefBar/birkHamBar/birkHamNor route explicitly. |
| `bpW:w0n:AB` | BYPASS-OK | The 11 PROVED direct consumers use two-mode actionA/det_actionA or the W3 infinite-mode birkQuartP_bar formula. No extension of W0 resonantQuarticPart_tangential_eq is required. AUDITOR CHECK A-B below. |
| `stepW:w0n:resavg` | BYPASS-OK | The finite-mode resonance and phase-average formulas are in ResonantBalance/ResonantPart. The infinite absolutely convergent sum used downstream is QuartBarAlg.birkQuartP_bar; stepW:w0n:sum uses the finite average identities. |
| `stepW:w0n:det` | BYPASS-OK | Nondegeneracy.lean proves det_actionA for Fin 2. The consumer nondeg never requires the determinant formula for arbitrary n. |
| `bpW:w0n:birkhoff#data` | BYPASS-OK | stepW:w3:Gz uses birkQuartForm and its coefficient/tuple split, not an unproved extension of quarticGComplex. QuartForm/QuartNormal/QuartBarAlg carry the prefactor 1/16 and the infinite normal/tangential split. |
| `bpW:w1:space` | BYPASS-OK | Transport.lean uses the existing lp carrier, its complete inner-product structure, coeffW/tauLp and truncations. No listed consumer requires the explicit countable rational dense subset assertion. |
| `stepW:w1:sep` | BYPASS-OK | Only consumer is the bypassed full space bundle. No proof requires the source’s explicit rational/Gaussian-rational dense-set construction; working on lp does not instantiate that statement. |
| `bpW:w1:diag` | BYPASS-OK | Seq/Diag and Flow supply the multiplier, isometry, group law and real coordinate equations. W3 weak linear transport uses its own birkZ coordinates, rather than the missing final W0-to-W1 conjugacy sentence. |
| `stepW:w1:realflow` | BYPASS-OK | The missing complete step includes the z(t) conjugacy; the route uses separate flowCLM norm/group/derivative lemmas and W3 coordinates. Editorial correction: real identities live in flowCLM lemmas, not only rotCLM lemmas (Flow.lean:126–245). |
| `bpW:w1:tails` | BYPASS-OK | Tails.lean supplies the three quantitative estimates. Homological/Wave discharges HomFreqHyp1/HomFreqHyp for the shifted wave frequencies; no P96-K Assumption-B package is required. |
| `bpW:w1:gradient-identity` | BYPASS-OK | HamHamiltonian uses the coefficient-pairing derivative and frozen Riesz formulas from GradIdentity/GradLp; QPair/QSymm supply the symmetric four-linear form. No general weighted-space Riesz-gradient theorem is invoked. |
| `stepW:w1:gradw` | BYPASS-OK | Only the frozen weighted-coordinate identities waveG_frozen_fderiv_apply and waveGradW_one_one_apply are needed. The full arbitrary-(a,p) Riesz-gradient statement is not used. |
| `stepW:w1:tricoord#via-cubic-bound` | BYPASS-OK | No direct consumer. TriSeq.waveTri_oneSided and SelectionOneSided.waveSel_oneSided implement the PROVED via-selection route. |
| `bpW:w3:Lambda` | BYPASS-OK | Positive results use the bounded form and field on the stronger source space. not_exists_birkXLam_bounded (:299) is weaker than the source’s failure of mapping every W into W and is not a premise of the listed consumers; the full negative assertion is not consumed. |
| `bpW:w3#data` | BYPASS-OK | The many W3 consumers carry ha:0≤a, hp:1/2≤p and fixed modeIdx/birkTanSet/birkNormalSet typing. No separate theorem with the standing-data paragraph as conclusion is required. |
| `bpW:w3:hamfield-def#hamilton` | BYPASS-OK | HamClass.IsBirkClassA.field_rho is class-A-specific. QuartIdent.birkZinv_birkQuartX_birkZ and MainBallReal.birkK_real_gradient supply precisely G and K for XG/XKconcl; no all-Hamiltonians real-point theorem is used. |
| `bpW:w4:from-w3` | BYPASS-OK | The W5 chart performs the shift J=j+2, the normal complex-to-real conversion, derivative inverse, norm estimates and symplectic check. No separate conjunction of remark (a)–(d) is used. AUDITOR CHECK W4 below. |
| `bpW:w5:w4-modified` | BYPASS-OK | The actual route uses HomModMultBounds supplied by homModMultBounds_of, reweighting, guarded equations and component estimates; RealStep uses the proved modified reality theorem. The full modified lemma with every source clause is not consumed as a unit. |
| `bpW:w5:solve` | KEEP (PARTIAL) | Component solve/bound/equation/smoothing route is viable, but cited KAM.Wave.FT_isRealTaylor does not exist. Actual declarations are WaveStepHyp.FT_isRealTaylor and StepHypMod.FT_isRealTaylor (RealStep.lean:138,159). Fail closed on the supplied reference; see S. |
| `bpW:w5:flow` | KEEP (PARTIAL) | “Only Phi=phi^1” is false in consumer proof closure: stepXplusB_time_bounds, stepPullback_bounds and flowCalcData use arbitrary t. W6 time-one exports do not erase those dependencies. AUDITOR CHECK FLOW below. |
| `stepW:w5:f-flow` | KEEP (PARTIAL) | norm_smoothDisp_le proves the |t|M bound, and flowII_disp uses it before specializing time; derivative estimates also use it. The PROVED f-image reference is a generic increment lemma, not a time-one theorem. AUDITOR CHECK DISPLACEMENT below. |
| `stepW:w5:f-par` | KEEP (PARTIAL) | StepPullbackBound.lean:138 applies flowII_disp_sub at arbitrary t, and StepPlusBound integrates the result. The note’s “only for Phi=phi^1” does not describe the root’s proof closure. |
| `stepW:w5:f-der` | KEEP (PARTIAL) | FlowCalcOnto.lean:112 applies flowII_deriv with ht for arbitrary t. The PROVED c-inv consumer exports an all-t target inverse; the note’s time-one-only premise fails. |
| `stepW:w5:f-real` | BYPASS-OK | Reality is discharged from isRealTaylor and stepField_real inside RealStep. The helpers are general per-time reality/equivariance statements conditional on a real field, rather than the full source W5 family assertion; the concrete exported real Phi is at time one. |
| `bpW:w5:flow-calc` | BYPASS-OK | Alternative FlowHyp calculus is real and instantiated: FlowVariational/FlowCalcJoint, FlowTransport/NewHamTransport, StepNfun and StepFlowConcrete supply the ingredients. The original joint all-clause W5 statement is not a required premise. Per-time calculus is used; this approval is not an unused-calculus claim. |
| `stepW:w5:c-cont` | BYPASS-OK | The recorded alternative is the generic FlowHyp joint continuity theorem, with concrete hypotheses supplied by StepFieldBound. It is used, but the source-specific packaged assertion is not a separate dependency. |
| `stepW:w5:c-var` | BYPASS-OK | FlowVariational.fderiv_holoFlow_eq is the recorded abstract integral equation, used in FlowSymplectic. StepFieldBound provides the concrete flow hypotheses; no missing source-specific supplier is assumed. |
| `stepW:w5:c-trans` | BYPASS-OK | NewHamTransport builds the field using transSolve and proves its specification; FlowTransport supplies conditional derivative transport. This alternative is used inside new-ham without needing the entire concrete source statement. |
| `bpW:w5#data` | BYPASS-OK | The relevant guards are explicit on the general declarations and supplied when specialized to wave weights. homGuard_one_one proves the required guard; the standing-data paragraph is not a separate proof premise. “Every W5 declaration fixes a=p=1” should read “wave instantiations fix a=p=1”. |
| `bpW:w5:pullback` | BYPASS-OK | StepPlusBound uses the concrete two-parameter stepPullback_bounds and transSolve_spec, with explicit domain, field, difference and invertibility inputs. This is the noted component alternative, not an invocation of a missing universal Y family theorem. It is used for arbitrary integration times. |
| `stepW:w5:p-ass` | BYPASS-OK | The assembly uses the concrete pair bounds (StepPullbackBound) inside stepXplus_pair_bound; Pullback.lean:71 gives factor-7 arithmetic separately. No standalone exact source lambda-family conclusion is assumed. |
| `bpW:w5:commutator` | BYPASS-OK | StepBracket gives field and difference bounds; StepPlusBound combines the explicit Mf,Delta,N constants and integrates. It does not invoke the source’s standalone 24εMF/(ση²) lambda-norm theorem. |
| `stepW:w5:k-bd` | BYPASS-OK | stepBrZ_norm_le and its difference form feed the concrete bound. stepCommutator_arith exists but has no call site outside its defining file; its numerical source invoice is not used as a standalone estimate. |
| `bpW:w7:count` | BYPASS-OK | Count.lean:36 bounds lamPlusFin for N≥2. ZoneSums.lean:90–150 proves the actually used cutoff is ≥18 and applies the bound to the candidate superset. ZetaExact supplies the lattice sum; no N=1 all-index-set formula is required. |
| `bpW:w7#data` | BYPASS-OK | Measure/Coords, Lambda and the fixed norm/volume/kAbs definitions carry these conventions directly. No theorem with the full standing-data paragraph is needed. |
| `bpW:w7:measure` | BYPASS-OK | Assembly/ShellEst uses exclSet_measure_le and exclSet_measurableSet in action coordinates. The affine image formula is available separately but the complete equivalent frequency-coordinate conclusion is not needed by the root. |
| `bpW:w7:shell-geom` | KEEP (PARTIAL) | The reverse inclusion is used inline by PROVED lower (Density.lean:89–93), hence by w8_density and nlw2_proof. Other listed consumers use disjointness, bounds or membership. AUDITOR CHECK SHELL below. |
| `stepW:w7:partition` | KEEP (PARTIAL) | Same consumed reverse inclusion as shell-geom. The lack of a separately named equality does not establish non-use of its exact set inclusion. |
| `bpW:w7:density` | BYPASS-OK | density_one_of_shells proves exactly the needed limit; w8_density calls it. The source’s separate uniform-tail quantitative bracket is not exported or invoked as a statement. |
| `bpW:w7:shell-est` | BYPASS-OK | shell_defect_le supplies the combined estimate; Clauses.lean:53–109 specializes α_n=t_n^(95/64) and proves convergence by squeezing. The full general eps_k convergence implication and two-term intermediate invoice are not required separately. |
| `bpW:w7:exponents` | BYPASS-OK | Consts.lean:135 fixes α_n; Clauses.lean:53–68 computes the 1/94 rate and proves convergence. The whole general admissible-window discussion is not a consumer premise. |
| `bpW:w7:dioph-use` | BYPASS-OK | Clauses.w8_dioph composes the shell final-frequency lower bound with isDiophantine_of_lower_bound. The per-shell γ=αcheck/(8π)>0 and τ=24 are retained; no separate W7 use-lemma is required. |
| `bpW:w8#data` | BYPASS-OK | Assembly/Consts and subsequent explicit definitions carry the constants, indices, frozen transport and radius formulas. nlw2_proof chooses witnesses in frozen order; no section-data conjunction is assumed. |

## Findings and mandatory auditor checks

### A: algebra and weight are present in the actual route

`Normal/Analysis/CubicHeadline.lean:46–58` contains, verbatim in mathematical content,
`waveAlgConst (3 / 2) ^ 2 = 8 * (1 + 2 * (riemannZeta 3).re)`.
`waveCubicConst_one` rewrites with **that exact lemma**; the headline cubic estimate then
rewrites with `waveCubicConst_one` at line 97. Thus the candidate's claim that only the cubic
constant is consumed does not remove the identity from its proof closure. `wave_algebra`
already proves the general algebra bound and absolute convergence. This looks like a candidate
for a corrected PROVED classification, rather than D27, but I do not promote it under this audit.

`Algebra/Algebra.lean:48–74` separately proves `wave_weight_ineq`, combining the exponential
triangle inequality and `waveJap_sub_le`. At line 102, `wave_algebra` invokes that theorem.
After unfolding `waveTwoWeight` and cancelling the positive powers of `waveJap`, its RHS is
the W0 weight inequality in the packet. There is no substituted route around it. The proposed
“step not separately formalized” assertion is false. The Young step differs: its full combined
source assertion is assembled from a nonnegative squared-sum version and local pointwise bounds,
which is the component form recorded in its note.

### A-B: finite W0 versus infinite W3 normal form

**AUDITOR CHECK: `bpW:w0n:AB` — PASS, BYPASS-OK.**

There are 14 direct consumers, 11 PROVED and three BYPASSED. In particular:

- `bpW:w0n:nondeg`, `stepW:w0n:A3red`, `bpW:w0n:nondeg-sec#data` use the explicit
  two-mode matrix and its determinant/nonzero pairings in `Normal/Nondegeneracy.lean`.
- `bpW:w7:omega0` uses `omegaTan`, `omegaNor`, `omegaTan_eq`, `omegaNor_eq`.
  `stepW:w7:inverse` and `stepW:w7:norms` use the explicit two-by-two inverse/determinant
  and max row-sum norms in `Measure/Coords{,Inverse}.lean`; `Coords.lean:70` calls
  `(det_actionA m hm).2.1`.
- `bpW:w4:wave` and `stepW:w4:waveLip` use `Homological/Wave.lean`'s explicit
  wave frequency formulas and bounds, with the shifted normal indexing.
- `bpW:w3:quartic-ident` and `stepW:w3:count` cite `birkQuartP_bar` and the W3 tuple
  count/split formulas, not an infinite W0 finite-sum average.
- `stepW:w5:a-nf` cites `aaMap_normalForm`. Its proof in
  `KamStep/ActionAngleNormal.lean:250–291` rewrites `birkHamBar` by `birkQuartP_bar`.
  `ActionAngleGbar.lean:43–53` independently exposes the same infinite formula as
  `birkHamBar_eq_aa`; `Birkhoff/MainRealId.lean:101–109` proves the real specialization
  `birkHamBar_birkZR`.

The infinite normal-action sum is explicit. The coefficients remain
`Aii=9/(8πλi²)`, `A12=3/(2πλ1λ2)`, `Bji=3/(2πλjλi)`; no printed uncorrected
P96 coefficient or unproved infinite extension of `resonantQuarticPart` is used.

### W4: chart ownership

**AUDITOR CHECK: `bpW:w4:from-w3` — PASS, BYPASS-OK.**

Read the full remark and ownership ruling in `blueprint-W/parts/w4-homological.tex:796–815`.
The only direct consumer, `bpW:w5:action-angle`, gets the normal identification internally:
`ActionAngle.lean:79–155` defines `aaShift`, sets tangential entries to zero, and forms
`aaNormal`; `aaMap_nor_true/false` at 236–244 explicitly map mode `j` to mode `j+2`,
with `(u±iv)/√2`. The normal weights are `homWt a p j`, matching the W3 weight at `j+2`.
`ActionAngleDeriv.lean:214–229` defines `aaUnshift x j=x(j+2)`; `aaDer` and
`aaDerInv` explicitly differentiate and undo this identification, and their inverse laws
are proved at 279 and 316. `ActionAngleSymp.lean:178` supplies `aaDer_symp`, and
`ActionAngleConj.lean:127` computes the field conjugacy directly. Norm/domain estimates
are in the action-angle modules and used in the initial perturbation construction.
Thus clauses (a)–(d) are verified where needed through this concrete chart, rather than
assumed as a separate W4 remark. This is the ownership substitution the note describes.

### FLOW: final time one does not imply proof time one

**AUDITOR CHECK: `bpW:w5:flow` — FAIL as phrased; KEEP PARTIAL.**

The named W6 consumers do expose time-one data:
`Iteration/SmoothSrc.lean:58–60` proves `w6ConvTorus` via the concrete smoothing interface;
its `W6PrepHyp.phiP_sharp` at 104–110 uses the modified smoothing interface.
`Iteration/PrepStep.lean:223–232` obtains `phiP_bounds` from `stepTheoremMod_clauses`.
But the task explicitly asks about their dependency closure, including W5 consumers:

1. `KamStep/StepPsi.lean:stepFlow_bounds_smooth` supplies `t=1` to **general-time**
   `flowII_disp`, `flowII_disp_sub`, `flowII_deriv`, `flowII_deriv_sub`.
2. `KamStep/FlowCalcOnto.lean:flowCalcData` applies `flowII_deriv ... ht` at line 112,
   for a variable `t ∈ [-1,1]`, to establish the all-time target inverse used by the
   PROVED `stepW:w5:c-inv` consumer.
3. `KamStep/StepPlusBound.lean:stepXplusB_time_bounds` calls
   `stepPullback_bounds ... (t := t)` at a variable `t ∈ [0,1]`.
   `stepXplusB_bounds` integrates these bounds, and `stepXplus_pair_bound` uses
   `stepXplusB_bounds`. These enter the new-Hamiltonian/step theorem route.
4. `StepPullbackBound.lean:138` uses `flowII_disp_sub ... ht` at that same variable time,
   and its image argument at 105–115 controls the whole trajectory.

These are actual calls in declaration bodies, not import-only associations. They refute
“the flow only as Phi=phi^1 ... not the per-t statements” for the union of consumers specified
in the question. The recorded generic `FlowHyp` component route may support a rewritten,
more carefully delimited D27 application; this audit does not silently rewrite the note.
The same false time-one restriction requires retaining `f-par` and `f-der` as proposed.
It does **not** imply every clause of the full source flow bundle has been formalized.

**AUDITOR CHECK: `stepW:w5:f-flow` — FAIL as phrased; KEEP PARTIAL.**

`FlowSmooth.lean:84–94` states `‖smoothDisp ι Z t w‖ ≤ M * |t|` exactly, with the
abstract flow hypothesis. `FlowStepBounds.lean:43` uses that all-time bound;
`FlowSmoothDeriv.lean:101` also uses it to obtain derivative control. Those results feed
the variable-time chain above. The candidate cannot justify bypass by restricting inspection
to the final `phiP_sharp` export.

Moreover the other PROVED consumer's LEAN_REF, `stepImage_mem` (`Flow.lean:78`), has **no time
parameter and no flow assumption at all**. It proves a domain inclusion from an arbitrary
increment `W` bounded by `M`. Its body is arithmetic on the phase norm. It neither consumes
nor certifies a time-one-only displacement assertion. The time-dependent applications are
in `StepFlowClauses` and `StepPullbackBound`. This is a useful alternative generic image lemma,
but it does not make the note's claim about the proof closure true.

### S: solve reference has a namespace defect

`KAM.Wave.FT_isRealTaylor` in the proposed `bpW:w5:solve` LEAN_REF is absent.
The real proofs are `KAM.Wave.WaveStepHyp.FT_isRealTaylor` and
`KAM.Wave.StepHypMod.FT_isRealTaylor` in `KamStep/RealStep.lean:138,159`.
Their concrete call sites discharge reality; they are not an added premise. The component
solve, smoothing and frequency bounds otherwise support the advertised route, but a
fail-closed check that the **cited** declarations exist cannot approve this row as written.
Retain PARTIAL until the reference is corrected and the note cites this audit or a successor.

### SHELL: the reverse inclusion is used, including inside a PROVED direct consumer

**AUDITOR CHECK: `bpW:w7:shell-geom` — FAIL; KEEP PARTIAL.**

The decisive PROVED consumer is `stepW:w7:lower`, whose LEAN_REF is
`volume_box_diff_le, exists_shell_index` in `Measure/Density.lean`.
Its `volume_box_diff_le` uses the forward covering inclusion at lines 72–76, but at
89–93 it also proves and uses the **reverse** inclusion to bound the measure of the shell union:

```lean
    _ ≤ ENNReal.ofReal ē * volume (boxIoo 0 (shellT q t0 k)) := by
        gcongr
        refine iUnion_subset fun l => ?_
        exact (sdiff_subset).trans (boxIoo_subset le_rfl
          ((shellT_antitone hq hq1 ht).antitone (Nat.le_add_right k l)))
```

This says `⋃l R_(k+l) ⊆ (0,t_k)²`. It is indeed immediate from `shellSet`, as the note
says, but it is **not unused**. The body of `density_one_of_shells` uses this lower-bound
lemma, and `Assembly/Clauses.lean:95–109` calls `density_one_of_shells` in `w8_density`;
`nlw2_proof` calls `w8_density`.

The other named consumers do not fix this counterexample:
`stepW:w7:lim-index` uses shell decay and the individual shell size bounds;
`stepW:w8:sd-trim` uses `w8Pi_subset_Rn`, `w8Rn_subset_box` and separation;
`bpW:w8:patch` and `stepW:w8:pl-dis` use disjointness and shell membership;
`p-close/p-size` use `shellSet_norm_ge` through `w8_tn_le_two_sum` and the arithmetic
in `Nlw2Proof.lean:54–132`. In particular, saying all seven use “only the inclusion”
is inaccurate: several instead use different clauses. The reverse inclusion is already
in the proof closure via `lower`, so both shell-geom and its `partition` step must be
retained under the supplied note. This is not a shell theorem counterexample.

### L: lambda facts and strict convexity

**PARTIAL-node ruling: retain `bpW:w0:basis#lambda-facts` PARTIAL. No PROVED consumer
requires the full strict-convexity statement on R or its derivative formula/strict monotonicity.**

The inventory has **37 direct consumers, of which 35 are PROVED and two are BYPASSED**
(`w1:tails`, `w3:Lambda`), not “37 PROVED consumers”. The W3 curvature supplier is
`Birkhoff/DivisorReal.lean:59–109`: `birkL_second_diff` proves
`m / L(k+2)^3 ≤ L(k)+L(k+2)-2L(k+1)` algebraically from squared frequencies;
`birkDelta_mono` follows. `DivisorCore.lean:171` uses that discrete result. This neither
assumes nor proves strict convexity on all real arguments.

There is also a genuine **non-strict** convexity result `Normal/NonresAux.lean:72`,
`lamExt_convex`, used at 92 and 95 in `lamExt_super` and hence by the older W0
nonresonance route (`stepW:w0n:22`). It would be wrong to report that no convexity of
any kind occurs. This is an algebraic non-strict inequality, not the full strict-convexity
and differentiability package of `w0-conventions.tex:45–47`. The remaining lambda consumers
use positivity, polynomial bounds, ratios, explicit two-mode facts, monotonicity or increments.

The reference audit also found a symbol collision that must be reported:

- `KAM.Wave.lam_pos`, `KAM.Wave.lam_ge`, `KAM.Wave.lam_succ_le` are not declarations at
  these names in the cited files. Those declarations are under **`KAM.Wave.W6SeqData`**
  (`Iteration/Sequences.lean:243,265`, `Iteration/IterArith.lean:313`). They concern
  the iteration weight `d.lam ν`, not the physical frequency `sqrt(j²+m)`.
- `KAM.Wave.lam_le` exists (`Recon/ReconAnalytic.lean:96`), but proves
  `lam m hm j ≤ (1+m)*j`, not `lam_j < j+sqrt(m)`.
- `lam_facts` (`Normal/Nondegeneracy.lean:314`) concerns the **two tangential modes**:
  positivity, `lamTan 0 < lamTan 1`, and gap less than one. It is not the claimed
  arbitrary-j strict monotonicity/increment package.

Physical-frequency suppliers do exist (e.g. `lam_pnat_pos`, `lam_gt`, `lam_div_pnat_le`,
`lam_sub_pnat_pos`, `lam_sub_pnat_le`, and W3's `birkL` lemmas). These observations do not
warrant silently repairing the current references or promoting the whole source paragraph.

## Frozen-root boundary, checks and handoff

`Nlw2Proof.lean` proves the full witness-ordered statement under `{m : R} (hm : 0<m)`.
The provider body is `KAM.Wave.nlw2_proof hm`. Its static local import envelope has
447 KAM modules, no provider and no frozen theorem. This import count is a conservative
search envelope, **not** a claim to have extracted Lean's elaborated declaration dependency DAG.
The proof-body chains above, rather than mere import membership, establish the counterexamples.
The eleven frozen W definitions carry no proofs of the rejected source clauses and introduce
no demand for the s<0 example, arbitrary-n determinant, general Riesz formula or strict convexity.
`KAM.IsDiophantine` is the additional K definition anchor specified by SPEC.

The existing SEAL-READY audit is applicable to the two inspected implementation blobs:

| File | Current SHA256 (matches seal audit) |
|---|---|
| `KAM/Wave/Assembly/Nlw2Proof.lean` | `79e0ee1e500dd02455cb9300a641b2531f705a2c064887132638fc9711a0c53f` |
| `KAM/Provider/Wave/Nlw2.lean` | `e1c75dde39e75e218a35293c60cfc7f78e303098c0ce61bb5ebd76d0c9a1b123` |

**Checkout qualification:** the actual frozen `KAM/Frozen/Wave/Theorems/Nlw2.lean` at
this commit still has `by sorry` between its proof markers. The SEAL-READY report itself
also says the anchor is unsealed and leaves sealing to the lander. The context describes
the prepared provider/proof route correctly, but this audit does not certify an already
sealed anchor at f04a53a7. This does not prevent auditing the prospective sealed proof closure.

Read-only checks performed: `git rev-parse HEAD` and branch name matched the requested scope;
packet parsing found 695 nodes and exactly 54 candidate rows; comparing every listed consumer
against packet DEPS and LEAN_STATUS found no inventory mismatch. A declaration-spelling scan
found all 303 candidate LEAN_REF occurrences by short name; a subsequent namespace-aware
inspection identified the four bad fully qualified references described in L and S. Thus the
short-name scan alone is explicitly **not** an existence certificate. The important declarations'
signatures and relevant bodies were read. `rg` and small Python text inspections were used;
no generated graph, source, frozen file, manifest or status was modified.

Required retained statuses for this proposal:

- **PARTIAL:** `bpW:w0:basis#lambda-facts`, `bpW:w0n:algebra`, `bpW:w5:solve`,
  `bpW:w5:flow`, `stepW:w5:f-flow`, `stepW:w5:f-par`, `stepW:w5:f-der`,
  `bpW:w7:shell-geom`, `stepW:w7:partition`.
- **NOT_STARTED:** `stepW:w0n:weight`, pending corrected reference/status review.
  Its supplier is already present; this retention does not assert the inequality is unproved.

The other 39 proposed bypasses and five definition promotions pass within this docs-only scope.
Existing W package receipts are not replaced by new compilation claims. No fresh `#print axioms`
was run; the seal audit's standard-axiom result is an inherited receipt for the matching blobs.
The nine rejected bypasses require corrected status/reference/route accounting before this
sync can pass. Some may properly become PROVED or support a narrower revised D27 note; that
would be a new proposal, not a repair performed by this auditor.

Suspected defects found here are in graph notes/references and their dependency claims, as
listed above. No new mathematical defect in a pinned paper is alleged; the already documented
normal-form corrections remain in force. No production-code deviation was introduced.
