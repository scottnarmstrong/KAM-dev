# B5-ROUTE independent package audit 1

Date: 2026-11-03. Worktree: `/root/code/KAM-inp-b5route`.
Audited HEAD: `25b51ee6bc81035b7ba64f2474952249b15a0375`.
Comparison ref `inp`: `e24669961b91521d0e3af783b46316c7a8098a0f`.
Prover commit: `d18be78b3a5304def084059d9052574fa3696036`.

## Verdict and scope

**PASS WITH NOTES** for B5-ROUTE and
`KAM.EffectiveStability.certifiedTorus_confinement` as an ordinary theorem with
the explicit premises in its handoff. Both B5-NF analytic obligations are actually
discharged. No mathematical or kernel failure was found. There is no frozen
B5-ROUTE anchor or provider: this is not a seal approval.

The main qualification is the finite-check boundary: `RouteChecks.hκc` is a
universally quantified derivative estimate for the certificate's approximate
embedding, not itself a Boolean or finite arithmetic test. It can be certified
using existing Fourier derivative majorants, but this package supplies neither
that new test nor its soundness bridge. Thus the analytic route from the stated
derivative bound is complete; automatic confinement from existing v2 checker
success plus numeric inequalities alone is not established here. The original
brief expressly permits this approximate-embedding derivative hypothesis.

Read: AGENTS, PLAN, DECISIONS; the generic package-audit brief; B5-ROUTE and
B1-common prover briefs; SPEC, FREEZE-PROPOSAL, B5-DESIGN, OWNER-DECISIONS
OD-B13–15; B5-ROUTE handoff including AUDIT FOCUS; program-b-plan §3.4
(`/root/code/KAM/docs/explorations/program-b-plan.md:426–457`); certificate
definitions/soundness APIs and inherited chart/Lagrangian/normal-form consumers.
Track B has no `statement.md` or B5-ROUTE node in blueprint-I/N/P; its controlling
statement is the focused Track B design and brief, not an unrelated I/N/P anchor.
The user's exact report destination overrides the generic brief's instruction
to write in the main inp worktree.

`git diff inp...HEAD` has 20 files, including six inherited B5-NF Lean modules,
its handoff/audit and Track B bookkeeping. B5-ROUTE adds nine modules (1108
lines at this HEAD). The only route-source changes after the prover commit are
two whitespace line wraps. The six NF files are byte-identical to the audited
NF revision `b4bf9142ede89c9a1a4aa2891825877787895e84` (empty `git diff` on those
paths); their prior audit is a scope receipt, not a substitute for checking the
route's use of their premises. I inspected that consumer and its drift inputs.

## Refutation checks

1. **Premises.** `G1Hyps` and `IsDiophantine` are the named certificate soundness
   premises; `CertifiedTorusAt` is literally the named-witness body of
   `CertifiedTorus` (`KAM/Application/Certified.lean:43`). All remaining main
   theorem inputs are radii, drift/margin inequalities, a common action bound
   `B`, initial data, and `RouteChecks`. No chart, inverse, Lagrangian, normal-form,
   smoothness, third-derivative, flow or confinement conclusion is assumed.
   `RouteChecks` has seven fields: six numerical radius/projection inequalities
   and the approximate-embedding derivative bound `hκc`. There is no additional
   sup-bound premise or conclusion-bearing typeclass. The real chart's
   Lagrangian condition comes from exact invariance and Diophantine input via
   B5-LAG, not from a field smuggled into the route checks.
2. **Projection and transpose.** `Strip.lean:28,74` applies the directional
   complex Cauchy estimate on the larger strip to `Kinf−c.K`, obtaining
   `‖D(Kinf^θ−id)‖ ≤ κc+disp/δ` throughout the smaller complex strip. The radius
   condition `δφ+δ≤rhoInf` supplies the actual strip inclusion, and the
   approximate embedding is holomorphic there by `G1Hyps.hK`.
   `Matrix.lean:74–115` proves the sup-norm transpose estimate by summing entry
   bounds, retaining the factor `n`. It derives nonzero determinant from
   injectivity and then proves `‖Aᵀ⁻¹J‖≤‖J‖/(1−nκ)`. Since `G1Hyps.hn` gives
   `n≥2` and `κ≥0`, this also gives `κ<1` for the real chart. No transpose
   operator norm is silently identified with the original operator norm.
3. **Exact real restriction and holomorphy.** `Chart.lean:35,40` defines the
   literal Jacobian and chart. Inverse entries are holomorphic by the
   adjugate/determinant formula with a proved nonzero determinant on the strip.
   `Real.lean:31` identifies the Jacobian at real points with the complexified
   real Jacobian; `map_transpose_inv_mulVec` proves inverse compatibility under
   inclusion, using nonsingularity. Consequently
   `torusCxChart_realInclusion` is equality of the entire phase point, at every
   real chart point, not only equality of real parts or equality on the zero
   section. `RouteChecks.realHam_comp_chart_eq` is therefore a global functional
   identity suitable for differentiating three times.
4. **Image and oscillation bound.** On
   `routeDomain = T_{δφ} × {J : ‖J‖<ρJ}`, the first chart component is exactly
   `Kinf^θ`, while the action displacement has norm at most
   `‖J‖/(1−nκ) < μ/2`. The strict action-domain bound and weak radius margin
   suffice even when the numeric margin is an equality. The product max norm
   gives membership in `ball (Kinf θ) (μ/2)`, contained in `c.D` by the actual
   certified witness. Composition with `G1Hyps.hholo` gives holomorphy of
   `c.H∘Ψ_ℂ`. `Bound.lean:111` applies the mean value inequality on this convex
   complex ball using `(G1Hyps.hbd z hz).1`, exactly `‖DH‖≤M`, and the complex
   energy identity at its centre. It derives
   `‖c.H(Ψ_ℂ w)−E0‖≤Mμ/2`; it does not confuse the derivative bound `M` with
   an absolute bound on `H`.
5. **Cauchy estimate and real transfer.** For `δ=r/4`, the proof uses open balls
   of radii `4δ,3δ,2δ,δ`. Each directional Cauchy step loses `δ`, so the third
   bound is `Mosc/δ³ = 64 Mosc/r³`, with `Mosc=Mμ/2`. Subtracting `E0` changes
   no derivative. Direction norms are retained through all three steps; this
   is an evaluated Fréchet-derivative estimate, not a coordinate bound requiring
   a later dimension conversion. The identification of nested directional
   derivatives uses neighborhood equality and differentiability of the
   operator-valued derivatives. `fderiv3_realPart_eq` uses third iterated
   Fréchet derivatives, scalar restriction and composition with the linear
   real inclusion and real-part map. `norm_realInclusion₂` preserves all three
   direction norms; `|Re z|≤‖z‖` supplies the scalar estimate. No factorial,
   polarization loss or missing dimension factor is hidden in this transfer.
6. **Cauchy ball bookkeeping and hG/hD3.** For every real point of the open
   cylinder `|J_j|<b_j+ε`, its complex ball of radius `r` lies in `routeDomain`
   by `r≤δφ` and `b_j+ε+r≤ρJ`. The proof retains both strict inequalities
   from the open ball/cylinder. Holomorphy plus the exact real functional
   identity gives C³ on this whole cylinder. `abs_fderiv3_realPart_le` with
   the derived oscillation bound gives B5-NF's `hD3` for all three directions
   on the same cylinder, with exactly `routeC3`. These are proof bodies in the
   final application, not new premises. Holomorphy also gives C² of the physical
   Hamiltonian on the full real slice of `c.D`.
7. **Consumer conclusion.** The final call to `torusNormalForm_confinement`
   uses `V={y | realInclusion₂ n y∈c.D}`, `H=realHam c.H`, the actual real chart
   and its inherited inverse, `E0=c.params.E0`, and `ω'=sinf • ωstar`.
   Periodicity is derived from `G1Hyps.hper` at the proved chart image points.
   `certifiedTorus_nfTorus` supplies energy and invariance from the certified
   torus. The conclusion retains `Tt<T₁`, the physical differential equation
   on `Ioo (-T₁) T₁`, uniqueness against every competing solution on every
   order-connected `I` containing zero within all of `V`, image/inverse identity,
   drift and action bounds for every `|t|≤Tt`, including endpoints. No frequency
   replacement by `ωstar`, rescaling of physical time, or weaker uniqueness is
   introduced. `η≥0` follows internally from `routeC3≥0`, `B²≥0`, and `hηB`.

## Finite-check boundary and deviations

**N1 — finite-checkable, but no new checker soundness theorem here.**
`Bound.lean:39` has
`hκc : ∀ θ ∈ complexStrip n δφ, ‖fderiv ℂ (fun θ => (c.K θ).1−θ) θ‖≤κc`.
It is a permitted quantitative source hypothesis about the approximate embedding,
not a conclusion about the unknown exact chart. Nevertheless, calling every field
of `RouteChecks` a finite numeric check would overstate the implemented interface.

The finite route is concrete: for each angle component and index `j`, form
`compDerivModel n c.weight c.piEnc (c.emb.angleDeg.getD i 0) c.emb.angle[i]? j`;
take its certified `supBound`, sum over `j` with outward rounding, and check
every row sum against a rational majorant `κc`. `Gram.lean:322` proves enclosure
of those actual angle-displacement derivatives; `CertModel.norm_le_supBound`
and the row-sum operator estimate give the desired bound on `T_ρ`, hence on
`T_{δφ}`. This needs the usual lawful arithmetic, weight and pi-enclosure checks
and the strip inclusion, as in `Sound/Embedding.lean:48–69`.
This is an available construction, not a newly verified Boolean interface.
The existing `checkEmbedding` checks rows of full `DK` against `σK−μ`, not rows
of `D(K^θ−id)` against `κc`; its success does not by itself supply the needed
smallness. OD-B15's finite-check integration remains checker-side follow-up.

Other deviations from the initial sketch are explicit and mathematically justified:

- `nκ<1` replaces `κ<1` in the complex transpose estimate; it is a stronger
  finite condition needed by the implemented sup-norm estimate, and is disclosed
  in the handoff/focused audit statement.
- The reference derivative bound holds on the complex strip, rather than only
  at real points. Real-point data alone do not provide the required complex
  invertibility; this strengthened hypothesis is also disclosed in the focus.
- `C₃=64(Mμ/2)/r³`, with `r≤δφ` and `b_j+ε+r≤ρJ`, replaces the sketch's
  `c₃ M/min(δφ,ρJ)³`. A ball about a nonzero action needs remaining action
  distance, and certificate `M` bounds `DH`; the derived oscillation bound is
  the correct Cauchy input. No independent sup-bound hypothesis is added.
- `RouteChecks` bundles the permitted bounds; no mathematical conclusion is
  added to its fields. All constants have explicit displayed dependence.

## Declaration-by-declaration review

All names in the following table have prefix `KAM.EffectiveStability`.
Each of the 45 explicit public theorems was independently axiom-probed.
Structure constructor/projections are covered by the `RouteChecks` row.

| Node/module | Declaration | Verdict | Reason / note |
|---|---|---|---|
| `CauchyThird` | `norm_fderiv_ball_le` | PASS | One Cauchy step on nested balls; arbitrary normed complex domain (finite-dimensional assumption omitted). |
| `CauchyThird` | `differentiableOn_fderivApply_cx` | PASS | Directional derivative holomorphy from analytic operator derivative. |
| `CauchyThird` | `fderiv_fderiv_apply_eq` | PASS | Differentiation commutes with fixed evaluation under actual local holomorphy. |
| `CauchyThird` | `fderiv_apply_fixed` | PASS | General complex operator-valued derivative/evaluation identity. |
| `CauchyThird` | `norm_fderiv3_ball_le` | PASS | Three losses r/4; arbitrary directions and centred oscillation bound, constant 64. |
| `CauchyThird` | `iteratedFDeriv_three_eq` | PASS | Exact identification with the nested third Fréchet derivative; general scalar field/carriers. |
| `CauchyThird` | `fderiv3_realPart_eq` | PASS | Third derivative scalar restriction and linear composition, exact equality. |
| `CauchyThird` | `abs_fderiv3_realPart_le` | PASS | Real third-direction bound with unchanged norms and constant. |
| `TorusRoute/Bound` | `RouteChecks` | PASS WITH NOTES | Permitted source-check fields; hκc needs a finite majorant soundness bridge (N1). |
| `TorusRoute/Bound` | `routeDomain` | PASS | Exact open strip times open sup-norm action ball. |
| `TorusRoute/Bound` | `isOpen_routeDomain` | PASS | Openness by continuous preimages, no positivity premise needed. |
| `TorusRoute/Bound` | `RouteChecks.routeKappa_nonneg` | PASS | Nonnegativity derived from actual norm bounds at zero. |
| `TorusRoute/Bound` | `RouteChecks.jac_le` | PASS | Complex entry bounds from strip Cauchy and certificate displacement. |
| `TorusRoute/Bound` | `RouteChecks.chart_differentiableOn` | PASS | Holomorphic chart on the whole angle strip, any action. |
| `TorusRoute/Bound` | `RouteChecks.chart_mem_ball` | PASS | Strict μ/2 image bound retaining n in the inverse estimate. |
| `TorusRoute/Bound` | `RouteChecks.chart_mem_D` | PASS | Uses the certified μ/2 ball inclusion at the actual angle. |
| `TorusRoute/Bound` | `RouteChecks.ham_differentiableOn` | PASS | Holomorphic Hamiltonian composition on routeDomain. |
| `TorusRoute/Bound` | `RouteChecks.ham_sub_le` | PASS | Oscillation bound Mμ/2 derived from DH and exact complex energy. |
| `TorusRoute/Chart` | `torusCxJac` | PASS | Actual complex angle Jacobian on coordinate vectors. |
| `TorusRoute/Chart` | `torusCxChart` | PASS | Intended complex cotangent chart formula; nonsingularity established before inverse use. |
| `TorusRoute/Chart` | `torusCxJac_differentiableOn` | PASS | Holomorphy of derivative entries from holomorphic K. |
| `TorusRoute/Chart` | `torusCxJac_sub_one_le` | PASS | Every entry of A−I bounded by the derivative operator norm. |
| `TorusRoute/Chart` | `torusCxChart_differentiableOn` | PASS | Inverse entries holomorphic where nκ<1; no action restriction required. |
| `TorusRoute/Chart` | `norm_torusCxChart_sub_le` | PASS | Action-component displacement bound; first-component difference is identically zero. |
| `TorusRoute/Data` | `torusNFGraph_torusReal` | PASS | Exact whole-function graph/real-restriction identity. |
| `TorusRoute/Data` | `certifiedTorus_angle_fderiv_le` | PASS | κc+disp/δ estimate throughout the stated smaller complex strip. |
| `TorusRoute/Data` | `certifiedTorus_chartData` | PASS | Derives all real chart fields including Lagrangian condition; no chart premise. |
| `TorusRoute/Data` | `differentiableAt_realHam_of_mem` | PASS | Physical real Hamiltonian differentiable at every real point over D. |
| `TorusRoute/Data` | `certifiedTorus_nfTorus` | PASS | Derives the three NF source fields with E0 and sinf•ωstar. |
| `TorusRoute/Matrix` | `differentiableOn_finset_prod_cx` | PASS | Finite product holomorphy, including empty product. |
| `TorusRoute/Matrix` | `differentiableOn_matrix_det` | PASS | Determinant expansion from entrywise holomorphy. |
| `TorusRoute/Matrix` | `differentiableOn_matrix_inv_entry` | PASS | Adjugate/determinant proof with explicit nonzero determinant premise. |
| `TorusRoute/Matrix` | `norm_le_transpose_mulVec_add` | PASS | Sup-norm row/column summation retains nκ. |
| `TorusRoute/Matrix` | `transpose_det_ne_of_entry_bound` | PASS | Proved nonsingularity from entry bounds and nκ<1. |
| `TorusRoute/Matrix` | `norm_transpose_inv_mulVec_le` | PASS | Correct inverse transpose bound with denominator 1−nκ. |
| `TorusRoute/Real` | `torusChartX_torusRealU` | PASS | Exact real base chart identity on all real angles. |
| `TorusRoute/Real` | `torusCxJac_realInclusion` | PASS | Exact matrix inclusion of the real Jacobian at every real point. |
| `TorusRoute/Real` | `map_transpose_inv_mulVec` | PASS | Inverse transpose commutes with real inclusion under nonzero determinant. |
| `TorusRoute/Real` | `torusCxChart_realInclusion` | PASS | Entire phase-point equality Ψℂ∘ι₂=ι₂∘Ψ at all real chart points. |
| `TorusRoute/Strip` | `norm_fderiv_le_of_strip_bound_cx` | PASS | Dimension-free directional Cauchy estimate at complex strip points. |
| `TorusRoute/Strip` | `norm_fderiv_angle_le_cx` | PASS | Derivative split plus Cauchy bound on the actual displacement. |
| `CertifiedTorusRoute/Glue` | `contDiffOn_realPart_of_holo` | PASS | Every stated regularity order from holomorphy on an open domain. |
| `CertifiedTorusRoute/Glue` | `RouteChecks.routeKappa_lt_one` | PASS | Uses n≥2 from G1Hyps and nonnegative κ to obtain κ<1. |
| `CertifiedTorusRoute/Glue` | `RouteChecks.chartData` | PASS | Discharges the projection inequality and applies item 1. |
| `CertifiedTorusRoute/Glue` | `RouteChecks.chart_det_ne` | PASS | Real nonsingularity from the derived real chart data. |
| `CertifiedTorusRoute/Glue` | `RouteChecks.realHam_comp_chart_eq` | PASS | Exact global pullback identity, suitable for repeated differentiation. |
| `CertifiedTorusRoute/Glue` | `ball_subset_routeDomain` | PASS | Correct remaining action distance b+ε+r and angle loss r≤δφ. |
| `CertifiedTorusRoute` | `routeC3` | PASS | Explicit constant 64(Mμ/2)/r³ with no existential dependence. |
| `CertifiedTorusRoute` | `routeC3_nonneg` | PASS | Nonnegativity from G1Hyps and nonnegative radius. |
| `CertifiedTorusRoute` | `certifiedTorus_confinement` | PASS WITH NOTES | Exact B1-T conclusion; hG and hD3 paid; checker integration limited as N1 states. |

## Definition classification

| Object | Classification | Whole-carrier / fallback assessment |
|---|---|---|
| `torusCxJac` | Geometric matrix | Actual total `fderiv` evaluated at coordinate directions everywhere. Theorems needing derivative meaning prove holomorphy/differentiability first. |
| `torusCxChart` | Complex chart formula | Literal `(K^θ,K^I+Aᵀ⁻¹J)` on the whole carrier. Mathlib's matrix inverse is total on singular matrices; the route proves determinant nonzero everywhere it uses inverse/chart claims. It never relies on a singular fallback. |
| `RouteChecks` | Prop-valued source-check bundle | Seven explicit fields; six scalar inequalities and the approximate-embedding derivative estimate. No bundled chart or confinement conclusion; see N1. |
| `routeDomain` | Analytic domain | Exact open strip times open sup-norm action ball, including empty/zero-dimensional cases of the literal set formula; no default branches. |
| `routeC3` | Explicit analytic bound | Literal `64*(M*(μ/2))/r³` for every real `r`. Lean's total division gives a value at zero; every application of the Cauchy/confinement theorem requires `r>0`, so no zero-radius fallback pays an estimate. |

There are four new `def`s, one `structure`, and no `abbrev`.

## Independent hygiene receipts

All commands ran in `/root/code/KAM-inp-b5route`. The literal prefix used was:

```sh
CAP='systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1'
```

All Lean/Lake/kernel commands, including lint's ABI subprocess, ran serially
under this prefix. No heartbeat, recursion or synthesis-budget override was used.
The targeted build additionally used the prescribed inp compile gate, whose
inner `nice -n 5` is retained. No clean, update, cache retrieval, full library
rebuild or opt-in certificate application build was requested.

### Targeted build

```sh
$CAP /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b5route KAM.EffectiveStability.CertifiedTorusRoute
```

Exit 0. The target imports all nine route modules. Output begins and ends:

```text
[inp-gate] slot 1 acquired 05:07:35 for KAM.EffectiveStability.CertifiedTorusRoute
Build completed successfully (3351 jobs).
```

Between these lines Lake replayed existing dependency warnings:
`Certificate/Arith/PiHigh.lean:218` unused simp argument;
`Certificate/Expr/Basic.lean:93` unreferenced variable;
`Certificate/Sound/Static.lean:99,152` unused section variable;
`Certificate/Sound/Ham.lean:68` unused section variable;
`Strip/CohomologicalRussmannLattice.lean:45` deprecated `if_pos`;
`Strip/CohomologicalRussmannBound.lean:72` deprecated `if_neg`.
There was no warning from any of the nine route modules.

### Kernel replay

```sh
$CAP lake env leanchecker --verbose KAM.EffectiveStability.CertifiedTorusRoute KAM.EffectiveStability.CertifiedTorusRoute.Glue KAM.EffectiveStability.CauchyThird KAM.EffectiveStability.TorusRoute.Matrix KAM.EffectiveStability.TorusRoute.Chart KAM.EffectiveStability.TorusRoute.Real KAM.EffectiveStability.TorusRoute.Strip KAM.EffectiveStability.TorusRoute.Data KAM.EffectiveStability.TorusRoute.Bound
```

Exit 0, exact output:

```text
replaying KAM.EffectiveStability.TorusRoute.Bound
replaying KAM.EffectiveStability.TorusRoute.Data
replaying KAM.EffectiveStability.TorusRoute.Strip
replaying KAM.EffectiveStability.TorusRoute.Real
replaying KAM.EffectiveStability.TorusRoute.Chart
replaying KAM.EffectiveStability.TorusRoute.Matrix
replaying KAM.EffectiveStability.CauchyThird
replaying KAM.EffectiveStability.CertifiedTorusRoute.Glue
replaying KAM.EffectiveStability.CertifiedTorusRoute
```

### Signature/application and axioms

```sh
$CAP lake env lean .lake/abi-scratch/b5route-audit-probe.lean
```

Exit 0. The probe imported the main route module, issued `#print axioms` for
every explicit public theorem in the nine files, and elaborated a copy of the
main theorem's complete declaration under the fresh name `auditB5RouteExplicit`
with body:

```lean
by
  exact certifiedTorus_confinement hG hdio hT h hr hrφ a b η ε Tt hε hTt hmargin hrJ
    B hB0 hB hηB w₀ hw₀
```

This supplies every explicit binder in order, without adding a premise. The
type was also compared manually with the brief and B1-T consumer as described
above. The generic frozen/provider `type_of%` and seal-copy checks are
inapplicable: neither a frozen route declaration nor a provider exists.

Exact output (all 45 declarations):

```text
+'KAM.EffectiveStability.norm_fderiv_ball_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_fderivApply_cx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_fderiv_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_apply_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_fderiv3_ball_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.iteratedFDeriv_three_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv3_realPart_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.abs_fderiv3_realPart_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.isOpen_routeDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.routeKappa_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.jac_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.chart_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.chart_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.chart_mem_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.ham_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.ham_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusCxJac_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusCxJac_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusCxChart_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_torusCxChart_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFGraph_torusReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorus_angle_fderiv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorus_chartData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableAt_realHam_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorus_nfTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_finset_prod_cx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_matrix_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_matrix_inv_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_le_transpose_mulVec_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.transpose_det_ne_of_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_transpose_inv_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartX_torusRealU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusCxJac_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.map_transpose_inv_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusCxChart_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_fderiv_le_of_strip_bound_cx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_fderiv_angle_le_cx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.contDiffOn_realPart_of_holo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.routeKappa_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.chartData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.chart_det_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.RouteChecks.realHam_comp_chart_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.ball_subset_routeDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.routeC3_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.certifiedTorus_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Lint and protected paths

```sh
$CAP sh scripts/lint_sources.sh
```

Exit 1. Exact combined output:

```text
+KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4571 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.908s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The sole failing check is the stale generated root expressly permitted by the
audit brief. It was not regenerated. Module conventions, the 25 guard tests,
frozen-anchor guard and core ABI hashes pass. The application anchors reported
as file-hash-only were not built or represented as ABI-rechecked here.

The unique-short-name command, with exactly the same nine module arguments
as kernel replay, was:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b5route KAM.EffectiveStability.CertifiedTorusRoute KAM.EffectiveStability.CertifiedTorusRoute.Glue KAM.EffectiveStability.CauchyThird KAM.EffectiveStability.TorusRoute.Matrix KAM.EffectiveStability.TorusRoute.Chart KAM.EffectiveStability.TorusRoute.Real KAM.EffectiveStability.TorusRoute.Strip KAM.EffectiveStability.TorusRoute.Data KAM.EffectiveStability.TorusRoute.Bound
```

Exit 0, exact output:

```text
short-name check OK (no reused public short name)
```

A Python scan of all nine files for lines longer than 100 Unicode characters
returned `Width violations: []`. File line counts, in the declaration-table
order by module, are CauchyThird 216, Bound 134, Chart 111, Data 106, Matrix
119, Real 96, Strip 106, Glue 100, CertifiedTorusRoute 120; maximum 216,
total 1108. All have the copyright header, `module`, public imports, module
docstring and exposed public noncomputable section. Bodies were reviewed for
the forbidden proof escapes/resource overrides; source lint supplies the
repository-wide guard check.

```sh
git diff --exit-code inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md lakefile.lean
```

Exit 0, no output. No protected source was changed. A static recursive import
walk from the route main module found 184 KAM modules, no provider, no
DRAFT_SORRY anchor and 23 frozen definition modules, each `SEALED` in the
current manifest. In particular, importing core namespace `KAM.Application`
here is not an import of an opt-in generated certificate application library.

```sh
git diff --check inp...HEAD
```

Exit 2, exact output:

```text
KAM/EffectiveStability/CauchyThird.lean:102: trailing whitespace.
+  have hA1 : AnalyticOnNhd ℂ (fderiv ℂ g) (ball z₀ r) := 
KAM/EffectiveStability/CauchyThird.lean:104: trailing whitespace.
+  have hA2 : AnalyticOnNhd ℂ (fderiv ℂ (fderiv ℂ g)) (ball z₀ r) := 
```

This is a cosmetic note, outside the mathematical and mandated source-lint
acceptance checks. No production file was repaired during the audit.

## Suspected defects, uncertainties and handoff

- **N2 — local documentation discrepancy:** `CauchyThird.lean:17` says
  “radii `r, 2r/3, r/3`”, while lines 99–137 use `r, 3r/4, r/2, r/4`.
  The statement and proved constant 64 are correct; the module summary is stale.
- **N3 — stale exported-name descriptions:** `Bound.lean:16–19` advertises
  `routeChart_mem_ball`, `routeHam_differentiableOn`, `routeHam_sub_le`, but the
  actual declarations are `RouteChecks.chart_mem_ball`,
  `RouteChecks.ham_differentiableOn`, `RouteChecks.ham_sub_le`.
  `Glue.lean:19–20` advertises `realHam_chart_mem` / `realHam_chart_shift`,
  which are not exported there; membership and periodicity are proved inside
  the final theorem. These are documentation defects, not missing proof steps.
- **Design correction:** B5-DESIGN's package table allocates the third-derivative
  Cauchy estimate to B5-NF. At these bytes it is implemented by B5-ROUTE's
  `CauchyThird`, with B5-NF consuming `hG` and `hD3`. The composed route pays
  both inputs; the table's allocation remains stale.
- No new defect in a pinned external mathematical source was identified.
  The proof is built from the local plan and existing Lean/Mathlib analytic
  results; this audit does not assert a fresh line-by-line audit of external
  GLS17/HL19 PDFs. No statement or manifest was frozen or altered.
- The finite majorant bridge in N1 remains an explicit limitation, not a claim
  that arbitrary certified tori have small projection defect. Folded projections
  remain outside this adapter as the design specifies.

Only this report is a repository edit. Audit-created probe/metadata files under
`.lake/abi-scratch/` were removed after their evidence was incorporated. No git
state-changing command, production repair, generated-root regeneration or memory
update was performed.
