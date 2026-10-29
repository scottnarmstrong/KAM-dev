# DEFS-P2 independent definitions audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-defaud2`.
Audited HEAD and comparison branch `inp` both resolve to
`4d8a6848e381c8baaa9072e8d9867e3fc7a36f2a`.

**Overall: FAIL for closing all six nodes under the handoff's literal whole-public-carrier and named-property gates.**
This is a definitions audit of existing code, not a provider/seal package. No new frozen anchor is offered;
provider/frozen signature equality and seal-body substitution are therefore not applicable.
The failures below concern the proposed definition-node coverage, not a refutation of a compiled theorem.

## Scope and method

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local handoff,
the relevant sections of `GAP-PLAN-P2.md`, the track-P statement, all six complete graph records,
their blueprint statements, the frozen coordinate definitions and the relevant existing Lean bodies.
The explicit user report path overrides the generic brief's main-worktree destination.
`git diff inp...HEAD` is empty, including protected paths. The initial untracked handoff was retained.
Only this report was authored; the prescribed lint script creates and removes its own ABI scratch file.
The audit's own elaboration probes used stdin and left no files.

Each row assesses the named object itself. FAITHFUL-WITH-NOTE records a coordinate adapter or a necessary
source-domain restriction; it does not certify a raw total extension outside that restriction.
A separately identified raw fallback fails the handoff's whole-public-carrier requirement even when all
legitimate mathematical uses are guarded. No conclusion-shaped hypothesis was introduced or used to
close a source result. No new declaration exists in this branch to inventory.

Locator abbreviations below are directory-relative, with declaration namespaces stated here:

- `TS/` = `KAM/Planetary/TwoScale/`; `AV/` = `KAM/Planetary/Averaging/`.
- `KE/` = `KAM/Kepler/`; `PO/` = `KAM/Planetary/Poincare/`.
- `SF/` = `KAM/Planetary/SecularForm/`; `SS/` = `KAM/Planetary/SecularSpectrum/`.
- `ND/` = `KAM/Planetary/Nondegeneracy/`; `PT/` = `KAM/Planetary/PlanarTorsion/`.
- `PA/` = `KAM/Planetary/PlanarAssembly/`; `WD/` = `KAM/Weighted/`.
- `FD/` = `KAM/Frozen/Planetary/Defs/`; `KD/` = `KAM/Frozen/Defs/`.
- Unless qualified otherwise, names have prefix `KAM.Planetary`;
  `KE` names have prefix `KAM.Kepler`, `SF` names `KAM.Planetary.SecularForm`,
  `SS` names `KAM.Planetary.SecularSpectrum`, `ND` names `KAM.Planetary.Nondegeneracy`,
  and `WD` names `KAM.Weighted`. Frozen `KD` names have prefix `KAM`.

## Node verdicts and usable references

| Node | Verdict | Closability and exact limitation / LEAN_REF |
|---|---|---|
| `bpP:p3:conv#data` | FAIL | **NOT CLOSABLE under the whole-carrier gate.** The raw numerical `wsum`/`wnorm` have documented junk values outside the summable, bounded locus; `WBound` is a faithful guarded bound interface, not an unconditional numerical norm. The row-sum/operator-norm dictionary is supplied by Mathlib, with its explicit matrix norm scope. Usable partial refs: `realFreq`, `dioBase`, `omegaSet`, `KamHyp`, `geometricWidth`, `coefficientDom`, `conv_data`, `realTube`, `firstBlock`, `lastBlock`, `KAM.Weighted.WBound`, `wbound_iff`, `WBound.mono`, `sup_le_wbound`, `wbound_mono_set`, `norm_coeff_zero_le`, `dp_nbhd_subset`. |
| `bpP:p3:limitmap#data` | FAIL | **NOT CLOSABLE.** No public declaration for arbitrary checked map `G ↦ S ∘ G ∘ S⁻¹`, or a general `L_*` predicate/constant, was located. `psi_lip_step` gives a particular displacement bound, not the general named objects. Partial refs: `limitmap_data`, `sc`, `unsc`, `sc_unsc`, `unsc_sc`, `limitmap_data_eq_norm_sc`, `phaseTube`, `realTube`, `mem_realTube_iff`, `PsiSteps.psi_lip_step`. |
| `bpP:p7:conv#data` | FAIL under whole-carrier gate; domain-restricted identification passes | **NOT CLOSABLE under the requested no-fallback rule.** The exact track-I `delaunay` is located and symplectic on `deDom`, but its public total carrier is `Phase 2`; its Kepler solver has an explicit off-ellipse zero branch. Domain-restricted refs: `quarterTurn`, `KAM.Kepler.rot`, `KAM.Kepler.ex`, `planeCross`, `KAM.symplecticForm`, `poincareGamma`, `KAM.Kepler.delaunay`, `KAM.Kepler.deDom`, `KAM.Kepler.delaunay_symplectic`. This resolves the survey's UNVERIFIED track-I identification on its actual source domain. |
| `bpP:p7:sec-product#data` | PASS WITH NOTES | **CLOSABLE. LEAN_REF:** `KAM.Planetary.Phase`, `assemble`, `fast`, `slow`, `bodyVector`, `planetBlock`. These are precisely coordinate and body-extraction data; no product-chart theorem or its off-domain extension is needed to close this node. |
| `bpP:p10:conv#data` | PASS WITH NOTES for the listed definitions and substantive analytic/spectral properties; incomplete literal property coverage | **NOT CLOSABLE if every asserted property needs a named lemma, as requested.** Open/convex/connected axes, analytic action diffeomorphism, sorted negative eigenvalues, the frequency formula, both open sets and their inclusion are located. No public lemma specifically exporting positive-dilation closure of `axes n` (the word “cone”) was located. Partial refs: `SecularForm.axes`, `action`, `axis`, `actionDomain`, `nu`; `SecularSpectrum.sigma`, `sorted`, `goodAxes`, `simpleAxes`, `length2`, `op2`, `frobenius`, `norm_compare`; `Nondegeneracy.action_diffeomorphism`, `nu_action_eq`, `isOpen_simpleAxes`, `isOpen_goodAxes`, `goodAxes_subset_simpleAxes`, `sigma_neg`; `SecularSpectrum.sorted_monotone`, `sorted_eq_eigenvalues_comp`. No openness gap remains. |
| `bpP:p12:sec-set#data` | FAIL | **NOT CLOSABLE.** The dictionary and Euclidean length are located, but the asserted cylinder inequality has no named public export in this checkout. It occurs as local `hsq` in `PT/FrozenBridge.lean:46` and related private estimates; this does not meet the explicit named-lemma gate. The chart has the same off-domain solver extension noted above. Partial refs: `PlanarData.kappa`, `PlanarData.actions`, `PlanarData.axes`, `p11c_axes`, `assemble`, `poincareProd`, `secularGamma`, `oscillatorAction`, `p11cL_slow`, `p11c_slowLength`, `cylinder`. |

The p10 cone issue is deliberately distinguished from a mathematical defect: closure under positive dilation
follows directly from the strict inequalities, but no proof was written or silently substituted in this audit.
Likewise the missing cylinder export is elementary; its ease does not create a public Lean declaration.

## Per-source-object classification

### Part 3 conventions

Source: `docs/graph/P/DEPGRAPH.md:6953`,
`blueprint-P/parts/p3a-two-scale-iteration.tex:11-34`.

| Source object or asserted property | Lean declaration (file:line) | Classification | Reason |
|---|---|---|---|
| Period-one angle coordinates / integer indices | `CPhase`, `CHam` (`AV/Setting.lean:40-41`); `KAM.Weighted.InClass` (`WD/Norm.lean:42`) | FAITHFUL-WITH-NOTE | Universal-cover functions on Pi carriers with explicit period-one predicate; no quotient phase carrier is silently substituted. |
| Fourier character | `KAM.character` (`KAM/Strip/Fourier.lean:40`) | FAITHFUL | Literal exponential with `2πi` and integer dot product. |
| `|k|₁` | `KAM.Fourier.modeSize` (`KAM/Fourier/Derivative.lean:37`) | FAITHFUL | Sum of absolute coordinate values. |
| Symplectic form and Hamilton equations | `KAM.symplecticForm` (`KD/SymplecticForm.lean:23`); `KAM.hamiltonianVectorField` (`KD/HamiltonianVectorField.lean:24`) | FAITHFUL-WITH-NOTE | Lean order is `(angle,action)` rather than source `(action,angle)`; the form and derivative signs are exactly the source convention after that explicit swap. Derivatives are interpreted at differentiability points. |
| Max vector and induced CLM norms | Pi/Prod norm; `KamHyp.hessian` (`TS/Setting.lean:59`) | FAITHFUL-WITH-NOTE | Standard sup-norm carriers and induced CLM norm; not the elementwise matrix norm. |
| Explicit rectangular matrix row-sum equality | `Matrix.linfty_opNorm_def`, `Matrix.linfty_opNorm_toMatrix` (Mathlib `Mathlib/Analysis/Matrix/Normed.lean:284,474`) | FAITHFUL-WITH-NOTE | The first gives the supremum of absolute row sums; the second identifies the matrix norm of a CLM with its operator norm. Use the explicit `Matrix.Norms.Operator` scope for these matrix expressions; Pi/CLM norms already have the required meaning. |
| Complex action neighborhood `D_r` | `KAM.actionNbhd` (`KD/ActionNbhd.lean:24`) | FAITHFUL | Existential strict ball around a real base point, including empty base sets without a distance-to-empty convention. |
| Real part of `D_r` | `realTube` (`AV/Setting.lean:48`); `mem_realTube_iff` (`TS/LimitMapPsi.lean:93`) | FAITHFUL | Preimage under real inclusion; named equivalence gives `∃ J ∈ D, ‖v-J‖ < r`. |
| Nested neighborhoods and radius monotonicity | `dp_nbhd_subset` (`TS/StepDp.lean:52`); `actionNbhd_mono` (`TS/StepFreq.lean:32`) | FAITHFUL-WITH-NOTE | First lemma handles any real intermediate base contained in the real tube, hence the real-base interpretation used here; complex-ball addition is `ball_subset_actionNbhd` (`TS/StepInj.lean:30`). |
| Strip `T_σ` and width dictionary | `geometricWidth`, `coefficientDom`, `conv_data` (`AV/Setting.lean:43,46,59`); `KAM.complexStrip` (`KD/ComplexStrip.lean:23`) | FAITHFUL | Literal width `σ/(2π)`; `conv_data` identifies the product with the frozen action neighborhood. |
| Fourier coefficient and exponential weight | `KAM.Weighted.coeff`, `modeWeight` (`WD/Norm.lean:48,52`) | FAITHFUL-WITH-NOTE | Weight is `exp(2π s |k|₁)` at geometric width `s=geometricWidth σ`, giving the source weight exactly. |
| Raw numerical weighted sum / supremum norm | `wsum`, `wnorm` (`WD/Norm.lean:55,69`) | NOT FAITHFUL on unrestricted public carrier | `wsum` is Lean's total `tsum`, explicitly documented as junk zero if nonsummable; `wnorm` is a real conditional supremum, explicitly meaningful only with `HasFiniteWNorm`. Neither is an everywhere meaningful source norm. |
| Guarded weighted bound | `WSummable`, `WBound`, `HasFiniteWNorm`, `wbound_iff` (`WD/Norm.lean:58,62,65,73`) | FAITHFUL-WITH-NOTE | `WBound` requires summability at every action and bounds its sum. On the finite locus it is related to the numerical supremum by `wbound_iff` (nonnegative bound). This avoids using the raw junk values in the estimates. |
| Norm monotonicity in radii / base | `KAM.Weighted.WBound.mono` (`WD/Norm.lean:95`); `wbound_mono_set` (`TS/StepMono.lean:46`) | FAITHFUL | Guarded summable bounds on smaller domains, including base-set restriction. |
| Supremum and zeroth coefficient bounded by norm | `KAM.Weighted.sup_le_wbound` (`WD/SupWeighted.lean:61`); `norm_coeff_zero_le` (`TS/StepMono.lean:59`) | FAITHFUL-WITH-NOTE | Named guarded pointwise bound exports, with holomorphy/periodicity where reconstruction needs them. |
| Two-scale Diophantine set | `twoScaleDiophantine` (`KAM/Planetary/Hamiltonian/Diophantine.lean:30`) | FAITHFUL | Exactly the two lattice cases and full `ℓ¹` denominator, with separate `γ₁,γ₂`. |
| Real frequency `ω₀` | `realFreq` (`TS/Setting.lean:29`); `freq_realInclusion_eq` (`TS/StepFreq.lean:88`) | FAITHFUL-WITH-NOTE | Raw definition takes the real part of the complex derivative. The named reality bridge identifies it with the source frequency under holomorphy/reality. It is not an identification for arbitrary complex-valued Hamiltonians. |
| `D^dio` | `dioBase` (`TS/Setting.lean:32`) | FAITHFUL-WITH-NOTE | Exactly `D ∩ realFreq⁻¹(twoScaleDiophantine)`; the preceding reality restriction applies. |
| Frequency image | `omegaSet` (`TS/Setting.lean:36`) | FAITHFUL-WITH-NOTE | Literal frequency image intersected with the Diophantine set. Additional useful setting object, not a replacement for `D^dio`. |
| `U` | `freq` (`KAM/Nekhoroshev/NormalForm/Setting.lean:38`); `KamHyp.hessian` (`TS/Setting.lean:59-63`) | FAITHFUL-WITH-NOTE | Hessian is `fderiv ℂ (freq h)` on the holomorphic domain, represented as a CLM. |
| `Uhat` | `lastBlock` (`AV/Setting.lean:53`); `KamHyp.hessian` (`TS/Setting.lean:61`) | FAITHFUL-WITH-NOTE | Last output block of the full Hessian; all input directions remain, giving the source rectangular carrier. |
| `T₁` | `firstBlock` (`AV/Setting.lean:51`); inverse field in `KamHyp.hessian` (`TS/Setting.lean:62-65`) | FAITHFUL-WITH-NOTE | First output rows of the inverse equivalence `A.symm`. Its two-sided inverse law follows from the equivalence and its stated equality with the Hessian; no arbitrary inverse matrix is supplied. |
| `T₂` | `lastBlock` (`AV/Setting.lean:53`); inverse field in `KamHyp.hessian` (`TS/Setting.lean:62-66`) | FAITHFUL-WITH-NOTE | Last output rows of the same inverse equivalence. |
| Source-premise package (supplement) | `KamHyp` (`TS/Setting.lean:42`) | FAITHFUL-WITH-NOTE | Contains regularity, reality, derivative/inverse bounds, positivity and numerical smallness; no limiting torus, limiting map, or final KAM conclusion. It is hypothesis infrastructure, not a proof of the convention node by itself. |

### Part 3 limit-map data

Source: graph record at `DEPGRAPH.md:7010`; `p3b-two-scale-limit.tex:43`.

| Source object | Lean declaration (file:line) | Classification | Reason |
|---|---|---|---|
| Rescaling `S` | `sc` (`TS/LimitMapScale.lean:42`) | FAITHFUL-WITH-NOTE | Lean input `(θ,I)` and flattened output `(2πθ/s,I/R)` reverse the source's action-first blocks. Put `R=rhoHat p`, `s=p.s`; this is an explicit coordinate permutation, not changed scaling. |
| `S⁻¹` | `unsc` (`TS/LimitMapScale.lean:37`); `sc_unsc`, `unsc_sc` (`:45,58`) | FAITHFUL-WITH-NOTE | Multiplication by `s/(2π)` and `R`. Inverse laws require `R≠0`, `s≠0`, as supplied by source positivity. Zero/negative parameters are not being certified as source rescalings. |
| Scaled norm `|.|_*` | `limitmap_data` (`TS/LimitMapScale.lean:30`); `limitmap_data_eq_norm_sc` (`:127`) | FAITHFUL-WITH-NOTE | Literal max of scaled angle/action norms; the named norm equality requires positive radii. Formula has no conditional fallback. |
| General checked map `Gcheck` | No public declaration located; nearest local expression `Δ` (`TS/LimitMapLip.lean:243-245`) | MISSING | Local `Δ` is `sc(Ψ(unsc z)-unsc z)`, a particular checked displacement, not a public definition for arbitrary `G`. `sc` and `unsc` permit writing the missing composition, but do not name that source object. |
| General scaled Lipschitz notation `L_*` | Nearest public theorem `PsiSteps.psi_lip_step` (`TS/LimitMapLip.lean:225`) | MISSING | The theorem states a particular pairwise scaled bound, faithfully, but there is no general named predicate or chosen scalar Lipschitz constant for arbitrary maps. |
| `calD_j` | `realTube` (`AV/Setting.lean:48`); `phaseTube` (`TS/LimitMapPsi.lean:36`) | FAITHFUL-WITH-NOTE | Substitute `D=Ds j`, `r=(seq p j).ρ/2`. `phaseTube` includes the unrestricted real angle factor; its action projection is the source domain. No arbitrary sequence is claimed to satisfy the iteration. |
| Real stage restriction (supplement) | `psiR` (`TS/LimitMapPsi.lean:32`) | FAITHFUL-WITH-NOTE | Literal `Re ∘ Ψ ∘ inclusion`. Equality with the unprojected stage map needs the real-on-real conclusion; `PsiSteps.psi_real`/`phi_real` carry that domain-specific output. |

### Part 7 conventions

Source: graph record at `DEPGRAPH.md:14465`; `p7-kepler-poincare.tex:27-33`;
track-I identification checked against `blueprint-I/parts/p7-delaunay.tex:158-164,208-210`.

| Source object | Lean declaration (file:line) | Classification | Reason |
|---|---|---|---|
| `m>0`, `κ=Gm₀>0` | `SecularForm.Data` (`SF/Basic.lean:38`); `PlanarData.kappa`, `PlanarData.Valid` (`PT/Setting.lean:37,36`) | FAITHFUL-WITH-NOTE | Physical typing data; positivity is explicit. Raw parameters to the chart are not intrinsically positive. |
| Planar length `l` | `planeLength` (`FD/PlaneLength.lean:38`) | FAITHFUL | Euclidean square-root-of-squares, not the Pi max norm. |
| Radian angles | `rot`, `ex` (`KE/Basic.lean:55,59`); `poincareF` (`PO/Chart.lean:40`) | FAITHFUL-WITH-NOTE | Real trigonometric angles and radian Kepler equation. This is separate from period-one torus parameters. |
| Quarter turn `J₀` | `quarterTurn` (`FD/QuarterTurn.lean:35`) | FAITHFUL | Exact `![-v 1,v 0]` on every real vector. |
| Rotation `R(g)` | `KAM.Kepler.rot` (`KE/Basic.lean:55`) | FAITHFUL | Literal cosine/sine rotation on every input. |
| `e_g` | `KAM.Kepler.ex` (`KE/Basic.lean:59`) | FAITHFUL | Literal `(cos g,sin g)`. |
| Oriented cross product `cr` | `planeCross` (`FD/PlaneCross.lean:35`) | FAITHFUL | Exact `q₀p₁-q₁p₀`. |
| Position-first physical phase and chart form | `Phase` (`FD/Phase.lean:37`); `KAM.symplecticForm` (`KD/SymplecticForm.lean:23`) | FAITHFUL | Form is `Σ(dp∧dq)`; on chart coordinates it is precisely `dΛ∧dλ+dη∧dξ`. |
| `Γ` | `poincareGamma` (`PO/Chart.lean:34`) | FAITHFUL | Exact half-sum of the second position/momentum coordinate squares. |
| Track-I Delaunay orbit formula on the elliptic domain | `KAM.Kepler.delaunay`, `orbitMapR`, `orbitFrame` (`KE/Orbit.lean:45,41,34`); `deDom`, `eccOf` (`KE/Energy.lean:36,30`) | FAITHFUL-WITH-NOTE | This is the actual track-I orbit map. On `0<G<L`, `sqrt(1-e²)=G/L`, giving exactly the track-I formula, strength one and mass one. No different map was substituted. |
| Raw total Delaunay map on `Phase 2` | Same `delaunay`; `eccAnom`, `keplerLong` (`KE/Equation.lean:272,117`) | NOT FAITHFUL under the whole-carrier/no-fallback criterion | Public type does not restrict to `deDom`. `keplerLong` explicitly returns zero when vector length is at least one; the orbit formula is totalized outside the source domain. The inverse chosen on the valid domain is unique (`keplerLong_unique :126`), so choice there is not an arbitrary physical witness. |
| Delaunay pullback identity | `KAM.Kepler.delaunay_symplectic` (`KE/DelaunaySymplectic.lean:447`) | FAITHFUL-WITH-NOTE | Named `IsSymplecticOn 1 delaunay deDom`; simultaneous reversal of the form on both sides yields the source `dq∧dp` identity. No off-domain symplectic claim. |

### Part 7 product-coordinate data

Source: graph record at `DEPGRAPH.md:14498`; `p7-kepler-poincare.tex:188`.

| Source object | Lean declaration (file:line) | Classification | Reason |
|---|---|---|---|
| `w ∈ Ph_(2n)` | `Phase` (`FD/Phase.lean:37`) | FAITHFUL | Position and momentum vectors on the required finite Pi carriers. |
| `w=((λ,ξ),(Λ,η))` | `assemble` (`FD/Assemble.lean:38`); `fast`, `slow` (`FD/Fast.lean:37`, `FD/Slow.lean:37`) | FAITHFUL | Exact `assemble Λ λ η ξ=(append λ ξ,append Λ η)` on every input; first `n` entries are fast. |
| Planetwise input block | `planetBlock` (`PO/Product.lean:41`) | FAITHFUL | Literal `((λ_i,ξ_i),(Λ_i,η_i))`. |
| Cartesian planet `q^(i)=body(q,i)` | `bodyVector` (`FD/BodyVector.lean:37`) | FAITHFUL | Uses `finProdFinEquiv (i,k)` with two Cartesian coordinates per planet. |
| Product chart (supplement, outside this node's coordinate contract) | `poincareProd`, `poincareProdDom` (`PO/Product.lean:45,51`) | FAITHFUL-WITH-NOTE on the declared chart domain | Bodywise formula and exact product of one-planet domains. Raw total `poincareProd` inherits the solver fallback outside that domain; it is not needed as a whole-carrier reference for this coordinate-only node. |

### Part 10 conventions

Source: graph record at `DEPGRAPH.md:17520`; `p10-nondegeneracy.tex:15-21`.

| Source object or property | Lean declaration (file:line) | Classification | Reason |
|---|---|---|---|
| `A_n` with increasing axes | `SecularForm.axes` (`SF/Basic.lean:47`) | FAITHFUL | Exact positive coordinates and `StrictMono`; `Fin n` indexing puts inner planet first. |
| Open, convex, connected `A_n` | `action_diffeomorphism` (`ND/Frequency.lean:80`), also `convex_axes`, `isConnected_axes` (`ND/GoodAxes.lean:33,49`) | FAITHFUL | Named conjunction exports all three properties; no owner premise assumes them. |
| “Cone” / positive-dilation closure of `A_n` | No dedicated public export located | MISSING | Directly true from the formula, but not a named property export. Search of planetary modules for axes scaling/cone lemmas found spectral scaling formulas, not this property. |
| `Λ_i(a)` | `SecularForm.action` (`SF/Basic.lean:48`) | FAITHFUL-WITH-NOTE | Literal `m_i sqrt(G m₀ a_i)`, with `Data` supplying positivity; no branch selecting a different map. Diffeomorphism claim is only on `axes`. |
| Inverse axis formula | `SecularForm.axis` (`SF/Basic.lean:49`) | FAITHFUL-WITH-NOTE | Literal `I_i²/(m_i² G m₀)`. Inverse law is on positive action image, not negative actions. |
| `A_n^Λ` | `SecularForm.actionDomain` (`SF/Basic.lean:50`) | FAITHFUL | Literal image of `axes` under `action`. |
| Real analytic diffeomorphism and open image | `action_diffeomorphism` (`ND/Frequency.lean:80`) | FAITHFUL | Explicit inverse identities, analyticity of both maps on their source sets, and openness. |
| `ν_i` in actions | `SecularForm.nu` (`SF/Basic.lean:51`) | FAITHFUL-WITH-NOTE | Literal `κ²m_i³/I_i³`; source action positivity guards the denominator. |
| `ν_i(a)=sqrt(κ)a_i^(-3/2)` | `nu_action_eq` (`ND/GoodAxesNodes.lean:94`) | FAITHFUL | Exact named formula after applying `action`, with only `a∈axes` and physical data. |
| `Q_h` | `SecularForm.coeffs` (`SF/Coefficients.lean:42`) | FAITHFUL-WITH-NOTE | Literal normalized pair-coefficient matrix; diagonal/off-diagonal split is its intended formula, not a fallback. Its meaning as secular coefficients is upstream Part 8, not independently reproved here. |
| Sorted spectrum `σ₁≤…≤σ_n` including multiplicity | `SecularSpectrum.sigma` (`SF/Coefficients.lean:121`); `sorted` (`SS/Norms.lean:34`); `sorted_monotone`, `sorted_eq_eigenvalues_comp` (`SS/LocalAnalytic/Sorted.lean:41,33`) | FAITHFUL | Reversed `eigenvalues₀` supplies increasing order; named bijection with the full eigenvalue list preserves multiplicities, without choosing an arbitrary labelling. |
| `σ_j<0` | `Nondegeneracy.sigma_neg` (`ND/GoodAxes/Induction.lean:35`); `SecularSpectrum.definite` (`SS/Definiteness.lean:169`) | FAITHFUL | Holds for `n≥2`, positive physical data and ordered positive axes, exactly the contract. |
| `D` (discriminant) | `discriminant` (`SS/GoodPolynomial.lean:37`) | FAITHFUL | Literal product of squared differences over `j<l`. |
| `K₄` | `k4` (`SS/GoodPolynomial.lean:34`) | FAITHFUL | All signed integer vectors of nonzero `ℓ¹` size at most four. |
| `NR₄` | `nr4` (`SS/GoodPolynomial.lean:35`) | FAITHFUL | Injective eigenvalue vector and no zero integer dot product for `k∈K₄`. |
| `Φ₄` | `good` (`SS/GoodPolynomial.lean:47`) | FAITHFUL | Discriminant times all mode and permutation factors. Finiteness is proved in `k4_finite`, not assumed. |
| `U_n` | `simpleAxes` (`SS/GoodPolynomial.lean:50`) | FAITHFUL | Exactly `axes ∩ {discriminant(sigma)≠0}`. |
| `G_n` | `goodAxes` (`SS/GoodPolynomial.lean:49`) | FAITHFUL | Exactly `axes ∩ {good(sigma)≠0}`. |
| Both sets open; `G_n⊆U_n` | `isOpen_simpleAxes`, `isOpen_goodAxes`, `goodAxes_subset_simpleAxes` (`ND/GoodAxesNodes.lean:56,89,85`) | FAITHFUL | Named unconditional-in-data exports, with `n≥2` only where required. The handoff's prior missing-openness concern is resolved. |
| Euclidean vector length, Pi max norm | `length2` (`SS/Norms.lean:31`) and standard Pi norm; `norm_compare` (`:102`) | FAITHFUL | Euclidean length is an explicit function on `Fin n→ℝ`; comparisons keep the max norm separate. |
| Euclidean operator / Frobenius norm and inequality | `op2`, `frobenius`, `norm_compare` (`SS/Norms.lean:32,33,102`) | FAITHFUL-WITH-NOTE | `op2` is supremum over the Euclidean unit sphere; boundedness is proved (`op2_bddAbove :81`). Zero-dimensional empty sphere uses real supremum zero, the correct zero-space operator norm; the node assumes `n≥2`. This is not the global elementwise matrix norm instance. |

### Part 12 section data

Source: graph record at `DEPGRAPH.md:31652`; `p12-planar-assembly.tex:15-20`.

| Source object or property | Lean declaration (file:line) | Classification | Reason |
|---|---|---|---|
| Fixed physical data, `κ=Gm₀` | `PlanarData`, `PlanarData.Valid`, `PlanarData.kappa` (`PT/Setting.lean:31,36,37`) | FAITHFUL | Only physical typing data and positivity. The tolerance `η>0` is a separate argument in `PA/Data.lean:84` and frozen `planarTwoPlanetKAM`, not an oscillator coordinate. |
| Increasing two-planet axes and index dictionary | `p11c_axes` (`PT/Setting.lean:38`) | FAITHFUL | Exact `0<a 0 ∧ a 0<a 1`; source printed planet indices 1,2 correspond to Lean 0,1. |
| `Λ_i^*` | `PlanarData.actions` (`PT/Setting.lean:39`) | FAITHFUL-WITH-NOTE | Literal mass-times-square-root formula; analytic/inverse interpretation uses `Valid` and positive axes. |
| `a_i(Λ)` | `PlanarData.axes` (`PT/Setting.lean:41`) | FAITHFUL-WITH-NOTE | Exact squared-action formula, no selected witness. |
| `Ph(4)=Ph(2+2)=Ph(2*2)` | `Phase` (`FD/Phase.lean:37`) | FAITHFUL | Definitional equality of dimensions; stdin probe proved it by `rfl`. |
| `(I,φ,p,q)=(Λ,λ,η,ξ)` | `assemble` (`FD/Assemble.lean:38`), `fast`, `slow` | FAITHFUL | Literal append order; stdin probe proved the complete assembled formula by `rfl`. |
| `Ψ=Ψ^(2)` on its chart domain | `poincareProd`, `poincareProdDom` (`PO/Product.lean:45,51`) | FAITHFUL-WITH-NOTE | Specialization `n=2`, masses `m` and strength `G*m₀`; a coordinate chart on the source domain. |
| Raw total chart outside that domain | `poincareProd` via `poincareF` and `keplerLong` | NOT FAITHFUL under whole-carrier/no-fallback criterion | Underlying total solver has zero fallback; physical chart interpretation must retain the domain. No such extension is supplied by the source. |
| `Γ_i(w)` | `secularGamma` (`FD/SecularGamma.lean:35`) | FAITHFUL | Exact frozen oscillator action of `(slow w.2,slow w.1)`; equality checked by `rfl`. |
| Oscillator variable `(x,y)=(q,p)` | `p11cL_slow` (`PT/Lift/Defs.lean:54`) | FAITHFUL | Exact pair of slow position and momentum blocks, checked against `(slow w.1,slow w.2)` by `rfl`. |
| `R_j` | `oscillatorAction` (`FD/OscillatorAction.lean:37`) | FAITHFUL | Exact half-sum of squares. Argument swap between `(p,q)` and `(x,y)` does not change the value. |
| Euclidean oscillator length `|z|₂` | `p11c_slowLength` (`PT/Setting.lean:51`) | FAITHFUL | Literal square root of sum of both blocks' coordinate squares on all `Phase 2`. |
| Cylinder `C(V,r)` | `cylinder` (`FD/Cylinder.lean:41`) | FAITHFUL-WITH-NOTE | Exact fast-action membership and product of strict slow discs. Source uses `r>0`; raw formula itself is polynomial in `r²`. |
| Asserted `|z|₂²<2r²` on `C(V,r)` | No named public export; local `hsq` (`PT/FrozenBridge.lean:46-52`); private `slowLength_lt` (`PA/Data.lean:65`) | MISSING | The local estimate contains exactly the needed sum-of-two-disc argument. It is inside a different theorem and cannot be cited as a public declaration. The private lemma has a different conclusion and extra radii. The planned GAP-PX `cylnorm` is absent from this checkout. |

## Definition classification and import hygiene

There is no new `def`, `abbrev`, `structure`, theorem, provider or seal body in `git diff inp...HEAD`.
The per-object tables classify all candidate definitions relevant to these nodes:

- Coordinate/index maps, rotations, polynomial actions, tubes and finite products are direct formulas.
- Physical data structures are standing data, not assumed KAM conclusions.
- `KamHyp` is source-hypothesis infrastructure. `PsiSteps` is a conditional output interface, not a source-premise
  replacement: `iterative_steps` (`TS/LimitMapPsi.lean:79`) obtains it from the actual iterative result.
- `realFreq`/`psiR` are explicit real-part adapters; their unprojected interpretation requires the recorded reality facts.
- `wsum`/`wnorm` are raw partial-mathematical operations totalized by Lean. `WBound` retains the necessary guards.
- The Kepler solver uses classical selection of a **unique** solution on the valid elliptic domain and literal zero
  outside. Uniqueness prevents arbitrary valid-domain behavior; it does not erase the off-domain fallback.
- Source formulas involving square roots and divisions are identified with their physical domains; no global
  inverse/diffeomorphism assertion is made about negative actions or zero radii.

A recursive local-import scan of the six checked root modules found **416 KAM modules**, **zero provider
imports**, and **zero frozen theorem imports**. Frozen definitions are permitted. Thus none of these checked
roots imports a DRAFT_SORRY anchor. The separately read frozen headlines are context only, not imports of the
probe. The protected-path diff is empty. No claim is made to re-audit the existing sealed headline proofs.

## Independent verification

All Lean/Lake operations were serial, at default heartbeats, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No source repairs, generated-root regeneration, clean, package-cache operation or state-changing git command
was run. Builds used the prescribed compile gate.

### Diff and build

Commands:

```sh
git rev-parse HEAD inp
git diff inp...HEAD
git diff --exit-code inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Output: both revisions are `4d8a6848e381c8baaa9072e8d9867e3fc7a36f2a`; both diffs empty, exit 0.

The initial target list included the survey's planned
`KAM.Planetary.PlanarAssembly.FastInverseNodes`. That invocation exited 1 with:

```text
error: no such file or directory (error code: 2)
  file: /root/code/KAM-inp-defaud2/KAM/Planetary/PlanarAssembly/FastInverseNodes.lean
Some required targets logged failures:
- KAM.Planetary.PlanarAssembly.FastInverseNodes
error: build failed
```

The initial command mistakenly treated a planned survey module as an existing target; the failure established its absence and was not a Lean elaboration failure. After checking the actual file
inventory, the completed targeted build was:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-defaud2 \
  KAM.Planetary.TwoScale.LimitMapLip KAM.Kepler.DelaunaySymplectic \
  KAM.Planetary.Poincare.Product KAM.Planetary.Nondegeneracy.GoodAxesNodes \
  KAM.Planetary.Nondegeneracy.Frequency KAM.Planetary.PlanarAssembly.Data
```

Output excerpts:

```text
[inp-gate] slot 1 acquired 03:02:52 for [the six modules above]
Build completed successfully (9462 jobs).
```

Exit 0. Replayed existing warnings concern unused variables/simp arguments, deprecated names and style;
no heartbeat or elaboration failure occurred in the completed target list. “Jobs” is Lake's reported build
job count, not a claim of simultaneous running Lean processes.

### Axiom and coordinate probes

Command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean --stdin`, importing exactly the six build roots above.
For each of these fully qualified declarations, executed `#print axioms <name>`:

```text
KAM.Planetary.conv_data
KAM.Planetary.block_bridge
KAM.Planetary.mem_realTube_iff
KAM.Planetary.sc_unsc
KAM.Planetary.unsc_sc
KAM.Planetary.limitmap_data_eq_norm_sc
KAM.Planetary.PsiSteps.psi_lip_step
KAM.Kepler.delaunay_symplectic
KAM.Kepler.keplerLong_unique
KAM.Planetary.poincare_facts
KAM.Planetary.poincareProd_eq_ofPlanets
KAM.Planetary.Nondegeneracy.action_diffeomorphism
KAM.Planetary.Nondegeneracy.isOpen_simpleAxes
KAM.Planetary.Nondegeneracy.isOpen_goodAxes
KAM.Planetary.Nondegeneracy.goodAxes_subset_simpleAxes
KAM.Planetary.Nondegeneracy.nu_action_eq
KAM.Planetary.SecularSpectrum.norm_compare
KAM.Planetary.SecularSpectrum.definite
KAM.Planetary.Nondegeneracy.sigma_neg
KAM.Planetary.PlanarAssembly.pg_hypotheses
KAM.Planetary.freq_realInclusion_eq
KAM.Planetary.dp_nbhd_subset
KAM.Planetary.actionNbhd_mono
KAM.Planetary.wbound_mono_set
KAM.Planetary.norm_coeff_zero_le
KAM.Weighted.WBound.mono
KAM.Weighted.wbound_iff
KAM.Weighted.sup_le_wbound
```

For **each** name the exact output format was:
`'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`.
No additional axiom appeared. The following probes in the same stdin invocation also elaborated:

```lean
open KAM KAM.Planetary
example (I phi p q : Fin 2 → ℝ) :
    assemble I phi p q = (Fin.append phi q, Fin.append I p) := rfl
example (w : Phase (2+2)) :
    secularGamma w = oscillatorAction (slow w.2) (slow w.1) := rfl
example (w : Phase (2+2)) : p11cL_slow w = (slow w.1, slow w.2) := rfl
example : Phase (2+2) = Phase (2*2) := rfl
example : KAM.Kepler.keplerLong 1 ![(1 : ℝ), 0] = 0 := by
  simp [KAM.Kepler.keplerLong, planeLength, planeSq, Fin.sum_univ_two]
```

Final stdin probe exit 0, no errors or warnings. An earlier probe used the unqualified namespace
`KAM.Planetary.psi_lip_step` and exited 1 for that unknown constant; the actual declaration is in namespace
`KAM.Planetary.PsiSteps`, as verified in the successful repeat. No Lean source was changed to repair it.

Supplementary stdin probe (after replay) confirmed `Matrix.linfty_opNorm_toMatrix`,
`dp_nbhd_subset`, `ball_subset_actionNbhd`, `sorted_monotone`, and
`sorted_eq_eigenvalues_comp` with `#check`. It printed:

```text
Matrix.linfty_opNorm_toMatrix ... (f : (n → α) →L[α] m → α) :
  ‖LinearMap.toMatrix' ↑f‖ = ‖f‖
'Matrix.linfty_opNorm_toMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0. The matrix row-sum formula is also supplied by `Matrix.linfty_opNorm_def`;
its separate stdin check (exit 0) printed:

```text
Matrix.linfty_opNorm_def ... (A : Matrix m n α) :
  ‖A‖ = ↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊)
'Matrix.linfty_opNorm_def' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Lint, frozen guard and ABI

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
check_lean_modules: PASS (1218 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Exit 0. No generated-root exception was needed. Global lint found no forbidden proof escapes, resource
budget overrides, oversized Lean files, module violations or protected frozen drift.
The directly inspected definition modules range from 62 to 474 lines; all are below 1500.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Planetary.TwoScale.LimitMapLip KAM.Kepler.DelaunaySymplectic \
  KAM.Planetary.Poincare.Product KAM.Planetary.Nondegeneracy.GoodAxesNodes \
  KAM.Planetary.Nondegeneracy.Frequency KAM.Planetary.PlanarAssembly.Data
```

Exact output:

```text
replaying KAM.Planetary.PlanarAssembly.Data
replaying KAM.Planetary.Nondegeneracy.Frequency
replaying KAM.Planetary.Nondegeneracy.GoodAxesNodes
replaying KAM.Planetary.Poincare.Product
replaying KAM.Kepler.DelaunaySymplectic
replaying KAM.Planetary.TwoScale.LimitMapLip
```

Exit 0. One invocation covered all six roots.

## Suspected defects, deviations and remaining uncertainty

1. **Handoff / checkout mismatch:** handoff final node says the cylinder-norm property “is exported by cylnorm,
   GAP-PX”. No such named export exists in this snapshot; `GAP-PLAN-P2.md` describes it as planned. Local
   `hsq` in `PT/FrozenBridge.lean:46` is real evidence of the calculation but not a public export.
2. **Whole-carrier versus source-domain contract:** `WD/Norm.lean:54` explicitly documents “junk `0` if not
   summable”, and `KE/Equation.lean:116` documents “junk `0` when `ℓ v ≥ 1`”. These are deliberate existing
   Lean totalizations. They contradict an unrestricted claim that the raw definitions have no off-source
   behavior. The guarded interfaces/domain-restricted identities remain valid. No frozen statement was
   silently weakened, no guard removed, and no replacement totalization introduced.
3. **Unexported notation / elementary property:** `Gcheck`, a general `L_*`, and positive-dilation closure of
   `axes` are not individually named by the candidate references. The missing declarations are an export/coverage
   issue; no mathematical counterexample to those source formulas is asserted.
4. **No newly established pinned-PDF erratum.** This audit compares local exact blueprint formulas and Lean;
   it does not claim an independent new PDF transcription check. The existing P3 weighted-norm deviation
   (`p3a-two-scale-iteration.tex:25-26`: track-N supremum-of-sums instead of CP10's sum-of-suprema) is explicit
   and was retained, not silently repaired. Track-I Delaunay sign conventions agree after reversing both forms.
5. **No implementation deviations introduced.** The only audit missteps were the planned absent build target
   and the initially incomplete namespace in the probe, both reported above and followed by successful checks
   on existing modules. Remaining closure gaps are exactly those in the node table; build success, axiom
   hygiene and kernel replay do not discharge them.

## Report validation

The exact requested absolute report path exists. All six node IDs occur in the verdict table; all six
source-object tables are present. `git diff --check` and the report-only whitespace check passed.
Final tracked-source diff is empty; `git status --short` lists only this report and the pre-existing
untracked handoff.
