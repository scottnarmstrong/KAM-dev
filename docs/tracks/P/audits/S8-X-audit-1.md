# S8-X independent package audit 1

**Verdict: PASS WITH NOTES for the S8-X internal helper package.** No signed declaration or frozen anchor belongs to S8-X; no seal-readiness or closure of `quadratic_form` is claimed. The literal cross-Hessian computation is sound and usable as the S8-Q proof cut specified by the design. The notes below concern hygiene and evidence, not an extra mathematical premise.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-s8x`. Report destination follows the user's explicit override of the generic brief's main-worktree destination.

## Scope, authority, and frozen-v1 inputs

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff's AUDIT FOCUS, track-P statement, pinned blueprint Part 8 and the relevant Part 7 chart/Kepler statements, and design rows S8-X/S8-Q. Tier-2 focused source/proof audit. Permission envelope: read-only code/source inspection; prescribed targeted validation; scratch only under `.lake/abi-scratch/`; this report is the only repository edit. No git mutation, source repairs, network access, delegation, generated-root regeneration, or frozen-file edits.

- HEAD: `0a5d9f1ed4896fe439fd6cb914bdf85a3d6c73b7`.
- `inp` at inspection: `312ad165a54f89ca92b3f6ae004d60658180bfce`.
- Merge base for `git diff inp...HEAD`: `81bb576d2ebe1ee5c4cb309059b68d4b24148218`.
- Compared the requested three-dot diff. It contains seven new CrossJet files plus twelve changed files outside CrossJet. Only the seven CrossJet files are audited, per AUDIT FOCUS; unrelated changes receive no verdict here.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (exit 0).
- Pre-existing untracked `docs/tracks/P/audits/S8-X-handoff.md` was read and left unchanged.

All line locators below refer to this frozen-v1 commit plus these SHA256 hashes (the handoff was untracked):

| File | SHA256 |
|---|---|
| `KAM/Planetary/SecularForm/CrossJet.lean` | `5b0abdda1f3cafe036fe84844aab78a75a8b72804fb9c25d60ed5509b326c14b` |
| `KAM/Planetary/SecularForm/CrossJet/MixedKernel.lean` | `2507da098fb4acd56407662a2ace4f82ab443c740aff5035e3e22ed9d77983ce` |
| `KAM/Planetary/SecularForm/CrossJet/PairAverage.lean` | `a447cdeb83dc86e01a3fdb93d37466a585c70abb1072c151dc9969fb05a40490` |
| `KAM/Planetary/SecularForm/CrossJet/PairIntegrand.lean` | `2b51ddd8e1d044818eec39ee7577d78572dde1460c70a9e7e5c39041988323bd` |
| `KAM/Planetary/SecularForm/CrossJet/Parametric.lean` | `f6047cd428885a112494aa2499b1346ee228442c9d1d7903ff070f85e3bd71d9` |
| `KAM/Planetary/SecularForm/CrossJet/Selection.lean` | `d922747492a4e41b688b7acad1d8964b9c45dbe81b7bbeb165343fbfb958ab91` |
| `KAM/Planetary/SecularForm/CrossJet/Variation.lean` | `b36369b5d791267ad5eeab0c9ca9696b5e0fc0486a81e097a993b18a21ce4af3` |
| `blueprint-P/parts/p8-secular-form.tex` | `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc` |
| `blueprint-P/parts/p7-kepler-poincare.tex` | `3a10ddf74067a3c7b54184a190710deaba3019c97d2e0d5e9a3773b889cc26ab` |
| `docs/tracks/P/design/P810-LEAN-DESIGN.md` | `f555e21a468123ce906f6818359cb8faaffc5d0435ea0f70c65967cec38722c4` |
| `docs/campaign/OVERNIGHT.md` | `731959fced1dc5edb101949fe7a6f8a6ea41c1d5d6a2385e8df1d8940c69eb33` |
| `docs/tracks/P/statement.md` | `06d876320d40f7ae0cb5cdbe7e5b08a00b431125630079a2b3d3abcaac2e0b66` |
| `docs/tracks/P/audits/S8-X-handoff.md` | `b9f93cb46eacbc8084c89b4e9a467348127302e07d759817e1adbbf515fe6478` |
| `KAM/Planetary/SecularForm/Basic.lean` | `320b40faa3dff8d572d5cd18849b17b96e85fab69a3d85e1a0bff01acc380e47` |
| `KAM/Planetary/SecularForm/Coefficients.lean` | `020f705f29aade61727b94073ae30d6e9cf97b8ce450e1559d9f4fc6d72e0cda` |
| `KAM/Planetary/SecularForm/LaplaceCoeff.lean` | `5952590c940e5a48d4275e1b404b7eed7530273592b1e32fcab8484ba461873e` |

## Source contract and refutation pass

Part 8 L17–21 fixes positive masses, `kappa=G*m0`, radian angles of period `2*pi`, `Gamma=|u|²/2`, and `a=Lambda²/(m²*kappa)`. The frozen `assemble` places `(phi,q;I,p)` in that order, hence the slow slice used here is xi with eta=0. `planeLength` is the physical sqrt of the sum of coordinate squares, despite the ambient Pi sup norm. `Basic.lean:74–81` defines the actual pair interaction average with exactly two normalized angle integrals, not an arbitrary coefficient function.

The decisive source text is Part 8 L166–168, `stepP:p8:qf-cross`: “Let i<j”, “r_i'=-a_i cos lambda_i”, “theta_i'=2 sin lambda_i”, and “B_ij=...=2 mathfrak b_ij/sqrt(Lambda_i Lambda_j)”. The coefficient definitions at L144–150 and `Coefficients.lean:34–45` give the off-diagonal entry `G*m_i*m_j*a_i/(4*a_j²) * b_(3/2)^(2)(a_i/a_j) / (sqrt(Lambda_i)*sqrt(Lambda_j))`. Thus the mixed Hessian must be twice this entry. There is no mass-dependent separation, factor-four hypothesis, arbitrary quadratic matrix, numerical ratio, or unproved coefficient structure in the exported identity.

Adversarial checks were performed as a separate second reading of statements and applications:

1. **Orbit sign and scale.** Part 7 L99–111 and L119–128 give `F_xi=sin(lambda)/sqrt(Lambda)` at zero. Differentiating the literal position formula gives `(a/sqrt(Lambda))*(-1-sin²(lambda),sin(lambda)cos(lambda))`. Its radial/tangential components are `-a*cos(lambda)` and `2*a*sin(lambda)` before the common inverse square root; they match the source.
2. **Mixed-kernel sign.** For `d=alpha-beta`, first differentiation in beta gives `-c*(d dot beta')/|d|³`; differentiation in alpha gives `c*(3(d dot alpha')(d dot beta')/|d|⁵ - alpha' dot beta'/|d|³)`. `MixedKernel` has exactly these signs and factors. Its generic smoothness/derivative premises are supplied by actual chart derivatives in `PairAverage.lean:120–146`.
3. **Integral and derivative totalization.** Noncollision follows for every pair of angles from distinct positive circle radii. `pairDom` is open, both chart blocks are admissible, and the compact cell at zero lies in it. `e_diff_slice` constructs one positive common tube radius; it does not assume one. Continuity supplies integrability before every Fubini/interchange/application of a continuous multilinear map. The eventual equality to the literal pair average is on this neighbourhood, so a default Bochner integral or default `fderiv` value cannot supply the result.
4. **Fourier selection and boundary terms.** The change `t=s-theta` uses second-angle periodicity and a proved Fubini step. `crossU_diag` is an exact algebraic identity; integrating cos²/sin² leaves `pi*(A+C)`. If `r²=a²+b²-2ab cos(theta)`, `fbar_eq` reduces the remainder to three times `[3ab sin²(theta)cos(theta)/r⁵-cos(2theta)/r³]`. This integrates to zero by integration by parts with `u=sin(theta)cos(theta)`, `v=r^-3`; both endpoint products vanish. Thus the average is `b_(3/2)^(2)(a/b)/(2*b³)` with the source's `(2*pi)^-1` Laplace convention, not twice that value.
5. **Consumer normalization.** Multiplication by `G*m_i*m_j*(a_i/sqrt(Lambda_i))*(a_j/sqrt(Lambda_j))` gives `G*m_i*m_j*a_i/(2*a_j²*sqrt(Lambda_i)*sqrt(Lambda_j))*b`, exactly `2*coeffs`. A compiled term-level probe expands this coefficient completely. Symmetry plus S8-W can supply the eta/xi-eta blocks as the design intends. This audit does not assert that the S8-Q assembly, remainder bound, or its producer-to-consumer proof has already been completed.

No mathematical defect survived these challenges. This was a single independent auditor with two passes; no separate-agent review is claimed.

## Declaration ledger

All names below have prefix `KAM.Planetary.SecularForm.`. Node shorthand: **X** = `stepP:p8:qf-cross` (p8 L166–168); **E** = `bpP:p8:e-diff` (p8 L27); **C** = `stepP:p8:pa-circ` and `pa-unif` (p8 L48–49); **K** = `bpP:p7:regular-kepler` and `poincare-def` (p7 L99–128). Every public theorem and definition is listed, including auxiliary algebra/calculus declarations. These are internal helpers in the campaign sense, even though exported through public Lean modules.

| Node | Declaration and location | Verdict | Reason / note |
|---|---|---|---|
| X | `crossKernel_smul` — `CrossJet.lean:34` | PASS | Bilinear scaling proved by unfolding; no positivity premises. |
| X | `cross_hessian` — `CrossJet.lean:43` | PASS | Literal pair-average mixed Hessian = 2 coeffs; only ordered positive axes and standing Data. |
| X | `crossKernel` — `MixedKernel.lean:29` | PASS | Explicit rational mixed-potential Hessian formula, defined algebraically on all vectors; derivative use proves d≠0. |
| X | `planeLength_eq_sqrt` — `MixedKernel.lean:33` | PASS | Physical plane length, not the Pi sup norm. |
| X | `hasDerivAt_pair_t` — `MixedKernel.lean:37` | PASS | Generic first t derivative; differentiable curve and noncollision are explicit calculus inputs. |
| X | `hasDerivAt_pair_s` — `MixedKernel.lean:68` | PASS | Generic s derivative of the preceding expression; correct positive mixed-kernel sign. |
| X | `iteratedFDeriv_two_mixed` — `MixedKernel.lean:100` | PASS | Generic calculus identity; hf identifies f literally, hC supplies C². Both are proved at the application. |
| C/X | `poincare_circle_fst` — `PairAverage.lean:31` | PASS | Circular position a(cos l,sin l), directly from the chart. |
| C/X | `circle_sub_ne` — `PairAverage.lean:36` | PASS | Distinct positive radii preclude coincidence for every pair of angles. |
| C/X | `slice_mem_pairDom` — `PairAverage.lean:49` | PASS | Zero slow slice lies in the chart and is collision-free; no assumed tube estimate. |
| X | `crossKernel_const_mul` — `PairAverage.lean:60` | PASS | Scalar linearity; algebra only. |
| X | `uvec` — `PairAverage.lean:65` | PASS | Explicit first-variation vector (-1-sin²(l),sin(l)cos(l)). |
| X | `cvec` — `PairAverage.lean:67` | PASS | Explicit circular unit vector (cos(l),sin(l)). |
| X | `pairSlowSecular_mixed_jet` — `PairAverage.lean:69` | PASS | Literal average differentiated twice; positivity and ordered axes suffice for the uniform tube. |
| X | `sliceBlock` — `PairIntegrand.lean:28` | PASS | Literal assembly ((lambda_k,xi_k),(I,0)); global affine map. |
| X | `contDiff_sliceBlock` — `PairIntegrand.lean:31` | PASS | Linear/constant coordinate assembly, valid globally. |
| C/X | `pairIntegrand` — `PairIntegrand.lean:45` | PASS | Literal -c/planeLength(q1-q2) of the two chart positions; analytic claims restricted to pairDom. |
| C/X | `pairDom` — `PairIntegrand.lean:49` | PASS | Literal intersection of both chart domains and q1-q2≠0; no conclusion or coefficient field. |
| C/X | `isOpen_pairDom` — `PairIntegrand.lean:53` | PASS | Open chart preimages intersect the noncollision locus. |
| C/X | `contDiffOn_pairIntegrand` — `PairIntegrand.lean:72` | PASS | Smooth reciprocal physical distance on the actual chart/noncollision domain. |
| E/X | `iteratedFDeriv_slice` — `Parametric.lean:27` | PASS | Partial derivative restriction through inr; all orders j≤2 including 0. |
| E/X | `e_diff_slice` — `Parametric.lean:49` | PASS | C² neighbourhood of compact cell×{0} produces a positive common radius and integral identity. |
| E/X | `cell_two_eq` — `Parametric.lean:94` | PASS | Exact product-cell identification; no measure normalization introduced. |
| E/X | `integral_cell_two` — `Parametric.lean:101` | PASS | Measure-preserving piFinTwo and Fubini; continuity supplies integrability. |
| X | `sep2` — `Selection.lean:32` | PASS | Explicit squared separation a²+b²-2ab cos(theta). |
| X | `sep2_pos` — `Selection.lean:34` | PASS | Positive inner radius and strict ordering give separation for every angle. |
| X | `continuous_sep2` — `Selection.lean:38` | PASS | Unconditional polynomial/trigonometric continuity. |
| X | `hasDerivAt_sep2_inv_cube` — `Selection.lean:41` | PASS | Correct derivative -3ab sin(theta)/r^5 on separated radii. |
| X | `ibp_selection` — `Selection.lean:57` | PASS | Periodic boundary term vanishes; integral of 3ab sin²(theta)cos(theta)/r^5 equals cos(2theta)/r^3 integral. |
| X | `torus_reduce` — `Selection.lean:97` | PASS | Periodicity removes the shifted interval, then justified Fubini swaps s and theta. |
| X | `cN20` — `Selection.lean:126` | PASS | Polynomial coefficient of cos²(s) in the product of separation/variation dot products. |
| X | `cN11` — `Selection.lean:128` | PASS | Polynomial coefficient of cos(s)sin(s) in that product. |
| X | `cN02` — `Selection.lean:130` | PASS | Polynomial coefficient of sin²(s) in that product. |
| X | `cM20` — `Selection.lean:131` | PASS | Polynomial coefficient of cos²(s) in the variation dot product. |
| X | `cM11` — `Selection.lean:132` | PASS | Polynomial coefficient of cos(s)sin(s) in the variation dot product. |
| X | `cM02` — `Selection.lean:133` | PASS | Polynomial coefficient of sin²(s) in the variation dot product. |
| X | `crossU` — `Selection.lean:136` | PASS | Literal crossKernel 1 at a*cvec(s)-b*cvec(t) and the two uvec variations. |
| X | `crossU_diag` — `Selection.lean:139` | PASS | Exact quadratic expression in cos(s),sin(s); all polynomial coefficients checked against crossKernel. |
| X | `quad_integral` — `Selection.lean:183` | PASS | cos² and sin² integrals equal pi; mixed integral vanishes. |
| X | `avg_cross_diag` — `Selection.lean:205` | PASS | Integrates the exact diagonal identity; no positivity needed for this algebraic identity. |
| X | `fbar_eq` — `Selection.lean:222` | PASS | Pointwise identity separating the target mode and a term with zero period integral. |
| X | `planeLength_circ` — `Selection.lean:246` | PASS | Exact squared-distance trigonometric identity under sqrt. |
| X | `continuous_crossU` — `Selection.lean:256` | PASS | Separation proves nonzero denominators globally in both angles. |
| X | `crossU_periodic` — `Selection.lean:279` | PASS | Period 2pi in the second angle for every fixed first angle. |
| X | `sep2_eq_mul` — `Selection.lean:284` | PASS | Factors b² and the ratio a/b; b>0 is sufficient. |
| X | `inv_cube_sep2` — `Selection.lean:288` | PASS | Real-power conversion with positive b and positive radicand; no absolute-value sign loss. |
| X | `integral_cos_two_inv_cube` — `Selection.lean:304` | PASS | Literal laplace_def with (2pi)^-1 normalization, k=2, s=3/2. |
| X | `cross_double_average` — `Selection.lean:317` | PASS | Normalized double average = laplace_def(3/2,2,a/b)/(2b³), proved by exact integration. |
| X/K | `lineC` — `Variation.lean:26` | PASS | Literal chart prefactor sqrt((1-s²/(4Λ))/Λ). Inherits real sqrt/division totalization; differentiation only at Λ>0. |
| X/K | `poincare_line_fst` — `Variation.lean:29` | PASS | Global algebraic unfolding along xi=s, eta=0; no new chart semantics. |
| X/K | `hasDerivAt_lineC` — `Variation.lean:42` | PASS | Stationary prefactor at zero for positive action. |
| X/K | `lineC_zero` — `Variation.lean:53` | PASS | Exact prefactor value, even as a total real-sqrt identity. |
| X/K | `hasDerivAt_keplerLong_line` — `Variation.lean:57` | PASS | Implicit-equation derivative gives sin(l)/sqrt(action). |
| X/K | `hasDerivAt_poincare_fst_xi` — `Variation.lean:83` | PASS | Position variation (a/sqrt(action))(-1-sin²(l),sin(l)cos(l)); stronger in arbitrary m,kappa. |

## Definition classification

There are **15 new definitions, 39 public theorems, and no new abbrev/structure** in scope. All definitions in the ledger are literal formula/domain/coordinate abbreviations, not characterization-by-choice objects. `cN*`/`cM*` are algebraic scratch coefficients whose exact relationship to the kernel is proved by `crossU_diag`; they do not assume the intended quadratic form. No definition uses `Classical.choose`, an if/dite fallback, a result bundle, or a purported source object with deferred characterization.

For each of the 15 definitions: **BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS.** Real sqrt/division and the imported chart are total Lean operations; the physical derivative/analytic uses prove positive action and noncollision. Pure global algebra identities also hold for their total definitions off the physical domain and do not introduce physical claims there.

## Expanded binder audit

The following table records each external binder separately, in declaration order (braces mean implicit). Numeric/vector/function/set parameters are TYPING; logical inputs are SOURCE or STANDING. Generic calculus helpers have their own abstract source contract (chain rule / E), and are not offered as unconditional physical results. `iteratedFDeriv_two_mixed`'s `hC`, `hf`, `hα`, `hβ`, `hne` and `e_diff_slice`'s neighbourhood hypotheses are discharged inside the physical computation. Thus none leaks into `cross_hessian` or the signed `quadratic_form`.

For `D : Data n` we expand the record below: its data fields are typing and its positivity fields are precisely the standing p8 convention. `ha` expands to positivity and strict ordering. There are no instance binders or hidden assumption bundles beyond those recorded. Quantifiers inside a logical binder retain the source scope shown, e.g. `D.hm` is universal over all indices, and the tube radius is produced before all angles/nearby slow points.

| Theorem | Binder / expanded field | Type / meaning | Bin | Source |
|---|---|---|---|---|
| `crossKernel_smul` | `c` | `ℝ` | TYPING | X |
| `crossKernel_smul` | `p` | `ℝ` | TYPING | X |
| `crossKernel_smul` | `q` | `ℝ` | TYPING | X |
| `crossKernel_smul` | `d` | `Fin 2 → ℝ` | TYPING | X |
| `crossKernel_smul` | `x` | `Fin 2 → ℝ` | TYPING | X |
| `crossKernel_smul` | `z` | `Fin 2 → ℝ` | TYPING | X |
| `cross_hessian` | `{n}` | `ℕ` | TYPING | p8 L17 |
| `cross_hessian` | `D.G` | `ℝ` | TYPING | p8 L17; Basic:38–45 |
| `cross_hessian` | `D.m0` | `ℝ` | TYPING | p8 L17; Basic:38–45 |
| `cross_hessian` | `D.m` | `Fin n → ℝ` | TYPING | p8 L17; Basic:38–45 |
| `cross_hessian` | `D.hG` | `0 < D.G` | STANDING | p8 L17; Basic:38–45 |
| `cross_hessian` | `D.hm0` | `0 < D.m0` | STANDING | p8 L17; Basic:38–45 |
| `cross_hessian` | `D.hm` | `∀ i, 0 < D.m i` | STANDING | p8 L17; Basic:38–45 |
| `cross_hessian` | `D.hn` | `0 < n` | STANDING | p8 L17; Basic:38–45 |
| `cross_hessian` | `{a}` | `Vec n` | TYPING | X |
| `cross_hessian` | `ha.1` | `∀ i, 0 < a i` | STANDING | p8 L21; Basic:47 |
| `cross_hessian` | `ha.2` | `StrictMono a` | STANDING | p8 L21; Basic:47 |
| `cross_hessian` | `{i}` | `Fin n` | TYPING | X |
| `cross_hessian` | `{j}` | `Fin n` | TYPING | X |
| `cross_hessian` | `hij` | `i < j` | SOURCE | X, “Let i<j” (p8 L166) |
| `planeLength_eq_sqrt` | `d` | `Fin 2 → ℝ` | TYPING | X |
| `hasDerivAt_pair_t` | `c` | `ℝ` | TYPING | X |
| `hasDerivAt_pair_t` | `a` | `Fin 2 → ℝ` | TYPING | X |
| `hasDerivAt_pair_t` | `{β}` | `ℝ → Fin 2 → ℝ` | TYPING | X |
| `hasDerivAt_pair_t` | `{β'}` | `Fin 2 → ℝ` | TYPING | X |
| `hasDerivAt_pair_t` | `hβ` | `HasDerivAt β β' 0` | SOURCE | X (generic chain-rule contract) |
| `hasDerivAt_pair_t` | `hne` | `a - β 0 ≠ 0` | SOURCE | X (generic chain-rule contract) |
| `hasDerivAt_pair_s` | `c` | `ℝ` | TYPING | X |
| `hasDerivAt_pair_s` | `{α}` | `ℝ → Fin 2 → ℝ` | TYPING | X |
| `hasDerivAt_pair_s` | `{α'}` | `Fin 2 → ℝ` | TYPING | X |
| `hasDerivAt_pair_s` | `b` | `Fin 2 → ℝ` | TYPING | X |
| `hasDerivAt_pair_s` | `β'` | `Fin 2 → ℝ` | TYPING | X |
| `hasDerivAt_pair_s` | `hα` | `HasDerivAt α α' 0` | SOURCE | X (generic chain-rule contract) |
| `hasDerivAt_pair_s` | `hne` | `α 0 - b ≠ 0` | SOURCE | X (generic chain-rule contract) |
| `iteratedFDeriv_two_mixed` | `c` | `ℝ` | TYPING | X |
| `iteratedFDeriv_two_mixed` | `{α}` | `ℝ → Fin 2 → ℝ` | TYPING | X |
| `iteratedFDeriv_two_mixed` | `{β}` | `ℝ → Fin 2 → ℝ` | TYPING | X |
| `iteratedFDeriv_two_mixed` | `{α'}` | `Fin 2 → ℝ` | TYPING | X |
| `iteratedFDeriv_two_mixed` | `{β'}` | `Fin 2 → ℝ` | TYPING | X |
| `iteratedFDeriv_two_mixed` | `hα` | `HasDerivAt α α' 0` | SOURCE | X (generic chain-rule contract) |
| `iteratedFDeriv_two_mixed` | `hβ` | `HasDerivAt β β' 0` | SOURCE | X (generic chain-rule contract) |
| `iteratedFDeriv_two_mixed` | `hne` | `α 0 - β 0 ≠ 0` | SOURCE | X (generic chain-rule contract) |
| `iteratedFDeriv_two_mixed` | `{f}` | `Vec 2 → ℝ` | TYPING | X |
| `iteratedFDeriv_two_mixed` | `hf` | `∀ y, f y = -c / planeLength (α (y 0) - β (y 1))` | SOURCE | X (generic chain-rule contract) |
| `iteratedFDeriv_two_mixed` | `hC` | `ContDiffAt ℝ 2 f 0` | SOURCE | X (generic chain-rule contract) |
| `poincare_circle_fst` | `{m}` | `ℝ` | TYPING | X |
| `poincare_circle_fst` | `{κ}` | `ℝ` | TYPING | X |
| `poincare_circle_fst` | `{Λ}` | `ℝ` | TYPING | X |
| `poincare_circle_fst` | `hm` | `0 < m` | STANDING | p8 L17–21, X |
| `poincare_circle_fst` | `hκ` | `0 < κ` | STANDING | p8 L17–21, X |
| `poincare_circle_fst` | `hΛ` | `0 < Λ` | STANDING | p8 L17–21, X |
| `poincare_circle_fst` | `l` | `ℝ` | TYPING | X |
| `circle_sub_ne` | `{a₁}` | `ℝ` | TYPING | X |
| `circle_sub_ne` | `{a₂}` | `ℝ` | TYPING | X |
| `circle_sub_ne` | `h₁` | `0 < a₁` | STANDING | p8 L17–21, X |
| `circle_sub_ne` | `h` | `a₁ < a₂` | STANDING | p8 L17–21, X |
| `circle_sub_ne` | `x` | `ℝ` | TYPING | X |
| `circle_sub_ne` | `y` | `ℝ` | TYPING | X |
| `slice_mem_pairDom` | `{m₁}` | `ℝ` | TYPING | X |
| `slice_mem_pairDom` | `{m₂}` | `ℝ` | TYPING | X |
| `slice_mem_pairDom` | `{κ}` | `ℝ` | TYPING | X |
| `slice_mem_pairDom` | `{I₁}` | `ℝ` | TYPING | X |
| `slice_mem_pairDom` | `{I₂}` | `ℝ` | TYPING | X |
| `slice_mem_pairDom` | `hm₁` | `0 < m₁` | STANDING | p8 L17–21, X |
| `slice_mem_pairDom` | `hm₂` | `0 < m₂` | STANDING | p8 L17–21, X |
| `slice_mem_pairDom` | `hκ` | `0 < κ` | STANDING | p8 L17–21, X |
| `slice_mem_pairDom` | `hI₁` | `0 < I₁` | STANDING | p8 L17–21, X |
| `slice_mem_pairDom` | `hI₂` | `0 < I₂` | STANDING | p8 L17–21, X |
| `slice_mem_pairDom` | `hsep` | `I₁ ^ 2 / (m₁ ^ 2 * κ) < I₂ ^ 2 / (m₂ ^ 2 * κ)` | STANDING | p8 L17–21, X |
| `slice_mem_pairDom` | `t` | `Vec 2` | TYPING | X |
| `crossKernel_const_mul` | `k` | `ℝ` | TYPING | X |
| `crossKernel_const_mul` | `c` | `ℝ` | TYPING | X |
| `crossKernel_const_mul` | `d` | `Fin 2 → ℝ` | TYPING | X |
| `crossKernel_const_mul` | `x` | `Fin 2 → ℝ` | TYPING | X |
| `crossKernel_const_mul` | `z` | `Fin 2 → ℝ` | TYPING | X |
| `pairSlowSecular_mixed_jet` | `{n}` | `ℕ` | TYPING | p8 L17 |
| `pairSlowSecular_mixed_jet` | `D.G` | `ℝ` | TYPING | p8 L17; Basic:38–45 |
| `pairSlowSecular_mixed_jet` | `D.m0` | `ℝ` | TYPING | p8 L17; Basic:38–45 |
| `pairSlowSecular_mixed_jet` | `D.m` | `Fin n → ℝ` | TYPING | p8 L17; Basic:38–45 |
| `pairSlowSecular_mixed_jet` | `D.hG` | `0 < D.G` | STANDING | p8 L17; Basic:38–45 |
| `pairSlowSecular_mixed_jet` | `D.hm0` | `0 < D.m0` | STANDING | p8 L17; Basic:38–45 |
| `pairSlowSecular_mixed_jet` | `D.hm` | `∀ i, 0 < D.m i` | STANDING | p8 L17; Basic:38–45 |
| `pairSlowSecular_mixed_jet` | `D.hn` | `0 < n` | STANDING | p8 L17; Basic:38–45 |
| `pairSlowSecular_mixed_jet` | `i` | `Fin n` | TYPING | X |
| `pairSlowSecular_mixed_jet` | `j` | `Fin n` | TYPING | X |
| `pairSlowSecular_mixed_jet` | `{I}` | `ℝ` | TYPING | X |
| `pairSlowSecular_mixed_jet` | `{J}` | `ℝ` | TYPING | X |
| `pairSlowSecular_mixed_jet` | `hI` | `0 < I` | STANDING | p8 L17–21, X |
| `pairSlowSecular_mixed_jet` | `hJ` | `0 < J` | STANDING | p8 L17–21, X |
| `pairSlowSecular_mixed_jet` | `hsep` | `I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))` | STANDING | p8 L17–21, X |
| `contDiff_sliceBlock` | `I` | `ℝ` | TYPING | X |
| `contDiff_sliceBlock` | `k` | `Fin 2` | TYPING | X |
| `isOpen_pairDom` | `{m₁}` | `ℝ` | TYPING | X |
| `isOpen_pairDom` | `{m₂}` | `ℝ` | TYPING | X |
| `isOpen_pairDom` | `{κ}` | `ℝ` | TYPING | X |
| `isOpen_pairDom` | `{I₁}` | `ℝ` | TYPING | X |
| `isOpen_pairDom` | `{I₂}` | `ℝ` | TYPING | X |
| `isOpen_pairDom` | `hm₁` | `0 < m₁` | STANDING | p8 L17–21, X |
| `isOpen_pairDom` | `hm₂` | `0 < m₂` | STANDING | p8 L17–21, X |
| `isOpen_pairDom` | `hκ` | `0 < κ` | STANDING | p8 L17–21, X |
| `contDiffOn_pairIntegrand` | `{c}` | `ℝ` | TYPING | X |
| `contDiffOn_pairIntegrand` | `{m₁}` | `ℝ` | TYPING | X |
| `contDiffOn_pairIntegrand` | `{m₂}` | `ℝ` | TYPING | X |
| `contDiffOn_pairIntegrand` | `{κ}` | `ℝ` | TYPING | X |
| `contDiffOn_pairIntegrand` | `{I₁}` | `ℝ` | TYPING | X |
| `contDiffOn_pairIntegrand` | `{I₂}` | `ℝ` | TYPING | X |
| `contDiffOn_pairIntegrand` | `hm₁` | `0 < m₁` | STANDING | p8 L17–21, X |
| `contDiffOn_pairIntegrand` | `hm₂` | `0 < m₂` | STANDING | p8 L17–21, X |
| `contDiffOn_pairIntegrand` | `hκ` | `0 < κ` | STANDING | p8 L17–21, X |
| `iteratedFDeriv_slice` | `{W}` | `Set (Vec 2 × Vec 2)` | TYPING | E |
| `iteratedFDeriv_slice` | `hW` | `IsOpen W` | SOURCE | E (generic calculus contract) |
| `iteratedFDeriv_slice` | `{F}` | `Vec 2 × Vec 2 → ℝ` | TYPING | E |
| `iteratedFDeriv_slice` | `hF` | `ContDiffOn ℝ 2 F W` | SOURCE | E (generic calculus contract) |
| `iteratedFDeriv_slice` | `{t}` | `Vec 2` | TYPING | E |
| `iteratedFDeriv_slice` | `{y}` | `Vec 2` | TYPING | E |
| `iteratedFDeriv_slice` | `hty` | `(t, y) ∈ W` | SOURCE | E (generic calculus contract) |
| `iteratedFDeriv_slice` | `j` | `ℕ` | TYPING | E |
| `iteratedFDeriv_slice` | `hj` | `j ≤ 2` | SOURCE | E (generic calculus contract) |
| `e_diff_slice` | `{W}` | `Set (Vec 2 × Vec 2)` | TYPING | E |
| `e_diff_slice` | `hW` | `IsOpen W` | SOURCE | E (generic calculus contract) |
| `e_diff_slice` | `{F}` | `Vec 2 × Vec 2 → ℝ` | TYPING | E |
| `e_diff_slice` | `hF` | `ContDiffOn ℝ 2 F W` | SOURCE | E (generic calculus contract) |
| `e_diff_slice` | `hK` | `∀ t ∈ cell 2, (t, (0 : Vec 2)) ∈ W` | SOURCE | E (generic calculus contract) |
| `cell_two_eq` | — | No external binders | — | E |
| `integral_cell_two` | `{g}` | `Vec 2 → ℝ` | TYPING | E |
| `integral_cell_two` | `hg` | `ContinuousOn g (cell 2)` | SOURCE | E (generic calculus contract) |
| `sep2_pos` | `{a}` | `ℝ` | TYPING | X |
| `sep2_pos` | `{b}` | `ℝ` | TYPING | X |
| `sep2_pos` | `ha` | `0 < a` | STANDING | p8 L17–21, X |
| `sep2_pos` | `hab` | `a < b` | STANDING | p8 L17–21, X |
| `sep2_pos` | `ϑ` | `ℝ` | TYPING | X |
| `continuous_sep2` | `a` | `ℝ` | TYPING | X |
| `continuous_sep2` | `b` | `ℝ` | TYPING | X |
| `hasDerivAt_sep2_inv_cube` | `{a}` | `ℝ` | TYPING | X |
| `hasDerivAt_sep2_inv_cube` | `{b}` | `ℝ` | TYPING | X |
| `hasDerivAt_sep2_inv_cube` | `ha` | `0 < a` | STANDING | p8 L17–21, X |
| `hasDerivAt_sep2_inv_cube` | `hab` | `a < b` | STANDING | p8 L17–21, X |
| `hasDerivAt_sep2_inv_cube` | `ϑ` | `ℝ` | TYPING | X |
| `ibp_selection` | `{a}` | `ℝ` | TYPING | X |
| `ibp_selection` | `{b}` | `ℝ` | TYPING | X |
| `ibp_selection` | `ha` | `0 < a` | STANDING | p8 L17–21, X |
| `ibp_selection` | `hab` | `a < b` | STANDING | p8 L17–21, X |
| `torus_reduce` | `{G}` | `ℝ → ℝ → ℝ` | TYPING | X |
| `torus_reduce` | `hG` | `Continuous (Function.uncurry G)` | SOURCE | E (generic calculus contract) |
| `torus_reduce` | `hper` | `∀ s, Function.Periodic (G s) (2 * π)` | SOURCE | E (generic calculus contract) |
| `crossU_diag` | `a` | `ℝ` | TYPING | X |
| `crossU_diag` | `b` | `ℝ` | TYPING | X |
| `crossU_diag` | `s` | `ℝ` | TYPING | X |
| `crossU_diag` | `ϑ` | `ℝ` | TYPING | X |
| `quad_integral` | `A` | `ℝ` | TYPING | X |
| `quad_integral` | `B` | `ℝ` | TYPING | X |
| `quad_integral` | `C` | `ℝ` | TYPING | X |
| `avg_cross_diag` | `a` | `ℝ` | TYPING | X |
| `avg_cross_diag` | `b` | `ℝ` | TYPING | X |
| `avg_cross_diag` | `ϑ` | `ℝ` | TYPING | X |
| `fbar_eq` | `{a}` | `ℝ` | TYPING | X |
| `fbar_eq` | `{b}` | `ℝ` | TYPING | X |
| `fbar_eq` | `ha` | `0 < a` | STANDING | p8 L17–21, X |
| `fbar_eq` | `hab` | `a < b` | STANDING | p8 L17–21, X |
| `fbar_eq` | `ϑ` | `ℝ` | TYPING | X |
| `planeLength_circ` | `a` | `ℝ` | TYPING | X |
| `planeLength_circ` | `b` | `ℝ` | TYPING | X |
| `planeLength_circ` | `s` | `ℝ` | TYPING | X |
| `planeLength_circ` | `t` | `ℝ` | TYPING | X |
| `continuous_crossU` | `{a}` | `ℝ` | TYPING | X |
| `continuous_crossU` | `{b}` | `ℝ` | TYPING | X |
| `continuous_crossU` | `ha` | `0 < a` | STANDING | p8 L17–21, X |
| `continuous_crossU` | `hab` | `a < b` | STANDING | p8 L17–21, X |
| `crossU_periodic` | `a` | `ℝ` | TYPING | X |
| `crossU_periodic` | `b` | `ℝ` | TYPING | X |
| `crossU_periodic` | `s` | `ℝ` | TYPING | X |
| `sep2_eq_mul` | `{a}` | `ℝ` | TYPING | X |
| `sep2_eq_mul` | `{b}` | `ℝ` | TYPING | X |
| `sep2_eq_mul` | `hb` | `0 < b` | STANDING | p8 L17–21, X |
| `sep2_eq_mul` | `ϑ` | `ℝ` | TYPING | X |
| `inv_cube_sep2` | `{a}` | `ℝ` | TYPING | X |
| `inv_cube_sep2` | `{b}` | `ℝ` | TYPING | X |
| `inv_cube_sep2` | `ha` | `0 < a` | STANDING | p8 L17–21, X |
| `inv_cube_sep2` | `hab` | `a < b` | STANDING | p8 L17–21, X |
| `inv_cube_sep2` | `ϑ` | `ℝ` | TYPING | X |
| `integral_cos_two_inv_cube` | `{a}` | `ℝ` | TYPING | X |
| `integral_cos_two_inv_cube` | `{b}` | `ℝ` | TYPING | X |
| `integral_cos_two_inv_cube` | `ha` | `0 < a` | STANDING | p8 L17–21, X |
| `integral_cos_two_inv_cube` | `hab` | `a < b` | STANDING | p8 L17–21, X |
| `cross_double_average` | `{a}` | `ℝ` | TYPING | X |
| `cross_double_average` | `{b}` | `ℝ` | TYPING | X |
| `cross_double_average` | `ha` | `0 < a` | STANDING | p8 L17–21, X |
| `cross_double_average` | `hab` | `a < b` | STANDING | p8 L17–21, X |
| `poincare_line_fst` | `m` | `ℝ` | TYPING | X/K |
| `poincare_line_fst` | `κ` | `ℝ` | TYPING | X/K |
| `poincare_line_fst` | `Λ` | `ℝ` | TYPING | X/K |
| `poincare_line_fst` | `l` | `ℝ` | TYPING | X/K |
| `poincare_line_fst` | `s` | `ℝ` | TYPING | X/K |
| `hasDerivAt_lineC` | `{Λ}` | `ℝ` | TYPING | X/K |
| `hasDerivAt_lineC` | `hΛ` | `0 < Λ` | STANDING | p8 L17–21, X |
| `lineC_zero` | `{Λ}` | `ℝ` | TYPING | X/K |
| `hasDerivAt_keplerLong_line` | `{Λ}` | `ℝ` | TYPING | X/K |
| `hasDerivAt_keplerLong_line` | `hΛ` | `0 < Λ` | STANDING | p8 L17–21, X |
| `hasDerivAt_keplerLong_line` | `l` | `ℝ` | TYPING | X/K |
| `hasDerivAt_poincare_fst_xi` | `{m}` | `ℝ` | TYPING | X/K |
| `hasDerivAt_poincare_fst_xi` | `{κ}` | `ℝ` | TYPING | X/K |
| `hasDerivAt_poincare_fst_xi` | `{Λ}` | `ℝ` | TYPING | X/K |
| `hasDerivAt_poincare_fst_xi` | `hΛ` | `0 < Λ` | STANDING | p8 L17–21, X |
| `hasDerivAt_poincare_fst_xi` | `l` | `ℝ` | TYPING | X/K |

Expanded totals (record container replaced by its fields): SOURCE=20; STANDING=50; TYPING=133; RULED=0; EXCESS=0. No constant/witness has broader dependence than the source.

## Findings, deviations, and boundaries

| ID | Severity / disposition | Exact evidence | Refutation / effect |
|---|---|---|---|
| N1 | Minor hygiene; leave to author/orchestrator | `Selection.lean:198`, `simp_rw [mul_comm (Real.cos _)] ` has a trailing space. `git diff --check inp...HEAD` exits 2 and names that line. | Confirmed by direct line inspection; no proof or lint gate effect. No code repair authorized. |
| N2 | Minor handoff accuracy | Handoff says “The longest file has 326 lines” and “file lengths ≤ 326”; actual `Selection.lean` has 344 lines. | Count includes all physical lines and remains far below the 1500-line hard cap. Seven-file total is 1066 lines. |
| N3 | Evidence/provenance note | Handoff AUDIT FOCUS attributes the proof-cut ruling to “13:08” in `docs/campaign/OVERNIGHT.md`; that checkout file contains no such entry or S8-X/S8-Q reference. | The controlling content is independently explicit in `P810-LEAN-DESIGN.md:431–432,454–458`: “DiagonalJet/CrossJet return identities for the literal pair average, Quadratic sums them.” Therefore no mathematical/scope blocker; reconcile the log citation at landing. |
| N4 | Expected generated-root exception | `KAM.lean is out of date; run scripts/gen_root_imports.py`. | The brief explicitly permits this isolated lint failure and prohibits editing/regenerating the root during audit. |

Deviation already disclosed by the prover: the Euler/B1/(I2) source derivation is replaced by an exact trigonometric diagonal integration plus periodic integration by parts. The resulting normalized identity is identical; no numerical evidence enters the proof. This is an acceptable proof-route change, not a source erratum. Audit introduced no deviations to source or Lean code.

**Suspected new blueprint/pinned-source defects: none in the audited node.** The p8 L157 quote “Le calcul complet est un peu long” and unpinned [LR95] remain background motivation for recomputation, not an imported theorem. Existing factor-half/source normalization concerns are described explicitly by p8 L173–178 (`factor-half`); this package proves the p8 corrected cross coefficient and does not independently audit Fej04r/CP11 PDFs or resolve their ledger entries.

Name search found one same-short-name candidate: existing `KAM.Planetary.iteratedFDeriv_slice` in `PGAssembly/JetsSlice.lean:33`. The new name is `KAM.Planetary.SecularForm.iteratedFDeriv_slice`, so it is distinct, with no duplicate fully qualified name. No other candidate was found among the 54 declaration short names. Recursive KAM import inspection reached 82 modules, with 47 frozen-definition modules and **no provider or frozen-theorem module**, hence no DRAFT_SORRY/theorem quarantine dependency. No signed declaration is changed or supplied with a new premise.

## Independent validation

All Lean/Lake/checker commands were serial, with `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper supplies `nice`). No clean, update, cache fetch, or library-wide build. The targeted build replayed cached dependencies; this is recorded as a targeted build, not a fresh clean rebuild.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8x KAM.Planetary.SecularForm.CrossJet
```

Exit 0. Output begins `[inp-gate] slot 2 acquired 14:18:05 for KAM.Planetary.SecularForm.CrossJet` and ends `Build completed successfully (9128 jobs).` Cached warnings occurred in `KAM.Kepler.Energy`, `Poincare.Chart`, `KAM.Kepler.Mass`, `SecularForm.Coefficients` and `Poincare.Holomorphic` (unused binders/deprecated `ite_cond_eq_false`); no warning from a CrossJet file and no default-heartbeat failure.

### Axioms and consumer probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8XAudit.lean
```

Exit 0. The probe imported `KAM.Planetary.SecularForm.CrossJet`, then issued `#print axioms KAM.Planetary.SecularForm.<name>` for **all 39 theorem names in the ledger**, not just the five from the handoff. Every command returned exactly:

```text
'KAM.Planetary.SecularForm.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In particular this was the exact output for `cross_hessian`, `cross_double_average`, `pairSlowSecular_mixed_jet`, `hasDerivAt_poincare_fst_xi`, `e_diff_slice`, and the other 34 exports. No `sorryAx` or project axiom. The same scratch file elaborated this explicit coefficient identity:

```lean
example {n : ℕ} (D : Data n) (a : Fin n → ℝ) (ha : a ∈ axes n)
    (i j : Fin n) (hij : i < j) :
    iteratedFDeriv ℝ 2 (fun y : Fin 2 → ℝ =>
      pairSlowSecular D i j (action D a i) (action D a j) (![y 0, 0], ![y 1, 0]))
      0 ![Pi.single 0 1, Pi.single 1 1] =
    2 * (D.G * D.m i * D.m j * a i / (4 * a j ^ 2) *
      laplace_def (3 / 2) 2 (a i / a j) /
        (Real.sqrt (action D a i) * Real.sqrt (action D a j))) := by
  have h := cross_hessian D ha hij
  have hc : coeffs D a i j =
      D.G * D.m i * D.m j * a i / (4 * a j ^ 2) *
      laplace_def (3 / 2) 2 (a i / a j) /
        (Real.sqrt (action D a i) * Real.sqrt (action D a j)) := by
    unfold coeffs qhat pairB
    simp only [ne_of_lt hij, if_false, min_eq_left hij.le, max_eq_right hij.le]
  simpa only [hc] using h
```

The probe's `if_false` spelling produced a deprecation warning only. No frozen/provider equality or seal-body probe applies: S8-X has no signed/frozen declaration. The explicit physical probe above checks the actual exported proof cut without fabricating an anchor.

### Kernel replay and source lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.CrossJet KAM.Planetary.SecularForm.CrossJet.Variation KAM.Planetary.SecularForm.CrossJet.Parametric KAM.Planetary.SecularForm.CrossJet.PairIntegrand KAM.Planetary.SecularForm.CrossJet.MixedKernel KAM.Planetary.SecularForm.CrossJet.PairAverage KAM.Planetary.SecularForm.CrossJet.Selection
```

Exit **0**, one invocation. Complete output:

```text
replaying KAM.Planetary.SecularForm.CrossJet
replaying KAM.Planetary.SecularForm.CrossJet.Selection
replaying KAM.Planetary.SecularForm.CrossJet.PairIntegrand
replaying KAM.Planetary.SecularForm.CrossJet.Variation
replaying KAM.Planetary.SecularForm.CrossJet.MixedKernel
replaying KAM.Planetary.SecularForm.CrossJet.PairAverage
replaying KAM.Planetary.SecularForm.CrossJet.Parametric
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the permitted stale generated root. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (690 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module check, frozen-anchor guard and ABI hash gate all pass. The generated root was left untouched.

Additional static checks:

- `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/SecularForm/CrossJet.lean KAM/Planetary/SecularForm/CrossJet` returned no matches (exit 1).
- `wc -l KAM/Planetary/SecularForm/CrossJet.lean KAM/Planetary/SecularForm/CrossJet/*.lean` returned 83, 149, 153, 88, 131, 344, 118, total 1066. All files have copyright, `module`, `public import`, module documentation, and `@[expose] public noncomputable section`; the module checker passed.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output (exit 0).
- `git diff --check inp...HEAD` returned the sole trailing-space diagnostic recorded as N1 (exit 2).
- All 16 frozen-v1 file hashes were rechecked at closeout; all still match. The declaration ledger covers all 54 new declarations.


## Closeout

**Audit complete: PASS WITH NOTES.** All 54 declarations classified; 39/39 theorem axiom closures checked; 7/7 modules replayed; targeted build passes; lint has only its explicitly permitted generated-root exception; protected-path diff empty; no source or proof repairs made. Notes N1–N3 are bounded hygiene/evidence issues. Temporary audit probes, scripts and logs were removed after their results were transcribed here. Only this report was created by the auditor outside scratch.

S8-Q must still perform its own assembly and validation against its signed `quadratic_form`; S8-X alone closes no frozen anchor, analytic remainder estimate, or full campaign theorem.
