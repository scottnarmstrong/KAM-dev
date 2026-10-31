# W1-CUBIC independent audit 1

Date: 2026-10-30. Worktree: `/root/code/KAM-inp-wph`, branch `inp-wph`.
Snapshot v1: HEAD `448ac3f5f1ba4fd585668b8c0611229ac1f467b3`;
comparison `inp` = `2f8550f34646d98317b50a3c677675e616c80026`;
merge base = `eb722cbc51ba0a6d84e3c8567fcba010df8eb6ab`.

## Verdict and envelope

**FAIL for completion of the entire assigned cubic subsection; PASS WITH NOTES for the implemented infrastructure.**
The exact selection bounds, complex trilinear map, frozen `cubicGrad` identification, analytic cubic map,
Hamiltonian coordinate formulas, and full `X^w` specialization of coordinatewise invariance pass.
The complex reconstruction estimate and its series consequences close the carrier omission in W0-ANALYSIS audit F1.
The symmetric continuous four-linear form in gradient-identity (i), and two-sided trilinearity/symmetry in selection,
remain unproved as exported results. These are disclosed omissions, not counterexamples to the proved theorems.
Do not mark those full nodes PROVED from this package.

No provider or seal is in scope (handoff AUDIT FOCUS); audit item 1 is N/A. In particular,
`wave.nlw2.v1` remains DRAFT_SORRY / FROZEN_UNPROVED, with no theorem-anchor promotion.
The eleven Wave definition anchors are SEALED; the nine appearing in the implementation import closure have
matching whole-file manifest hashes. No provider or DRAFT_SORRY theorem occurs in that closure.

Authorization: report-only audit, ephemeral probes/logs under this worktree's `.lake/abi-scratch/`,
no source repair, git mutation, commit, root regeneration, or network work. The user expressly overrides the
brief's generic main-worktree output instruction: this report is in the exact requested **package worktree** path.
The handoff authorizes the existing generated `KAM/Root/Wave.lean` delta and requires `w_lint.sh` for this slim checkout.
All auditor Lean/Lake/checker invocations are serialized, `LEAN_NUM_THREADS=1`, with `nice -n 5`
(the prescribed build gate applies nice itself). Other sessions' processes are outside this audit's control.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md (D30, D41, D43), the external package audit brief,
the entire W1-CUBIC handoff, the assigned blueprint statements/proofs, relevant frozen definitions and their
manifest entries, frozen nlw2 clause (4), W0-ANALYSIS audit F1 and its subsequent scope ruling,
and every file in `git diff inp...HEAD` (19 files, 3087 insertions).
`docs/tracks/W/statement.md` does not exist; the actual statement document is `W-STATEMENTS.md`.
The 17 new Lean files contain 2929 lines and 196 public declarations: 96 theorems, 67 lemmas, 32 definitions,
one abbreviation. The declaration ledger below accounts for all of them.

Method: tier-2 source-correspondence and refute-first package audit, with a separate search/refutation pass
on candidate gaps, direct proof/body inspection on the spine, exhaustive declaration/definition inventory,
then mechanical checks. Existing upstream analytic/algebraic infrastructure is consumed, not independently
re-audited as a new package. Published PDFs and the entire W2/W3/W8 campaign are outside this audit;
no new claim about a published-source erratum is made.

## Findings and independent refutation pass

### F1 — gradient-identity (i) is still partial

Snapshot v1, `blueprint-W/parts/w1-sequences.tex:526-527` requires the
“symmetric continuous $4$-linear form” `Q(q1,q2,q3,q4) = <T(q1,q2,q3),q4>_0`, with
`|Q| ≤ C_* ∏ ‖qi‖`. `GradIdentity.lean:31` proves the diagonal pairing identity;
`GradLp.lean:68` identifies its weighted inner-product representation. The derivative is genuinely proved:
`GradLp.lean:143` uses analyticity, coordinate derivatives, and density of finite-support vectors.
Thus the derivative does not assume the missing Q theorem.

Refutation attempt: searched all `KAM/Wave` for four-linear forms, `Fin 4`, quartic-form/symmetry exports,
and examined the imported `waveCubicMultilinear` and `waveTriML`. Both are three-linear maps; their symmetry
only permutes the first three slots. `sineQuarticCoeff_perm` proves finite coefficient symmetry, not the
four-argument continuous form and norm statement. The diagonal identity alone is not that exported statement.
The handoff's “Labels / parts NOT done” item 1 explicitly confirms the omission.
**SURVIVED: missing source conclusion; blocks full gradient-identity node closure.**
Repair criterion for a later authorized package: export the actual four-linear form, defining pairing identity,
full four-slot symmetry, continuity and exact C_* bound on the source carriers. No repair was made here.

### F2 — selection's two-sided algebraic conclusions are missing

Snapshot v1, `blueprint-W/parts/w1-sequences.tex:411` states
“In both cases T_c is trilinear; it is symmetric if c is symmetric in its first three indices.”
`SelectionTwoFinal.lean:44` proves absolute convergence, target membership, and the exact `64 M K_s²` bound,
but exports no additivity, scalar-linearity, or symmetry theorem for `waveSelTwo`/`waveSelSumZ`.

Refutation attempt: searched the entire Wave tree for both two-sided definitions and examined every declaration
in the three two-sided files. Their only uses implement the norm estimate. `waveSelSum_add_*`, `waveSelSum_smul_*`
and swaps in SelectionOneSided have domain `ℕ+`, not the guarded `ℤ` triple sum, and cannot be applied directly
as the absent two-sided theorem. General tsum lemmas would support a future proof but are not that proof.
The handoff's item 2 confirms the omission.
**SURVIVED: missing source conclusion; blocks full selection node closure, not either numerical estimate.**

### Notes (not false-theorem findings)

- N1: `cubic-analytic` (ii) exports the second derivative and its bound in directional form
  (`CubicDeriv.lean:87,113`), not the bundled operator norm of `fderiv K (fderiv K N) y`.
  Analyticity plus the evaluated derivative identity supports that standard reformulation, but no exported bundled
  norm theorem was located. Preserve this API distinction; do not cite `waveCubicNL_second_norm_le` as having that type.
  The third derivative is fully bundled through `iteratedFDeriv` and is correct.
- N2: complex reconstruction is presented by linearity, uniform convergence, every derivative formula and pointwise
  derivative sup bound, rather than a bundled bounded map into a chosen `C^k([0,π])` normed type. This matches the
  approved W0 representation. Its “in particular” complex U_m/V_m/λq wrappers are not newly exported here;
  the assigned complex coefficient estimate and its series consequences are present. This resolves the specific F1
  carrier gap; it does not add those wrapper declarations or a new C^k-space API.
- N3: `not_exists_bounded_waveXLam` is literally the single-component multiplier obstruction. A bounded same-weight
  phase-space field would give that multiplier by inclusion of `(0,y)` and first projection. The theorem is adequate
  obstruction infrastructure but is not literally quantified over maps on the product.
- N4: the real W0 norm-chain proof is duplicated rather than refactored; `waveTrilinear_eq_waveTriSeq` proves exact
  identification. This is a maintenance cost, not a constant/carrier mismatch.
- N5: the CubicDeriv module docstring mentions `waveCubicNL_hasFDerivAt_fderiv`, but no declaration of that name is
  supplied. The actual implemented higher-derivative exports are the three listed above (N1). No closure relies on
  the docstring name.

## Source-node ledger

| Node / clause | Lean evidence | Verdict | Exact scope |
|---|---|---|---|
| selection (a), convergence/membership/bound | waveSel_oneSided | PASS | RCLike K, a≥0, p≥1/2, exact 2 M K_(p+1/2)²; no hidden dependence on m or inputs. |
| selection (b), convergence/membership/bound | waveSel_twoSided | PASS | ℂ, all nonzero indices, exact 64 M K_(p+1/2)²; output zero at index 0. Inputs may even have nonzero index-0 value, a valid strengthening. |
| selection, one-sided algebraic clauses | waveSelSum_add_*, smul_*, swap_* | PASS WITH NOTES | Summability premises in generic additivity helpers are supplied by the proved selection estimate on its source domain; not excess premises on waveSel_oneSided. |
| selection, two-sided algebraic clauses | no exported theorem located | FAIL | F2. |
| trilinear (i) | waveTriML, coeffW_waveTriML, waveTriML_unique, waveTriML_perm, waveTriML_norm_le | PASS | Actual continuous map; coordinates, uniqueness, symmetry and exact C_* norm. |
| trilinear (ii) | waveTriML_complexify, waveTriML_conj | PASS | Commutes with landed real inclusion and conjugation. |
| trilinear (iii) | waveTriML_embed | PASS | Both input and output weight inclusions, correct inequalities and p+1 targets. |
| trilinear (iv) | waveCubic_coeffW_eq_coeffW_triML, cubicGrad_eq_triML_div | PASS | Literal frozen cubicGrad, not an alternate cubic definition. General integral identification uses a>0. |
| cubic-analytic (i),(iii),(iv) | waveCubicNL_analyticOnNhd, norm/sub bounds; waveGw* | PASS | Global K-analytic polynomial; exact C_* and headline constant. |
| cubic-analytic (ii) | waveCubicNL_hasFDerivAt, fderiv, norm bounds, second_apply/second_norm_le, third_apply | PASS WITH NOTES | Exact first and third derivatives; directional second derivative form (N1). |
| gradient-identity (i), diagonal identity | waveG_hasSum_pairing, waveG_coeffW_eq_inner | PASS | Unweighted pairing, correctly transported through rho. |
| gradient-identity (i), symmetric Q and bound | missing | FAIL | F1. |
| gradient-identity (ii) | waveG_coeffW_analyticOnNhd, hasFDerivAt, fderiv_apply | PASS | All directions, no assumed differentiability/gradient formula. |
| gradient-identity (iii), frozen formula | waveG_frozen_fderiv_apply, waveGradW_one_one_apply | PASS WITH NOTES | Correct weighted gradient; no separate general-carrier Riesz-gradient characterization/remark. |
| hamfield (i) | waveXLam, coeffW_waveXLam_*, norm_waveXLam_le, not_exists_bounded_waveXLam | PASS WITH NOTES | Exact sqrt(1+m) operator bound; single-multiplier obstruction (N3). |
| hamfield (ii),(iii) | waveXG*, waveXH*, coordinate exports | PASS | K-analytic on whole product; target weights p+1 / p−1 represented correctly. |
| hamfield (iv) | waveHw, waveHw_analyticOnNhd, hasFDerivAt, fderiv_p/q | PASS | Literal quadratic-plus-integral Hamiltonian and unweighted coordinate derivatives. |
| hamfield (v) | waveXw, waveXw_analyticOnNhd, coeffW_one_zero_waveXw_* | PASS | Exact D and S² coefficients, both signs, weight (1,0). |
| coordinatewise, X^w specialization | frozen_invariance_iff_waveXw | PASS | Only differentiability at θ beyond standing m>0 and typing; pointwise stronger than global differentiability. |
| w0n:recon-bounded, assigned complex clause | ReconComplex exports | PASS WITH NOTES | Earlier F1 carrier omission closed; N2 limits on packaging/wrappers retained. |
| w0n:cubic-bound, complex trilinear clause | waveTri_oneSided, TriLp/TriML, waveTrilinear_eq_waveTriSeq | PASS | Correct absolute sums and smoothing at exact C_*; no real-only restriction. |
| W-NLW2 anchor | no provider/seal in this package | N/A | FROZEN_UNPROVED, no closure certified. |

## Constants, signs, carriers, and frozen attachment

`waveSelCount` is precisely the eight sign-pattern indicators (multiplicity counted), not a support indicator.
`waveSelCountZ` does the same for integer indices. The one-sided proof passes from the three even majorants
(each factor √2) to an even convolution, then uses the half two-sided square norm; this yields 2, not 2√2.
The two-sided majorants each cost 2, and the sign split costs 8, giving 64. Neither bound assumes symmetry of c.
For c = g/(√λi √λj √λk √λl), `waveTriCoef_bound` uses λj≥j and the quartic sign bound with M=1/(2π).
`TriSeq.lean:88-90` computes `2*(1/(2π))*K² = K²/π`. `waveCubicConst` depends only on p;
`waveCubicConst_one` supplies the headline `8*(1+2*Re(riemannZeta 3))/π`. No input-dependent constant is chosen.

`TriProps.lean:116` identifies exactly the manifested `KAM.Wave.cubicGrad`; its transitive frozen body is
`(∫₀^π reconU(y,x)^3 * sineMode(l,x) dx)/√λl`. `coeffW_one_one` identifies the actual frozen coeff.
The general diagonal bridge consumes the already-proved integral-to-series theorem rather than assuming it.
No shadow definition or provider appears.

`waveXw(z) = (lamMul 1 z.2, -lamMul 1 z.1 - waveShift(waveShift(waveGw z.1)))`.
The multiplier is λj/j and waveShift is 1/j. At output weight (1,0), the two coefficient identities give
`(λj coeff z.2 j, -λj coeff z.1 j - cubicGrad z.1 j)`, exactly frozen clause (4).
`frozen_invariance_iff_waveXw` supplies both formerly conditional right-hand-side identifications inside its proof;
no hv₁/hv₂ premise survives in the public theorem. DK is applied to ν once, with no extraneous 2π factor.

For H, sigma is λj/ω_(a,p)(j)² and rho is 1/(ω_(a,p+1)(j)ω_(a,p)(j)). The test directions in
`waveHw_fderiv_p/q` are **ω_(a,p)(j) δj** in weighted coordinates, exactly the physical coefficient basis vectors.
Their derivatives are λj pj and λj qj+Gq(q)j, rather than derivatives in an unrescaled lp basis.
The waveXLam and waveXG coordinate identities then identify the Hamiltonian field, including its target weight.

## Expanded binder audit

SOURCE = explicit source hypotheses/domain membership; STANDING = m>0; TYPING = parameter, scalar instance,
function or index data; RULED = owner amendment; EXCESS = unsupported premise. Project predicates expanded:
`IsEll a p q = Memℓp (fun j => (ellWeight a p j : K)*q j) 2`, equivalent here to summability of the weighted squares;
`WaveTwoMem` is summability of `(waveTwoWeight a p j * ‖w j‖)^2`, not any output assumption.
RCLike is scalar typing, not a proof-obligation bundle. All ordinary lp arguments already carry their typing
membership. No custom instance hiding analytic conclusions was found.

### waveSel_oneSided

| Binder | Bin | Source / meaning |
|---|---|---|
| `K` | TYPING | Scalar field ℝ or ℂ (generalized to RCLike). |
| `[RCLike K]` | TYPING | Scalar structure. |
| `a` | TYPING | selection, w1:399. |
| `p` | TYPING | selection, w1:399. |
| `M` | TYPING | selection, w1:399. |
| `ha : 0≤a` | SOURCE | selection, w1:399. |
| `hp : 1/2≤p` | SOURCE | selection, w1:399. |
| `hM : 0≤M` | SOURCE | selection, w1:399. |
| `c` | TYPING | selection (a), coefficient array. |
| `hc` | SOURCE | selection (a), exact coefficient decay/selection rule. |
| `q` | TYPING | Input sequence. |
| `q'` | TYPING | Input sequence. |
| `q''` | TYPING | Input sequence. |
| `hq` | SOURCE | Input weighted-space membership, selection (a). |
| `hq'` | SOURCE | Input weighted-space membership, selection (a). |
| `hq''` | SOURCE | Input weighted-space membership, selection (a). |

Counts: SOURCE 7, STANDING 0, TYPING 9, RULED 0, EXCESS 0.

### waveSel_twoSided

| Binder | Bin | Source / meaning |
|---|---|---|
| `a` | TYPING | selection, w1:399. |
| `p` | TYPING | selection, w1:399. |
| `M` | TYPING | selection, w1:399. |
| `ha : 0≤a` | SOURCE | selection, w1:399. |
| `hp : 1/2≤p` | SOURCE | selection, w1:399. |
| `hM : 0≤M` | SOURCE | selection, w1:399. |
| `c` | TYPING | selection (b), integer coefficient array. |
| `hc` | SOURCE | selection (b), exact nonzero-index coefficient decay/selection rule. |
| `w` | TYPING | Complex integer sequence, selection (b). |
| `w'` | TYPING | Complex integer sequence, selection (b). |
| `w''` | TYPING | Complex integer sequence, selection (b). |
| `hw` | SOURCE | WaveTwoMem input membership, selection (b). |
| `hw'` | SOURCE | WaveTwoMem input membership, selection (b). |
| `hw''` | SOURCE | WaveTwoMem input membership, selection (b). |

Counts: SOURCE 7, STANDING 0, TYPING 7, RULED 0, EXCESS 0.

### cubicGrad_eq_triML_div

| Binder | Bin | Source / meaning |
|---|---|---|
| `m` | TYPING | Standing mass parameter. |
| `hm : 0<m` | STANDING | Wave conventions; frozen lam/cubicGrad typing. |
| `y` | TYPING | trilinear (iv), arbitrary real lp vector. |
| `l` | TYPING | trilinear (iv), positive output index. |

Counts: SOURCE 0, STANDING 1, TYPING 3, RULED 0, EXCESS 0.

### frozen_invariance_iff_waveXw

| Binder | Bin | Source / meaning |
|---|---|---|
| `m` | TYPING | Mass parameter. |
| `hm : 0<m` | STANDING | Wave conventions. |
| `Kmap` | TYPING | coordinatewise, w1:173-175; Fin 2 → ℝ parameter domain. |
| `θ` | TYPING | Base angle. |
| `ν` | TYPING | Direction/frequency. |
| `hK : DifferentiableAt ℝ Kmap θ` | SOURCE | Source differentiability; pointwise strengthening of global hypothesis. |

Counts: SOURCE 1, STANDING 1, TYPING 4, RULED 0, EXCESS 0.

### waveHw_fderiv_p and waveHw_fderiv_q (each)

| Binder | Bin | Source / meaning |
|---|---|---|
| `m` | TYPING | Mass parameter. |
| `hm : 0<m` | STANDING | Wave conventions. |
| `a` | TYPING | hamfield coefficient weight. |
| `p` | TYPING | hamfield coefficient exponent. |
| `ha : 0<a` | SOURCE | hamfield, w1:556. |
| `hp : 1/2≤p` | SOURCE | hamfield, w1:556. |
| `z` | TYPING | Arbitrary weighted phase point. |
| `j` | TYPING | Coordinate index. |

Counts: SOURCE 2, STANDING 1, TYPING 5, RULED 0, EXCESS 0.

### waveSineSeriesK_norm_le

| Binder | Bin | Source / meaning |
|---|---|---|
| `K` | TYPING | Scalar field ℝ or ℂ (generalized to RCLike). |
| `[RCLike K]` | TYPING | Scalar structure. |
| `a` | TYPING | recon-bounded, arbitrary positive radius. |
| `p` | TYPING | recon-bounded, arbitrary real exponent. |
| `ha : 0<a` | SOURCE | recon-bounded, w0-normalization:19. |
| `c` | TYPING | Complex-valued coefficient sequence (RCLike generalization). |
| `hc : IsEll a p c` | SOURCE | recon-bounded, source weighted-space membership. |
| `k` | TYPING | Derivative order. |
| `x` | TYPING | Evaluation point; all ℝ strengthens [0,π]. |

Counts: SOURCE 2, STANDING 0, TYPING 7, RULED 0, EXCESS 0.

The remaining source-facing trilinear/analytic exports use the same scalar/mass/weight/input typing and
ha/hp source hypotheses. Their derivative, continuity, coordinate, and norm conclusions are proved, not binders.
`waveTriML_unique` quantifies an arbitrary competitor S and its defining-coordinate property hS, as a uniqueness
statement must; this is not an existence assumption. Generic sum/additivity and majorant lemmas have explicit
intermediate summability/majorization hypotheses; the concrete constructions discharge them in their proofs
(`waveTriCoords_summable`, `waveTriCoords_isEll`, and the selection estimates). They are technical helpers and do
not replace a source theorem with an unproduced conditional theorem.

## Definition classification (all 33)

All bodies below were inspected. Every production map on lp/phase space is the stated object for every vector
in its declared carrier, with all convergence/boundedness proofs supplied by construction. No choose/default,
opaque object, or characterization deferred to a later package occurs.

| Definition / abbreviation | Classification and whole-carrier check | Verdict |
|---|---|---|
| `waveTriBil` | Literal continuous bilinear currying of the proved trilinear map; continuity bound constructed. | PASS |
| `waveCubicNL` | Literal diagonal of waveTriML, all lp vectors. | PASS |
| `waveCubicDeriv` | Literal 3 times third-slot partial evaluation; derivative characterization proved. | PASS |
| `waveGw` | Literal (a,p)=(1,1), K=ℝ specialization of N; exact frozen coordinate theorem proved. | PASS |
| `waveShift` | Literal bounded diagonal 1/j; j>0 and bound supplied. | PASS |
| `waveXw` | Literal pair (D y′, −D y − S²Gw(y)), all WaveSpace. | PASS |
| `waveRho` | Literal reciprocal of two positive weights; denominator never zero. | PASS |
| `waveRhoCLM` | Literal bounded diagonal rho for source a,p bounds; proof supplied. | PASS |
| `waveGradW` | Literal rho multiplier applied to N; gradient characterization proved. | PASS |
| `waveGw'` | Literal wrapper waveG(coeffW a p y); unused in source closure. Arbitrary a,p wrapper inherits integral/tsum totalization; analytic/source claims restricted to a>0,p≥1/2. | PASS |
| `WaveSpaceK` | Abbreviation for product of two lp 2 spaces, inherited max norm. | PASS |
| `waveXLam` | Literal continuous linear pair of λ/j multipliers, all vectors. | PASS |
| `waveXG` | Literal (0,−N(z.1)), all vectors, target interpreted at p+1. | PASS |
| `waveXH` | Literal linear field plus embedded nonlinear field; target p−1. | PASS |
| `waveSigma` | Literal λ/ω², positive nonzero weights for all real a,p. | PASS |
| `waveSigmaCLM` | Literal bounded diagonal sigma; bound proved under source weights. | PASS |
| `waveLamQuad` | Literal half-sum of sigma inner products; coordinate expansion is the source quadratic energy. | PASS |
| `waveHw` | Literal quadratic energy plus waveG integral at coeffW. | PASS |
| `waveHwDeriv` | Literal sum of the two quadratic derivative pairings and rho-N pairing; derivative proved. | PASS |
| `waveSineSeriesK` | Literal derivative sine-series tsum, not a selected reconstruction. Source-domain absolute convergence proved for every order. | PASS |
| `waveSelCount` | Literal finite sum of eight sign indicators on positive indices. | PASS |
| `waveSelSum` | Literal triple tsum on positive indices. Absolute convergence established on the complete source domain by selection estimates. | PASS |
| `waveSelTwo` | Literal output-zero convention at l=0 required by source; otherwise waveSelSumZ. This branch is source semantics, not a repair fallback. | PASS |
| `waveTwoMaj` | Literal even two-sided majorant, zero at index 0 as required by source. | PASS |
| `waveSelCountZ` | Literal finite sum of eight integer sign indicators. | PASS |
| `waveSelSumZ` | Literal guarded tsum omitting all zero input indices; guards implement precisely the punctured source carrier. | PASS |
| `waveSignZEmb` | Literal sign/positive-index reindexing; injectivity, nonzero image and surjectivity onto punctured triples proved. | PASS |
| `waveAbsPNat` | Literal natAbs with supplied proof that l≠0; never defaults at zero. | PASS |
| `waveTriCoords` | Literal T applied to three coeffW sequences. | PASS |
| `waveTriAux` | Literal tauLp of waveTriCoords with a proved IsEll witness; no arbitrary choice. Defining coefficients and pointwise uniqueness proved. | PASS |
| `waveTriML` | Literal mkContinuous of explicit trilinear operations, with bound proved; coordinate characterization and uniqueness proved. | PASS |
| `waveTriCoef` | Literal g divided by the four sqrt λ factors, all positive indices and m>0. | PASS |
| `waveTriSeq` | Literal specialization of waveSelSum to the real coefficients cast into K. | PASS |

Unrestricted sequence-form tsums (`waveSelSum`, `waveSelSumZ`, `waveTriSeq`, `waveSineSeriesK`) use Lean's usual
zero totalization if a sum does not converge. They are explicitly sum helpers; the source never assigns a
convergent map to arbitrary nonweighted sequences. No norm estimate, additivity claim requiring convergence,
physical identification or production lp construction uses such an off-domain value. In particular, the exported
lp maps do **not** have a good-locus/bad-locus branch: their bounds and convergence apply to every lp input.
The generic helper waveGw′ similarly carries no global source claim at negative a.

Definition audit: BODY_MATCH OK; PUBLIC_CARRIER OK on each declared source-domain map;
WELL_DEFINEDNESS OK (all convergence/membership constructed); CHARACTERIZATION OK for TriAux/TriML and the
frozen/gradient identifications, N/A_LITERAL for literal formulas; CHOICE_INDEPENDENCE N/A (no selected witness);
DEFINITION_VERDICT PASS. This certifies these definitions, not the missing Q object.

## Complete public-declaration ledger

All names are in namespace `KAM.Wave`; locators are relative to `KAM/Wave/Cubic/` at snapshot v1.
PASS here means the stated local declaration/body passes; node-wide omissions are recorded separately above.
Definitions are classified individually above. Technical helpers are not independent assertions that a whole
blueprint node has closed.

| Node / role | Declaration (file:line) | Verdict | Reason / limit |
|---|---|---|---|
| cubic-analytic(ii) / symmetry | `waveTriML_swap_vec` (CubicDeriv.lean:29) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic(ii) / symmetry | `waveTriML_perm` (CubicDeriv.lean:44) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic(ii) / symmetry | `waveCubicNL_third_apply` (CubicDeriv.lean:54) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic(ii) / symmetry | `waveTriBil` (CubicDeriv.lean:68) | PASS | Literal definition; classification above. |
| cubic-analytic(ii) / symmetry | `waveTriBil_apply` (CubicDeriv.lean:82) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic(ii) / symmetry | `waveCubicNL_second_apply` (CubicDeriv.lean:87) | PASS WITH NOTES | Directional second derivative; N1. |
| cubic-analytic(ii) / symmetry | `waveCubicNL_second_norm_le` (CubicDeriv.lean:111) | PASS WITH NOTES | Directional second derivative; N1. |
| cubic-analytic | `waveCubicNL` (CubicMap.lean:33) | PASS | Literal definition; classification above. |
| cubic-analytic | `waveCubicNL_eq` (CubicMap.lean:36) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `waveCubicNL_norm_le` (CubicMap.lean:43) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `waveCubicNL_analyticOnNhd` (CubicMap.lean:49) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `wave_update_const_zero` (CubicMap.lean:58) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `wave_update_const_one` (CubicMap.lean:62) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `wave_update_const_two` (CubicMap.lean:66) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `waveCubicDeriv` (CubicMap.lean:71) | PASS | Literal definition; classification above. |
| cubic-analytic | `waveCubicDeriv_apply` (CubicMap.lean:75) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `waveCubicNL_hasFDerivAt` (CubicMap.lean:80) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `waveCubicNL_fderiv` (CubicMap.lean:106) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `norm_waveCubicDeriv_le` (CubicMap.lean:112) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `norm_fderiv_waveCubicNL_le` (CubicMap.lean:126) | PASS | Proved at its stated type; source premise or technical input as described above. |
| cubic-analytic | `waveCubicNL_sub_le` (CubicMap.lean:132) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `ellWeight_add_one` (FrozenForm.lean:37) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `ellWeight_one_zero` (FrozenForm.lean:44) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `ellWeight_one_one` (FrozenForm.lean:47) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `ellWeight_one_two` (FrozenForm.lean:50) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveGw` (FrozenForm.lean:56) | PASS | Literal definition; classification above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveGw_apply` (FrozenForm.lean:60) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveGw_norm_le` (FrozenForm.lean:67) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveGw_analyticOnNhd` (FrozenForm.lean:73) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `coeffW_one_two_waveGw` (FrozenForm.lean:78) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveGw_weighted_one_one` (FrozenForm.lean:87) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveGw_weighted_one_zero` (FrozenForm.lean:94) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveShift` (FrozenForm.lean:101) | PASS | Literal definition; classification above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveShift_apply` (FrozenForm.lean:107) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveXw` (FrozenForm.lean:112) | PASS | Literal definition; classification above. |
| frozen cubic / hamfield(v) / coordinatewise | `lamRatio_one` (FrozenForm.lean:116) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `coeffW_one_zero_waveXw_fst` (FrozenForm.lean:120) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `coeffW_one_zero_waveXw_snd` (FrozenForm.lean:132) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `waveXw_analyticOnNhd` (FrozenForm.lean:147) | PASS | Proved at its stated type; source premise or technical input as described above. |
| frozen cubic / hamfield(v) / coordinatewise | `frozen_invariance_iff_waveXw` (FrozenForm.lean:167) | PASS | Exact frozen clause (4) at θ; hK is sole analytic premise. |
| gradient-identity(i) | `waveG_hasSum_pairing` (GradIdentity.lean:29) | PASS | Exact diagonal identity; does not supply missing four-linear Q (F1). |
| gradient-identity | `one_le_ellWeight` (GradLp.lean:32) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveRho` (GradLp.lean:40) | PASS | Literal definition; classification above. |
| gradient-identity | `waveRho_norm_le_one` (GradLp.lean:42) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveRhoCLM` (GradLp.lean:51) | PASS | Literal definition; classification above. |
| gradient-identity | `waveRhoCLM_apply` (GradLp.lean:55) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveGradW` (GradLp.lean:61) | PASS | Literal definition; classification above. |
| gradient-identity | `waveGw'` (GradLp.lean:65) | PASS | Literal definition; classification above. |
| gradient-identity | `waveG_coeffW_eq_inner` (GradLp.lean:69) | PASS | Exact diagonal identity; does not supply missing four-linear Q (F1). |
| gradient-identity | `waveG_coeffW_analyticOnNhd` (GradLp.lean:95) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveCoeffW_add_single` (GradLp.lean:114) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveG_coeffW_hasDerivAt_single` (GradLp.lean:130) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveG_coeffW_hasFDerivAt` (GradLp.lean:157) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveG_coeffW_fderiv_apply` (GradLp.lean:190) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveGradW_one_one_apply` (GradLp.lean:206) | PASS | Proved at its stated type; source premise or technical input as described above. |
| gradient-identity | `waveG_frozen_fderiv_apply` (GradLp.lean:218) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `WaveSpaceK` (HamField.lean:39) | PASS | Literal definition; classification above. |
| hamfield(i–iii) | `waveXLam` (HamField.lean:43) | PASS | Literal definition; classification above. |
| hamfield(i–iii) | `waveXLam_apply` (HamField.lean:49) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `coeffW_waveXLam_fst` (HamField.lean:53) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `coeffW_waveXLam_snd` (HamField.lean:63) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `norm_waveXLam_le` (HamField.lean:73) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `not_exists_bounded_waveXLam` (HamField.lean:97) | PASS WITH NOTES | Single multiplier obstruction; N3. |
| hamfield(i–iii) | `waveXG` (HamField.lean:104) | PASS | Literal definition; classification above. |
| hamfield(i–iii) | `waveXG_analyticOnNhd` (HamField.lean:108) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `waveXG_norm_le` (HamField.lean:118) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `waveXG_sub_le` (HamField.lean:124) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `waveXG_complexify` (HamField.lean:140) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `waveXH` (HamField.lean:152) | PASS | Literal definition; classification above. |
| hamfield(i–iii) | `waveXH_analyticOnNhd` (HamField.lean:158) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `coeffW_waveXH_fst` (HamField.lean:175) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(i–iii) | `coeffW_waveXH_snd` (HamField.lean:185) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `waveSigma` (HamHamiltonian.lean:34) | PASS | Literal definition; classification above. |
| hamfield(iv) | `waveSigma_norm_le` (HamHamiltonian.lean:36) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `waveSigmaCLM` (HamHamiltonian.lean:56) | PASS | Literal definition; classification above. |
| hamfield(iv) | `waveSigmaCLM_apply` (HamHamiltonian.lean:60) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `waveSigmaCLM_selfAdjoint` (HamHamiltonian.lean:64) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `waveLamQuad` (HamHamiltonian.lean:73) | PASS | Literal definition; classification above. |
| hamfield(iv) | `waveHw` (HamHamiltonian.lean:77) | PASS | Literal definition; classification above. |
| hamfield(iv) | `hasFDerivAt_inner_sigma` (HamHamiltonian.lean:80) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `waveHw_analyticOnNhd` (HamHamiltonian.lean:94) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `waveHwDeriv` (HamHamiltonian.lean:117) | PASS | Literal definition; classification above. |
| hamfield(iv) | `waveHw_hasFDerivAt` (HamHamiltonian.lean:127) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `wave_inner_single_right` (HamHamiltonian.lean:144) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `waveHw_fderiv_p` (HamHamiltonian.lean:151) | PASS | Proved at its stated type; source premise or technical input as described above. |
| hamfield(iv) | `waveHw_fderiv_q` (HamHamiltonian.lean:165) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK` (ReconComplex.lean:41) | PASS | Literal definition; classification above. |
| w0n:recon-bounded complex | `waveSineSeriesK_term_le` (ReconComplex.lean:44) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK_summable_norm` (ReconComplex.lean:51) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveEllK_real_norm` (ReconComplex.lean:57) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveEllK_summable_pow_mul` (ReconComplex.lean:64) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveEllK_tsum_pow_mul_le` (ReconComplex.lean:69) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK_norm_le` (ReconComplex.lean:80) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK_summable` (ReconComplex.lean:93) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK_add` (ReconComplex.lean:98) | PASS | Generic summability inputs; supplied by waveEllK_summable_pow_mul on source domain. |
| w0n:recon-bounded complex | `waveSineSeriesK_smul` (ReconComplex.lean:106) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK_tendstoUniformly` (ReconComplex.lean:113) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `wave_hasDerivAt_ofReal` (ReconComplex.lean:121) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `hasDerivAt_waveSineSeriesK` (ReconComplex.lean:125) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `contDiff_waveSineSeriesK` (ReconComplex.lean:144) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `iteratedDeriv_waveSineSeriesK` (ReconComplex.lean:161) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK_zero_eq` (ReconComplex.lean:172) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK_zero_apply` (ReconComplex.lean:178) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `waveSineSeriesK_pi` (ReconComplex.lean:183) | PASS | Proved at its stated type; source premise or technical input as described above. |
| w0n:recon-bounded complex | `integral_waveSineSeriesK_mul_sineMode` (ReconComplex.lean:191) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection / norm helpers | `waveEvenAbs_weighted_eq` (SelectionCore.lean:31) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection / norm helpers | `waveTripleConv_weighted` (SelectionCore.lean:51) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection / norm helpers | `waveSel_norm_step` (SelectionCore.lean:73) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `waveSelCount` (SelectionOneSided.lean:32) | PASS | Literal definition; classification above. |
| selection(a) / algebraic helpers | `waveSelSum` (SelectionOneSided.lean:38) | PASS | Literal definition; classification above. |
| selection(a) / algebraic helpers | `waveSelCount_nonneg` (SelectionOneSided.lean:41) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `wave_rpow_neg_half_prod` (SelectionOneSided.lean:44) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `wave_isEll_iff_summable` (SelectionOneSided.lean:56) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `wave_ellTsumNorm_eq` (SelectionOneSided.lean:66) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `waveSel_oneSided` (SelectionOneSided.lean:71) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `waveSelSum_smul_left` (SelectionOneSided.lean:229) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `waveSelSum_smul_mid` (SelectionOneSided.lean:235) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `waveSelSum_smul_right` (SelectionOneSided.lean:241) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `waveSelSum_add_left` (SelectionOneSided.lean:247) | PASS | Generic summability inputs; source instances provided by waveSel_oneSided. |
| selection(a) / algebraic helpers | `waveSelSum_add_mid` (SelectionOneSided.lean:256) | PASS | Generic summability inputs; source instances provided by waveSel_oneSided. |
| selection(a) / algebraic helpers | `waveSelSum_add_right` (SelectionOneSided.lean:265) | PASS | Generic summability inputs; source instances provided by waveSel_oneSided. |
| selection(a) / algebraic helpers | `waveSelSum_swap_left_mid` (SelectionOneSided.lean:275) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(a) / algebraic helpers | `waveSelSum_swap_mid_right` (SelectionOneSided.lean:292) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) | `waveSelTwo` (SelectionTwoFinal.lean:28) | PASS | Literal definition; classification above. |
| selection(b) | `waveTwoMaj_pnat` (SelectionTwoFinal.lean:31) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) | `waveTwoMaj_bound` (SelectionTwoFinal.lean:36) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) | `waveSel_twoSided` (SelectionTwoFinal.lean:50) | PASS | Exact convergence/membership/64 M K² bound; not two-sided algebraic exports (F2). |
| selection(b) majorant | `waveTwoMaj` (SelectionTwoMaj.lean:26) | PASS | Literal definition; classification above. |
| selection(b) majorant | `waveTwoMaj_nonneg` (SelectionTwoMaj.lean:29) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) majorant | `waveTwoMaj_neg` (SelectionTwoMaj.lean:32) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) majorant | `waveTwoMaj_zero` (SelectionTwoMaj.lean:40) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) majorant | `waveJap_of_ne_zero` (SelectionTwoMaj.lean:42) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) majorant | `waveTwoWeight_of_ne_zero` (SelectionTwoMaj.lean:48) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) majorant | `waveTwoMaj_weighted` (SelectionTwoMaj.lean:53) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSelCountZ` (SelectionTwoSided.lean:28) | PASS | Literal definition; classification above. |
| selection(b) reindexing | `waveSelSumZ` (SelectionTwoSided.lean:33) | PASS | Literal definition; classification above. |
| selection(b) reindexing | `waveSign_mul_sign` (SelectionTwoSided.lean:37) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSign_not` (SelectionTwoSided.lean:41) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSignZEmb` (SelectionTwoSided.lean:45) | PASS | Literal definition; classification above. |
| selection(b) reindexing | `waveSignZEmb_injective` (SelectionTwoSided.lean:49) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSign_exists` (SelectionTwoSided.lean:59) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSignZEmb_surj` (SelectionTwoSided.lean:69) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSignZEmb_ne_zero` (SelectionTwoSided.lean:76) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSelCountZ_emb` (SelectionTwoSided.lean:83) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSelCountZ_neg` (SelectionTwoSided.lean:98) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `abs_waveSign_mul_cast` (SelectionTwoSided.lean:110) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveAbsPNat` (SelectionTwoSided.lean:115) | PASS | Literal definition; classification above. |
| selection(b) reindexing | `waveSelCountZ_abs` (SelectionTwoSided.lean:117) | PASS | Proved at its stated type; source premise or technical input as described above. |
| selection(b) reindexing | `waveSelSumZ_pointwise` (SelectionTwoSided.lean:135) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriCoords` (TriLp.lean:37) | PASS | Literal definition; classification above. |
| trilinear(i) construction | `waveTriCoords_isEll` (TriLp.lean:41) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriCoords_summable` (TriLp.lean:47) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux` (TriLp.lean:54) | PASS | Literal definition; classification above. |
| trilinear(i) construction | `waveTriAux_apply` (TriLp.lean:58) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `coeffW_waveTriAux` (TriLp.lean:63) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_unique` (TriLp.lean:69) | PASS | Uniqueness given full defining coefficients; existence constructed separately. |
| trilinear(i) construction | `waveTriAux_norm_le` (TriLp.lean:75) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriCoords_add_left` (TriLp.lean:89) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriCoords_add_mid` (TriLp.lean:102) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriCoords_add_right` (TriLp.lean:115) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriCoords_smul_left` (TriLp.lean:127) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriCoords_smul_mid` (TriLp.lean:137) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriCoords_smul_right` (TriLp.lean:147) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_add_left` (TriLp.lean:157) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_add_mid` (TriLp.lean:164) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_add_right` (TriLp.lean:171) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_smul_left` (TriLp.lean:178) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_smul_mid` (TriLp.lean:184) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_smul_right` (TriLp.lean:190) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriSeq_swap_left_mid` (TriLp.lean:198) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriSeq_swap_mid_right` (TriLp.lean:215) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_swap_left_mid` (TriLp.lean:232) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_swap_mid_right` (TriLp.lean:238) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) construction | `waveTriAux_swap_left_right` (TriLp.lean:244) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) | `waveTriML` (TriML.lean:29) | PASS | Literal definition; classification above. |
| trilinear(i) | `waveTriML_apply` (TriML.lean:72) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) | `waveTriML_apply'` (TriML.lean:75) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) | `waveTriML_norm_le` (TriML.lean:79) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) | `coeffW_waveTriML` (TriML.lean:83) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) | `waveTriML_unique` (TriML.lean:90) | PASS | Uniqueness given full defining coefficients; existence constructed separately. |
| trilinear(i) | `waveTriML_swap_left_mid` (TriML.lean:104) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) | `waveTriML_swap_mid_right` (TriML.lean:109) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(i) | `waveTriML_swap_left_right` (TriML.lean:114) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(ii–iv) | `waveTrilinear_eq_waveTriSeq` (TriProps.lean:36) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(ii–iv) | `waveTriSeq_ofReal` (TriProps.lean:50) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(ii–iv) | `waveTriSeq_conj` (TriProps.lean:60) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(ii–iv) | `waveTriML_complexify` (TriProps.lean:70) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(ii–iv) | `waveTriML_conj` (TriProps.lean:82) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(ii–iv) | `waveTriML_embed` (TriProps.lean:94) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(ii–iv) | `waveCubic_coeffW_eq_coeffW_triML` (TriProps.lean:106) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear(ii–iv) | `cubicGrad_eq_triML_div` (TriProps.lean:116) | PASS | Exact manifested frozen definition; no substituted gradient. |
| trilinear / w0n:cubic-bound complex | `waveTriCoef` (TriSeq.lean:31) | PASS | Literal definition; classification above. |
| trilinear / w0n:cubic-bound complex | `wave_sqrt_pnat_le_sqrt_lam` (TriSeq.lean:35) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear / w0n:cubic-bound complex | `waveTriCoef_bound` (TriSeq.lean:39) | PASS | Proved at its stated type; source premise or technical input as described above. |
| trilinear / w0n:cubic-bound complex | `waveTriSeq` (TriSeq.lean:71) | PASS | Literal definition; classification above. |
| trilinear / w0n:cubic-bound complex | `waveTri_oneSided` (TriSeq.lean:76) | PASS | Proved at its stated type; source premise or technical input as described above. |

## Frozen input hashes

Hashes were recorded before findings and rechecked at closeout. The commit pins the complete branch diff and
all inherited sources; the table additionally pins the package, assigned raw blueprint, handoff and Wave anchors.

| File | SHA256 |
|---|---|
| `KAM/Wave/Cubic/CubicMap.lean` | `a9d143156c04e29f8eead8412852b42ce74bfed4ee78b59580bdada5f39d3ba4` |
| `KAM/Wave/Cubic/GradIdentity.lean` | `33497bff6eb84e03b567b7ffe361b24b0db2431b84d84f96a1d8156b2203e3f2` |
| `KAM/Wave/Cubic/TriLp.lean` | `05673377af9acc6603b2e363f3eb09afadc534a08d7cfd92de46012060e26ee3` |
| `KAM/Wave/Cubic/ReconComplex.lean` | `1dd46dc64150014410a38035451d2cd861c4c26cf059a1812ea1de7788c0d2b3` |
| `KAM/Wave/Cubic/SelectionTwoSided.lean` | `a2ab0a3e6bf3bd7c8593b24281c981e044deeea268d31b0ebcf71eb3a21517d6` |
| `KAM/Wave/Cubic/SelectionTwoMaj.lean` | `07af18ccf9ae9b5a4f963ee68ac526720ad55c2f4e312658ce090775fe88278a` |
| `KAM/Wave/Cubic/CubicDeriv.lean` | `534c6ac57dfab03687ccfcde62ce0d78c99057e9aed87f52a2ace315ea333c98` |
| `KAM/Wave/Cubic/HamField.lean` | `055b9a203890179a87462cf3a4e2be92a77d58f9fc88d0250ff481c532621ff8` |
| `KAM/Wave/Cubic/HamHamiltonian.lean` | `6fd1414872206763421ec5bc1d313cebc1ba6c4c75a7385be68ed6fc68d039ff` |
| `KAM/Wave/Cubic/SelectionTwoFinal.lean` | `d69758169517d537a40f50e1afcedcf8f3a861fd2a7953ffe2cc362d31445238` |
| `KAM/Wave/Cubic/TriSeq.lean` | `0d56f42fa2197706232ea5006d946c65c06b593f64a4c18968e020f7293a841e` |
| `KAM/Wave/Cubic/TriML.lean` | `3653395e41a10119af06758d0c7c1232fef646c6396c249ab13ad68be3a6ed46` |
| `KAM/Wave/Cubic/TriProps.lean` | `f8e644d0d3b9833077cb157951ac45e7581c685e69b79ee95c728159846b01fb` |
| `KAM/Wave/Cubic/FrozenForm.lean` | `bacd285c80c1338a44f31fb7adb009d041be332f6fa14e1254eb6b442f869b04` |
| `KAM/Wave/Cubic/SelectionCore.lean` | `373df75eb84d6fc154095ff5356199218ba643e50cc3d547f151598f1300ca05` |
| `KAM/Wave/Cubic/GradLp.lean` | `8607f4f1c090a70136d8453097a1cfaa97a2621deeac509a6d7d116911aea67a` |
| `KAM/Wave/Cubic/SelectionOneSided.lean` | `dac2e0391322bf707a9138db237c1d58071a14a5aae6c79a73dbdb6d1d4d4414` |
| `blueprint-W/parts/w1-sequences.tex` | `b27ab7134c188941198e547c4577e3263e0e5f618a41ebd6983ac48b8b07e796` |
| `blueprint-W/parts/w0-normalization.tex` | `83f7f2ebcbf97613e30433401435e374f2731749fd9ef8b44ba2ac9b7697505b` |
| `docs/tracks/W/audits/W1-CUBIC-handoff.md` | `c33d1ee0b519283a1ef3d28b0c9769057946bf367f90f791a4bac6632bc859e2` |
| `KAM/Frozen/Wave/Defs/CubicGrad.lean` | `bd4cba1cda91a3094fb53c9c4a830d9772c592aa8dde4b514254f13efb2064f1` |
| `KAM/Frozen/Wave/Defs/WaveSpace.lean` | `30ecc30f38ca120e2b4318453715629eb140aa2cb01225aa08f7116cdf9be301` |
| `KAM/Frozen/Wave/Defs/ReconV.lean` | `806e6a22726d296c11ef1c5aad0959a80445e463f3f7a864089cade9f29f3181` |
| `KAM/Frozen/Wave/Defs/Lam.lean` | `097b70740bbedd0463d2e0ffb98e99bf508f81207b8370ac05ddc91aa3e05f81` |
| `KAM/Frozen/Wave/Defs/LinearTorus.lean` | `8291b57c0d2a1625ae0353acf5d0acbcc10aff2a1302d80b6fa18de264db7acd` |
| `KAM/Frozen/Wave/Defs/SineMode.lean` | `708e6e5d2d878d13e87acb6f2e2b4a057be17a33f9999b417cbaf75bac555263` |
| `KAM/Frozen/Wave/Defs/IsClassicalSolution.lean` | `287cbac02095afbaeda096b6864ceadeef2ecdf1ccec353bfa870901438a524e` |
| `KAM/Frozen/Wave/Defs/IsAnalyticTorusEmbedding.lean` | `6fb4f36f9df08069dbdbb555bba9e758c607a58f34327b975b55a13ed108b4ef` |
| `KAM/Frozen/Wave/Defs/Coeff.lean` | `c30ede55986dd8f88f1b85544a38874a2aacb0d7f4bd072d9e4a486b72ab2622` |
| `KAM/Frozen/Wave/Defs/ReconU.lean` | `59f629f4ba2fd487e024d1a2564241010d2884e81ddc33a12a2e58f5da1a3245` |
| `KAM/Frozen/Wave/Defs/EllWeight.lean` | `88c0329883e40f8c1c852233a39eaa92482bf4b3a99041e5595e9b277d7e8722` |
| `KAM/Frozen/Wave/Theorems/Nlw2.lean` | `9ce65519e3108c55e50565b268e7138d5a47ed68fbfade07166d0641b2e2dde6` |

## Independent verification receipts

All commands below ran in `/root/code/KAM-inp-wph`. `$mods` abbreviates exactly these 17 module arguments:

```text
KAM.Wave.Cubic.CubicDeriv KAM.Wave.Cubic.CubicMap KAM.Wave.Cubic.FrozenForm
KAM.Wave.Cubic.GradIdentity KAM.Wave.Cubic.GradLp KAM.Wave.Cubic.HamField
KAM.Wave.Cubic.HamHamiltonian KAM.Wave.Cubic.ReconComplex KAM.Wave.Cubic.SelectionCore
KAM.Wave.Cubic.SelectionOneSided KAM.Wave.Cubic.SelectionTwoFinal KAM.Wave.Cubic.SelectionTwoMaj
KAM.Wave.Cubic.SelectionTwoSided KAM.Wave.Cubic.TriLp KAM.Wave.Cubic.TriML
KAM.Wave.Cubic.TriProps KAM.Wave.Cubic.TriSeq
```

1. Targeted gated build (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wph $mods
   ```

   Output starts `[inp-gate] slot 2 acquired 21:40:24 ...`; final output:
   `Build completed successfully (3307 jobs).`
   This was the permitted warm targeted validation, with replayed warnings; not a clean rebuild.
   Warnings are deprecations (`if_true`, `if_false`, `if_pos`, `if_neg`) and unused simp arguments;
   no build error, default-heartbeat failure, or proof escape was reported.

2. Kernel replay, **one invocation**, exit **0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose $mods
   ```

   Complete output (17 lines):

   ```text
   replaying KAM.Wave.Cubic.TriSeq
   replaying KAM.Wave.Cubic.TriProps
   replaying KAM.Wave.Cubic.TriML
   replaying KAM.Wave.Cubic.TriLp
   replaying KAM.Wave.Cubic.SelectionTwoSided
   replaying KAM.Wave.Cubic.SelectionTwoMaj
   replaying KAM.Wave.Cubic.SelectionTwoFinal
   replaying KAM.Wave.Cubic.SelectionOneSided
   replaying KAM.Wave.Cubic.SelectionCore
   replaying KAM.Wave.Cubic.ReconComplex
   replaying KAM.Wave.Cubic.HamHamiltonian
   replaying KAM.Wave.Cubic.HamField
   replaying KAM.Wave.Cubic.GradLp
   replaying KAM.Wave.Cubic.GradIdentity
   replaying KAM.Wave.Cubic.FrozenForm
   replaying KAM.Wave.Cubic.CubicMap
   replaying KAM.Wave.Cubic.CubicDeriv
   ```

3. Exhaustive axiom census, exit **0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/WphAxioms.lean
   ```

   The temporary probe imports all 17 modules and executes `#print axioms KAM.Wave.<name>` for every one
   of the 196 names in the complete declaration ledger (including all 163 theorem/lemma exports and all
   33 definitions/abbreviations). Output has exactly 196 results, with no missing declaration:

   ```text
   189 declarations: depends on axioms: [propext, Classical.choice, Quot.sound]
   waveSign_mul_sign, waveSign_not, waveAbsPNat: depends on axioms: [propext]
   waveSignZEmb_injective, waveSign_exists, waveSignZEmb_surj: depends on axioms: [propext, Quot.sound]
   waveSignZEmb: does not depend on any axioms
   ```

   In particular, each of the 37 main declarations named in the handoff independently reports exactly
   `[propext, Classical.choice, Quot.sound]`. No sorryAx, project axiom or additional trust input appears.

4. Exact-type and producer-to-consumer probes, exit **0**, **empty output**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/WphExact.lean
   ```

   Four examples were elaborated: (a) the frozen cubicGrad **integral body**, with the exact trilinear quotient
   on the right, proved directly by `cubicGrad_eq_triML_div`; (b) the literal frozen clause-(4) derivative
   conjunction iff the componentwise `embedCLM` derivative equals `waveXw`, with only `DifferentiableAt`,
   proved by `frozen_invariance_iff_waveXw`; (c) the complex coefficient integral, where summability is supplied
   by `waveEllK_summable_pow_mul ha hc 0`, not assumed; (d) the complex iterated derivative bound, supplying
   `iteratedDeriv_waveSineSeriesK` and `waveSineSeriesK_norm_le` at the same source input and weight.
   The two composed complex probes are reproduced here:

   ```lean
   example {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℂ} (hc : IsEll a p c) (l : ℕ+) :
       ∫ x in (0 : ℝ)..Real.pi, waveSineSeriesK 0 c x * (sineMode l x : ℂ) = c l := by
     have hs := waveEllK_summable_pow_mul ha hc 0
     simp only [pow_zero, mul_one] at hs
     exact integral_waveSineSeriesK_mul_sineMode hs l

   example {a p : ℝ} (ha : 0 < a) {c : ℕ+ → ℂ} (hc : IsEll a p c) (k : ℕ) (x : ℝ) :
       ‖iteratedDeriv k (waveSineSeriesK 0 c) x‖ ≤
         Real.sqrt (2 / Real.pi) * (waveEllMajorant a p k * ellTsumNorm a p c) := by
     rw [iteratedDeriv_waveSineSeriesK ha hc, zero_add]
     exact waveSineSeriesK_norm_le ha hc k x
   ```

5. Public short-name scan, exit **0**:

   ```sh
   python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-wph $mods
   ```

   Exact output: `short-name check OK (no reused public short name)`.

6. Slim-worktree lint, exit **0**:

   ```sh
   LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wph
   ```

   Complete output:

   ```text
   check_lean_modules: PASS (1726 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (158 frozen declarations)
   ```

   No expected-stale-root exception was needed. The wrapper runs `scripts/lint_sources.sh` with the prescribed
   slim overlay; it builds nothing. Module headers, source escape/override scans, provider/draft/root quarantine,
   line caps, generated root consistency, errata rendering, frozen guards and ABI checks pass.
   Maximum package file size is 309 lines (SelectionOneSided); all 17 files have the required module structure
   and exposed noncomputable public sections.

7. Scope/diff checks:

   ```sh
   git diff --check inp...HEAD
   git diff --check
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   ```

   All exit **0**, all output **empty**. The only generated-source delta is the authorized 17 new Cubic imports
   in `KAM/Root/Wave.lean`; no frozen/manifest/README/root-facade edit occurs.
   The two assigned blueprint files are also byte-identical to current `inp` (`git diff inp -- <both files>` empty).
   Transitive import scan: 56 KAM modules, nine frozen definition modules, all SEALED with matching manifest
   full-file hashes; zero provider modules, zero DRAFT_SORRY imports. All snapshot-v1 file hashes were rechecked
   after verification and are unchanged.

## Errata, deviations and closeout

No new suspected defect in a pinned published source is asserted. The source's √2 even-extension correction and
negative linear force are preserved; this audit does not reopen the previously recorded published-source errata.
No blueprint mathematical contradiction was found in the implemented proofs. F1/F2 are omissions of required
blueprint conclusions, not proposed source corrections. The stale implementation docstring name is N5.

Accepted implementation forms: RCLike generalization; pointwise instead of global differentiability in the
coordinatewise bridge; unrestricted-real spatial convergence/bounds (stronger than the closed interval);
weighted lp representatives rather than duplicate weighted Banach carriers; and literal guarded integer sums
implementing the source's punctured indices. Remaining differences are N1–N4 and F1/F2, not silently repaired.

Only this report is an intended repository edit. All auditor-created probes, inventories, snapshots and logs were
confined to `.lake/abi-scratch/` and removed after their evidence was transcribed here. No source, manifest,
generated file or git state was changed. No worker receipt was substituted for the independent reruns above.

Closeout: mechanical package validation PASS; frozen identification and X^w specialization PASS;
assigned complex-carrier attachments PASS with N2; full selection and gradient-identity node completion FAIL
until F2/F1 are supplied or explicitly reassigned by the orchestrator. No whole-subsection, downstream-consumer,
provider, frozen nlw2, or campaign theorem closure is certified.
