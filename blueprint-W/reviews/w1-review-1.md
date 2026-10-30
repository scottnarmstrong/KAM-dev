# W1 independent review, round 1

**Verdict: REVISE.** The frozen-object identifications and cubic estimates pass. The claim to supply all W4 analytic inputs does not yet pass: P96-K p. 127 uses an operator-valued Fourier square-sum estimate which is false, whereas W1 proves only the valid Hilbert-valued estimate. There are also missing guards on quantitative analytic lemmas, a Fourier-shift sign error, and two incorrect Mathlib names. None of these findings refutes a frozen Wave declaration.

Reviewer provenance: **GPT-6.1-Sol (codex-3), reasoning effort medium**, independent, refute-first. I did not write or change W1.

## Reviewed state and checks

- Commit: `a13f96f730361eb3a8a6177ec3fc8239acfe24dd`; reviewed `blueprint-W/parts/w1-sequences.tex`, **944 lines, 69,385 bytes**, exported by `git archive` into `.drafts/W/review-w1/`. All blueprint line locators below refer to that export, not subsequent writer edits.
- Read the two review briefs, writer conventions, AGENTS.md, PLAN/DECISIONS, blueprint-W PLAN/preamble/W0 conventions/W0 normalization/headline, W-STATEMENTS and W-BP0-handoff. The older statement/design documents still say draft; current main D41 and the frozen Lean control.
- Checked authoritative main `/root/code/KAM/KAM/Frozen/Wave/Defs/*.lean` and `Theorems/Nlw2.lean`, including the literal `HasDerivAt` clauses (4), analyticity and reconstruction clauses (3)/(5). Main was `73534ef0bf7a44efcc0ca37ac11cbe4f77ef0f2d` when inspected. These are statement checks, not proof-body certification.
- Read committed W3, especially its W1 inputs/requests, explicit analytic flow construction, and interface to W4–W6. W2 and W4–W8 are not written parts at this commit; their coverage is checked against PLAN, frozen consumers, W3's interface, and P96-K, not against imaginary completed proofs.
- Read pinned P96-W pp. 277–284, 290, 294–295 (PDF 10–17, 23, 27–28); P96-K pp. 120–124, 126–130, 145–147 (PDF 3–7, 9–13, 28–30); KP96 author pp. 12–13, 16, 31–32. Inspected page images of P96-K pp. 127 and 147 because the text layer loses crucial formulas.
- Checked Mathlib sources at `56a005855ea17e0b0958f73ec801ae140b0a1679`. No direct Lean probes or builds were run: the review brief explicitly forbids builds. The mandatory repository lint internally attempted its ABI Lean probe, with the failure and deviation recorded below. No new Lean results were introduced, so a new `#print axioms` inventory is inapplicable; the frozen `nlw2` body remains `by sorry` in the inspected source.
- Pristine export build: `latexmk -pdf -interaction=nonstopmode blueprint.tex`, **exit 0**, **41 pages**, **zero `^!` errors and zero final undefined-reference warnings**. Read the rendered PDF via `pdftotext -layout`; W1 occupies pp. 12–27 (W3 starts on p. 27).
- Repository lint: `scripts/lint_sources.sh`, **exit 1**. It printed `check_lean_modules: PASS (1464 Lean files, 0 comparator configurations)` and `FROZEN-ANCHOR GUARD OK`, then its internal ABI probe failed with `error: unknown module prefix 'KAM'` in this worktree's `.lake/abi-scratch/`. The subprocess also materialized pinned dependencies in this worktree's `.lake`. This is a tooling deviation from the brief's main-only Lean-probe location and report/scratch-only writes, caused by the required lint wrapper; no direct probe was launched, no library build was run, and no repair or retry was attempted. This lint run is **not a PASS**.
- Numerical checks: `python3 .drafts/W/review-w1/checks.py`, exit 0; results below. These supplement the analytic recomputations, not replace them.

## Findings

| ID | Location | Severity | Finding and evidence | Exact proposed fix |
|---|---|---|---|---|
| W1-R1 | Opening coverage claim, lines 7–11; `bpW:w1:fourier-l2`, `bpW:w1:schur`; ledger W4 | **major** | The two lemmas do not justify the operator-valued Fourier summation used by P96-K p. 127. `fourier-l2` correctly assumes a **Hilbert** target. Bounded operators on infinite-dimensional ℓ² with operator norm are not such a target. The source explicitly says “with operator-valued coefficients” and “we have, as before” before its weighted square-sum bound. The diagonal counterexample below disproves that bound even in finite rank. The entrywise Schur estimate does not repair the Fourier summation. | Add a Banach-valued coefficient estimate `‖Â_k‖ ≤ M exp(-2π|k|₁s)` and an explicit lattice-sum estimate after a positive strip loss; carry these through the operator homological solve **and its parameter differences**, recomputing the powers/constants. Alternatively prove an appropriate row/column estimate before taking operator norms. Record the p. 127 source defect and assign the changed estimate to W4. Do not claim the source's operator square-sum bound follows from W1. |
| W1-R2 | `bpW:w1:cauchy`, lines 698–710; `bpW:w1:uniform-limit`, lines 716–719; supremum convention, line 694 | **major** | Radius positivity and bounded-supremum guards are missing. The first Cauchy statement does not assume `r>0`: for `f(z)=z`, `v=0`, `r=0`, `M=0`, its hypothesis is vacuous and its conclusion is `1≤0`. The subsequent assertions need `δ>0`. Uniform convergence does not imply `f` bounded on `U`; taking every `f_k=f=id` on ℂ gives a valid unbounded uniform limit. Its real-valued supremum norm is not available without a boundedness guard (and Lean's unbounded real `sSup` cannot be used as an analytic norm). | Bind `0<r` and `0<δ` in the respective claims. Keep the qualitative uniform-limit theorem without a boundedness hypothesis; state its quantitative derivative estimate separately under `∀z∈U, ‖f z‖≤M` with `M≥0` (or an explicitly guarded finite supremum). Guard every real supremum subsequently used as a norm. |
| W1-R3 | `stepW:w1:shift`, lines 867–874 | **minor** | The shifted Fourier coefficient has the wrong sign. With the displayed coefficient convention, the coefficient of `x↦u(x+iη)` is `û_k exp(-2π k·η)`, not the positive exponential printed twice. Test `u(z)=exp(2πiz)`. The final norm estimate is true because both signs of η are available. | Replace both shifted exponential factors by the negative sign; in `orthants` choose `η=-s'ε`, or explicitly relabel `η↦-η` before using the positive exponent. |
| W1-R4 | External facts, lines 70, 81; reconstruction proof line 649 | **minor** | Not every cited Mathlib name exists. `lp.instCompleteSpace` is not the ℓᵖ completeness instance; `lp.completeSpace` is (`Analysis/Normed/Lp/lpSpace.lean:1359`). There is no declaration or exact-token occurrence of `AnalyticAt.comp2` anywhere in the checked Mathlib tree. | Use `lp.completeSpace`. For the inner-product composition use `ContinuousLinearMap.analyticAt_bilinear` for the uncurried bilinear map, then `AnalyticAt.comp` with `AnalyticAt.prod` of the two component maps. Replace both `comp2` citations. |
| W1-R5 | `bpW:w1:flow`, `stepW:w1:picardholo`, lines 787–791 | **minor** | Differentiation under the parameter integral needs measurability of the operator-valued derivative; the displayed dominating norm alone is insufficient. The definition of holomorphic only assumes complex Fréchet differentiability, and the external list has no general theorem giving continuity of its derivative on Banach domains. This is a proof-detail obligation, not a need for holomorphic⇒analytic. | Add an elementary Banach-domain holomorphic derivative-continuity lemma from one-variable Cauchy integrals on complex lines, or prove the required derivative measurability by uniformly controlled difference quotients along the Picard curves. Cite that step and the local neighborhood domination when applying `hasFDerivAt_integral_of_dominated_of_fderiv_le`. |

### W1-R1: exact source counterexample and consumer obligation

Fix a strip width `s>0` and let `H=ℓ²(ℕ+)`. For any integer `N`, define a finite-rank, entire operator family (period one, depending only on the first angle)

`A_N(θ)e_j = exp(-2π j s) exp(2π i j θ₁)e_j` for `1≤j≤N`, and zero otherwise.

On `T_s⊂ℂⁿ`, `sup ‖A_N(θ)‖op=1`. Its only nonzero coefficients are at `k=(j,0,…,0)`, with `‖Â_k‖op=exp(-2π j s)`. Consequently

`Σ_k ‖Â_k‖op² exp(4π|k|₁s) = N`.

Choose `N>2ⁿ`. This disproves the source's claimed bound with constant `2ⁿ`, even if its printed RHS is corrected to the square of the supremum. For `n=2`, `N=8` already gives `8>4`. These coefficients can also be realized as the mixed normal Hessian of a quadratic Hamiltonian, rather than an unrelated operator family. If reality is required, replace each exponential by the corresponding normalized cosine; the same unbounded-in-N contradiction remains, with two Fourier coefficients per diagonal entry. Passing between the weighted input/output Hilbert spaces is by exactly W1's diagonal transports, so the one-smoothing target does not rescue the claimed estimate.

This is a **suspected pinned-source defect** at P96-K p. 127 (PDF 10), in the display following “Expanding R̃ into its Fourier series with operator-valued coefficients R̃_k we have, as before”. It is independent of the A.4 issue the writer recorded. It does not by itself refute Theorem A: the homological estimate must be repaired and its constants/strip powers propagated.

A concrete safe replacement available from the same contour proof is the Banach-valued bound

`Σ_k ‖Â_k‖ exp(2π|k|₁(s-σ)) ≤ M coth(πσ)ⁿ`, `0<σ<s`.

Polynomial divisor weights require the corresponding weighted lattice sums. Their estimates, and the Lipschitz differences of the inverse divisors, remain explicit W4 obligations. This review does not certify that the published final smallness exponents survive unchanged.

## Frozen objects and constants: recomputations that passed

### Weighted coordinates and conclusion (4)

The authoritative definitions are exactly

`WaveSpace = lp ℝ 2 × lp ℝ 2`, product **max** norm; `coeff y j = y_j / ω_{1,1}(j)`.

Write `S=D_(1/j)`, `D=D_(λ_j/j)`, and `Gʷ(y)_j=ω_{1,2}(j)cubicGrad(m,hm,y,j)`. The weaker-target field is

`Xʷ(y,y') = (Dy', -Dy-S²Gʷ(y))`.

Indeed its entries are `e^j(λ_j coeff(y')_j, -λ_j coeff(y)_j-cubicGrad(y)_j)`. The inclusion `E_{1,1}→E_{1,0}` has representative `(S,S)`. Therefore

`(S,S)(DK(θ)ν) = Xʷ(K(θ))`

is precisely the pair of frozen coordinate `HasDerivAt` assertions, **provided K is differentiable at θ**, as W1 assumes. Compose with `t↦θ+tν`, apply each bounded coefficient functional, use uniqueness of the scalar derivative, and use injectivity of the coefficient map for the converse. There is no illicit promotion from mere coordinate differentiability to Banach differentiability. Clause (3)'s `AnalyticOnNhd` supplies the guard for the actual headline consumer. No extra `2π` belongs in this equation: ν is already the period-one frequency.

`Xʷ` is a bounded-coordinate polynomial representing a field with a weaker target; it is not a claim that the original unbounded linear field maps `E_{1,1}` into itself. This distinction is correctly retained.

### Trilinear identity, smoothing, gradient

The quartic coefficient is `g_ijkl=∫φ_iφ_jφ_kφ_l`. The coefficient in the trilinear sum is

`c_ijkl = g_ijkl / √(λ_iλ_jλ_kλ_l)`.

The signed sine-product identity bounds it by the selection-rule majorant with `M=1/(2π)` because `λ_j≥j`. For the even extensions `x_i=|q_|i||/√|i|`, `‖x‖_{a,p+1/2}=√2 ‖q‖_{a,p}`. The triple convolution is even, so positive-index restriction saves `1/√2`. Thus

`‖T_c(q,q',q'')‖_{a,p+1} ≤ (M/√2) K_s² (√2)³ ∏‖q‖ = 2M K_s² ∏‖q‖`, `s=p+1/2≥1`.

It gives exactly `C_*=K_s²/π`; at `p=1`, `C_*=8(1+2ζ(3))/π=8.6685046259…`, independent of positive m and nonnegative a. The two-sided bound `64 M K_s²` is loose but valid: each symmetrized majorant costs at most 2, and summing eight sign patterns costs 8. No even-restriction saving was incorrectly used there.

The frozen integral expands to this triple sum by uniform absolute convergence of `reconU` on the compact integration interval. Therefore

`cubicGrad m hm y l = T^{1,1}_ℝ(y,y,y)_l / ω_{1,2}(l)`

is correct, including the output weight, the `√λ_l` denominator, and the absence of an extra factor 3 or 4. The numerical finite-support check at `m=1.7`, four input modes and twelve output modes agrees with direct Simpson integration to **4.34e-19**. The integral identity for general coefficients is asserted only for `a>0`, where W0's reconstruction proof applies; the abstract convolution map also exists at `a=0`.

The derivative bounds `3C_*‖y‖²`, `6C_*‖y‖`, the cubic difference bound, and the unweighted pairing identity all follow by multilinearity. The ℓ² Riesz gradient is `Gʷ(y)_j/(ω_{1,1}(j)ω_{1,2}(j))`; W1 correctly distinguishes it from the physical cubic gradient.

### Linear flow, strip and KAM constants

- `λ_j/j∈(1,√(1+m)]`; positive powers attain the claimed multiplier norm at `j=1`, negative powers have supremum 1. The real linear flow preserves the squared Hilbert sum of q/p norms. Its max-norm bound is exactly `√2`, and is sharp: take equal q/p supported at one mode and `λ_jt=π/4`. The numerical ratio is `1.414213562373095`.
- `x=2πθ` gives the geometric strip width `s=s_K/(2π)` and the Fourier square weight `exp(4π|k|₁s)=exp(2|k|₁s_K)`. These are geometric widths, not a second conversion of sequence weight a. The θ velocity is `ẋ/(2π)`. W4–W6 must also retain the pulled-back symplectic form `2π Σdθ_i∧dy_i + Σdu_j∧dv_j` if y is unchanged: equivalently both canonical tangential Hamiltonian equations in θ/y have the `1/(2π)` factor when expressed through the pulled-back Hamiltonian.
- P96-K uses the sum `‖u‖+‖v‖`; frozen WaveSpace uses the max. The comparison is between factors 1 and 2, distinct from the `√2` Hilbert-sum comparison. The domain margin in `kam-domain` is valid with `0<σ≤1`; it leaves strict room in all three defining inequalities.
- `λ_j-j=m/(λ_j+j)≤m/(2j)` gives exactly W1's spectral tail and Lipschitz constants. With `d=1`, `δ=-1`, `p̄=p+1`, `p-p̄=δ` and `δ<d-1` are correct. After reindexing normal modes by `j↦j+2`, the fixed asymptotic sequence must be `j+2`, not j with a nondecaying term left in the tail. W1 allows this; W3 additionally records the shifted-weight equivalence. Zero-padding the first two entries is an encoding on the normal subspace, not permission to add two zero-frequency normal oscillators to Assumption A.
- Schur's row/column calculation gives `Λ=π/√3=1.8137993642…`, combined diagonal/off-diagonal constant `1+Λ=2.8137993642…<3`. The weighted matrix ratios are preserved. This estimate passes independently of the Fourier problem in W1-R1.

## P96-K Lemma A.4 and the proposed repair

The p. 147 image says V is an “open domain”, X is “C¹ on V and Lipschitz on Π”, and assumes the parameter flows map `U×Π` into V for `|t|≤1`. It does not assert convexity of V. Its second estimate invokes `‖DX‖_V ‖Δφ^s‖_U` to bound the difference of the field at two parameter-dependent trajectory points. A derivative bound controls this difference along a segment only when that segment is in the derivative-controlled domain. Merely knowing the two points lie in V is insufficient. The writer has correctly identified this missing justification.

The repair in W1 is valid: for each fixed starting point w, **both** parameter trajectories and every Picard iterate lie in the same convex `B(w,δ)`, because displacement is at most `|t|M<δ`. The `2δ` margin gives `‖DX‖≤M/δ=L` on that ball by Cauchy. This gives local existence/uniqueness through time ±1, derivative estimate `exp(L|t|)`, and parameter estimate

`‖φ^t_ξ(w)-φ^t_ζ(w)‖ ≤ |t| exp(L|t|) ‖X_ξ-X_ζ‖_V`.

The Picard factorial estimates and the uniform-limit argument do not use an infinite-dimensional holomorphic⇒analytic theorem. Subject to W1-R5's integral detail, they establish **holomorphy**, which is what is stated.

Two qualifications to the source-gap wording: failure to assume finite `‖DX‖_V` means the source estimate need not be a useful finite bound; it is not by itself a counterexample if infinite norms are allowed. The geometric segment issue is the substantive proof gap. Also A.4 has two displayed estimates, not estimates numbered “(i), (iv)” as W1's source line says. In the KAM use, the convex domains on pp. 129–130 and the quantitative smallness/margin estimates permit the repair; W5 must instantiate those inequalities in its chosen scaled norm, not merely cite A.4 on arbitrary open domains. No edit to a frozen object is indicated.

## Analyticity and Mathlib audit

The proposed avoidance of the infinite-dimensional implication is sound **for the advertised route**, with the preceding qualifications:

1. The cubic maps and quartic Hamiltonians have explicit finite multilinear power series, hence are analytic even on infinite-dimensional domains.
2. Reconstruction features have a **one-complex-variable** domain and Banach target. The normal convergence, one-variable holomorphy/analyticity theorem, real restriction and continuous bilinear pairing prove real analyticity of both frozen reconstructions, including their x-derivatives. The endpoint `derivWithin` identification is valid because `0<π` and `uniqueDiffOn_Icc` applies.
3. `holo-analytic-fd` is mathematically valid for **Banach-valued** maps. Track K's iterated Cauchy integral argument uses compactness of the **domain polydisc**, not finite-dimensional compactness of the target. Fubini, coefficient bounds and termwise integration work for complete F. For an explicit Lean step converting multi-index coefficients to `FormalMultilinearSeries`, group by total degree m: sums of coordinate-projection tensors have norm at most `binomial(m+n-1,n-1) M r^(-m)`. Their norm series converges at every `ρ<r`. This supplies the local Banach-valued `HasFPowerSeriesOnBall`. If claiming convergence on the closed radius-r polydisc, use the larger radius `r₁>r` from the cited margin step; the radius-r coefficient bound alone only proves absolute convergence inside. State `r>0` explicitly.
4. The real torus domain is finite-dimensional, so `torus-analytic` proves exactly the analyticity clause of the frozen embedding predicate. It does not claim its injectivity or immersion clauses.
5. W3 has its own explicit power-series flow construction. At the reviewed commit it expressly **does not consume W1's general holomorphic-flow lemma** for analytic Γ; its two-sided coordinates, weak symplectic form, Λ and sharper majorants are proved there. Those requests are not unpaid W1 dependencies. Its holomorphic remainder-field class is a deliberate interface to W4–W6, which must stay in that class rather than invoke an unproved general holomorphic⇒analytic bridge.

I checked the other named Mathlib facts against their declaration sites, not just approximate search matches. Apart from W1-R4, these exist with the relevant scope:

| Group | Verified declarations / source location |
|---|---|
| ℓ² | `lp.instInnerProductSpace`, `lp.inner_eq_tsum` in `Analysis/InnerProductSpace/l2Space.lean`; `memℓp_gen_iff`, `lp.norm_apply_le_norm`, `lp.norm_le_of_forall_sum_le`, `lp.hasSum_single` in `Analysis/Normed/Lp/lpSpace.lean`. Specialize p=2 and discharge its nonzero/finite-exponent conditions. |
| Series | `hasSum_zeta_two` in `NumberTheory/ZetaValues.lean` (ℕ sum, whose zero term is zero; reindex to ℕ+); `Real.summable_one_div_nat_rpow` in `Analysis/PSeries.lean`; `tsum_prod'` and `Summable.tsum_comm` are available for the appropriate summability hypotheses. |
| Analytic algebra | `ContinuousMultilinearMap.analyticAt`, `.cpolynomialAt` in `Analysis/Analytic/CPolynomial.lean`; `ContinuousLinearMap.analyticAt`, `.analyticAt_bilinear` in `Analysis/Analytic/Linear.lean`; `AnalyticAt.comp`, `.prod`, `.restrictScalars`, `.differentiableAt` in Composition/Constructions and Calculus/FDeriv/Analytic. `MultilinearMap.mkContinuous` and `ContinuousMultilinearMap.hasFDerivAt` also exist. |
| Complex analysis | `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` in `Analysis/Complex/Liouville.lean`; `DifferentiableOn.analyticOnNhd` in `CauchyIntegral.lean` and `TendstoLocallyUniformlyOn.differentiableOn` in `LocallyUniformLimit.lean` have **domain ℂ**, with Banach-valued targets; they do not assert the general Banach-domain implication. |
| Limits/integrals/ODE | `hasFDerivAt_of_tendstoUniformlyOn`, `hasFDerivAt_integral_of_dominated_of_fderiv_le`, `IsPicardLindelof`, `ODE_solution_unique`, `norm_le_gronwallBound_of_norm_deriv_right_le` exist in the cited UniformLimitsDeriv/ParametricIntegral and ODE files. The integral theorem requires integrability/measurability as well as domination. |
| Fourier/endpoints | `fourierBasis`, `tsum_sq_fourierCoeff` in `Analysis/Fourier/AddCircle.lean`; `UnitAddTorus.mFourierBasis` in `AddCircleMulti.lean`; `uniqueDiffOn_Icc` in `Analysis/Calculus/TangentCone/Real.lean`. The normalized Haar versus interval Lebesgue factor in the sine-completeness proof is correct. |

## Consumer disposition and remaining limits

- **W2:** W1 supplies the frozen coefficient dictionary, a differentiable-curve invariance equivalence, exact cubic attachment, sine completeness, and joint real analyticity/endpoint derivatives for reconstruction. Together with W0's bounded reconstructions and coefficient-to-PDE theorem, these are the required analytic inputs. W2 must still construct the all-time orbit and verify the full classical-solution predicate and the common constant C; W1 does not claim to have assembled (5).
- **W3:** Its actual W1 citations are satisfied. Its additional two-sided/symplectic/analytic-flow facts are proved locally, and its final return transport retains weighted coordinates and max-norm factors.
- **W4:** Hilbert-valued Fourier vectors and the Schur matrix bound pass. **Operator-valued Fourier summation remains unpaid as explained in W1-R1.** Shifted normal weights, period conventions, and parameter estimates must be carried explicitly.
- **W5–W6:** The corrected Cauchy/uniform-limit statements and repaired flow are suitable ingredients. The source smallness/margin conditions must be instantiated; this is not a review of an already written KAM iteration.
- **W8:** The finite-dimensional torus analyticity bridge and coordinatewise invariance interface suffice for their stated roles. Density, continuity of the parameter family, action reconstruction, and family injectivity remain later assembly obligations.

All repository/source defects proposed here are reported, not silently repaired. The only authored changes are this report and the authorized review scratch directory; the lint-generated `.lake` side effects are disclosed above. `git diff --check` passed and tracked-source status remained unchanged (`git status --short` showed only the untracked review directory). No state-changing git commands, generated-root edits, frozen edits, or proof-budget overrides were used.
