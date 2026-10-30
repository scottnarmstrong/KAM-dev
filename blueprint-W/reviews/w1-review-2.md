# W1 review, round 2

**Verdict: ACCEPT WITH FIXES.** The five round-1 findings are resolved at W1's scope. The new Fourier replacement, Cauchy guards, derivative-continuity argument and W2 reconstruction interface pass. Three minor corrections remain in the changed lines, listed below. The W4 homological solve and propagation of its constants remain explicitly assigned to W4; this acceptance does not certify that later argument or the published Theorem A exponents.

Reviewer: **GPT-6.1-Sol (codex-3), reasoning effort medium**, independent, refute-first.

## Scope and validation

Reviewed commit `46ad361a711e6df561c55d9555bb6413125f6409`, specifically the diff from `a13f96f7` in `blueprint-W/parts/w1-sequences.tex`, the round-1 findings, and the named W2-consumed interfaces. W1 is now 1,161 lines / 88,311 bytes. Line numbers below refer to this commit's pristine export under `.drafts/W/review-w1-r2/`. I did not re-audit the unchanged whole part or W2's proof.

Exported `blueprint-W` and `blueprint` using `git archive 46ad361a`; ran `latexmk -pdf -interaction=nonstopmode blueprint.tex` **inside that export**, capturing `build-review.log`. Result: **exit 0, 53 pages, zero TeX errors, zero undefined references, no LaTeX warnings**. Read the changed material in the rendered PDF via `pdftotext -layout`.

Rechecked the pinned P96-K page images for pp. 125, 127, 128 and 147, the directly cited track-K analytic proof steps, and the changed/new Mathlib names in the authoritative main Mathlib tree. Ran only scratch Python checks and read-only source/git checks. **No lint, Lean or Lake command was run.** No frozen or generated file was edited. The only authored files this round are this report and the permitted review scratch artifacts.

## Status of round-1 findings

| Finding | Status | Evidence |
|---|---|---|
| W1-R1: operator-valued Fourier square sum | **Resolved for W1; W4 application explicitly outstanding** | `fourier-banach` (i)–(iv), `lattice` and `operator-fourier` supply valid replacement estimates, identify the source defect, and prohibit reuse of its square-sum argument. The displayed bound `(3M/α)S_{n,τ}(σ)` is correct under the stated source divisor bound, `α>0`, `τ≥1` and `0<σ<s`. Minor counterexample transport correction below. |
| W1-R2: radius/supremum guards | **Resolved** | Lines 738–741 bind `r>0`, `δ>0`, `M≥0`; `uniform-limit` (i) has no boundedness assumption and (ii) separately assumes a pointwise bound. Multiplier, Fourier, flow and feature estimates now use explicit bounds. Remaining suprema are bounded operator/ℓ∞ norms, bounded unit-vector tests, explicit bounded counterexamples, or quoted source notation; no unbounded function supremum drives an estimate. |
| W1-R3: Fourier-shift sign | **Resolved** | Lines 968–981 give `û_k exp(-2πk·η)` and Parseval weight `exp(-4πk·η)`, then choose `η=-s'ε`. The single-mode check and the final positive orthant weight agree. |
| W1-R4: Mathlib names | **Resolved** | `lp.completeSpace` replaces the incorrect instance name; both `AnalyticAt.comp2` citations are removed and replaced by the uncurried bilinear theorem followed by `.prod` and `.comp`. Newly cited names checked below exist. |
| W1-R5: Picard integral measurability | **Resolved** | `deriv-continuous` proves continuity of the operator-valued derivative without general Banach-domain holomorphic⇒analytic. `picardholo` now inducts on continuity in time of `D_wφ_k`, establishes continuity/measurability of the differentiated integrand, and supplies neighborhood-uniform domination. Its last displayed integration shorthand needs the minor correction below. |

## Minor fixes in changed lines

| ID | Locator | Finding | Exact fix |
|---|---|---|---|
| W1-2a | `operator-fourier`, lines 1078–1083 | The counterexample is correct as a family of **representative** operators on ℓ², but the final claim that the two diagonal weighted transports “change nothing” is incorrect for unequal input/output weights. A raw diagonal Hessian `diag(a_j)` has representative entries `j^(p̄-p)a_j`. The displayed raw Hamiltonian therefore does not have the displayed representative Hessian when `p̄=p+1`. This does not undermine the operator counterexample. | Set the **raw** quadratic Hamiltonian coefficient to `j^(p-p̄) exp(-js_K) exp(ijx₁)` (and the same weight factor for the cosine variant), so its conjugated Hessian is exactly the stated `R̃`. Replace “change nothing” with this explicit calculation. For shifted normal indices use the actual corresponding weight ratio. |
| W1-2b | `holo-analytic-fd`, lines 802–807, 824–831 | The new stars-and-bars equality and binomial formula assume `n≥1`, which the lemma does not explicitly bind. For `n=0`, the displayed `n-1` is not a valid ordinary binomial parameter; interpreting subtraction in ℕ also does not give the asserted counting equality for positive degree. The summability sentence should also quantify a nonnegative radius, not every real `ρ<r₁`. | Bind `n≥1` for the quantitative formula and use `0≤ρ<r₁` in `hagroup`. If the qualitative theorem is intended for `n=0` too, handle that case separately as a map on a singleton. |
| W1-2c | `stepW:w1:picardholo`, lines 884–886 | The final shorthand `1+∫₀^|t| L exp(Lσ)⋯ ≤ Σ_{i≤k+1}(L|t|)^i/i!` is not a valid inequality if the exponential is the integrand: for `k=0`, `L=1/2`, `t=1`, its left expression is `exp(1/2)>1+1/2`. The preceding induction supplies the correct stronger bound, so the claimed conclusion is valid. | Write the actual calculation: `1+∫₀^|t| L Σ_{i=0}^k (Lσ)^i/i! dσ = Σ_{i=0}^{k+1}(L|t|)^i/i!`. Retain `L exp(L)` only as the uniform domination used for differentiation under the integral. |

No new blocking or major defect was found in the revised lines.

## Recomputed Fourier replacement

For any complex Banach target F, applying a continuous complex-linear functional to the Bochner coefficient commutes with integration. Scalar contour shift gives, for `0≤s'<s`,

`|φ(û_k)| ≤ ‖φ‖ M exp(-2π|k|₁s')`.

Letting `s'↑s` and using the dual norm bound proves `fourier-banach` (i). Consequently (ii) follows by summing `M exp(-2π|k|₁σ)`, with or without the polynomial weight. In (iii), the weighted ℓ¹ hypothesis gives uniform convergence of trigonometric partial sums on the open strip; the qualitative uniform-limit lemma gives holomorphy, and integrating termwise gives the coefficients. All these constructions are linear, so (iv) applies to parameter differences. For a Lipschitz constant multiply the difference estimate by `1/|ξ-ζ|` only for distinct parameters. No Hilbert-target Parseval claim is used here.

The lattice calculations are correct. Put `ε=2πσ>0`. The one-dimensional geometric sum is

`Σ_{m∈ℤ} exp(-ε|m|) = (1+exp(-ε))/(1-exp(-ε)) = coth(ε/2)`;

Tonelli gives its n-th power. Counting sign choices and weak compositions gives

`#{k:|k|₁=m} ≤ 2^n binomial(m+n-1,n-1) ≤ 2^n(m+1)^(n-1)`.

For `b=c+n-1≥0`, split off half the exponential and maximize `t^b exp(-εt/2)`. This gives exactly

`S_{n,c}(σ) = 2^n (2b/(eε))^b exp(ε/2)(1+2/ε)`,

with the stated value 1 for the power factor when `b=0`. The final geometric inequality follows from `1-exp(-x)≥x/(1+x)`. For `τ≥1`, `1+x^τ≤(1+x)^τ`, so (iv) follows for `γ,β≥0`. The definition of the source's `B_σ²` agrees with the p. 125 image. Its exponential `exp(-2|k|σ_K)` corresponds to `S(σ_K/π)`, exactly as written. This is distinct from converting a geometric strip width by `1/(2π)`.

For the mixed operator solve, the p. 127 divisor bound gives off-diagonal entry domination by `(A_k/α)|R̃_{k,ij}|/|i-j|`, and the diagonal domination by `(A_k/α)|R̃_{k,ii}|`; the `(k,i-j)=(0,0)` coefficient is set to zero. Schur (iii) therefore gives

`‖F̃_k‖ ≤ 3(A_k/α)‖R̃_k‖`.

Combining this with coefficient decay and strip summation proves

`‖F̃(θ)‖ ≤ (3M/α) Σ_k A_k exp(-2π|k|₁σ) ≤ (3M/α)S_{n,τ}(σ)`.

Thus the requested factor **3M/α is right**; no extra factor `2^n`, `√2` or `2π` belongs in this representative-operator estimate. Period conversion of the Hamiltonian equations is a separate consumer convention. Inverse-divisor differences yield the additional `A_k²(1+|k|₁)` weight, and coefficient differences the `A_k` weight (the text's `A_k(1+|k|₁)` is a valid overestimate). Hence the indicated `S_{n,τ+1}` and `S_{n,2τ+1}` route is valid. The displayed `S=O(σ^-(c+n))` is a small-σ assertion, or a uniform bound for `0<σ≤1`, as appropriate in the KAM step. Actual constants and smallness propagation remain W4's work.

### Source quotation and counterexample

The p. 127 quotation matches the image, including “operator valued coefficient” and the **unsquared** RHS. The writer explicitly distinguishes that literal formula from its likely intended squared RHS. The diagonal representative family has bound 1 and weighted coefficient square sum N, and disproves both readings when `N>2^n`. The unnormalized real-on-reals cosine variant as written has bound at most 1 and weighted square sum `N/2`, so `N>2^(n+1)` suffices without knowing its exact supremum. The only correction needed is the raw-to-representative Hessian transport in W1-2a. The source defect is preserved in `sourcegap`; Theorem A is not declared false.

Scratch Python independently checked 100 weighted-lattice cases (`n=1,…,4`, five nonnegative exponents, five positive widths), all within the displayed upper bound; twelve geometric/coth checks also passed. These are supplementary finite numerical checks; the preceding derivation proves the infinite-sum estimates.

## Derivative continuity, flow and finite-dimensional analyticity

For `w,w'∈B(w₀,ρ/2)` and `|ζ|=ρ/2`, both line points lie in `B(w₀,ρ)`. Cauchy on the ρ-margin ball gives `‖Df‖≤B/ρ` there, hence their value difference is at most `(B/ρ)‖w-w'‖`. Subtracting the line Cauchy integrals gives

`(1/(2π))·(πρ)·(ρ/2)^(-2)·(B/ρ) = 2B/ρ²`.

Thus the new Lipschitz constant is correct. Local boundedness of f comes from continuity at w₀ and openness of U. This proves operator-norm continuity of Df using only one-variable Cauchy theory.

In `picardholo`, continuity in the integration variable gives strong measurability of both integrand and derivative. The neighborhood `B(w₀,ε)⊂U` is fixed, and for every w in that neighborhood the iterates remain in `B(w,δ)` with `‖DX‖≤L`. Therefore `L exp(L)` uniformly dominates the derivative on the compact time interval and the whole neighborhood. The operator-valued integral theorem now has the required hypotheses. The polynomial recurrence is as corrected in W1-2c.

A.4 wording is now accurate: it identifies the missing segment justification, treats possibly infinite derivative norms as a potentially vacuous estimate rather than a separate counterexample, and assigns the concrete margin instantiation to W5. “(i)” and “(iv)” now explicitly refer to W1's own conclusions, not purported source numbering.

For `holo-analytic-fd`, `hamargin` legitimately enlarges the **domain** polydisc and bounds f there by compactness. `hacoef` uses Banach-valued iterated Cauchy/Fubini, with no compactness assumption on F. For positive n, each coordinate-product tensor in `hagroup` has norm at most 1, so summing the degree-m coefficients gives exactly

`‖p_m‖ ≤ binomial(m+n-1,n-1) M₁ r₁^(-m)`.

These need not be symmetric tensors: their diagonals give the requisite monomials, and `FormalMultilinearSeries` does not require symmetry. At every `0≤ρ<r₁` their norm series converges. The radius is therefore at least r₁, positive, and absolute regrouping supplies the `HasSum` field at every `‖h‖<r₁`. These are precisely the three requirements of `HasFPowerSeriesOnBall` (with positive r₁ embedded in `ℝ≥0∞`). There is no boundary-convergence overclaim: the original closed radius-r polydisc lies strictly inside radius r₁. W1-2b is a parameter-domain fix, not a failure of this argument.

The corrected/new cited Mathlib names exist: `lp.completeSpace`; `ContinuousLinearMap.analyticAt_bilinear`; `AnalyticAt.prod`/`.comp`; `DiffContOnCl.deriv_eq_smul_circleIntegral` (`CauchyIntegral.lean:828`, stated in integral-equals-scaled-derivative form); `ContinuousLinearMap.integral_comp_comm` (Bochner/ContinuousLinearMap); `NormedSpace.norm_le_dual_bound` (DoubleDual:97); `innerSL`; `ContinuousMultilinearMap.mkPiAlgebraFin` and `.smulRight`. The dual-bound theorem accepts bounds `‖φ(x)‖≤M‖φ‖` for arbitrary φ; the norm-one argument extends to those by scaling, with φ=0 handled separately. No unavailable Banach-domain holomorphic⇒analytic theorem is invoked.

## W2 interface check

The named W2-consumed labels still provide their required statements:

| W1 input | Checked disposition |
|---|---|
| `space` (especially (ii), (iv)) | Bounded coefficient evaluations, exact `coeff=κ_{1,1}`, and the weighted-coordinate product max norm are unchanged. |
| `coordinatewise` | Differentiability into ℓ² is still an explicit hypothesis. Equal weights give the identity inclusion for W2's curve derivative; the frozen invariance specialization still uses `E_{1,1}→E_{1,0}`. |
| `trilinear` (iv), `trifrozen` | Exact frozen integral/triple-series identification and output weight `ω_{1,2}` are unchanged. |
| `cubic-analytic` (iv) | Global analytic weighted cubic map and its `j^-1`, `j^-2` transports remain unchanged. |
| `sine-completeness` (ii) | Vanishing sine coefficients plus continuity on `[0,π]` still implies pointwise zero, including endpoints. |
| `sine-feature` (i)–(iii) | (i) now uses an explicit summable majorant `b_j`, which yields the previous uniform convergence without an unguarded supremum; analyticity and the exact absolutely convergent pairing identity are retained. |
| `recon-analytic`, `recder` | The new definitions `U_y^(k)`, `V_y^(k)` are absolutely convergent series/pairings. Part (i) identifies k=0 with the frozen functions, and part (ii) gives `HasDerivAt` with next derived reconstruction and the endpoint `derivWithin=U^(1)` identity. |
| `recon-analytic` (iii) | The parameter may be **any real normed space S**, including ℝ as used by W2. Pairing analytic feature/Y maps after continuous linear projections proves analyticity at `(s₀,x₀)`; neither finite dimensionality nor completeness of S is needed. |
| `hamfield` (v) | `Xʷ=(Dy',-Dy-S²Gʷ(y))` still represents the weaker-target field and its coordinates are exactly the frozen right sides times `e^j`. Only its proof's bound notation changed. |

I checked these against W2's cited uses at its feature/derivative, force attachment, coefficient-curve derivative, hidden-regularity and joint-analyticity steps. They do not require restoring the old `ℝ^n`-only reconstruction statement or identifying derivatives before proving them. No W2-consumed label was dropped or repurposed.

The remaining three minor fixes are blueprint details. No frozen statement change or additional source erratum is proposed beyond the already recorded p. 127/A.4 issues. Scope remains this revision and the named consumer interface; no whole-part or theorem-closure claim is made.

## Fix verification (sub-orchestrator kam-d4, 2026-10-30)

The three minor fixes were applied in the commit after 2a3f1643 and checked against the proposed fixes by the
sub-orchestrator, not by a third codex round (to save codex-3 quota). Findings:
- W1-2a: raw coefficient j^{p−p̄}e^{−js_K}e^{ijx₁}. The representative entry is ω_{a,p̄}(j)/ω_{a,p}(j)·R̈_jj =
  j^{p̄−p}·j^{p−p̄}e^{−js_K}e^{ijx₁} = R̃_jj; the shifted-index ratio is stated, and so is the cosine variant. CLOSED.
- W1-2b: `n ≥ 1` is bound for the quantitative formula, `n = 0` is treated separately, and `0 ≤ ρ < r₁` is used in
  hagroup. CLOSED.
- W1-2c: 1 + ∫₀^{|t|} L Σ_{i≤k} (Lσ)^i/i! dσ = Σ_{i≤k+1} (L|t|)^i/i! (termwise integration); L·e^L is kept only as
  the domination bound. CLOSED.
Diff: 17 insertions, 10 deletions, confined to those three places. Compile: exit 0, no '^!' lines, no undefined
references (writer's check). W1 status: ACCEPTED.
