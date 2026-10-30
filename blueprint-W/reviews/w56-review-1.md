# W5–W6 and W3 weak transport: independent review, round 1

**Verdict: REVISE.** The unmodified KAM step, flow margins, action–angle attachment, iteration arithmetic and weak-to-strong transport have sound underlying arguments. The modified homological estimate has an unfilled proof obligation for the action component of the vector field. Consequently the full parameter-Lipschitz preparatory bound, and the wave iteration consuming it, are not yet established by this blueprint. There is also an omitted positivity hypothesis in the preparatory construction. W3's new weak-transport corollary is accepted.

Reviewer provenance: GPT-6.1-Sol, codex-1, reasoning effort medium (the launch's reviewer identifier takes precedence over the generic brief's codex-3 identifier). Independent reviewer; no authorship or repairs of the reviewed mathematics. Tier 2, source correspondence and refutation audit. Findings below were subjected to a separate attempt to defeat them using the surrounding statements and stronger available bounds; those attempts are recorded explicitly.

## Frozen scope and permission envelope

Reviewed commit: **9682a585c814606cd8f0dab9fa5e4de785c4953e**, exported with `git archive` to `.drafts/W/review-w56/`. All manuscript locators below refer to that export, not subsequent working-tree edits.

| File | Lines | SHA-256 |
|---|---:|---|
| `blueprint-W/parts/w5-kamstep.tex` | 685 | `2006f2b85dababfb6d22f862fa43bbb7015fb155781b92d1039eab33be3122ef` |
| `blueprint-W/parts/w6-iteration.tex` | 415 | `3a0d0c37dc04eafc3ce7cb44276ed947769f08341fe7ee7e82ee9fc0ef833565` |
| `blueprint-W/parts/w3-birkhoff.tex` | 963; new corollary at 831–868 | `1e09a1eb1b06815116809f1f45e996b1ba79962ebfb755e3c75b797e5a19b161` |

Authorized writes: this review and `.drafts/W/review-w56/` only. No state-changing git command, manuscript edit, lint, Lean process or Lake command was run. No commit or push. No subagents used. Existing accepted W1/W3/W4 inputs, W4 guard (G), E-W-Pos96K-1 and the W4-R3 action–angle ownership ruling were retained.

Read: repository `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, both review briefs, W writer conventions, blueprint PLAN/preamble/W0/headline, W statement and BP0 handoff documents, the relevant W1/W3/W4 interfaces, W7 `family`/`w6-needs` and constants, W8 `sharp-prep`/`w6-general` and their consumers. Compared the final-use interface with the authoritative `/root/code/KAM/KAM/Frozen/Wave/Theorems/Nlw2.lean`; no frozen change is proposed.

Pinned source checked directly: P96-K pp. 120–122, 125–135, 140–142, 145–147, using the local PDF text; page images independently inspected for pp. **129, 134, 140 and 147** (PDF pages 12, 17, 23, 30). Also KP96 author-version pp. 25–28 and P96-W p. 290. The p. 140 formula was read from the page image, not reconstructed from defective OCR.

## Findings

| ID | Location at frozen commit | Severity | Finding and evidence | Exact proposed fix / closure criterion |
|---|---|---|---|---|
| W56-R1 | W5 `bpW:w5:w4-modified`, especially `stepW:w5:m-ass`, lines 171–184; W4 `stepW:w4:Fcomp`/`assembly`/`lip`, lines 670–703 | **major** | The proof treats the normal operator estimates, but claims the remaining assembly is unchanged. W4's action component uses the **bilinear** estimates for `Λ ∂θ Q_F`, obtained by applying the division multiplier on `mathcal B`, not the smoothing operator space. The factor `I^{-c}` introduced at W5 lines 175–183 belongs to the changed normal target norm; it is absent in the bilinear norm on two copies of `ell^N_{a,p}`. Thus `2 beta <= c` proves the displayed normal-operator Lipschitz bound but does not prove the full field bound being imported. See the detailed refutation below. | Supply both sup and parameter-Lipschitz estimates for the quadratic contribution to `F_theta` under the modified divisors. Identify the source and target bilinear spaces, prove the multiplier estimate actually used, and carry its constants and strip powers through `solve`, `step`, W6 `prep-step(v)` and W8 `sharp-prep`. Alternatively rederive this component using the smoothing operator bounds and additional angle differentiation/strip loss, then explicitly update `c_F`, `t`, `c_0`, `C_2` and dependent constants as needed. The present constants cannot be certified merely by saying the assembly is unchanged. |
| W56-R2 | W6 `bpW:w6:prep-step`, lines 214–220, and `wave-iteration`, lines 266–271 | **major** | The statement allows `epsilon=0`: take `P=0`. It then defines `eta_P=0`, `r_0=0`, while W5 step data require `eta>0`, `r>0`, and W6 sequences require `r_0>0`, `epsilon_0>0`. The permitted interval `[epsilon_0^flat, gamma_1 checkalpha]` also includes `epsilon_0=0` in this case. The claim that the construction works for every admissible starting size therefore includes data for which the cited constructions do not apply. | Require a **strictly positive chosen majorant** `0 < epsilon <= gamma alpha` in `prep-step`, and retain `epsilon_0 >= epsilon_0^flat > 0`; this still covers a zero perturbation by choosing a positive majorant. Alternatively give a separate zero-error construction with positive radii and state its interface separately. Ensure `to-w8`'s “every value” quantifier uses that corrected admissible range. |
| W56-R3 | W6 `stepW:w6:i-weak`, lines 190–193 | minor | The weak conjugacy chain is asserted by induction using preservation of `P^{p_+}`. That observation alone does not compose identities whose intermediate vector fields may be only in `P^{p-1}`: a derivative on `P^p` cannot simply be applied to such a field. The displayed composite weak identity nevertheless follows from the already available **function identities**, so this is a repairable explanation gap, not a counterexample to invariance. | First compose the identities `H_mu o Phi_{mu+1}=H_{mu+1}+constant` to obtain `H_0 o Phi^nu=H_nu+constant`. Differentiate this scalar identity against `W in P^{p_+}` and use the derivative/pairing formulas proved in W5 `new-ham(iii)`. Then apply `strong` at the torus. This avoids any extension of `D Phi` to `P^{p-1}`. |
| W56-R4 | W5 `bpW:w5:ext-taylor`, lines 44–51 | minor | `DifferentiableOn.hasFPowerSeriesOnBall` and `second_derivative_symmetric` exist. The literal name `HasFPowerSeriesOnBall.norm_sub_le` was not found in the checked Mathlib sources. It is described as a “type” of bound and there is a valid direct-Cauchy alternative, so no analytic result is blocked by this naming issue. | Remove the nonexistent literal name or replace it with an existing result and its hypotheses. `HasFPowerSeriesWithinOnBall.uniform_geometric_approx'` exists in `Analysis/Analytic/Basic.lean:691`; for the explicit constants used here, the already offered Cauchy coefficient estimate plus a geometric-tail sum is the clean route. |

### Refutation of W56-R1: why normal smoothing does not finish the action estimate

W4 deliberately avoids an extra angle strip loss by using, for each angle coordinate,

`||Λ ∂θ Q||_bil <= 16 pi epsilon`,

and by solving in the Banach space `mathcal B` of bounded bilinear forms on `ell^N_{a,p} x ell^N_{a,p}`. W4 `schur(ii)` applies when the actual coefficient multiplier satisfies `|d_ij| <= C/|i-j|`. With modified divisors it only has

`|d_ij| <= (A_k/hatalpha) min(I,J)^beta / |i-j|`,

and its parameter difference has `min(I,J)^{2 beta}`. The weighted bilinear matrix is

`d_ij (∂θ Q)_ij / (omega_{a,p}(I) omega_{a,p}(J))`.

There is no factor `I^{-c}` in this expression. Changing the regularity of the **normal output** changes neither the finite-dimensional action coordinate nor these two argument norms.

Independent attempted rebuttals:

1. **Use the same weighted Schur lemma anyway.** This fails as an operator statement on `mathcal B`. On adjacent indices, take a single matrix entry normalized to have bilinear norm one. An allowed abstract multiplier proportional to `min(I,J)^beta` makes the output bilinear norm tend to infinity. The analogous difference multiplier grows with `2 beta`. This refutes the proposed unchanged application of W4 `schur(ii)`; it is not claimed to be a counterexample satisfying every frequency condition of the whole KAM lemma.
2. **Use the `p_+` norm of the full field.** Its action component is still `|F_theta|/(2 pi r^2)`, with no normal weight. This does not introduce the missing factor.
3. **Use the bounded inclusion of the smoothing operator space into bilinear forms.** This supplies useful alternative data for `Q`, but W4's no-extra-loss input for its derivative is the bilinear bound. Differentiating the operator-valued Fourier series introduces an angle-frequency factor. Such an alternative may well repair the argument; it is not the unchanged assembly written here, and its constants/strip powers have not been supplied.

Disposition: **survived as a proof gap**, not as a disproof of the modified lemma. It affects even the sup action-component argument; separating `beta=1/4` from the loss `1/2` does correctly repair the displayed **normal-operator** reciprocal-difference estimate, but does not by itself discharge this separate obligation. W6 `prep-step(v)` and W8 `sharp-prep` inherit exactly this unpaid estimate.

### Refutation of W56-R2 and the minor findings

A zero field satisfies the stated smallness bound with `epsilon=0`; neither the unperturbed frequency hypotheses nor the removal of `Xi` forces that chosen error majorant to be positive. The later sequence definition does impose strict positivity, but that is precisely a hypothesis that `applicable` must establish, not an earlier restriction on `prep-step`. Positive majorants provide the straightforward repair. W5's flow invocation similarly needs either `epsilon>0` or a trivial `F=0` branch when its chosen `M_F` is zero.

For R3 I tried the stronger available scalar Hamiltonian identities: they do establish the desired composite identity by differentiation. For R4 I searched the analytic and Cauchy-integral sources and checked the existing alternatives; the mathematics does not depend on the absent name.

## P96-K p. 140: what is and is not verified

**Printed assertion verified.** The page image states (23) with `min(i^varpi,j^varpi)` in the denominator and subsequently states the bound

`|X_F|^lambda_{check p,r,D(s-sigma,r)} <= (a B_sigma/hatalpha) |X_R|^lambda_{bar p,r,D(s,r)}`, with `check p=bar p-varpi`.

It really is the full lambda norm. There is no missing “sup only” qualification in the image.

**Termwise obstruction verified.** For a varying divisor,

`Delta(1/delta) = -Delta(delta)/(delta(xi) delta(zeta))`.

The two modified lower bounds produce `min(I,J)^{2 beta}`. A loss `c=bar p-check p` cancels this by the stated weighted-operator proof when `2 beta <= c`. At `beta=c=1/2`, adjacent high indices leave a factor of order `I^{1/2}`. The modified W5 calculation is correct for the normal operators with `beta=1/4`, `c=1/2`. Its general-exponent lemma for the **unmodified** divisors also correctly handles the weaker `j^{-1/2}` frequency tails.

**Full source erratum remains suspected, not certified by the proposed example.** W5 lines 193–196 assert blow-up with `eta -> 0` and `J_0=(hatalpha n/(A_k eta))^2`. That describes a locally adverse reciprocal multiplier, but does not exhibit a frequency family and parameter domain on which *all* the modified Melnikov inequalities and the pinned spectral hypotheses hold while this limit is taken. The source's initial tails have exponent `-1`, whereas the more general W5 frequency hypothesis admits `-1/2`. One cannot substitute arbitrary near-resonant matrix entries for the source's frequency differences.

For example, in the wave-tail model `Omega_J=J+c/J`, `c>0`, and an adjacent divisor of the favorable sign, the large-J form is `delta_J=eta+c/(J(J+1))`. Requiring `sqrt(J) delta_J >= h` for **every** J has a minimum of order `eta^{3/4}`, so fixed `h=hatalpha/A_k>0` prevents `eta -> 0`. This defeats a fixed-h reading of the purported counterexample. It does not prove the printed estimate: letting h vary exposes further possible losses, and proving or disproving a uniform source estimate requires a complete admissible family.

Recommendation: record p. 140 as a **suspected parameter-Lipschitz source gap / insufficient printed justification**, with the exact displayed formula, the doubled-weight obstruction and the scope distinction above. Replace “not only a defect of the bound” by an appropriately conditional statement unless a complete counterexample or a structural repair is supplied. No claim here reopens the already confirmed operator square-sum erratum E-W-Pos96K-1.

## What I recomputed and accepted

### W5 flow, Taylor approximation and unmodified step

- **Repaired A.4 margins:** in `|.|_{p,r}`, `U=D(s-2 sigma,r/2)` has a ball of radius `sigma/2=2 delta` inside `V=D(s-sigma,r)`. Angle margin is sigma, action-radius margin is `3r^2/4`, normal-radius margin is `r/2`; `sigma<=1/4` is more than sufficient. Smallness gives `M_F<=sigma eta^2/16<=sigma/1024<delta=sigma/4`, hence `L<=1/256`; the displayed weaker `1/64` bound is safe. Both parameter trajectories stay in the same convex `B(w,delta)`. The zero-bound endpoint needs the trivial branch noted above.
- **Derivative and image:** the rescaled ball in `D(s-3 sigma,r/4)` has radius `sigma/8` in `|.|_{p,r}`. Cauchy gives sup derivative increment `8 M_F/sigma` and full lambda increment `16 M_F/sigma`. The increments fit inside `D(s-4 sigma,2 eta r)` in all three radii. Reality and angle equivariance follow from uniqueness. Symplecticity uses a genuine symmetric second derivative; the Neumann argument works both on `P^p` and `P^{p_+}`.
- **Taylor:** the identity `varpi(X,S_t W)=varpi(T_t X,W)` is correct. For `w in D(s,4 eta r)`, `rho=1/(4 eta)>=2`; the bound on the rescaled field is `rho^2 epsilon`, the third-and-higher tail is `epsilon/(rho-1)<=8 eta epsilon` in scale `4 eta r`, and conversion to scale `eta r` costs 16. This gives **128**, without an angle strip loss. On the original domain each of the three coefficients costs at most epsilon, giving **3**. The Hessian symmetry and the displayed complex-coordinate block formulas agree with W4's convention `<Qz,bar z>`.
- **Constants:** `|X_F|^lambda<=9 C_1 B_sigma epsilon/alpha` gives `c_F=9 C_1 b_W`, exponent `t-1=2 tau+3`. Then `c_0=16 c_F` is exactly equivalent to the stated flow smallness. The unmodified homological solver is available with the generalized smoothing exponent and weaker frequency tails; the uses of diagonal extraction, pairings and tail growth remain valid at `a=p=1`.
- **New Hamiltonian:** expanding the functions along the flow gives `R(t)=(1-t) hat N+tR` with the stated sign. Only `DN . X_F=-L_N F` under (G) is used for N. The bracket field is `DX_G X_F-DX_F X_G`, and its derivation uses only smoothing fields. No undefined pullback of the unbounded normal field is needed. The constant `hat a_0` is retained.
- **Pullback/error:** after rescaling, the inverse has norm at most 2; its weighted parameter difference costs at most 4. The composition difference contributes at most `1/2 |Y|`, so the total is at most `6.5 |Y|+2 lambda |Y|^L <=7 |Y|^lambda`. The commutator costs `2*(2/sigma)*6 epsilon M_F`, then `eta^{-2}`. Thus the two error terms cost **896** and **168 c_F**, and `C_2=896+168 c_F` is safe. This verifies the unmodified step, and verifies the subsequent algebra conditionally on the missing modified-field estimate in R1.
- **Frequency correction and finite cutoffs:** `6 pi epsilon` and `3 epsilon` follow from the Taylor bound and W4's diagonal extraction, including the lambda parts. The divisor-shift estimate `6 pi(1+K)(1+K^tau)epsilon` is sufficient for either index weight, which is at least one.

### Action–angle substitution and initial perturbation

- The principal square-root branch is guarded by `Re(xi_i+y_i)>0`. The derivative inverse has the correct factors `4 pi i` and `sqrt(xi_i+y_i)`. The pulled-back tangential form is `2 pi dtheta wedge dy`; the normal transform is unitary in the Hilbert sum norm, also for independent complex u,v.
- At `a=p=1`, the exact upper tangential coefficient is
  `2(e^2+4 e^4)e^{pi/2}=2172.235100677... <2173`.
  The normal Hilbert-square contribution is less than `r^2`, so **c_A=2200** safely puts the entire image inside the ball with squared radius `c_A(t+r^2)`. The strict comparison with `rho_1^2` is the required native-ball attachment, and W5 owns it as instructed.
- Keeping Dirichlet labels J avoids the old `3^p e^{2a}` conversions. The remaining `sqrt(2)`/2 factors between sum and Hilbert norms are correctly carried. Substitution in the corrected quartic normal form yields the stated `omega^0`, `Omega^0`, constant energy and `tilde Q`.
- The polynomial theta coefficient is at most `(3/5+1/(4 pi))/(2 pi)=0.108158... <1/8`; its normal contribution is at most `9/(4 pi) r^2 <3r^2/4`. Thus the polynomial bound `r^2` is safe. `G^nor` contributes `2 C_* r^2`. Applying the displayed derivative inverse to `X_K` gives exactly the three terms `3/r+2 sqrt(t+r^2)/r^2`. The finite-mode exponential/weight estimates are conservative.
- The complex parameter-neighborhood hypothesis supplies positive square-root margins and the same uniform K bound. A Cauchy estimate on a max-norm polydisc is an operator estimate along complex lines; it incurs no extra dimension factor. Near parameter pairs cost `2 epsilon_in/rho_xi`; far pairs cost `4 epsilon_in/rho_xi`. The stated multiplier `1+4 lambda/rho_xi` is safe.

### W6 sequences, convergence, invariance and consumers

- `sum sigma_nu=2 sigma_0` gives `s_infty=3s_0/4`. The recurrence gives `q_{nu+1}<=2^{t+2}C_2 q_nu^{4/3}<=q_nu/4`; hence the weaker `q_nu<=gamma_0 2^{-nu}` also holds. `eta_nu<=1/8`, W5 smallness, the Lipschitz-budget increment and `M_nu(1+2^{-nu-2})<=M_{nu+1}` all check. The cutoff computation leaves `alpha_0 2^{-nu(tau+4)}/4 <= alpha_nu-alpha_{nu+1}`. No exceptional k=0 condition is lost.
- Frequency sums use `epsilon_{nu+1}<=epsilon_nu/4` and `lambda_nu>=lambda_0/4`. They give the advertised sup bounds `8 pi epsilon_0`, `4 epsilon_0`, and Lipschitz bounds no worse than `64 pi epsilon_0/lambda_0`, `16 epsilon_0/lambda_0` (the omega Lipschitz constant is deliberately loose). The k=0 separation follows from `8 epsilon_0<=beta_0`.
- The composition derivative bound must be read from scale `r_nu` to scale `r_0` with the **same** exponent q, as W6 now explicitly does. The product is at most `exp(1/2)<2`. The smoothing errors converge in `P^{p_+}`: their sum is bounded by `4 c_F q_0 sigma_0/(1-1/8)<5 c_F q_0 sigma_0`. The closed image set remains strictly inside `D_0`. Holomorphy, equivariance, reality, joint continuity and angle-derivative convergence follow on the specified strips.
- The strong-conjugacy lemma is correct at points where the new field lies in `P^p`: use symplecticity there, then test against unit vectors in the onto image of `P^{p_+}`. With the corrected proof of the weak chain in R3, torus-point invariance passes in **P^{p-1}**, since the original linear field is continuous into that space. The limiting right side lies in P. There is no need to assert an ambient bounded field on P.
- **Preparatory arithmetic:** with `beta=1/4` and loss `1/2`, `2 beta=c`; the normal-operator Lipschitz estimate applies. Subject to R1, the full bound is
  `epsilon_0^flat=2 C_2 epsilon^{4/3}(hatalpha sigma_P^t)^{-1/3}`.
  The identity `4/3-(44/47)/3=48/47` and the chosen gamma give `epsilon_0^flat<=gamma_1 checkalpha`. `lambda_0=checkalpha/(2M)<=alpha/M` preserves the bound. The shift still gains one full weight because it is extracted from the input Taylor polynomial, with no divisor division. The stronger sup displacement `M_{F,P}` in `prep-step(iii)` follows from the integral proof of W5 flow, although the cited step statement displays the looser `2M_F` lambda bound.
- **Arbitrary starting size:** for every **positive** `epsilon_0 in [epsilon_0^flat,gamma_1 checkalpha]`, the frequency-family calculations use only those two bounds. They give exactly W7 (H1)–(H2): `epsilon_omega=6 pi gamma alpha+8 pi epsilon_0`, `epsilon_1=3 gamma alpha`, `epsilon_2=4 epsilon_0`; `134 pi<425` verifies the uniform theta budget. The sets are Borel by relative openness and countability. The exclusion sets use the correct domains `D_nu=Pi_{nu-1}`, the correct initial cutoff `K_{-1}=0`, and levels no larger than checkalpha. Limit divisors give `checkalpha/(2A_k)` for l=0 and the stated final frequency Lipschitz bound.
- These are precisely the contents requested by W7 `w6-needs`. W8 `w6-general` and `sharp-prep` need no stronger uniformity in epsilon_0, but inherit R1 and the endpoint qualification R2. W8's statement that W6 records “only the weaker bound” in `prep-step(v)` is stale: the pinned W6 already records the sharp bound there. This does not change the mathematics.
- The final tori have values in **W^{p+1/2}**, including the finite tangential coordinates, and invariance in **W^{p-1}**. The closeness estimate follows by adding the prep displacement to the iteration error and using `r_0<=r`. `s_0/2=7/128`. Holomorphy into the base space suffices for real analyticity after Gamma. The sharp-size formula in `to-w8` correctly makes `epsilon_0^flat/checkalpha` a constant times `(epsilon/alpha)^{4/3}`, so `e_tor ->0` with `epsilon/alpha`. None of this asserts that W6 alone proves the injectivity, patching or density clauses delegated to W8.

### W3 `transport-tori-weak`

Accepted as written. Its hypothesis is meaningful because multiplication by lambda maps W^p continuously into W^{p-1}. At a fixed theta, the invariance equation identifies `X_Lambda(w)` with an element of W^p: the tangent vector minus the three smoothing nonlinear fields. Coordinate equality survives the injective embedding into W^{p-1}. Since `|l|<=lambda_{|l|}`, multiplication by `1/lambda'_l` maps this vector into W^{p+1} with norm at most one. The advertised bound follows; the disjoint coefficient sets for `bar G+G^nor` permit the single C_* bound from W3's quartic majorant. Applying `main(iv)` pointwise then transports invariance through Gamma. Differentiability into W^{p+1} is unnecessary; the chain rule is used into W^p. Reality and the coordinate functionals produce exactly the frozen coefficient invariance equations, with the correct period-one frequency.

## Verification and closeout

- Pristine export built with `latexmk -pdf -interaction=nonstopmode blueprint.tex`: **exit 0**, **113 pages**, **0** lines beginning `!`, **0** undefined references, **0** `Warning:` entries in the final log. Rendered text read; W3 weak transport is on PDF p. 52, W5 starts p. 67, W6 starts p. 79 (contents-page repetitions excluded).
- Mechanical label/reference scan of the exported blueprint: **no missing internal ref/eqref targets; no duplicate labels**.
- Numerical recomputations above used `python3` in the permitted scratch workflow. An initial final-log read encountered a Latin-1 character; rerunning the log scan with Latin-1 decoding succeeded. No mathematical check failed.
- Mathlib names checked read-only: `DifferentiableOn.hasFPowerSeriesOnBall`, `Analysis/Complex/CauchyIntegral.lean:693` (closed-disc differentiability; use a smaller contour); `second_derivative_symmetric`, `Analysis/Calculus/FDeriv/Symmetric.lean:483`; the replacement geometric approximation result at `Analysis/Analytic/Basic.lean:691`. `AnalyticOnNhd` is the established predicate used by the accepted interfaces. No Lean compilation or axiom probe was needed or performed; this report is not a formal-proof certificate.
- Main uncertainty retained explicitly: the printed p. 140 estimate is not accepted as proved by its termwise argument, but a complete counterexample to the source under every hypothesis was not established here. R1 is a definite missing proof obligation in our adaptation, independent of that source-erratum classification.
- Closeout: one report delivered; manuscript untouched; no frozen/manifest change; no new errata ledger entry made. **Acceptance requires R1 and R2 to be resolved and R3/R4 corrected.** Conditional checks above should be retained when re-reviewing the repaired modified solver rather than treated as unconditional closure of the wave theorem.
