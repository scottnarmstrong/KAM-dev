# W4 independent review, round 1

**Verdict: REVISE (one domain guard).** The operator-sum repair, field constants, Lipschitz estimate and strip exponent pass. The claimed generality `a,p ≥ 0` does not justify calling the weak bracket an actual derivative of `N`: the scalar normal Hamiltonian can diverge. Add the guard below, or distinguish the formal pairing from a derivative. This does **not** obstruct the intended wave consumer `a=p=1` and does not refute a frozen statement.

Reviewer provenance: **GPT-6.1-Sol (codex-3), reasoning effort medium**, independent, refute-first.

## Reviewed state and checks

- Commit `7c07c3d5eb8157771cb86f56a1e7d4bfdf7504dc`; `blueprint-W/parts/w4-homological.tex`: **783 lines, 63,520 bytes**. All locators below refer to this committed file, exported with `git archive` into `.drafts/W/review-w4/`; no writer edits were reviewed.
- Read AGENTS.md, both review briefs, writer conventions, PLAN/DECISIONS (including both D30 entries and D41), W-STATEMENTS/W-BP0-handoff, committed blueprint-W PLAN/preamble/W0/headline, W1 Fourier/Schur inputs and W1 review, and W3's coordinates, field convention and interface. Compared the relevant authoritative main frozen `WaveSpace`, `coeff`, `lam`, `linearTorus` and `nlw2` declarations. W4 adds no final frozen theorem transcription.
- Pinned P96-K: read pp. 119–120 and 124–128 (PDF 2–3 and 7–11), and Appendix A.1 pp. 145–146 (PDF 28–29). **Inspected page images of pp. 124, 125, 127 and 128**, including all disputed formulas. Read P96-W p. 290 (PDF 23), with corrected coefficients controlled by W0 rather than its printed values.
- Pristine-export `latexmk -pdf -interaction=nonstopmode blueprint.tex`: **exit 0**, **78 pages**, **0 lines beginning `!`**, **no final undefined/multiply-defined reference warnings**. Read rendered text using `pdftotext -layout`; W4 spans pp. **52–64** (W7 starts on p. 64). Layout warnings remain; no mathematical reference failure.
- `python3 .drafts/W/review-w4/checks.py`: **exit 0**, `ALL NUMERICAL CHECKS PASS; finite sums are spot checks, not tail proofs`. Independent computations are recorded below. `git diff --check` is the final whitespace gate.
- No lint, Lean/Lake command, state-changing git command, frozen edit or generated-root edit. No Lean result was introduced; `#print axioms` is inapplicable to this source review. The inspected frozen headline still has its manifest-bound `by sorry`; this review does not certify its proof.

## Findings

| ID | Location | Severity | Finding and evidence | Exact proposed fix |
|---|---|---|---|---|
| W4-R1 | `bpW:w4:index`, lines 55–56; `lie`, lines 460–493; Lemma 1(ii), lines 588–589; `to-w5`, lines 752–754 | **major** | For the permitted `a=p=0`, take `Ω_j=j+2`, `z_j=zbar_j=1/j`. Both sequences lie in the phase space, but `Σ Ω_j z_j zbar_j = Σ(1/j+2/j²)` diverges. Thus `N` is not a scalar Hamiltonian on the stated domain, and line 492's claim that the pairing is its derivative is unjustified. The smoothing argument correctly defines the *pairing* `-L_NF`; it does not define `N` or an actual derivative of it. | Keep the coefficient solve/weak bracket at `a,p≥0`, but explicitly name the weak pairing and use `DN·X_F` only under `sup_j (j+2)/ω_{a,p}(j+2)² < ∞` (equivalently here, `a>0` or `p≥1/2`). Prove this guard makes the quadratic form continuous and its displayed differential valid. Alternatively add that guard to the convention and dependent theorem. State explicitly that the W5 consumer `a=p=1` satisfies it. |
| W4-R2 | `bpW:w4:lattice`(iv), lines 323–345; `melnikov`, line 163 | **minor** | The constant uses a sum over the **set** `{1,2τ,2τ+1}`, whereas the proof needs three occurrences. At `τ=0` or `τ=1/2` duplicate exponents collapse. Also `A_0=1` is separately specified in line 163, whereas the lattice's unqualified `1+|k|^τ`, with its `0^0=1` convention, yields `A_0=2` at `τ=0`. Neither issue affects the intended `τ>1` consumer, but the stated `τ≥0` formula is ambiguous and its written proof does not cover the set interpretation. | Write `b_W=2(C_0+C_1+C_{2τ}+C_{2τ+1})`, where `C_0=(1+1/π)²` and `C_q=4/π·((q+1)/(eπ))^(q+1)` for `q>0`. Declare `A_0=1` throughout, defining `A_k` piecewise; alternatively explain that the lattice uses a larger dominating sequence at zero. |
| W4-R3 | `from-w3`, lines 733–747, versus W3 `interface`, lines 819–848 | **minor/interface** | W4 consistently keeps wave weights and assigns the action–angle substitution to W5. The committed W3 interface still assigns that construction, its domain check, and weight-equivalence factors to **W4**. These are inconsistent ownership instructions, although W4's chosen weights avoid those equivalence factors correctly. | Have the W3 owner replace its W4 action–angle/domain assignments by W5, and state that W4 retains shifted wave weights; only the explicit phase-norm comparisons remain. W5 must retain the stated obligations to construct `R∈T_s`, including bounded holomorphic `Q^T`, and parameter bounds. No change to the W4 solve is needed. |

## What I recomputed

### 1. Field constants and Lipschitz bound

At a point of `D(s,r)`, `‖z‖,‖zbar‖<r/√2`. Extraction from the full field bound gives

- `|b|≤2πε`, `‖c±‖_(p+1)≤rε/√2`, and `‖2P‖,‖Q‖,‖Q^T‖,‖2P'‖≤ε`.
- For each angle derivative: bounds `2πr²ε` for `a`, `2πε` for the ℓ¹ norm of `b`, `2√2πrε` for the dual norm of `c±`, `4πε` for the bilinear norms of `P,P'`, and `16πε` for that of `Q`.

The one-variable test radius is `r/√2`; for the mixed scalar coefficient it is `r/(2√2)` in each variable. Four roots of unity in each variable isolate every coefficient of degree at most two without aliasing. Symmetric bilinear polarization and the Hilbert parallelogram law give the asserted `4πε` bound without an extra factor. These arguments also apply to `R(ξ)-R(ζ)`.

The three contributions to the field of the solve are respectively

`1`, `4+6K_S`, and `2+4K_S`,

all multiplied by `B_W ε/α`. Thus `C_1=7+10K_S`, with

`K_S=2.813799364234218`, `C_1=35.13799364234218<36`.

The reciprocal-divisor difference is bounded by

`2(1+|k|₁) A_k² M |ξ-ζ| / (α² w)`.

Indeed the divisor difference is at most `(|k|₁+2)M|ξ-ζ|`, the denominator at least `α²w²/A_k²`, and `w≥1`. Schur therefore gives precisely the same assembly with `ε` replaced by `ε^L+2Mε/α`. No extra angle-derivative factor is required for the parameter difference: extraction applied to the difference supplies the derivative-data bounds in the same weak norms.

For the correction, `|[b]|≤2πε` and `(j+2)|([Q])_jj|≤‖[Q]‖≤ε`. In real normal coordinates its gradients are `Ωhat u, Ωhat v`, so the tangential contribution is at most `ε` and the normal contribution at most `ε(‖u‖+‖v‖)/r≤ε`. This proves `|X_Nhat|≤2ε`, including its Lipschitz version. It is a safe estimate; W4 need not prove the source's sharper factor one.

Finally `λM/α≤1` gives `ε+λε^L+2λMε/α≤3(ε+λε^L)`. Hence the advertised absolute constant is **`a=3C_1=105.41398092702654<108`**. No claim of optimal constants is needed.

### 2. Why the strip power survives, and lattice checks

The replacement uses Banach coefficient decay, followed by an **ℓ¹** sum. Schur is applied separately to each coefficient, never to a fictitious Hilbert norm on the operator space. For angle derivatives, first transport `P,Q,P'` to bounded bilinear forms, and `c±` to the weighted dual. Their angle derivatives are bounded on the original strip by the field extraction above. Hadamard division commutes with these transports and with angle differentiation. Thus solving the derivatives uses the same inverse-divisor bounds, including Lipschitz differences, and needs only

`B_W(σ)=Σ_k (1+|k|₁) A_k² exp(-2π|k|₁σ)`.

There is no second `|k|` multiplier. Solving the strong operator-valued components first ensures `F∈T_(s-σ)`; passing to the weak bilinear spaces supplies the sharper derivative estimate. This distinction is essential and is made explicitly in `stepW:w4:Fcomp`.

The shells contain `4N` points. For `q>0`, splitting `exp(-2πσN)` into two equal factors gives

`S_q≤4/(πσ)·((q+1)/(eπσ))^(q+1)`.

Also `S_0=coth(πσ)²≤(1+1/(πσ))²`. The elementary bound `(1+N^τ)²≤2(1+N^(2τ))` then gives, with the occurrence convention of W4-R2, the stated exponent **`2τ+3=2τ+n+1`** for `σ≤1`.

Independent shell sums through `N=20000`, at `σ∈{.02,.05,.1,.2,.5,1}`, gave:

| τ | b_W(τ) | Maximum observed `B_W σ^(2τ+3)/b_W` |
|---|---:|---:|
| 3 | 5.7591640253 | 0.185233 |
| 3.5 | 9.2103557027 | 0.116519 |
| 5 | 195.7931126088 | 0.005979 |

The zero-mode contribution was set to one, as in the divisor convention. These are spot checks; the preceding shell proof supplies convergence and the full bound. Additional checks at `τ=0,.5,1` passed with the explicit occurrence formula proposed in W4-R2.

The repaired bound has exactly the power required for P96-K's later `t=2τ+n+2`; fixed norm/period conversions and the factor two for `Nhat` alter constants. This verifies W4's local claim about preserving the exponent. It does not independently certify the unwritten W5/W6 iteration or its complete smallness bookkeeping. W5 must actually use the same conventions; homogeneity alone is not a substitute for that check.

### 3. Schur, Banach multipliers, extraction, and equation

The weighted representative is `(μ_i A_ij ν_j)`. Positive diagonal weights leave the entrywise divisor ratio unchanged. Off the diagonal, row and column Cauchy–Schwarz bounds use `Σ_(h≠0) h^-2=π²/3`, giving `π/√3`; adding the diagonal costs one. This proves `K_S` on both operator spaces and bilinear forms. For complex bilinear forms the Riesz identification includes coordinate conjugation to obtain a complex-linear operator with the same norm; the displayed weighted entries and Schur estimate are correct. The transpose identity is used only where the transpose belongs to the stated operator space, as required for `Q^T`.

The multiplier solve follows directly from norm-summability. Its difference splits as `T(ξ)(fhat(ξ)-fhat(ζ))+(T(ξ)-T(ζ))fhat(ζ)`. Integration by parts gives `widehat(∂_i f)=2πik_i fhat`; uniformly summable derivative coefficients justify commuting solve and derivative. The W1 Banach-valued Fourier lemma and scalar uniqueness have the stated strength at this commit. No operator-valued Parseval estimate is reused.

Fourier comparison on finite-support normal variables, scalar uniqueness, and density then prove `L_NF+Nhat=R-ahat_0`. Pairings with `Ωz∈ℓ_(a,p-1)` and smoothing gradients in `ℓ_(a,p+1)` are bounded because the exponents sum to `2p≥0`. This verifies the weak equation on the full stated space. Identifying its second version with an actual derivative requires W4-R1.

### 4. Wave frequencies, k=0, and interfaces

The shift is `J=j+2`; it must occur in the weights and fixed spectral sequence. The corrected coefficients give exactly the maximal first row sum for `M_ω` and the asserted `M_Ω=3/(2π)(λ_1^-1+λ_2^-1)`. The tail identity `λ_J-J=m/(λ_J+J)` gives the claimed `M_0`. P96-K Assumption B explicitly allows fixed lower-order terms: **`Ωbar_j=j+2` is legitimate**, and the remaining tail is in `ℓ∞^1`. For `|l|≤2`, either the signs agree (shifted weight ratio at most three) or their sum is zero (difference weight unchanged). No missing configuration of `l` remains.

For k=0 put `β=3⟨b,ξ⟩/(2π)`, so `|β|≤3`. Single modes and sums are bounded by `j+1` and `i+j+2`. For differences,

`Ω_i-Ω_j=(λ_I-λ_J)(1-β/(λ_I λ_J)) ≥ (2/3)(I-J)/sqrt(1+m/9) = α_0(m)(i-j)`.

Here `I,J≥3`, and `α_0=2/sqrt(9+m)<1`. This proves every claimed k=0 condition under `|⟨b,ξ⟩|≤2π`. The affine dependence makes the endpoint values `β=±3` sufficient for numerical checking. With `j≤150`, the minimum ratios to `α_0⟨l⟩` were `1.125048`, `1.148172`, `1.169650`, `1.395331`, `1.741799` for `m=.001,.5,1,10,1000`, respectively. W4 correctly leaves k≠0 to parameter exclusion; it does not assume that all wave parameters satisfy Melnikov.

The W0 sign `z=(u+iv)/√2` gives `zdot=-iH_zbar` and reverses the source's normal signs. The displayed divisors, including `δ^Q_(k,ij)=k·ω+Ω_i-Ω_j` for the monomial `z_j zbar_i`, agree. Exchanging `z,zbar` sends `l` to `-l`, preserving the entire Melnikov family. Reality relations of the solved coefficients pass. The tangential factor is `1/(2π)`, consistent with positive frozen frequencies `ν=ω/(2π)` and the minus sine in `linearTorus`.

W3's normal restriction has exactly the shifted weights. Its Hilbert norm satisfies `‖what‖²=‖u‖²+‖v‖²`, hence `‖what‖≤‖u‖+‖v‖≤√2‖what‖`. Working with these weights avoids the `3^p e^(2a)` conversion entirely. The smoothing field supplies normal gradients, but does not itself supply the parameterized Taylor Hamiltonian after the tangential action–angle substitution. W4 correctly lists that as a W5 obligation (subject to the ownership correction W4-R3). The normal correction lies in `ℓ∞^1` in the P96-K index since `j≤j+2`; both its size and Lipschitz bounds propagate with explicit increments. No use of the outgoing correction in its own divisor assumptions occurs.

## Pinned-source errata and gap verdicts

These are reports for the orchestrator's ledger; I did not edit the ledger.

1. **E-W-Pos96K-1, confirmed/rechecked:** p. 127 (PDF 10), display after “with operator valued coefficient … we have, as before”. The operator-norm square-sum bound is false even after squaring its RHS. W4's finite-rank diagonal family has supremum norm one and weighted square sum `N`; choose `N>4`. Weighted transports realize it as a mixed Hessian in the one-smoothing class. If real Hamiltonians are required, normalized cosines give the same unbounded-in-rank counterexample. The **unsquared RHS is also a literal printing error**, visible in the image, and does not explain away the structural defect.
2. **Divisor-factor slip, confirmed as an inference error:** p. 127 (PDF 10) prints `|⟨k,ω⟩+Ω_i-Ω_j|≥α(1+|i-j|)/A_k`, followed by “since d≥1”. The hypothesis provides `α max(1,|i^d-j^d|)/A_k`; at `d=1` this is `α max(1,|i-j|)/A_k`, not the printed larger expression. A factor `1/2` suffices for the printed `1+|i-j|` version. W4's corrected max-weight bound suffices directly for Schur, including its diagonal cases; no factor two need be inserted into `C_1` for this repair.
3. **Omitted constant, confirmed:** the mean definition is actually on **p. 124 (PDF 7)** and sums over `|m|+|q|=1`, omitting the constant. P. 125 (PDF 8) then asserts `Nhat=[R]` and the exact scalar equation. Taking `R≡1` makes the defect immediate. Add `ahat_0` to `Nhat`, or keep W4's equation modulo `ahat_0`; vector fields are unaffected. W4 makes the deviation explicit and correctly preserves the constant in the identity sent to W5.
4. **P. 128 (PDF 11), proof compression confirmed; no additional false theorem established:** the image says the other components “admit the same estimates, or even better ones”, and adds “at most eight such terms” per component before concluding the field estimate. Thus the source **does give a term-count assertion**, but does not display the angle-derivative extraction or its norms. W4 supplies that bookkeeping correctly. Classify this as an expanded justification/source proof gap at the estimate level, not a new numerical counterexample or a second operator-sum erratum. The replacement and constants checked above close this local omission.

## Remaining scope

The generic `N`/derivative guard is the only major finding. W4-R2 and W4-R3 are small precision/interface repairs. No suspected defect of a frozen Wave declaration was found; no original source hypothesis, normalizer or sign was silently changed. The analytic estimate repair is complete at the blueprint level, with the W5 Taylor/parameter/domain obligations retained explicitly.
