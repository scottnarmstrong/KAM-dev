# W5, W6, W8 — Round 2 tight delta review

**W5: ACCEPT WITH FIXES (one minor general-range constant/notation issue). W6: ACCEPT. W8: ACCEPT.** These are verdicts on the requested delta, not fresh acceptance of unchanged material or a claim that the frozen Lean theorem is proved. The Round-1 action-component blocker and its inherited W8 dependency are closed for the wave application, where tau = 24.

Reviewer: GPT-6.1-Sol, codex-1, reasoning effort medium; independent, refute-first. The launch identifier takes precedence over the generic brief's codex-3. Focused tier-2 audit; separate discovery and adversarial recheck passes by this reviewer, no subagents.

## Frozen scope and checks

Compared only `9682a585c814606cd8f0dab9fa5e4de785c4953e` to **`3560d19f6d97e3d199ff399fd5e5e48928fb7b44`**, for the three named files. Read the latter from a pristine `git archive` export in `.drafts/W/review-w568-2/`; all line numbers below refer to that revision.

| File under `blueprint-W/parts/` | Lines | SHA-256 |
|---|---:|---|
| `w5-kamstep.tex` | 729 | `44da0d2d416fc87ee12e043a23066a7f269c86da968bdd3a3f21ee502f6ce6cf` |
| `w6-iteration.tex` | 426 | `7d284062a4f177bc7f8ba03562ca801053bd4593b9db41838e931d3199f0eeba` |
| `w8-assembly.tex` | 650 | `dfe5c696903edc33308c3dcbe38198c872f3bfa71e2de61cd39573fffdda46f0` |

Read AGENTS.md, PLAN/DECISIONS, both review briefs, writer conventions, the Round-1 reviews, blueprint PLAN and the relevant W4 component/Schur/Fourier/lattice/assembly interfaces. Unchanged statements are context, not reopened audit targets. Direct source check: local P96-K journal pp. 140–141 (PDF 23–24), using `pdftotext -f 23 -l 24 -layout`; the changed source-gap wording is checked against the displayed assertion quoted in Round 1 and the surrounding source argument. No new source counterexample is claimed.

Ran `latexmk -pdf -interaction=nonstopmode blueprint.tex` only in the pristine export: **success**, `Output written on blueprint.pdf (114 pages, 1591887 bytes)`; final log has no undefined-reference warning. Three overfull boxes remain (9.04924pt, 13.28886pt, 1.3483pt); these do not affect this mathematical delta verdict. Build log: `.drafts/W/review-w568-2/blueprint-W/review-build.log`.

No lint, Lean/Lake command, state-changing git command, manuscript repair, commit or push. Authorized writes were this report and its scratch directory only. Mathlib names were checked by reading `/root/code/KAM/.lake/packages/mathlib`, without compilation. Axioms: not probed; no Lean result is under implementation review.

## New finding

| ID | Frozen location / anchor | Severity | Evidence and refutation | Exact proposed fix |
|---|---|---|---|---|
| W568-R2-1 | W5 `bpW:w5:w4-modified(iii)`, lines 174–175, and `stepW:w5:m-const`, lines 216–219: “sum over q in {2,2 tau,2 tau+2}” | minor | The proof uses **four terms with multiplicity**, `4(S_0+S_2+S_{2tau}+S_{2tau+2})`, but the displayed constant uses a set, which drops a repeated exponent at tau=1 or 0. At tau=0 it also uses the positive-q expression at q=0, although W4's lattice bound requires `C_0=(1+1/pi)^2`. Attempted rebuttal: perhaps the domain excludes these tau, or the constants are deliberately oversized. W4 allows tau>=0; the generous constant may still bound the sum, but that does not justify the stated term-by-term proof. This is a defect in the general-range derivation/notation, **not a demonstrated counterexample to its final bound**. For tau=24 all three exponents are positive and distinct, so the checked wave chain is unaffected. | Write `b^natural(tau)=4(C_0+C_2+C_{2tau}+C_{2tau+2})`, explicitly counting multiplicities and using W4's piecewise `C_q` (including its q=0 case). Alternatively restrict this assertion to tau=24. |

No new blocking or major defect survived the recheck. W5 acceptance requires the small displayed-constant clarification above; W6/W8 need no corresponding change at tau=24.

## Round-1 dispositions and recomputation

### W56-R1 and W78-B-D1: CLOSED for tau=24

W5 `stepW:w5:m-act`, lines 189–209, now supplies the previously unpaid action estimate through operators from ell^N_(a,p) to ell^N_(a,p_+), followed by the unweighted pairing. This avoids the unavailable modified multiplier on the old bilinear input space.

Recomputed coefficient bound:

`||2 pi i k_i (Q_F)_k|| <= 2 pi |k_i| K_S A_k epsilon exp(-2 pi |k|_1 s) / hatalpha`.

The output weight contributes `I^(-c)` with `c=p+1-p_+`; it cancels `min(I,J)^beta` in size, and `min(I,J)^(2 beta)` in parameter differences. The same Schur constant covers the diagonal: for k!=0 it is divided by `<k,omega>`, and for k=0 its resonant diagonal is zero. Thus the diagonal does not require the modified off-diagonal inequality. The derivative series converges on the smaller strip by the displayed summable majorant; termwise differentiation is legitimate there (or locally via an intermediate strip).

Since `|k_i| A_k <= (1+|k|_1) A_k^2`, the size sum remains B^W_sigma. Pairing the output with bar-z costs at most `||z||_p ||bar-z||_p`, by W4's pairing inequality with p+p_+>=0. Its coefficient `2 pi K_S` is below W4's old `16 pi K_S`, so keeping `C_1=7+10K_S` is safe.

For parameter differences, expansion into `d(xi) Delta Q + Delta d Q(zeta)` gives exactly the two terms stated in m-act. Differentiation contributes the extra `|k|_1`, so the reciprocal-difference term is bounded by

`2 pi K_S B^natural_sigma / hatalpha * (epsilon^L + 2 M epsilon/hatalpha) |xi-zeta|`.

All other components fit the same bound because B^W_sigma<=B^natural_sigma. With lambda M/hatalpha<=1 the full norm is bounded by `3 C_1 B^natural_sigma/hatalpha` times the input full norm. No circular reliance on the desired action estimate remains.

At tau=24 the pointwise inequality `(1+x)^2(1+x^tau)^2 <= 4(1+x^2)(1+x^(2tau))`, W4's lattice bounds, and sigma<=1 give the displayed b^natural and exponent **52**. The modified step therefore uses **t^natural=53**, `c_F^natural=9 C_1 b^natural`, `c_0^natural=16 c_F^natural`, and `C_2^natural=896+168 c_F^natural`. Rechecked the W5 smallness equivalence `M_F<=sigma eta^2/16` and the error terms: the 896 term is unchanged, while the commutator term takes the new c_F. The explicit replacement convention in `bpW:w5:data` carries these constants through the later step statements.

W6 `constants`/`prep-step` now use `eta_P^3=epsilon/(hatalpha sigma_P^53)` and `M_{F,P}=c_F^natural epsilon/(hatalpha sigma_P^52)`. If `q_P<= (c_0^natural)^(-3)`, then eta_P<=1/c_0^natural<=1/8 and `q_P<=eta_P^2/c_0^natural`, as required. The sharp error is

`epsilon_0^flat = 2 C_2^natural epsilon^(4/3) (hatalpha sigma_P^53)^(-1/3)`.

The identity `4/3-(44/47)/3=48/47` and the revised last entry of gamma give `epsilon_0^flat<=gamma_1 checkalpha`. Decreasing lambda to `lambda_0=checkalpha/(2M)` preserves the full-norm estimate. The subsequent unmodified iteration retains t=52 and the original constants, correctly.

W8 `const`, `sharp-prep`, `shell-iter`, `w6-general`, `etor` carry the revised quantities without reverting to the old preparatory powers. In particular:

- `epsilon_0,n^flat <= kappa_n^(4/3) gamma_1 checkalpha_n = epsilon_0,n <= gamma_1 checkalpha_n`.
- `E_4 = c_F^natural gamma sigma_P^(-52) + 5 c_F gamma_1 sigma_0^(-51)`, `E_5=E_3 E_4/gamma`.
- The preparatory displacement is `c_F^natural sigma_P^(-52) gamma kappa_n alpha_n^(3/47)`; the iterative displacement is `5 c_F sigma_0^(-51) gamma_1 kappa_n^(4/3)`. Since alpha_n,kappa_n<=1, their sum is at most `E_4 kappa_n=E_5 t_n^(1/64)<=7/256`.
- The unchanged closeness consumer uses `sqrt(t_n) e_tor` and a `t_n^(3/2)` remainder, giving `E_7 t_n^(33/64)`. Since `t_n<=2 r(I)^2`, this yields `eta(r)=2^(33/64) E_7 r^(1/32)`. The new fixed constants affect the prefactor and admissible t_0, not the decay exponent.

Adversarial recheck tried the original bilinear obstruction, a missing diagonal estimate, an extra r-factor in the action norm, and a lost strip power in W8. Each is paid by the new operator/pairing argument or the explicit revised constants above.

### W56-R2: CLOSED

W5 `data` now requires a positive majorant even for P=0. W6 `prep-step` explicitly assumes `0<epsilon<=gamma alpha`, making eta_P, r_0 and epsilon_0^flat positive. The allowed interval therefore forces epsilon_0>0. W8 `shell-data` supplies `epsilon=epsilon_n^sharp=E_3 t_n^(3/2)>0`, since t_n>0 and E_3>=1. Tried the Round-1 P=0/epsilon=0 counterexample: it is excluded by the corrected hypotheses, while P=0 itself remains covered by choosing a positive majorant.

### W56-R3: CLOSED

W6 `stepW:w6:i-weak`, lines 189–199, first composes `H_mu o Phi_(mu+1)=H_(mu+1)+c_mu` as scalar function identities on the nested domains. Differentiation against W in P^(p_+) and the W5 derivative/pairing formulas give the required composite weak identity. Constants vanish on differentiation. The derivative is applied only to W, with its image in P^(p_+), never to an arbitrary P^(p-1) field. The existing strong-conjugacy argument at torus points can therefore consume it.

### W56-R4 and W78-B-2: CLOSED

Checked actual declarations and their hypotheses:

- `DifferentiableOn.hasFPowerSeriesOnBall`: `Mathlib/Analysis/Complex/CauchyIntegral.lean:693`, requires differentiability on a positive-radius closed ball; the new “slightly smaller closed disc” qualification supplies this.
- `HasFPowerSeriesWithinOnBall.uniform_geometric_approx'`: `Mathlib/Analysis/Analytic/Basic.lean:685`, gives existential geometric constants, exactly as the revised text says. The explicit remainder instead follows from Cauchy coefficients and the geometric tail, as stated. The absent `HasFPowerSeriesOnBall.norm_sub_le` name is removed.
- `Complex.norm_exp_ofReal_mul_I`: `Mathlib/Analysis/Complex/Trigonometric.lean:952`, norm equals one.
- `Real.norm_exp_I_mul_ofReal_sub_one_le`: `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean:286`; the order of factors is reconciled by commutativity.

### W78-B-1: CLOSED

W8 now describes epsilon_0,n as a value of W6's existing starting-size parameter. The obsolete “W6 records only the weaker bound” and extension request are removed, including in the deviations ledger. W6 explicitly retains uniformity over the corrected positive interval.

## Closeout limits and errata

The three-file delta is fully classified; one minor general-range clarification remains in W5. No fresh full-part, frozen-statement, dependency-graph or Lean-proof audit was performed. No change to protected files is proposed.

The revised P96-K p. 140 note now correctly calls the printed full-lambda justification insufficient/suspected, retains the doubled-weight obstruction, and explicitly disclaims a complete admissible counterexample. Its additional action-component strip cost is identified as the blueprint's proof route. This review does not certify a new source erratum; the adopted beta=1/4, loss=1/2 and t^natural=53 deviations remain explicit.
