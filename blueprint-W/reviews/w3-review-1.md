# W3 independent review, round 1

**Verdict: REVISE.** The analytic normal-form construction and its numerical constants withstand the checks below. The outstanding major issue is the claimed *exact* P96-K interface: the proof deliberately stops short of the source's analytic-field regularity and then says that upgrade is unused. There are also three incorrect Mathlib identifiers and an overstated source-error diagnosis. No counterexample to the divisor lemma or normal-form bounds was found.

Provenance: GPT-6.1-Sol (codex-3), reasoning effort medium. Independent, refute-first review of commit **a13f96f730361eb3a8a6177ec3fc8239acfe24dd**, part `w3`, round 1. Reviewed `blueprint-W/parts/w3-birkhoff.tex`: **777 lines, 57,843 bytes**, SHA-256 `95499b0967a8c07d0f8214c982799ec14a8b9314908f6d528123a7d93291bbf1`. All W3 line locators below refer to that committed file, exported under `.drafts/W/review-w3/`; they do not refer to subsequent writer edits.

## Materials and scope

Read repository AGENTS.md, docs/PLAN.md and docs/DECISIONS.md; the general blueprint-review brief and track-W review/writer briefs; committed blueprint-W PLAN, preamble, W0 conventions, W0 normalization, headline, W3, and the W1 statements actually cited by W3. Read W-STATEMENTS.md and W-BP0-handoff.md. D41 and the authoritative frozen Wave definitions/theorem were checked in `/root/code/KAM` because the worktree documentation predates that ruling. W3 introduces no frozen statement and does not alter the positive-mass carrier, weighted-coordinate WaveSpace, standard actions, period-one frequencies, or frozen analytic-embedding requirement.

Read the pinned P96-W PDF pp. 281–286 (PDF pp. 14–19), also pp. 280 and 287–289 for context; P96-K pp. 119–122, especially Assumption C and norm (1) on p. 121; KP96 author v2.1 pp. 25–28. Inspected page images of P96-W pp. 282, 285–286 and P96-K p. 121 to disambiguate OCR. Source hashes:

- P96-W: `77f083dc4f3d45802460c880a588ef227065810aa93cc963ff7684714d25d6a2`.
- P96-K: `3fac82b098ac6add2e3b336978d8bcf70166590707a997c0684b008b6df9420f`.
- KP96: `d05ec70b6308d99bf2e6d2e1d22299791cb58bd2aefc8aee29c4a21f1ff2dc7e`.

W1 was checked only for existence, scope and what W3 consumes; its proofs were not independently audited. No subagents were used. Only this report and permitted review scratch were retained; the permitted transient Mathlib probe was deleted.

## Findings

| ID | Location / label | Severity | Finding and evidence | Exact proposed fix |
|---|---|---|---|---|
| W3-R1 | 142–157, 617–620, 645–651, 702–721; `bpW:w3:hamfield-def`, `class-remark`, `interface` | **major** | The implemented class requires only `DifferentiableOn Complex` for the smoothing field. P96-K Assumption C, p. 121, explicitly requires the field to define a **real analytic map** into the higher-weight phase space. The line-map Cauchy argument supplies derivative estimates but does not itself supply a Banach-space power series or the literal source hypothesis. The remark says field analyticity is “not used”, while the interface presents an exact match. This is a missing bridge in the blueprint, not a counterexample to the mathematics. | Add and prove a labelled upgrade for this particular `X_K`, then export `AnalyticOnNhd Complex X_K Bρ₁` and its real restriction. One route: expand `DΓ_t-I`, its Neumann inverse, and the cubic `X_Z′∘Γ_t` on smaller balls; prove uniform absolute convergence for `t∈[0,1]`, integrate multilinear coefficients, and identify their sum with `∫Y(t,w)dt`. Alternatively state/prove the general holomorphic-to-analytic Banach theorem as an explicit new dependency. If W4–W6 instead use only the holomorphic class, declare and prove that source-interface substitution there; do not call the present output literally P96-K Assumption C. |
| W3-R2 | 637–643, especially “neither field is in that class”; `sourcegap` after `bpW:w3:main` | minor | The source's p. 285 sentence starts **“with X_H ∈ A”**: it is a conditional pullback property for a smoothing field, not an unconditional claim that the original `Λ+G` is smoothing. Moreover, the assertion that the commutator is not smoothing is false after the homological identity: `{H,F}=Z′+{G,F}` has a smoothing field. The cancellation/application needs explanation; the two general conditional properties printed in the source are not themselves refuted. | Replace the diagnosis by: “The printed proof leaves implicit the application of its pullback/bracket facts to the Taylor remainder when the original linear field is unbounded. The homological identity shows `{Λ,F}=Z′`, so `{H,F}=Z′+{G,F}` has a smoothing field.” Retain the explicit K2/XK2 proof as the supplied expansion. Do not list the bracket as a false source statement. |
| W3-R3 | 56; external fact E2 | minor | Bare `analyticOnNhd_uncurry_of_multilinear` is unknown in the pinned Mathlib. The actual theorem is in namespace `ContinuousLinearMap`. Verified by the single Lean probe. | Use `ContinuousLinearMap.analyticOnNhd_uncurry_of_multilinear`. |
| W3-R4 | 76; external fact E6 | minor | `NormedRing.tsum_geometric_of_norm_lt_one` does not exist. The unqualified theorem with the latter basename is for a **normed division ring**, hence is not the operator-algebra theorem needed here. | Use the Banach-ring results `geom_series_eq_inverse` and `tsum_geometric_le_of_norm_lt_one`, together with the already correct `Units.oneSub` and `NormedRing.inverse_one_sub`. |
| W3-R5 | 81; `bpW:w3:ext-flows` | minor | Bare `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` is unknown. | Qualify it as `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`. This is background only; the W3 construction does not depend on it. |

Implementation notes, not additional mathematical failures: `(t^k Φ_k)` denotes a series with degrees `2k+1`; a `FormalMultilinearSeries` must explicitly put zero in degree zero and every even degree. E3's cited `hasFDerivAt_tsum` / `hasDerivAt_tsum` versions have whole-space hypotheses; use their `_of_isPreconnected` variants on the open convex domains used here. The optional uniqueness remark at 532–534 needs a local Lipschitz uniqueness theorem or a restriction/extension argument: the displayed `ODE_solution_unique` assumes global Lipschitzness, while a nonzero cubic field is only locally Lipschitz. None of these is used to obtain the inverse, symplecticity, or estimates.

## What I recomputed: divisor lemma

Write `a≤b≤c≤d`, `λ_k=√(k²+m)`, `β=m/(27λ_a³)`. The signed spatial selection rule gives exactly `d=a+b+c` or `d=b+c-a`, allowing repetitions. The spatial signs are independent of the signs of the frequency divisor; the proof correctly checks all latter signs. Global sign reversal reduces to at most two minus signs.

- **No minus signs:** `δ≥4>β`, since `β≤1/(27λ_a)≤1/27`.
- **One minus sign:** the smallest signed sum is `λ_a+λ_b+λ_c−λ_d`. Using `λ_k−k=m/(λ_k+k)`, `a+b+c−d≥0`, and cancellation of the c and d reciprocal terms leaves at least `m/(λ_a+a)≥m/(2λ_a)≥β`. It is positive, so passing to absolute value is justified.
- **Outer two-minus pattern:** `δ₃=(λ_c−λ_a)+(λ_d−λ_b)`. Unless all indices coincide (paired), at least one interval has integer length at least one, giving `δ₃≥a/λ_a≥β`.
- **Alternating two-minus pattern:** `δ₂=(λ_b−λ_a)+(λ_d−λ_c)`. If `a=b,c=d`, it is paired and excluded; otherwise the same gap bound gives `δ₂≥a/λ_a≥β`. This explicitly covers the nonpaired outer divisor when `a=b<c=d`.
- **Inner two-minus pattern, d=b+c−a:** nonpairing implies `t=b−a=d−c≥1`. The right interval shifts left to `[b,b+t]`; monotonicity of f′ gives the double integral over `s∈[a,a+1], r∈[s,s+1]`. Since `f″(r)=m/(r²+m)^(3/2)` decreases, `δ₁≥f″(a+2)≥m/(27λ_a³)`, using `a+2≤3a`.
- **Inner pattern, d=a+b+c:** shift `[c,d]` left by `c−a` to `[a,2a+b]`. Then `δ₁≥λ_(b+2a)−λ_b≥2a f′(b)≥2/√(1+m)≥β`.

These cases prove the claimed `1/27` constant. If a tangential index is present, `a≤2`, giving exactly `δ_*(m)=m/(27(4+m)^(3/2))`. Neither pairing nor division by zero is silently used: zero quartic coefficients can be assigned zero under Lean totalized division; the divisor lemma is needed only where the coefficient is nonzero. The final asymptotic claim has the right order: second differences are `~m/n³` for fixed m and large n.

### Numerical refutation attempts

Scratch program `.drafts/W/review-w3/divisor_checks.py` uses **mpmath at 120 decimal digits**; output is `divisor-output.txt`. It checks all sorted selection tuples generated by `1≤a≤b≤c≤20` with both allowed d values, plus near-second-difference tuples, equal-pair tuples, indices through `10^12`, and 300 reproducible random large-index triples with both d values (seed 20261030). There are **3,698 tuples**, **29,120 nonpaired signed cases per mass**, and **320,320 divisor comparisons** over eleven masses. It tests every frequency sign pattern modulo global reversal. No failures.

Minimum observed ratios `|δ| / [m/(27(a²+m)^(3/2))]`:

| m | Minimum ratio |
|---|---:|
| 10^-30 | 4.5000000000000 |
| 10^-12 | 4.5000000000041 |
| 10^-6 | 4.5000040937493 |
| 0.01 | 4.5408667779411 |
| 0.1 | 4.9023674148878 |
| 1 | 7.9693542717923 |
| 10 | 17.204602820546 |
| 10^3 | 25.881658253434 |
| 10^6 | 26.959535424824 |
| 10^12 | 26.999959500035 |
| 10^30 | 27.0000000000000 |

The first six minima occur at `(1,2,2,3)`, signs `(+−−+)`. Large-m minima migrate to near-second-difference tuples. These are finite numerical checks, not a substitute for the case proof. High precision matters: ordinary floating-point subtraction can erase the very small divisors in the small-m/large-index tests.

## P96-W errata verification

1. **p. 285 Case 1: confirmed false displayed inequality.** The page image prints `δ′(m)=½(1/λ_i+1/λ_j+1/λ_k−1/λ_l)≥1/λ_i`. For `(i,j,k,l)=(1,10,10,19)`, m=1, the derivative is **0.42677769305289084142**, while `1/λ_1=0.70710678118654752440`. The selection rule holds. The valid bound is `1/(2λ_i)`; W3's algebraic proof supplies it without integrating in m. The lemma survives with a smaller absolute constant.
2. **p. 286 Case 2: confirmed missing subcase in the reduction.** The source compares the other divisors to `δ_(+−−+)` and then studies that divisor alone. At `i=j<k=l`, it is paired and zero. The divisor `δ_(−−++)=2(λ_k−λ_i)` is nonpaired and still needs a positive bound. For `(1,1,2,2), m=1`, it equals **1.6437088302533892952**, whereas the comparison divisor is zero. This is a proof omission, not a false lemma. W3's separate outer-pair bound repairs it.
3. **p. 286 intermediate factor: confirmed slip.** The page prints `λ_(j+2i)−λ_j≥2(λ_(j+1)−λ_j)≥2i f′(j)`. The second inequality fails, e.g. i=2,j=3,m=1: its two sides are **1.9216559308985624** and **3.7947331922020552**. Replace the first `2` by `2i`; summing 2i increasing unit gaps proves the corrected chain. W3's direct integral bound is valid. This can be embedded in the source case with k=4,l=9.
4. **p. 285 regularity: qualify the diagnosis.** The original field `X_Λ+X_G` and its conjugate are unbounded on the base space, so estimating them separately as smoothing would be invalid. The source, however, states its pullback fact conditionally. Its commutator has a smoothing extension after the homological cancellation. The missing explanation can be supplied either through that observation and the printed Taylor formula, or through W3's K2 integral. Thus the suspected source proof is terse/incomplete at this application, but the claim that *both* displayed fields fail the smoothing class is refuted; see W3-R2.

No source errata ledger was edited. These locators and quoted formulas are the handoff to the orchestrator.

## Analytic construction, symplecticity and remainder

The coordinate map Z is a complex linear isomorphism with `‖x‖_max≤‖Zx‖≤√2‖x‖_max`, including the higher-weight space. The involution is isometric and its fixed set is precisely the real phase space. The bilinear symplectic form is continuous and weakly nondegenerate. The proof never assumes that its induced map to the full Banach dual is surjective: Hamiltonian fields are explicitly constructed, and weak nondegeneracy is used only for uniqueness. This is the correct infinite-dimensional argument.

The absolute majorant yields the form constant `C_*/4`: the two output signs contribute √2, the three input sums contribute `(√2)^3`, and the quartic prefactor is 1/16. Hence the cubic field bound is `C_*‖w‖³`. With the divisor estimate, `S=4∇F` has norm at most `C_F=C_*/δ_*`. The conjugation signs are correct: `f_(-x)=−f_x`, so the imaginary prefactor gives a real Hamiltonian. Direct substitution gives

`DΛ(w) X_F(w)=−(1/16)∑δ_x f_x w_x=Gbar−Gtan=Z′`.

This agrees with W0's `c/(-iδ)=ic/δ` and its time convention `ż=−iλz`. Λ is a continuous scalar quadratic form for `p≥1/2`, even though its field is unbounded on the base space. The Cauchy–Schwarz argument also controls the absolute coefficient series after multiplication by λ, so the symmetrization is legitimate.

For the Lie coefficients, inserting S in all slots gives `(k+1)φ_(k+1)=Lφ_k`. The norm recursion has factor `(2k+1)/(k+1)<2`; the same recursion holds with higher-weight codomain once k≥1. The iterated Leibniz rule gives the cubic Cauchy-product identity and its derivative. Thus `‖Φ_k‖≤(2C_F)^k`, also into W+ for k≥1, proves all the claimed series convergence on `|t|<2`, `‖w‖<ρ₀`, `ρ₀=(40C_F)^(-1/2)`.

Here `r=2|t|C_F‖w‖²<1/10`. The geometric sum gives `‖Γ_t w‖≤10‖w‖/9`; its tail is at most `(20/9)|t|C_F‖w‖³≤3|t|C_F‖w‖³`. The differentiated tail is

`∑_(k≥1)(2k+1)r^k = 2r/(1−r)²+r/(1−r) ≤5r`.

The latter remains valid through r=1/4 (ratio 4.8888889); at r=1/10 the ratio is 3.5802469. Hence the bound `10|t|C_F‖w‖²≤1/2` and the Neumann inverse bounds hold on both spaces. Mixed differentiated series have the same geometric margin, justifying the variational equation. Joint continuity/differentiability can be proved locally by uniform convergence of these derivative series; compactness of infinite-dimensional balls is not needed.

The inverse proof correctly uses the **transport** equation for `Γ_(-s)` and the **flow** equation for `Γ_s`; the composition stays inside Bρ₀. It does not rely on ODE uniqueness. Both image inclusions, and the extra √2 real-coordinate restriction, check out. Symplecticity follows by differentiating `Ω(DΓ_t ξ,DΓ_t η)` and using four-linear symmetry of F. Invertibility then yields `X_(P∘Γ)=DΓ^(-1)X_P∘Γ`, including preservation of the higher-weight target. The inverse on W+ agrees with the restriction of the inverse on W by uniqueness of solutions of the bounded linear equation.

For the remainder, the split `K=(G∘Γ−G)+(Λ∘Γ−Λ−Z′)` is exact. The scalar K1 constant before rounding is `3(10/9)^3=4.11522634<5`. Differentiating along Γ_t turns K2 into `∫_0^1[Z′(Γ_tw)−Z′(w)]dt`, so its scalar bound is even at most `(5/2)C_*C_F‖w‖^6`; the stated 5 is harmless. Thus `C_K=10C_*C_F` is safe.

Gradient transport gives a K1 field constant `18(10/9)^2+20=42.22222223<44`. For K2, the same bound has an extra t; integrating gives 22. Thus `C′_K=66C_*C_F` is safe. The integrands and their derivatives admit uniform bounds on smaller balls from the convergent series and Neumann inverse; this suffices for the complex differentiation under the Bochner integral that W3 actually claims. The homological identity removes the unbounded linear field before estimation. The proof is not circular and introduces no conclusion-shaped hypothesis. Conjugacy is correctly restricted to W+, where X_Λ is defined as a base-space vector, and yields the required coordinatewise coefficient equations. The remaining analyticity upgrade for the higher-weight field is W3-R1.

## Consumer interface and normalization

The shift of normal indices is controlled exactly by

`j^p e^(aj) ≤ (j+2)^p e^(a(j+2)) ≤ 3^p e^(2a) j^p e^(aj)`.

Use p+1 in the higher-weight target, so its conversion factor is `3^(p+1)e^(2a)`. The sum of the u,v norms is between the max norm and twice that max norm. Together with Z's √2 conversion these are finite fixed factors; W4 must actually propagate them when defining its domains and normed perturbation size.

For d=1, P96-K requires pbar>p; pbar=p+1 satisfies it, with spectral exponent δ=−1 compatible with `p−pbar=−1`. The loss parameter Δ is 1. Both scalar and field bounds have the right orders. With κ=2, g=6 satisfies `6>4+(4−1)/2=11/2`. Independent complex w_j,w_(-j), the conjugation involution, and the real structure are correctly retained. KP96's coordinate `q_KP=√2 z=q+ip` agrees with its `(i/2)dq_KP∧d qbar_KP` and the standard real q,p coordinates. Thus its `I=|q_KP|²/2` becomes our `I=|z|²`; this introduces no new factor in A or B.

P96-K Theorem A still receives its actual `N+P` only after the action-angle substitution and parameter/domain choices. The unabsorbed quartic y terms belong to P, as KP96 Step 1 explains. W3 is appropriately an input to that later construction, not a proof of the smallness and Lipschitz gates. KP96 p. 28 does explicitly put the embeddings in the pbar space, as the return-trip argument needs. Literal analytic-field applicability is the remaining issue W3-R1. **Complex Fréchet differentiability is mathematically sufficient** via the classical Banach holomorphy theorem; it is also sufficient for linewise Cauchy estimates. What is missing is an explicit proved bridge to the specific analytic predicate/hypothesis being claimed, not stronger estimates or a new PDE premise.

The coefficients agree with Part 0. Off-diagonal paired terms have 24 orderings and contribute `24/(16πλ_rλ_s)=3/(2πλ_rλ_s)`. Diagonal terms have 6 orderings and contribute `6·3/(32πλ_r²)=9/(16πλ_r²)=A_rr/2`. Thus `A_rr=9/(8πλ_r²)` and `A_rs=B_sr=3/(2πλ_rλ_s)`. The source's `(6/π)(4−δ_rs)/(λ_rλ_s)` is 16 times these coefficients. The p. 282 image confirms the two losses of a factor 1/4 in passing from q to the first complex expansion and then to the primed w sum. W3 uses the repaired prefactor consistently, including in F and the homological identity. No normalization ruling is reopened.

## W1 citations checked, without reviewing W1

All requested labels exist in committed `parts/w1-sequences.tex`:

| Label | W1 line | What W3 uses |
|---|---:|---|
| `bpW:w1:space` | 111 | Complete weighted lp model, bounded coordinate evaluations; frozen max-norm real phase space. Finite truncation convergence is also included here. |
| `bpW:w1:embed` | 186 | Norm-one inclusion from p+1 to p, preserving coefficients. |
| `bpW:w1:diag` | 205 | λ multiplier from p+1 to p, norm at most √(1+m). |
| `bpW:w1:twosided` | 283 | Independent pair of complex sequences, square-sum norm, isometric identification with the zero-at-zero two-sided space. |
| `bpW:w1:gradient-identity` | 495 | Unweighted gradient of G, not the weighted Riesz gradient. Its a>0 scope is respected in the identification with the integral Hamiltonian; a=0 uses the absolutely convergent coefficient definition. |
| `bpW:w1:hamfield` | 529 | Hamiltonian convention and real/complex cubic field; W3 supplies its own two-sided version. |
| `bpW:w1:holomorphic` | 691 | Holomorphic means complex Fréchet differentiable on an open Banach domain. |
| `bpW:w1:flow` | 765 | Background discussion only; not an input to the Lie-series construction. |

All W0/W1 labels referenced by W3 resolve in the clean LaTeX build. The a=0 scalar extension, independent complex coordinates, and weak symplectic argument are supplied in W3 rather than silently attributed to the real W1 gradient result.

## Mathlib name audit and checks

One permitted process was run, from `/root/code/KAM`:

`LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/BpW3Review.lean`

The probe was a module importing Mathlib, with no budget overrides, no declarations of new mathematical facts, and no build. It was deleted after the run. Exit **1**, with exactly three unknown identifiers (W3-R3–R5); all other #checks succeeded. Full signatures are retained in `.drafts/W/review-w3/mathlib-probe.txt`. The following cited declarations were positively checked:

- `ContinuousMultilinearMap.opNorm_le_bound`, `.hasFDerivAt`, `.compContinuousLinearMap`, `.analyticOnNhd`.
- `HasFPowerSeriesOnBall.analyticAt_of_mem`, `.fderiv`; `AnalyticAt.comp`; `analyticAt_inverse`; `AnalyticOnNhd.fderiv`.
- `hasFDerivAt_tsum`, `hasDerivAt_tsum`, `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`.
- `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, `is_const_of_deriv_eq_zero`.
- `hasFDerivAt_integral_of_dominated_of_fderiv_le`, `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `ContinuousLinearMap.intervalIntegral_comp_comm`, `intervalIntegral.norm_integral_le_of_norm_le`.
- `NormedRing.inverse_one_sub`, `Units.oneSub`, `IsPicardLindelof`, `ODE_solution_unique`, `DifferentiableOn.analyticOnNhd`.

The replacement names in W3-R3–R5 were also positively #checked. Source search confirms `ContinuousMultilinearMap`, `FormalMultilinearSeries`, `HasFPowerSeriesOnBall`, `AnalyticOnNhd`, `DifferentiableOn`, and `HasFDerivAt` exist as the standard types/predicates. `tsum` is the standard infinite-sum notation/operation, not an additional analytic theorem. `DifferentiableOn.analyticOnNhd` is indeed limited to source `ℂ`; it does not directly solve W3-R1. Cauchy products for the trilinear S require iterated continuity/summation and reindexing; the displayed multiplication theorem is the ring prototype, not a direct theorem about an arbitrary trilinear map.

Validation:

- Pristine archive command: `git archive a13f96f7 blueprint-W blueprint | tar -x -C .drafts/W/review-w3`.
- `latexmk -pdf -interaction=nonstopmode blueprint.tex` in the exported blueprint-W: **exit 0**, **41-page PDF**; log contains **0** lines starting `!`, **0 undefined-reference warnings**, and **0 overfull boxes**. Read rendered PDF text; W3 occupies printed pp. **27–39**. Build log: `.drafts/W/review-w3/build-output.txt`.
- `python3 .drafts/W/review-w3/divisor_checks.py`: **exit 0**, final output `ALL DIVISOR AND CONSTANT CHECKS PASS`.
- Mathlib probe: **exit 1**, exactly the three expected name failures above; successful replacement checks in the same single process. This is a diagnostic failure, not a claimed passing Lean gate.
- `git diff --check`: clean before report finalization; checked again after writing the report.
- No `lake build`, kernel replay, axiom probe, generated-root regeneration or repository-wide lint was run. The specific review brief forbids builds; no Lean result was changed or proved. Axioms of main results: **not applicable to this source/blueprint review**. This report does not certify a Lean implementation or campaign closure.

Uncertainties and deviations: no numerical or algebraic failure of the divisor or analytic normal-form construction remains. The unapplied holomorphy-to-analyticity bridge is explicit in W3-R1. Uniformity and analytic dependence in m are deliberately omitted by W3, consistently with the fixed-m frozen target; the displayed bounds would give uniform radii on compact positive-m intervals, but parameter analyticity was not claimed or checked. Source defects must be recorded with the qualification in W3-R2. W1 proof correctness and later KAM domain/parameter/smallness work remain outside this review.
