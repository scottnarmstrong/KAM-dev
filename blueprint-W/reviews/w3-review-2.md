# W3 independent review, round 2

**Verdict: ACCEPT.** All five round-1 findings are closed. The revised analytic-field proof supplies the missing power series and real restriction. No new defect was found in the changed lines.

Provenance: GPT-6.1-Sol (codex-3), reasoning effort medium. Reviewed commit **c677f6ed**, using only its diff against **a13f96f7** for `blueprint-W/parts/w3-birkhoff.tex`, the round-1 findings, and the immediate dependencies needed to check those revisions. This is the requested tight delta review; the unchanged divisor proof, numerical search, normalization and other W3 proofs were not re-audited.

The pristine export is `.drafts/W/review-w3-r2/`. The reviewed W3 file has **904 lines, 68,901 bytes**, SHA-256 `7ca800871d26ad819f4ca4a6508f070c1a45021e8ff7181f7d6cb78c104de074`. All line locators below refer to that export.

## Findings and disposition

| Round-1 ID | Previous severity | Revised location | Status | Evidence |
|---|---|---|---|---|
| W3-R1 | major | 158–160, 170–188, 602–675, 683–688, 722–736, 761–767, 818–845 | **CLOSED** | `bpW:w3:Yseries` supplies an absolutely convergent higher-weight power series for the integrated field. `bpW:w3:real-restrict` supplies real analyticity. The class A(U), main(ii), XK2 step and regularity remark now assert the analytic predicates actually proved. The retitled interface states the Cartesian input and leaves the action-angle/domain/parameter work to W4. |
| W3-R2 | minor | 750–759, 900–903 | **CLOSED** | The sourcegap now describes conditional pullback/bracket facts, acknowledges that they are correct, and identifies an omitted application to the remainder. It explicitly uses `{H,F}=Z′+{G,F}` to obtain a smoothing field. The status list no longer calls that conditional statement false. |
| W3-R3 | minor | 56–57 | **CLOSED** | `ContinuousLinearMap.analyticOnNhd_uncurry_of_multilinear` exists; positively checked in the pinned Mathlib. |
| W3-R4 | minor | 86–87 | **CLOSED** | The nonexistent namespaced geometric-series theorem is replaced by the correct Banach-ring results `geom_series_eq_inverse` and `tsum_geometric_le_of_norm_lt_one`. Both were positively checked. |
| W3-R5 | minor | 92–93 | **CLOSED** | The Picard–Lindelöf existence theorem is now correctly qualified by `IsPicardLindelof`; positively checked. |

No new blocking, major or minor finding. The round-1 implementation notes are also addressed: the formal series now explicitly inserts zero coefficients in absent degrees (520–523); E3 uses the open/preconnected-domain differentiation theorems (65–68); multilinear regrouping is distinguished from its ring prototype; and the optional ODE identification uses uniqueness with a Lipschitz bound on a region containing the curves (563–566).

## Recomputed analytic repair

The new argument is independent of the general theorem that Banach-space holomorphy implies analyticity. It constructs multilinear coefficients directly.

Write R=ρ₁. Since `R²=1/(160 C_F)`, the majorant parameter satisfies

`r=2 C_F s ρ² ≤ 1/80` for `0≤s≤1`, `0≤ρ≤R`.

The flow coefficients have time degree k and spatial degree `2k+1`. Their majorant is `ρ/(1−r)`. Inserting the variable v into every slot of Φ_k produces a continuous `2k`-linear map into `L(W+)`, whose norm is at most `(2k+1)(2C_F)^k`: Φ_k already has higher-weight codomain, and the inclusion of the v input from W+ to W has norm at most one. Consequently the series A for `DΓ_t−I` on W+ has

`μ_A ≤ ∑_(k≥1)(2k+1)r^k = 2r/(1−r)²+r/(1−r) ≤ 5r ≤ 1/16`.

At the endpoint, the exact sum is `239/6241 ≈ 0.0382951450`, so the coarser 1/16 bound is safe.

For the inverse, A has no time-degree-zero coefficient. Hence `(-A)^n` has no time degree below n, and each coefficient of

`N_(j,d)=∑_(n≤j) ((-A)^n)_(j,d)`

is a **finite** sum of continuous multilinear maps. Composition of bounded operators contributes no extra norm factor. The coefficient majorant, rather than merely the norm of the evaluated inverse, is therefore bounded by

`μ_N ≤ ∑_(n≥0) μ_A^n ≤ 16/15`.

This justifies absolute summability of the weighted coefficient families and evaluated families before regrouping. Regrouping yields the Neumann inverse of `I+A(t,w)` on W+. The identity term is a zero-linear coefficient in position (0,0). The grading `d=2j` is preserved, including that term. Thus no infinite coefficient sum or unproved inverse-series analyticity is hidden here.

The cubic field `X_Z′∘Γ_t` has shift 3 and majorant `C_*ρ³(1−r)^(-3)`. Applying N and subtracting `X_Z′(w)` gives a series of shift 3, so its only possible spatial degree at time degree j is `2j+3`. At the boundary,

`∑_j ‖Y_j‖ R^(2j+3) ≤ [ (16/15)(80/79)^3 + 1 ] C_* R³`

`= (3117517/1479117) C_* R³ ≈ 2.107687898 C_* R³ < 4 C_* R³`.

The subtraction is bounded by the triangle inequality; no unjustified cancellation is needed for this estimate. In fact, the time-degree-zero coefficient cancels exactly, since Γ₀=I and N₀=I. Non-symmetric multilinear coefficients cause no difficulty: their diagonal evaluations give the required function, and the norm estimates and formal power series do not require symmetrization.

For fixed w in B_R, `t↦t^jY_j(w,…,w)` is continuous and bounded on [0,1] by the summable constant `‖Y_j‖R^(2j+3)`. Thus the newly cited dominated-convergence theorem applies with that constant as its j-th dominating function. Its sum is a finite constant, hence interval integrable. It gives precisely

`∫₀¹Y(t,w)dt = ∑_j Y_j(w,…,w)/(j+1)`.

The coefficients q in degrees `2j+3` and zeros in all other degrees satisfy `∑_n ‖q_n‖R^n<∞`. The resulting formal multilinear series therefore has radius **at least R**, and the function agrees with its sum on B_R. No claim about analyticity across the boundary is needed.

The XK2 step first identifies the integral as the Hamiltonian field by differentiation of the scalar integral and the symplectic pairing, then uses the new lemma for analyticity into W+. These two steps are compatible and noncircular. Uniform derivative bounds on every smaller ball follow from the same boundary coefficient bound: with `0<ρ<R`, the factors `(2j+3)(ρ/R)^(2j+2)` are bounded. This also gives the continuity and derivative bounds used in that integral argument. The previously accepted field bound `22 C_* C_F ‖w‖⁵` is retained; the coefficient majorant is used for analyticity and does not replace the sharper vanishing-order estimate.

## Real restriction and revised interface

`AnalyticOnNhd.restrictScalars` applies with scalar tower ℝ⊂ℂ, giving real analyticity into the underlying real Banach target. The projection

`Π(y)=Z⁻¹((y+ϱy)/2)`

is continuous and real linear from either V=W or V=W+ into its corresponding real form E_V. For real x, equivariance puts `f(Zx)` in the fixed set, so `Π f Z` equals the stated real restriction. Composing real analytic maps proves the claimed real-target predicate without any assumption about an analytic map taking values in a subspace. The scalar case uses the continuous real-linear map Re and the reality of P. The preimage domain is open, and `‖Zx‖≤√2‖x‖` gives the advertised real ball in main(ii).

The changed A(U) now requires both the Hamiltonian and its higher-weight field to be analytic on the complex domain. K1 has that field regularity by composition and bounded-operator inversion; K2 has it by the new coefficient argument. Reality and the real restriction then give the literal Cartesian real analytic field. The class remark no longer says that this upgrade is unused.

The interface now claims **input toward** P96-K, not a completed application of Theorem A. It explicitly assigns the action-angle substitution, mapping of its domain into B_R, parameter choices and perturbation norms to W4. It includes the p+1 target-weight conversion `3^(p+1)e^(2a)` as well as the phase-space factor, max/sum conversion, and √2 coordinate factor. Its analytic regularity assertion is now supported. No stronger conclusion or new consumer applicability gap is introduced by those changed lines.

The rewritten sourcegap is consistent with the round-1 PDF check. The original field is unbounded on the base space, but the conditional pullback/bracket facts are valid and `{Λ,F}=Z′` supplies the needed cancellation. This is accurately presented as an omitted application rather than a false source formula. No new source erratum is alleged by the revision.

## Mathlib verification

One module probe importing Mathlib was run **only in `/root/code/KAM`**, serialized with `LEAN_NUM_THREADS=1`:

`nice -n 5 lake env lean .lake/abi-scratch/BpW3ReviewR2.lean`

**Exit 0; no errors or warnings.** The transient probe was deleted. Full signatures are retained in `.drafts/W/review-w3-r2/mathlib-probe.txt`. All changed/new cited names below exist:

| Name | Applicability checked |
|---|---|
| `ContinuousLinearMap.analyticOnNhd_uncurry_of_multilinear` | Analytic evaluation of a continuously linear family of continuous multilinear maps. |
| `geom_series_eq_inverse` | Geometric series equals `Ring.inverse (1−x)` for a normed ring with summable geometric series. Applies to the Banach operator algebra. |
| `tsum_geometric_le_of_norm_lt_one` | Norm bound for the geometric series in a normed ring. |
| `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` | Correct namespace for the background existence theorem. |
| `HasSum.sigma` | Regroups an already summable sigma-indexed family using its fiber sums; the majorants supply the requisite summability here. |
| `Summable.sigma` | Summability of fiber sums in the complete additive target. |
| `intervalIntegral.hasSum_integral_of_dominated_convergence` | Constant summable coefficient bounds give all domination and integrability hypotheses for [0,1]. |
| `ODE_solution_unique_of_mem_Icc` | Uses `LipschitzOnWith` on a region containing both curves, with initial time in the interval interior; applies locally around time zero. Background identification only. |
| `AnalyticOnNhd.restrictScalars` | Gives ℝ-analyticity from ℂ-analyticity on the same underlying domain with the standard scalar tower. |
| `hasFDerivAt_tsum_of_isPreconnected` | Open/preconnected-domain version; suitable for the convex domains used in W3. |
| `hasDerivAt_tsum_of_isPreconnected` | Corresponding one-variable derivative theorem. |

## Validation and limits

- Exported `c677f6ed` using `git archive c677f6ed blueprint-W blueprint` into the requested scratch directory. Saved the exact scoped diff as `diff.txt` there.
- `latexmk -pdf -interaction=nonstopmode blueprint.tex` in the **exported** blueprint-W: **exit 0**, **49-page PDF**, **0 LaTeX errors**, **0 undefined-reference warning lines**, **0 overfull boxes**. W3 occupies printed pp. **33–48**. Read the rendered text of the revised lemmas and adjacent changed claims. Build output and rendered text are retained in scratch.
- `python3 .drafts/W/review-w3-r2/majorant_checks.py`: **exit 0**, `ALL ROUND-2 MAJORANT CHECKS PASS`. Exact rational arithmetic checks the constants above; output retained as `majorant-output.txt`.
- Mathlib probe: **exit 0** as above. No budget overrides, proof declarations or axioms were introduced.
- `git diff --check -- blueprint-W/reviews/w3-review-2.md`: clean; the untracked report was also checked directly for trailing whitespace and conflict markers.
- No lint or lake command was run in `/root/code/KAM-inp-wbp`; no Lean build, generated-root change, source edit, frozen edit or state-changing git command was performed. Axiom audit: not applicable to this blueprint delta review.

Acceptance closes W3-R1–R5 at the source/blueprint level. It is not a Lean implementation audit, a renewed audit of unchanged W3 material, or a certification of W4's deferred domains and parameter gates.

## Post-acceptance interface edit (sub-orchestrator kam-d4, 2026-10-30)

After the W4 review (W4-R3) and the ownership ruling, the W3 interface remark (`bpW:w3:interface-sec`) now assigns
the action–angle substitution, the D(s,r) ⊂ B_{ρ₁} check and the weight-equivalence factors to W5 instead of W4.
Three sentences changed; they are pointers only, with no mathematical change. W4 records the ruling in
`bpW:w4:from-w3`.
