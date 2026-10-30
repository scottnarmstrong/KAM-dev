# W4 independent review, round 2 — tight delta

**Verdict: ACCEPT (specified delta).** All three round-1 findings are resolved within W4. No new defect was found in the changed lines. This is not a renewed audit of unchanged proofs or certification of W5's outstanding work.

Reviewer provenance: **GPT-6.1-Sol (codex-3), reasoning effort medium**, independent, refute-first.

## Scope and checks

Reviewed only `git diff 7c07c3d5 b5e82025 -- blueprint-W/parts/w4-homological.tex` and round-1 findings in `blueprint-W/reviews/w4-review-1.md`, with the required repository instructions and review briefs. Read the affected passages from the pristine `git archive b5e82025 blueprint-W blueprint` export in `.drafts/W/review-w4-r2/`. Committed W4: **831 lines, 68,533 bytes**; exported bytes match `git show b5e82025:blueprint-W/parts/w4-homological.tex`, SHA256 `ebe3abccae2cab3141be0f3daf4fadbce8caca939d9d96080676362bded8f0ff`. All line references below are to that export.

- Pristine-export `latexmk -pdf -interaction=nonstopmode blueprint.tex`: **exit 0**, **79 pages**, **0 TeX error lines**, no final undefined-reference or multiply-defined-reference warnings. Layout warnings are outside this mathematical delta verdict.
- `python3 .drafts/W/review-w4-r2/checks.py`: **exit 0**, focused finite-sum checks pass. These are spot checks; the analytic arguments below justify the bounds.
- Checked the two newly cited derivative API names by source search in Mathlib's `Analysis/Calculus/FDeriv/{Linear,Bilinear}.lean`; both exist. No Lean probe was needed.
- No lint, Lean/Lake command, state-changing git command, frozen edit, generated-file edit, or writer-source edit. Only this report and the authorized scratch directory were written. No Lean result was introduced; axiom printing is inapplicable.

## Status of round-1 findings

| Finding | Status | Committed locators | Evidence / remaining action |
|---|---|---|---|
| W4-R1 — scalar normal Hamiltonian and derivative guard | **RESOLVED** | `index` 60–62; `guard` 469–478; `lie` 480–543; Theorem 1(ii) 624–626 and proof 658–659; `to-w5` 798–802 | Weak bracket is explicitly defined for all `a,p≥0`; only its identification with `DN·X_F` requires (G). The guard equivalence, wave value, bounded bilinear estimate and genuine Fréchet derivative proof are correct. The theorem and W5 handoff preserve this distinction and the additive constant. No repair requested. |
| W4-R2 — multiplicity and zero mode | **RESOLVED** | `melnikov` 165–166; `lattice` 326–333; `stepW:w4:bw` 348–354 | `A_0=1` is now explicit throughout, including `τ=0`. The four constants are counted with multiplicity, including both duplicate cases. The proof isolates the zero contribution as one and correctly dominates the nonzero sums. No repair requested. |
| W4-R3 — W3/W4/W5 ownership | **RESOLVED in W4 by explicit precedence** | `from-w3` 786–792; `to-w5` 803–808 | The coordinator ownership paragraph assigns action–angle construction, domain inclusion and phase-norm comparisons to W5 and explicitly supersedes the conflicting W3 instruction. Shifted wave weights avoid the advertised weight-equivalence factor. The outgoing contract retains holomorphic bounded Taylor components, including `Q^T`, parameter bounds and the W3 analytic-field obligation. W3 textual synchronization and W5 execution are downstream work, not claimed completed here. |

## What I recomputed

For (G), the defining ratio is `J^(1−2p) exp(−2aJ)`, `J≥3`. Exponential decay bounds it for `a>0`; for `a=0` boundedness is exactly `p≥1/2`, including the endpoint. At `a=p=1`, `exp(−2J)/J` strictly decreases, giving **`gamma=e^(−6)/3`**. The divergence example outside (G) remains valid.

Writing `w_j=omega_(a,p)(j+2)`, the frequency bound gives

`Σ |Ω_j z_j zbar_j| ≤ (1+M_0) gamma Σ w_j² |z_j| |zbar_j| ≤ (1+M_0) gamma ‖z‖ ‖zbar‖`.

Thus the stated bilinear constant is sufficient. Its differential is the sum of the two bilinear cross terms; the remainder is bounded by `(1+M_0) gamma ‖Z‖ ‖Zbar‖`, hence quadratic in the increment. Smoothing places the normal components of `X_F` in the ambient space, so substituting them gives the weak bracket termwise. The signs give exactly `DN·X_F=−L_NF`. Independently of (G), the weak pairing uses exponents `p−1` and `p+1`, whose sum is nonnegative. Nothing in the revised coefficient identity (iii) requires an actual derivative of `N`.

For the lattice delta, `k=0` contributes exactly one. For every nonzero shell `N≥1`, `(1+N^τ)²≤2(1+N^(2τ))`; summing preserves four occurrences even when exponents agree. At `τ=0`, the nonzero `N^0` sum is `S_0−1`, safely bounded by the displayed `S'_0=S_0`. All resulting powers are bounded by `sigma^(−(2τ+3))` for `0<sigma≤1`. Independent shell sums through `N=20000`, for `τ∈{0,.5,1,3,3.5,5}` and `sigma∈{.02,.05,.1,.2,.5,1}`, give maximum ratios to the claimed bound respectively **0.146602, 0.274276, 0.275564, 0.185233, 0.116519, 0.005979**. No counterexample was found.

No new suspected pinned-source erratum or unmarked mathematical deviation was identified in this delta. Round-1 source errata are not re-audited here; the added guard is explicitly marked as the authors' addition. Unchanged statements, source pages, frozen signatures and later iteration estimates remain outside this tight review.
