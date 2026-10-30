# Track W cleanup delta review 1

**Verdict: ACCEPT.** No blocking, major, or minor finding in the requested delta. All six repairs pass the checks below. This accepts the blueprint-text delta, not the full blueprint or a Lean proof of W-NLW2.

Reviewer: GPT-6.1-Sol, codex-1 (launch identity; the generic W brief says codex-3), reasoning effort medium. Date: 2026-10-30. Method: focused, tier-2, refute-first manuscript audit, with a separate adversarial recheck of the proposed failure cases.

## Scope and frozen inputs

Reviewed exactly `git diff 1827c292 149ffb1d -- blueprint-W/parts/`, against accepted baseline `1827c292b221333727980a1a5a55251c690e5460`, target `149ffb1df725acc8d77deff684a1c3a55e6cfe6e`. Read the changed parts in the pristine `git archive` export under `.drafts/W/review-cleanup/`; surrounding unchanged text was read only to check definitions, hypotheses, and consumers. No working-tree manuscript edits were used as review inputs.

The user authorized only this report and that scratch directory. No state-changing git command, lint, lake, Lean probe, source repair, or frozen-file edit was performed. The task-specific no-lint/no-lake instruction governs this documentation review. No delegation was used.

Snapshot manifest (SHA-256 of exported target files; sizes include all source lines):

| File under `blueprint-W/parts/` | Lines | SHA-256 |
|---|---:|---|
| `w-headline.tex` | 109 | `d61a19cded0f187e5db05a3a7979b570001407ec41d18073361155a5cf7a8a0a` |
| `w0-conventions.tex` | 188 | `1c8be225befe013fb4b18db8ea62dd8c154f2c3d8e231739569209902645310c` |
| `w0-normalization.tex` | 431 | `83f7f2ebcbf97613e30433401435e374f2731749fd9ef8b44ba2ac9b7697505b` |
| `w1-sequences.tex` | 1211 | `b27ab7134c188941198e547c4577e3263e0e5f618a41ebd6983ac48b8b07e796` |
| `w3-birkhoff.tex` | 915 | `d7150c6133cfe2c26eb7c66255fefbddce4d2ffc5c35992aa237e19a8a7af1bf` |

Materials checked: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md (including D30/D41), both review briefs, W writer conventions, blueprint-W PLAN/preamble and relevant surrounding parts, W-STATEMENTS.md and W-BP0-handoff.md; authoritative main-tree frozen `CubicGrad.lean`, `ReconU.lean`, `Coeff.lean`, `EllWeight.lean`, and `Nlw2.lean`; local Mathlib sources named below. Read pinned P96-W pp. 279–280 (PDF 12–13) and 282–284 (PDF 15–17) with `pdftotext -layout`. The new contour proof is standard mathematics with local Mathlib evidence; it adds no new published-source claim requiring an internet lookup.

## Findings table

| ID | Location at target revision | Severity | Finding | Evidence / refutation status | Exact proposed fix |
|---|---|---|---|---|---|
| — | Five-file delta | — | No reportable defect found | All six checks below passed; attempted refutations failed | None |

## What I recomputed

1. **Arbitrary Banach-valued contour shift — PASS.** `w1-sequences.tex:117–125,967–998,1014–1016`, `bpW:w1:ext-rect`, `bpW:w1:fourier-shift`, `fshift-one/iter/end`, and consumer `stepW:w1:shift`.

   The rectangle joining 0 to `1+iτ` stays strictly inside the strip for both signs of τ, including τ=0. Periodicity cancels the two vertical integrals with the displayed orientation. For each coordinate, the affine slice stays in the original strip, its scalar exponential is periodic because the corresponding Fourier index is an integer, and composition preserves complex differentiability. Each integrand is continuous on a compact box, hence Bochner integrable; Fubini applies even without a global bound on u. Its compact image supplies the needed separable range. Thus `I_r=I_{r-1}` and `I_n=exp(2π k·η)` times the shifted Fourier coefficient, giving precisely the stated negative exponential. The Hilbert-space consumer supplies all hypotheses directly.

   Verified the actual declaration `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` at `/root/code/KAM/.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:292`: its ambient target is a complex normed space, its hypothesis is `DifferentiableOn ℂ f` on the product of **unordered** closed intervals, and its four boundary integrals have exactly the displayed signs and scalar actions. The Banach hypothesis is sufficient. Verified `MeasureTheory.integral_prod` in `Mathlib/MeasureTheory/Integral/Prod.lean:443`: it takes an integrable Banach-valued function on a product measure and returns the iterated Bochner integral. Restricted Lebesgue measures on the compact coordinate boxes meet its requirements; finite-dimensional reindexing supplies the coordinate iteration. Both names exist and fit; no substitute theorem is required.

   Adversarial recheck: negative τ, mixed signs of η, negative Fourier indices, and a single mode `u(z)=v exp(2π i h·z)` give the same sign and factor. No scalar-inner-product reduction or restricted sign-dependent contour lemma remains hidden in the new proof.

2. **W3 derivative at a=0 — PASS.** `w3-birkhoff.tex:298–312`, `stepW:w3:XG`, under the part's standing `a≥0`, `p≥1/2` at lines 22–25.

   The quoted “absolute series is” equality is exact: pairing the cubic majorant with `|q⁴_l|` includes all four factors `λ^{-1/2}`. For each finite truncation, Cauchy–Schwarz and weights at least 1 bound this nonnegative sum by `C_* ∏‖qᵗ‖_{a,p}`. Passing to the nonnegative limit proves absolute convergence before rearrangement. This establishes a continuous four-linear form; symmetry follows by index permutations and the symmetric sine-integral coefficient. Expanding `¼ Q(q+t e_l)^4` gives coefficient `¼·4 Q(q,q,q,e_l)=T(q,q,q)_l`. The finite-coordinate vector belongs to every space in question. No exponential-decay hypothesis is used here.

   Adversarial recheck: at a=0 the W3 quartic coefficient definition and its earlier absolute-convergence proof suffice to expand the 16 sign choices, so the reference to `stepW:w3:Gz` need not import its separate a>0 integral identification. This avoids using the a>0 W0 gradient lemma at a=0. The derivative is the unweighted coordinate derivative, consistent with the Hamiltonian-field convention, not a weighted Riesz gradient.

3. **W1 versus W0 scope wording — PASS.** `w1-sequences.tex:324–334`, `stepW:w1:ext/restr`.

   Recomputed both squared-norm comparisons using `j/λ_j≤1`; all positive weights cancel for every real p and a≥0. Restriction works for arbitrary X, with the factor `1/√2` only when `|X|` is even. The new wording “self-contained” and “analogous” correctly avoids inheriting W0's narrower `p≥1/2` and triple-convolution hypotheses. No theorem strength changed.

4. **Convolution domain — PASS.** `w0-conventions.tex:67–77`, `bpW:w0:twosided`.

   For a≥0 and s≥0, both factors lie in unweighted ℓ²; for each l, `Σ_i |c_i d_{l-i}| ≤ ‖c‖₂ ‖d‖₂`, because reflection/translation preserves the second ℓ² norm. This proves absolute convergence even at a=s=0. It does not assert closure in the weighted space at that endpoint. The displayed counterexample is correct: at a=0, s=−1, the constant sequences have finite weighted squared norm `1+2ζ(2)` but their convolution diverges.

   Searched the exported parts for convolution uses. W0/W1 algebra uses s≥1; cubic/majorant uses s=p+1/2≥1; W1 associativity uses s>1/2. Young's raw ℓ²*ℓ¹ products have ℓ¹⊂ℓ² and can use s=0, or W1's explicit summability guard (`bpW:w1:twosided-transport`, lines 297–303). The extension/restriction statements for arbitrary real p do not themselves take convolutions. No negative-s unguarded consumer was found.

5. **Extended G and Gq domain; frozen specialization — PASS.** `w0-conventions.tex:91–112`, `w0-normalization.tex:76–85,119–130`.

   For a>0 and any real p, exponential decay makes `Σ |q_j| j^k` finite by weighted Cauchy–Schwarz, for every fixed derivative order k. In particular U is continuous and both integral formulas define their values independently of the choice of containing weighted space. The extension does not assert a smoothing bound at arbitrary negative p. The stated coordinate derivative identity is restricted to a>0, p≥0 by W0's cited lemma; the `ℓ^{a,p+1}` claim is restricted to a>0, p≥1/2. W0's trilinear theorem itself retains a≥0, p≥1/2, and identifies its diagonal with the integral-defined Gq only for a>0 and real q. W1's stronger Fréchet gradient identity remains a>0, p≥1/2. These ranges match their citations.

   Compared the authoritative frozen `cubicGrad (m) (hm) (y : lp … 2) (l : ℕ+)`: it is the same integral divided by `Real.sqrt (lam m hm l)`. Here `q_j=coeff y j=y_j/(j exp j)` represents exactly ℓ^{1,1}, and frozen `reconU` reconstructs that same q. Multiplication by `λ_l^{-1/2}` equals the frozen division since m>0 and l≥1. The new broader blueprint definition leaves that specialization and the frozen weighted-coordinate encoding unchanged. No frozen definition has been silently generalized in Lean.

6. **Headline status and byte preservation — PASS.** `w-headline.tex:1–15,47`.

   D41 supports the new FROZEN status, eleven-definition count, and retained `DRAFT_SORRY` qualification; authoritative main `Nlw2.lean` still has `by sorry`. Python byte comparisons against `git show 1827c292:blueprint-W/parts/w-headline.tex` establish that the entire Definitions subsection, theorem content starting at `\label{bpW:wh:nlw2}` through before `\end{theorem}`, and all poststatement text are unchanged. The theorem-body slice hashes to `60b03e29b94dd682856806ee22351e1849f81553d0d3a39ab9570cdad667a9f4`. Only the introductory status prose and theorem title change. `git diff --name-only 1827c292 149ffb1d -- KAM/Frozen/ manifest/` is empty. This is delta-preservation evidence, not a new audit of every preexisting headline/frozen correspondence.

## Verification and limits

- Export: `git archive 149ffb1d blueprint-W blueprint | tar -x -C .drafts/W/review-cleanup`. Python subsequently verified all five exported source files byte-for-byte against `git show 149ffb1d:<path>`; hashes and byte-comparison results are preserved in `.drafts/W/review-cleanup/verification.txt`.
- Build in the export: `latexmk -pdf -interaction=nonstopmode blueprint.tex` exited 0; **81 pages**, zero `^!` errors, zero undefined-reference warnings, zero multiply-defined-label warnings. Two overfull boxes are in unchanged `w4-homological.tex:264–273,331`, outside this delta. Build transcript: `.drafts/W/review-cleanup/latexmk-review.log`; TeX log remains in its exported blueprint-W directory.
- Read the rebuilt PDF through `pdftotext -layout`, including the new contour proof on pp. 28–29, W3 field argument on p. 44, and headline status on p. 79. Extracted text is preserved as `.drafts/W/review-cleanup/blueprint-rendered.txt`.
- `git diff --check 1827c292 149ffb1d -- blueprint-W/parts/` exited 0 with no output.
- No Lean results were introduced or checked by elaboration; `#print axioms` is not applicable to this text delta. Existing theorem proof gaps and draft status are not upgraded by the PDF build.

No new suspected pinned-source errata, normalization deviations, unresolved delta findings, or frozen-object concerns were found. Unchanged global status prose elsewhere and the accepted blueprint's other mathematical arguments are outside this review. The six requested checks are complete; no repair was applied.
