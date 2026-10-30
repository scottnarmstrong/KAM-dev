# W7 review, round 1

Reviewed commit: `4fa09944df9d0f4eb3a74dec291948cf05d8e3c0`, committed `blueprint-W/parts/w7-measure.tex` (758 lines, 56,437 bytes). All line numbers below refer to that export, not the concurrently edited worktree.

Reviewer provenance: GPT-6.1-Sol (codex-3), reasoning effort medium. Independent, refute-first review; no blueprint or Lean edits.

## Verdict: ACCEPT WITH FIXES

No blocking or major mathematical defect found in W7. The conditional measure argument works, including its replacement of the source's extension argument, its explicit exceptional-set treatment, and its density and Diophantine interfaces. The minor fixes below concern an inapplicable Mathlib citation and the precision of the source-erratum discussion. W6 and W8 are still forward obligations at the reviewed commit; this review does not certify their implementation or close frozen `nlw2`.

## Materials and checks

Read the general and W-specific review briefs, AGENTS.md, docs/PLAN.md, docs/DECISIONS.md (including D30/D41), W-STATEMENTS.md, W-BP0-handoff.md, the W writer conventions, and the exported W PLAN, preamble, W0 conventions/normalization, headline, and relevant W3 interface. Compared the authoritative main-tree frozen `KAM/Frozen/Wave/Theorems/Nlw2.lean` and `KAM/Frozen/Defs/IsDiophantine.lean` directly. The old “proposed/not frozen” status prose elsewhere in the exported document was not treated as authority over D41 or the frozen files.

Source reads: pinned P96-K pp. 120–125 and 131–142 (PDF pp. 3–8 and 14–25), P96-W pp. 287–291 (PDF pp. 20–24), KP96 author pp. 22–31. Independently inspected page images of P96-K pp. 122, 123, 131, 132, 137, 140, 142; in particular all three requested suspected errata. Text extracts and images are under `.drafts/W/review-w7/`.

Pristine export made with `git archive 4fa09944 blueprint-W blueprint`, under `.drafts/W/review-w7/`. In its `blueprint-W/`, `latexmk -pdf -interaction=nonstopmode blueprint.tex` returned **0**; `blueprint.log` has **0** lines beginning `!`, **0** undefined-reference warnings, and **0** overfull-box warnings. Output: **65 pages**, W7 on pp. **52–64**. Read the rendered text with `pdftotext -layout`. The W6 forward labels appear intentionally as literal text, so the absence of undefined-reference warnings does not mean W6 exists.

`python3 .drafts/W/review-w7/check_w7.py` returned **0**, ending `boundary layer sample grid: PASS; ALL CHECKS PASS`. No lint, Lake, Lean probe, build of Lean modules, or state-changing git command was run. No new Lean result exists whose axioms could be printed.

## Findings

| ID | Location / label | Severity | Finding and evidence | Exact proposed fix |
|---|---|---|---|---|
| W7-R1-1 | Lines 56–58, `bpW:w7:ext-borel` | minor | The asserted Borel fact is correct for Borel D, but `ContinuousOn.isOpen_inter_preimage` requires **IsOpen D**. Main Mathlib `Topology/ContinuousOn.lean:188` explicitly takes `(hs : IsOpen s)`. It cannot justify the stated arbitrary-Borel-domain case. This matters because the slicing route deliberately avoids extensions and its domains can be Cantor sets. | Replace that API citation by `continuousOn_iff'` (`Topology/ContinuousOn.lean:124`): for the open target interval, obtain ambient open U with `f ⁻¹' target ∩ D = U ∩ D`, then use `MeasurableSet.inter` and `IsOpen.measurableSet`. For a subtype-valued f, first use continuity on the subtype / `continuousOn_iff_continuous_domRestrict`. No strengthening of D is needed. |
| W7-R1-2 | Lines 724, 726–732, `bpW:w7:errata` (b),(c) | minor | The source really says “Lipschitz close of order α” on p. 142, but its weighted estimate supplies sup-smallness of order α and only a sufficiently small unweighted Lipschitz seminorm. W7 correctly repairs this through θ₀; the closing phrase “not a false claim” overstates what has been checked about the literal rate. Also the spectral asymptotic on p. 123 is **unnumbered**, not equation (15); (15) is the divisor-update estimate on p. 131. | Replace the final sentence of (c) by: “The printed order-α assertion for the unweighted Lipschitz seminorm is not justified by these estimates. The proof needs only sufficiently small Lipschitz seminorm, made explicit here by θ ≤ θ₀; the measure conclusion is retained.” In (b), replace “p. 123, (15)” by “p. 123, the unnumbered spectral-asymptotic display preceding Theorem B”. |

## Frozen clauses (1) and (2)

**Density.** `bpW:w7:density` (lines 605–635) proves the required quotient in **ENNReal**, with numerator `volume (Γ ∩ Metric.ball 0 h)`, denominator `volume (P ∩ Metric.ball 0 h)`, and filter `nhdsWithin 0 (Set.Ioi 0)`. On `Fin 2 → ℝ`, the ambient norm is the sup norm, so `P ∩ ball 0 h = (0,h)^2` for h > 0; its volume is h², strictly positive and finite. Γ ⊆ P gives the upper bound 1. The lower bound is obtained by subtracting the measurable missing set from this finite measure and dividing by h². Thus there is no implicit replacement of the frozen denominator by the full ball, no Euclidean-ball substitution, and no hidden passage from a real-valued quotient to an unguarded ENNReal quotient.

The shell errors are in [0,1]; hence their tail suprema are finite and tend to zero. For `t_(k+1) < h ≤ t_k`, the missing measure is at most `sup_(l≥k) ε_l · t_k²`, yielding the stated factor q⁻². Endpoint h = t_j is covered by the adjacent choice of k. Any negative real lower bound is interpreted after truncation at zero when transferred to ENNReal. All denominators used are positive and finite. These are routine formalization details, not additional hypotheses.

**Diophantine.** The frozen definition uses `S = ∑ i, |(k i : ℝ)|` and `γ / S^τ ≤ |∑ i, (k i : ℝ) * ν i|`; it contains no 2π. W7 uses exactly this integer ℓ¹ norm. For nonzero k, S ≥ 1 and `1 + S^24 ≤ 2 S^24`. Therefore

`|k·(ω/(2π))| ≥ c/(2π(1+S^24)) ≥ (c/(4π))/S^24`.

Thus `bpW:w7:dioph` is precisely `KAM.IsDiophantine (c/(4π)) 24 (ω/(2π))`, with real exponent 24. The W6 lower bound uses c = checkα/2, giving γ = checkα/(8π) > 0 per shell; τ = 24 > 1 is chosen once after m, before I. A shell-dependent γ is allowed by frozen clause (2). No extra 2π belongs in the definition or on its integer denominator.

**Limit.** `bpW:w7:limit` (lines 693–708) proves the limit along `nhdsWithin Γ 0`, rather than the right-hand scalar filter used for density. A point I in shell k has `‖I‖∞ ≥ t_(k+1)`, forcing k → ∞ as I → 0 in Γ. Its estimate `(e_k + N_A ‖I‖∞)/(2π)` tends to zero. The frozen target is exactly `(λ₁,λ₂)/(2π)`, with Lean mode `(i : ℕ).succPNat`. To state the Lean limit with the frozen total ν, extend the subtype map arbitrarily outside Γ; equality on Γ makes this immaterial. No limit or continuity outside Γ is claimed.

**Borel sets and assembly boundary.** H1/H2 give continuity of each divisor on its Borel domain; every divisor has finite normal support. Relative open sublevel sets in Borel domains are Borel, and all unions involved are countable. The proof of `bpW:w7:measurable` is correct once R1-1's citation is fixed. In W8 one can explicitly choose shell pieces `R_k ∩ (Π_k \ E_k)` (or further measurable core restrictions), and take their countable union. This supplies Borel Γ inside the final KAM set because `Π_k \ Π_* ⊆ E_k`. The summary's “Borel Γ” means this construction, not measurability of an arbitrary superset Γ in `shell-est`. W8 must still choose the pieces, prove their frequency/embedding continuity, and enforce `sqrt(I₀+I₁) < r₀`; W7 does not independently prove those preamble clauses.

## What I recomputed (refutation attempts that failed)

### Coordinates, constants and spectrum

Writing `D = diag(1/λ₁,1/λ₂)`, the matrix is `(3/(8π)) D [[3,4],[4,3]] D`. The middle determinant is −7 and its inverse is `(1/7)[[-3,4],[4,-3]]`. Consequently W7's inverse, absolute determinant `63/(64π² λ₁² λ₂²)`, and `A⁻¹b = (8π/21)λ_J` are correct. The largest row of A is its first; that of |A⁻¹| is its second. This verifies `L_A = N_A/D_A` and `N_A < 15/(8π) < 3/5`.

The coordinate relation is `s(ζ) = λ_J·(ζ−λ_J) = (21/(8π)) b·ξ`, hence `b·ξ = (8π/21)s` and `Ω_j⁰ = λ_j + 4s/(7λ_j)`. Both the direction and the constants in this conversion check. There is no factor 16 from the printed wave coefficients.

For `‖ξ‖∞ ≤ 1/2`, |s| < 1. On plus-type l, `Ω_j⁰ ≥ (8/9)j` dominates `3β_* j`. On a difference, the exact factorization is

`Ω_i⁰−Ω_j⁰ = (λ_i−λ_j)(1−4s/(7λ_iλ_j))`.

Here `λ_iλ_j > 12`, the second factor exceeds 1/2, and increasing `x/sqrt(x²+m)` gives `λ_i−λ_j ≥ 3(i−j)/sqrt(9+m)`. This proves the claimed `3β_*〈l〉`. The drift costs at most 4α ≤ β_*, leaving 2β_* for the perturbed frequencies. This also excludes k = 0 resonances without invoking transversality.

For κ = 2, the difference of `m/(λ_n+n)` costs at most `m(i−j)/(2j²)`, and the reciprocal-frequency term costs at most `(i−j)/j²`. Thus `a_κ = m/2+1` works uniformly over the stated action cube.

Python samples used m = 0.001, 0.1, 1, 10, 1000; all nine ξ in {−1/2,0,1/2}²; j = 3,4,10,31,100; and i−j = 1,2,7,30. The separation ratio is the minimum of the singleton and difference lower-bound ratios; the κ ratio is the maximum actual error divided by the asserted upper bound:

| m | max AA⁻¹−Id residual | max A⁻¹b residual | min separation ratio | max κ ratio |
|---:|---:|---:|---:|---:|
| 0.001 | 1.33e−15 | 6.66e−16 | 1.920675 | 0.354738 |
| 0.1 | 2.22e−16 | 4.44e−16 | 1.945439 | 0.372955 |
| 1 | 4.44e−16 | 2.22e−16 | 1.982791 | 0.511878 |
| 10 | 4.44e−16 | 2.66e−15 | 2.137601 | 0.846844 |
| 1000 | 6.66e−16 | 3.55e−14 | 2.329266 | 0.920344 |

The Ω coordinate formulas agreed to ≤ 4.44e−16. Determinant and operator-norm identities also passed. These finite checks supplement the preceding algebra; they are not proofs of the uniform estimates.

### Slicing, exceptions and summation

The slicing lemma needs no convexity, connected fibers, or extension. On each coordinate fiber, two points of the sublevel set have distance < 2η/σ, so its one-dimensional measure is ≤ 2η/σ. The other-coordinate projection lies in an interval of length ρ. Even if that projection is not Borel, using its enclosing interval avoids any projection-measurability assumption. Tonelli applies to the Borel sublevel set itself. Empty domains are handled separately with measure zero.

Choosing |k_i| ≥ |k|/2 and subtracting the two Lipschitz defects leaves `(1/2−1/8−1/8)|k| = |k|/4`, giving the factor 8. The factors L_A and D_A occur in the correct places. The finite X dichotomy uses `j_* = (16c_Λ)²` correctly. For sloped exceptional divisors, θ₀ bounds the defect by half σ_X. For constant exceptional divisors, the two C4 bounds keep the drift and threshold strictly below the nonzero constant. The zero-slope and nonzero-slope minima use the stated empty-set default 1; neither positivity is assumed without A3 and finiteness.

For the preparatory difference zones, set `x = hatα/A_k` and `j₀ = ceil(x^(−2/5))`. The finite part is bounded by `2 sqrt(2) x^(4/5)` and the tail by `a_κ x^(4/5)`. Summing n up to |k|/ϑ and doubling signs gives the coefficient bounded by `16(3+a_κ)ϑ⁻²|k| A_k^(−4/5)`. No infinite family of normal differences is counted as finite.

For iteration zones, `j₀ = ceil((A_k/checkα)^(1/3))` gives `(2+a_κ)n(checkα/A_k)^(2/3)` plus `2(ε₁+ε₂)A_k^(−1/6)`. The finite part plus the one tail slab fits the j₀ count (normal indices start at 3). Each k occurs at most |k| times because K_ν ≥ 2^ν. The slowest resulting lattice term is `|k| A_k^(−1/6) ≤ |k|⁻³` for τ = 24. Summing with `# {|k|=N}=4N` gives Z₃ = 2π²/3. The explicit C_P and C_I cover these terms, the sign doubling and the exceptional-zone multiplicities; I found no missing factor.

### Exponents, boundary layer and shells

Exact rational arithmetic verifies

`w=1/23`, `hatα=α^(20/23)`, `checkα=α^(24/23)`,

`hatα^(4/5)=checkα^(2/3)=α^(16/23)`.

The remaining drift is O(α), dominated by α^(16/23) for α ≤ 1. With α(t) = t^(47/32), the excluded fraction is O(t^(1/46)), while `t^(3/2)/α(t) = t^(1/32) → 0`. This is compatible with an arbitrarily large fixed KAM smallness constant once t₀ is reduced. Also α(t) ≤ t for t ≤ 1. The coarse exponent 2/3 cannot supply this density argument under the same lower bound on α.

For the boundary layer, the four outer/axis strips cost at most 4at, and the inner max-coordinate band costs at most `2qt a+a² ≤ 3at`. The strict core inequalities give distance strictly greater than a, as the definition requires. The 7at bound remains valid when the core is empty or the band is clipped by the outer square. A direct area calculation on q = 0.1,0.5,0.9, t = 0.01,0.2,0.5 and six relative a values also passed. The shells form a genuine disjoint Borel partition, with boundaries assigned by `t_(k+1) ≤ max I < t_k`; no positive-volume seam is lost. The geometric tail sums to t_k², exactly what the density proof uses.

## W6 forward interface

At this commit W6 is absent, so this is an audit of the requested contracts, not a verification of W6 proofs. The four contracts at lines 275–303 are consistent with P96-K pp. 122, 131–135, 140–142:

- `prep-step` must use hatα and the modified difference weights, and retain the preparatory frequency shift with j⁻¹ decay.
- `freq-lip` must bound the **total** drift from the original affine pair, not merely the drift from the post-preparation pair. The post-preparation drift has j⁻¹/² decay. Fixed reindexing constants (including √3 in the preparatory divisor) must be absorbed before claiming H1/H2.
- The weighted frequency bound `sup + (a/M)Lip ≤ c ε` with ε ≤ γa gives sup ≤ cγa and Lip ≤ cγM, at the relevant stage parameter a. Shrinking γ depending on m and X can make the sum of preparatory and iterative seminorms ≤ θ₀. In the restarted iteration a is checkα, not master α. This is compatible with, but does not automatically prove, W7's H1/H2.
- `exclusion` has the correct containment direction. Levels α_ν ≤ checkα enlarge into the zones used by W7; K_ν ≥ 2^ν suffices for its counting. `final-freq` is the surviving l = 0 estimate with limiting divisor parameter checkα/2, plus the final sup-drift bound. It is a legitimate analytic output of the iteration, not an assumed density conclusion.

H1/H2 and exclusion are conditional data for a distinctly named measure theorem about arbitrary families. Density is proved by W7's independent geometry and counting, and the frozen Diophantine condition is deduced with an explicit normalization. This is not a conclusion-shaped shortcut. To avoid circularity, W6's analytic convergence and exclusion proofs must be established without assuming W7's final density result; W7 supplies the domain measure afterwards. The current text respects that separation.

## Requested source-erratum dispositions

**(a) P96-K p. 137 (PDF p. 20), Lemma 5: confirmed as a displayed-derivation defect.** The image has an r-interval of radius `4δ/|k|`, followed by measure coefficient 4. That interval has length `8δ/|k|`. For the printed oblique coordinates, with Euclidean transverse measure on v-perp, the Jacobian is |v|₂ = √n, not 1. The displayed argument therefore does not establish the coefficient 4. This confirms the writer's objection to that inference; it does not by itself prove that no sharper argument could establish the same numerical coefficient under stronger estimates. W7's coordinate-line proof establishes its own coefficient 8 independently, and subsequent source bounds use an unspecified constant.

**(b) P96-K p. 140 (PDF p. 23): confirmed notation clash, not a mathematical error.** The image's nonlinear-step exponent is the κ = 4/3 explicitly printed on p. 132 (PDF p. 15). Indeed `ε^(4/3)/hatα^(1/3)` with ε proportional to α yields `α^(1+w)`. Substituting spectral κ = 2 would instead yield `α^(1+3w)`. On p. 142 the κ in `κ/(κ+1−ϖ/4)` is again the spectral exponent. Keep the two meanings distinct in W5/W6; fix the locator noted in R1-2.

**(c) P96-K p. 142 (PDF p. 25), Lemma 10: confirmed unsupported unweighted rate; repaired argument valid.** The sentence is visibly present. Compare p. 122's weighted frequency estimates and p. 131 (14): sup-smallness and Lipschitz-smallness have different scaling. A fixed sufficiently small Lipschitz seminorm preserves slopes of the finitely many nonconstant affine divisors, while sup-smallness protects nonzero constants. Those are exactly W7's two cases in `Xzones`. Thus the order-α Lipschitz assertion is unnecessary and is not justified by the quoted estimates; the measure conclusion survives via θ₀. The source's Corollary C actually handles exceptional modes by choosing K₀ large enough that their zones use the unperturbed frequencies (p. 123 and top of p. 140). W7's small-gradient-defect argument is an explicit alternative treatment, not a quotation of that mechanism.

No additional suspected defect in a frozen statement was found. No additional source erratum is proposed beyond the requested (a) and (c) qualifications; (b) is notation. Declared deviations—Dirichlet labels, coordinate slicing, explicit constants, combined drift, rounded cutoffs, boundary layer, and measurability—are mathematically accounted for. Remaining uncertainties are the future W6/W8 proofs and Lean implementation; none was silently assumed complete.

## Fix verification (sub-orchestrator kam-d4, 2026-10-30)

Checked by the sub-orchestrator rather than by a second codex round, to save codex-3 quota:
- W7-R1-1 (ext-borel): the fact is now justified for Borel D through `continuousOn_iff'`, `IsOpen.measurableSet` and
  `MeasurableSet.inter`, with no openness assumption. Its consumers (the slicing Borel step, `measurable`, the
  assembly step) have Borel domains. CLOSED.
- W7-R1-2: the reviewer's wording for errata (c) and the p. 123 locator for (b) are in place. CLOSED.
- Discussion point (not a finding row): both mentions of "as P96-K Corollary C, p. 123" are rewritten as "an
  explicit alternative to P96-K Corollary C, pp. 123 and 140, which chooses K₀ large so that the exceptional zones
  use the unperturbed frequencies". Edited by kam-d4.
Compile: latexmk exit 0. W7 status: ACCEPTED, conditional on W6 delivering the four forward labels.
