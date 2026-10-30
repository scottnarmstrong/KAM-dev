# W2 independent review, round 1

**Verdict: ACCEPT.** No blocking, major, or minor defect in W2 was found. The reconstruction argument delivers the four conjuncts of frozen `nlw2` clause (5), with its last constant supplied by `bpW:w2:clause5`. This accepts the blueprint argument and its consumer interface; it does not certify W1, construct the W8 family, or close a Lean theorem.

Provenance: GPT-6.1-Sol (codex-3), reasoning effort medium. Reviewed commit: `98d8c1b337ce7ee7c7daef316b89b16583e2b9a6`. Reviewed file: `blueprint-W/parts/w2-reconstruction.tex`, 403 lines, 31,254 bytes, SHA-256 `918a2df76dd4b837f6c4a3eff8dc9b5b3caf7a6748bfa4bd116d41c054eb2de7`.

The review used the pristine `git archive` export under `.drafts/W/review-w2/`. The live W1 file changed during review; those edits were excluded. The pinned W1 SHA-256 is `1a63bd388146a6084dfd9d28074812d84f41271785bdc52404a34842f58737d4`.

## Findings

| ID | Location/label | Severity | Finding | Evidence | Exact proposed fix |
|---|---|---|---|---|---|
| — | W2 | — | No actionable defect found. | Checks and dependency qualifications below. | None. |

## Materials and build

Read the review and writer briefs, repository instructions, PLAN and DECISIONS (including D30 and main-checkout D41), W-STATEMENTS revision 1, W-BP0 handoff, and the exported blueprint PLAN, preamble, W0 conventions/normalization and headline. Read the W1 statements and proof steps actually consumed by W2. The authoritative comparison used `/root/code/KAM/KAM/Frozen/Wave/Theorems/Nlw2.lean` and the frozen definitions `IsClassicalSolution`, `ReconU`, `ReconV`, `CubicGrad`, `Coeff`, and `IsAnalyticTorusEmbedding`, rather than the older proposal-status text in the blueprint headline.

Read P96-W printed pp. 277–280 (PDF pp. 10–13), pp. 272–273 (PDF pp. 5–6), and pp. 290–291 (PDF pp. 23–24), using `pdftotext -layout`; additionally inspected the page image of p. 278. W2 directly consumes no P96-K or KP96 theorem, so no independent audit of those sources is claimed.

In the pristine export, `latexmk -pdf -interaction=nonstopmode blueprint.tex` returned **0** and produced **47 pages**. The final log contains **0** lines beginning `!`, **0 undefined references**, and **0 overfull boxes**. W2 occupies pp. **27–33**. Read the rendered W2 text extracted from that PDF, including the main theorem and constant corollary. No lint or build was run in the docs worktree, as required by the specific review brief.

## Frozen clause (5), conjunct by conjunct

| Frozen requirement | W2 statement and proof | Result |
|---|---|---|
| `∀ z ∈ univ ×ˢ Icc 0 π, AnalyticAt ℝ (fun z : ℝ × ℝ => reconU … (K (θ₀ + z.1 • ν)).1 z.2) z` | `bpW:w2:main` (a), lines 313–314; `bpW:w2:curve` (i), `stepW:w2:joint`. | Exact function, scalar field, ambient product, and point quantifiers. Analyticity on all of `ℝ × ℝ` is proved and then restricted; no relative analyticity is substituted at the endpoints. |
| `IsClassicalSolution m hm u` | Main (b); curve (v), `stepW:w2:frozen`, lines 281–289. | Exact frozen predicate. There are **four existential derivative witnesses**, in order `ut, ux, utt, uxx`; together with `u` these are the five continuous functions. |
| `∀ t, ∀ x ∈ Icc 0 π, HasDerivAt (fun s => reconU … (K (θ₀+s•ν)).1 x) (reconV … (K (θ₀+t•ν)).2 x) t` | Main (c); `stepW:w2:t1`. | Two-sided time derivative at every real time, with the exact frozen velocity reconstruction. |
| `|u| + |derivWithin (u t) (Icc 0 π) x| + |reconV …| ≤ C √(I₀+I₁)` | Main (d) first gives `M_m B`; `bpW:w2:clause5` substitutes `B=C₃√(I₀+I₁)` and enlarges the common constant. | Exact `derivWithin`, domain, velocity term, and quantifier order after the corollary. Main alone deliberately uses the intermediate constant. |

For the second row, the witnesses are explicitly

`ut=V_m(Y₂)`, `ux=D¹Y₁`, `uxx=D²Y₁`, `utt=uxx-m*u-u^3`.

The last definition does not assume the equation: `stepW:w2:t2` independently identifies the derivative of `ut` with this function. Joint analyticity gives continuity of all five uncurried functions on `univ ×ˢ Icc 0 π`. The two time clauses use `HasDerivAt`; the space clauses restrict the proved two-sided derivatives using `HasDerivAt.hasDerivWithinAt`. `uniqueDiffOn_Icc Real.pi_pos` identifies `derivWithin` at **both endpoints** as well as the interior. Every sine summand vanishes at 0 and π, so the Dirichlet equalities hold at all times. The cubic is exactly the frozen `cubicGrad`, and the equation has the frozen negative mass and negative cubic signs.

## Hypotheses and W8 constant interface

H1 is frozen clause (3)'s analytic embedding; its analyticity projection is `h.2.1`. H2 is clause (4) verbatim for a fixed action, including derivatives at time 0 for every angle and positive mode. H3 is clause (3)'s bound. To obtain H1/H3 for `I ∈ Γ`, W8 takes `hI` from the frozen inclusion `Γ ⊆ {I | (∀ i, 0 < I i) ∧ …}` and specializes (3) to `I, hI` and its membership proof. No PDE, reconstructed time derivative, or force identity is an input hypothesis. The embedding assumption is stronger than W2 uses, but it is literally available; the optional analyticity-only helper is separately described.

The all-time shift is valid: at `θ=θ₀+tν`, substitute `h=s-t` in the time-0 invariance statement. Then `θ₀+tν+(s-t)ν=θ₀+sν`. No periodicity or frequency nonresonance is needed for this step. Banach differentiability of the analytic orbit, followed by the continuous coefficient functionals, identifies its derivative coordinates. In particular, the additional weighted regularity of `λp` is a **consequence**, not an extra premise or an application of an unbounded operator to arbitrary phase-space vectors.

Recomputed

`c₀ = sqrt(2/π)/sqrt(e²-1) = 0.315661568929…`,

`M_m = c₀ (2+(1+m)^(1/4)) > 0`.

For displacement and its first space derivative, the feature norm squares are bounded by `(2/π) Σ exp(-2j)`, since `λ_j⁻¹ j^(2k-2) ≤ 1` for `k=0,1`. For velocity, `λ_j/j² ≤ sqrt(1+m)`. Cauchy–Schwarz and the **max** product norm therefore give exactly the claimed sum bound. The second space derivative needs only summability, not this same uniform feature bound.

With `r=√(I₀+I₁) ≥ 0`, choose `C=max(1,M_m) C₃` after the fixed mass and before the actions. Then `C≥C₃>0` and `M_m C₃ r≤Cr`. W8 must apply W2 with the original bound **`B=C₃r`**, as lines 357–359 do; using the enlarged `Cr` and then claiming `M_m Cr≤Cr` would fail. Increasing C preserves clause (3) and affects no other frozen clause. Positivity of r is unnecessary for this corollary. The construction of a uniform `C₃(m)` remains W6/W8 work; W8 is not written in this commit, so this review verifies the exact available interface from clauses (3)–(4), not their independent construction.

## Force identity recomputed

Write `w_j=j exp(j)`, `q_j=y_j/w_j`, `λ_j=√(j²+m)`, and

`G_j = (∫₀^π U(y)^3 φ_j)/√λ_j`.

Then `√λ_j G_j` is precisely the sine coefficient of `U(y)^3`. The uniformly absolutely convergent sine reconstruction has those same coefficients; sine completeness and continuity imply equality on `[0,π]`, including its endpoints. The linear summand satisfies

`√λ_j λ_j q_j φ_j = (j²+m) q_j φ_j/√λ_j`,

so `Σ_lin=-D²y+mD⁰y`. The derivative-coordinate identities give

`U(Y₁')=Σ (λ_j coeff(Y₂)_j)/√λ_j φ_j=V(Y₂)`

and

`V(Y₂')=-Σ_lin-Σ_cub=D²Y₁-mU(Y₁)-U(Y₁)^3`.

There is no extra weight in the cubic force: the factors `w_j` enter only when moving between the Banach vector derivative and `coeff`. In `stepW:w2:fsum`, `G_j=G^w_j/(j² exp(j))`; multiplication by `√λ_j` leaves a summable exponential majorant. This also justifies splitting the two force sums, rather than manipulating nonsummable default `tsum` values.

Independent numerical check: `.drafts/W/review-w2/check_force.py`, run with `python3 check_force.py`, exit **0**. It takes `m=0.7`, weighted displacement `(0.8,-0.4,0.3)`, weighted momentum `(0.2,0.6,-0.1)`, computes the frozen integral by 128-point Gauss quadrature, and compares it to the exact quartic sine-integral coefficients. All cubic output modes **1 through 9** are included; this is not a truncation back to the original three modes. On 701 space points, including endpoints:

```text
integral cubicGrad vs exact quartic coefficients: max error 4.510e-17
force sum over all generated modes 1..9 vs u^3: max error 5.898e-17
linear force vs -uxx+m*u: max error 1.110e-16
reconU(ydot) vs reconV(p): max error 0.000e+00
reconV(pdot) vs uxx-m*u-u^3: max error 2.220e-16
c0=0.315661568929; M_0.7=0.991763934673
bound lhs=0.376114902702 <= rhs=0.935628224716
PASS (finite-mode normalization/sign check; not a proof of an invariant orbit)
```

## W0/W1 dependency audit

All the mathematical W1 statements cited by W2 exist in the **reviewed commit** and have the required specialization. No missing or merely planned W1 statement was silently supplied.

| Input | Pinned location in W1 (`w1-sequences.tex`) | What W2 actually uses |
|---|---|---|
| `bpW:w1:space`, `ext-lp` | Space/transport lemma; external facts lines 66 onward | Continuous coefficient evaluations, `coeff=κ₁,₁`, coordinate separation, Hilbert norm estimates. |
| `bpW:w1:coordinatewise` | Lines 147–169 | Same-weight specialization `(1,1)→(1,1)` identifies coefficients of a differentiable curve's derivative; no lowered-space converse is assumed by W2. |
| `bpW:w1:trilinear` (iv), `stepW:w1:trifrozen` | Frozen identification lines 453–459 | Literal equality between frozen integral `cubicGrad` and `G_q(κy)`. |
| `bpW:w1:cubic-analytic` (iv) | Lines 461–490 | `G^w_j=ω₁,₂(j) cubicGrad_j` belongs to real ℓ². |
| `bpW:w1:sine-completeness` (ii) | Lines 579–601 | Continuous function with all zero sine coefficients vanishes on the closed interval. |
| `bpW:w1:sine-feature` (i)–(iii) | Lines 603–635 | Real analytic Hilbert-valued features, coordinates, and absolutely convergent pairings, for arbitrary polynomial coefficient growth. |
| `bpW:w1:recon-analytic`, `stepW:w1:recder` | Lines 637–658 | Joint reconstruction and feature derivative identification. W2 also spells out the joint-analytic composition itself. |
| `bpW:w1:hamfield` (v) | Proposition at lines 529 onward | Used only to explain the hidden-regularity remark; not needed for the actual reconstruction proof. |

W0's `bpW:w0n:force` is equation (4), within `bpW:w0n:pde-equiv`; its proof `stepW:w0n:force` is at lines 186–192 of `w0-normalization.tex`. W2 uses the **static force identity**, not the proposition's additional time-regularity hypotheses. Its proof depends only on W0 gradient/smoothing and sine completeness. Thus no cycle with W2 or W8 is introduced.

W1 remains under separate revision/review. The acceptance here is conditional on retaining these interfaces with valid proofs. One upstream API spelling deserves preservation in that separate revision: pinned W1 says ASCII `AnalyticAt.comp2` (external list and reconstruction proof), whereas Mathlib provides `AnalyticAt.comp₂`. W2's explicit replacement at lines 255–259 uses the existing `AnalyticAt.prod` and `.comp`, so this is **not a W2 proof gap**. Also, W1 states its reconstruction corollary with parameter `ℝⁿ`; W2's direct product-composition proof covers its scalar time domain without relying on an unstated literal type equality `ℝ = (Fin 1 → ℝ)`.

## Mathlib and Lean feasibility checks

One serialized probe was run, from `/root/code/KAM`:

`LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/BpWW2Review1.lean`

Exit **0**, no errors or warnings. The module imported analytic constructions, inner-product calculus, derivative shift and the real tangent-cone API. It checked `innerSL`, `ContinuousLinearMap.analyticAt_bilinear`, `AnalyticAt.prod`, `HasDerivAt.comp_sub_const`, `uniqueDiffOn_Icc`, `HasDerivWithinAt.derivWithin`, and `HasFDerivAt.comp_hasDerivAt`. Three proved examples verified the actual applications: `(innerSL ℝ).analyticAt_bilinear` on a real inner-product space, translating a derivative at 0 to time t, and obtaining `derivWithin = d` for every `x ∈ Icc 0 π` from a two-sided derivative. In particular, `innerSL`'s sesquilinear type reduces correctly over ℝ. The temporary main-checkout probe was deleted; its source is retained only in the authorized review scratch directory.

Source searches also confirmed `AnalyticAt.smul`, `HasDerivAt.inner`, `Summable.of_norm_bounded`, `tsum_geometric_of_lt_one`, `abs_real_inner_le_norm`, `Real.div_sqrt`, and the derivative/projection operations used in W2. The geometric theorem is indexed by ℕ, so its use for positive modes requires the ordinary `j=n+1` reindexing and multiplication by `exp(-2)`; the resulting sum is exactly `(e²-1)⁻¹`.

No Lean theorem implementing W2 was submitted, so there is no main-result `#print axioms` receipt or kernel-closure claim. The API probe contains no assumed PDE or reconstruction theorem and no `sorry` or budget override. It is evidence of feasibility of these local APIs only.

## Source fidelity, refutation attempts, and limits

P96-W Lemma 1 on p. 278 assumes a real analytic coefficient solution and concludes a classical real analytic PDE solution. W2 openly reorganizes its proof using bounded functionals; its velocity identification and explicit bound are declared strengthenings. The p. 290 assembly really invokes Lemma 1 to recover PDE solutions from torus motions. No new source premise is added by W2.

The existing N-4 erratum is confirmed on the p. 278 image: the second `u_tt` equality prints `λ_j² q_j − √λ_j ⟨f(u),φ_j⟩` inside the factor `1/√λ_j`; the linear term must be **`−λ_j² q_j`**, from `q̇=λp`, `ṗ=−λq−G_q`. The next printed line already has the correct negative linear force. W2 records and corrects this openly. No new suspected source erratum or frozen-statement defect was found.

Refutation attempts checked endpoint uniqueness, two-sided time translation, the square-root factors in both reconstructions, the `j exp(j)` weights, the cubic sign, summability before splitting force sums, the product max norm, and constant dependence/quantifier order. None refuted W2. The proof deliberately avoids assuming that the unbounded diagonal wave operator is a bounded endomorphism of `WaveSpace`. W1 proof closure and W8 construction remain outside this scoped acceptance.

Only this report and the authorized scratch export/check artifacts were written, apart from the explicitly permitted transient Lean probe, which was removed. No state-changing git command, frozen edit, generated-root edit, or docs-worktree Lean/Lake invocation was performed. `git diff --check` returned **0** during validation; concurrent edits to the live blueprint were not reviewed or changed.
