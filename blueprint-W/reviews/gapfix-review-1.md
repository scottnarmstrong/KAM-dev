# W4–W6 tight delta review: gap repairs

**Verdict: ACCEPT WITH FIXES (one minor external-fact description correction).** All ten named SOURCE_GAP obligations are substantively closed by this delta. The new Riesz construction, symmetry applications, triangular integral proof, parameter-difference bounds, preparatory displacement bound, and direct W6 divisor/Borel arguments are valid. Correct the description of complex `InnerProductSpace.toDual` from “linear” to **conjugate-linear**. This does not invalidate the construction or require a changed hypothesis.

Provenance: independent, refute-first review; requested reviewer designation **GPT-6.1-Sol, codex-1** (launch designation takes precedence over the brief's codex-3 designation). Focused tier-2 manuscript audit, followed by a separate adversarial recheck of the candidate finding and the repaired estimates. This is a blueprint delta verdict, not Lean proof closure or a full re-audit of W4–W8.

## Frozen scope and permission envelope

Reviewed ONLY `git diff ccf61a7e 5aa0e866 -- blueprint-W/parts/w4-homological.tex blueprint-W/parts/w5-kamstep.tex blueprint-W/parts/w6-iteration.tex`, reading unchanged surrounding material to verify applications and consumers. Full revisions:

- Baseline: `ccf61a7ea2b4b2cbfdb64984e432aed87594b892`.
- Reviewed: `5aa0e866ae510d85219d51e22d065b04e7a5dcd8`.
- Pristine export: `.drafts/W/review-gapfix/`, produced with `git archive 5aa0e866 blueprint-W blueprint`.
- Mathlib inspected read-only: `/root/code/KAM/.lake/packages/mathlib`, HEAD `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The launch authorizes this report and scratch directory only; no manuscript repairs, git mutations, lint, or Lean/Lake commands were run. Context checked: AGENTS, PLAN, DECISIONS D30/D41, both review briefs, writer conventions, exported blueprint plan/preamble/W0/headline, W-BP0 handoff and statement document, frozen main `Wave` theorem surface, graph packet NOTE fields, and relevant W1/W4–W8 interfaces. No model or definition has been silently substituted.

| Exported file | Lines | SHA-256 |
|---|---:|---|
| `parts/w4-homological.tex` | 853 | `6155560473fbf3f0292fd08ed158aa2d221c27dcc6f5937c9114eb8a350872fe` |
| `parts/w5-kamstep.tex` | 754 | `d8daf4af9d63da34ae860d2ce9aeefec0a5fe8e7d603cdddb26af6f463e5153c` |
| `parts/w6-iteration.tex` | 435 | `afc3683d68df30065aca21af4ba1e7af7a65b3700b167d6ecbacdc517744ed06` |

All blueprint line locators below refer to that export at 5aa0e866.

## Per-gap verdicts

| Graph obligation | Repaired anchor | Verdict | Recomputed evidence / hypothesis check |
|---|---|---|---|
| `stepW:w4:schurrep` | W4:53–62, 419–435 | **CLOSED**, minor wording fix F1 | The transported bilinear form has the same norm because κ is onto and isometric. With coordinate conjugation C, `B(v,w)=β̂(Cv,w)` has exactly the semilinearity required by Mathlib. `T=C B♯ C` is complex linear, and `⟨Tx,y⟩₀=⟨B♯Cx,y⟩=β̂(x,y)`. The Hilbert dual norm formula proves equality of norms; the entries are `μ_i μ_j β(e_j,e_i)`. The converse follows by Cauchy–Schwarz and the same norm formula. Both conjugations are necessary and correctly placed. |
| `stepW:w5:t-comp` | W5:57–61, 300–309 | **CLOSED** | `DP(w)=symp(X_P(w),·)` holds in a neighbourhood by the smoothing-Hamiltonian definition. The form is continuous bilinear; holomorphic `X_P` gives differentiability of this operator-valued derivative. Thus the listed second-derivative symmetry theorem applies over ℂ without assuming symmetry as a new premise. Block transpose conclusions follow. |
| `stepW:w5:c-skew` | W5:450–453 | **CLOSED** | F is C² by `s-class`; differentiating `DF(w)B=symp(X_F(w),B)` yields the second derivative. The same external theorem supplies symmetry. Antisymmetry of `symp` then gives `symp(DX_F A,B)+symp(A,DX_F B)=0`. |
| `stepW:w5:n-exp` | W5:68–71, 491–501 | **CLOSED** | For continuous Banach-valued g, set `h(t)=∫₀ᵗg`. Integration of `((t−1)h(t))′=h(t)+(t−1)g(t)` has zero boundary contribution and gives the triangular identity with weight `1−t`. Applying this to `{N̂−R,F}∘φᵗ` and adding `R∘φ` yields exactly `{(1−t)N̂+tR,F}`, with the displayed signs. No triangular Fubini premise is used. |
| `stepW:w5:p-inv` | W5:526–543 | **CLOSED** | Both derivative and inverse differences now retain `|ξ−ζ|`. Smallness gives `16M_F/(ση²)≤1`, the inverse norms are ≤2, and the resolvent identity gives the weighted inverse difference ≤`4|ξ−ζ|`. The assembled Lipschitz quotient plus sup term is `(13/2)|Y|+2λ|Y|^L≤7|Y|^λ`. No parameter-diameter bound is needed. |
| `stepW:w5:a-hol` | W5:62–67, 662–666 | **CLOSED** | `Re(ξ_i+y_i)>0` puts the argument in the slit plane and excludes zero. The principal cpow root is complex differentiable there and squares to its argument. Composition with the affine coordinate and entire exponential is valid; on positive real inputs the branch is the positive real square root. |
| `bpW:w6:prep-step` | W6:232–235, 250–254 | **CLOSED** | The new citation is only to `zones(i)`, whose hypotheses are Borel Π and `0<α≤α₀`, already present. Negating each strict zone inequality on `Π\Ξ` gives the non-strict lower bound. The difference-mode weight is exactly `|I−J|min(I,J)^(−1/4)` and the loss is `1/2=2β`; other Dirichlet weights dominate W4's. No admissible-family premise is imported. |
| `stepW:w6:p-lipp` | W6:260–263 | **CLOSED** | W5 `f-flow` supplies `|φ¹−id|_{p_+,r}≤M_F` directly from the time integral, rather than the weaker λ-norm bound `2M_F`. In the modified case W5 data give exactly `M_F=c_F^natural ε/(α̂ σ_P^(t^natural−1))=M_{F,P}`. `s₀=s−5σ_P` and `η_P≤1/8` ensure `D₀⊂U=D(s−2σ_P,r/2)`. The Lipschitz conclusion remains available from step(v). |
| `bpW:w6:freq-lip` | W6:299–309 | **CLOSED** | “The three constants … are ≤α” now excludes θ. The proof bounds θ only by θ₀, consistently with W7's definition. The constants γ, γ₁, M and hence θ depend on m only, selected before α. No claim `θ≤α` survives. |
| `stepW:w6:fl-borel` | W6:321–325 | **CLOSED** | Each preparatory divisor is a finite affine function on all ℝ², so its strict sublevel set is open and `S_kl=Π∩U_kl` is Borel. Z is countable, hence Ξ and `Π\Ξ` are Borel. The frequency maps are Lipschitz, hence continuous, before admissibility is asserted; convergence(i) obtains subsequent Borel domains recursively. Neither W7's ambient measurable lemma nor an already admissible family is required. |

## External facts checked against actual Mathlib text

All requested names exist. Paths below are relative to the Mathlib checkout above.

| Name | Actual declaration and applicability |
|---|---|
| `InnerProductSpace.continuousLinearMapOfBilin` | `Analysis/InnerProductSpace/Dual.lean:193`: takes `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`, returns `E →L[𝕜] E`; complete inner product space. The constructed B has precisely this type. |
| `InnerProductSpace.continuousLinearMapOfBilin_apply` | Same file:205: `⟪B♯ v,w⟫=B v w`, with the convention used in the new proof. |
| `InnerProductSpace.toDual` | Same file:136: `E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E`, **conjugate-linear**, not complex-linear. Its norm isometry supplies the claimed formula. `toDual_apply_apply` exists at :175 with the stated evaluation identity. |
| `second_derivative_symmetric_of_eventually` | `Analysis/Calculus/FDeriv/Symmetric.lean:464–468`: `[IsRCLikeNormedField 𝕜]`, `hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y`, `hx : HasFDerivAt f' f'' x`; concludes `f'' v w=f'' w v`. Matches the listed external and both point-of-use arguments. |
| `Complex.cpow_ofNat_inv_pow` | `Analysis/SpecialFunctions/Pow/Complex.lean:145–147`: `(x ^ ((ofNat(n):ℂ)⁻¹)) ^ (ofNat(n):ℕ)=x`, `[n.AtLeastTwo]`. Instantiate n=2; no slit-plane hypothesis needed for this identity. |
| `Complex.mem_slitPlane_iff` | `Analysis/Complex/Basic.lean:630`: exactly `0<z.re ∨ z.im≠0`. The first disjunct is supplied. |
| `DifferentiableAt.cpow_const` | `Analysis/SpecialFunctions/Pow/Deriv.lean:116–118`: requires differentiable f and `f x∈slitPlane`. Identity/affine f supplies differentiability, and the positive-real-part guard supplies the branch condition. |
| `intervalIntegral.integral_hasDerivAt_right` | `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:725–728`: requires interval integrability, strong measurability at the endpoint filter, and continuity there. A continuous g on `[0,1]` supplies these in its interior; for ordinary derivatives at the two endpoints extend g continuously by constant endpoint values. This harmless extension leaves all integrals unchanged. Equivalently use within-interval derivatives. Thus the triangular proof is valid for the stated continuous-on-interval input. |

The extra square-root modulus and positive-real-branch assertions follow directly from the principal logarithm definition (`exp((1/2)log ζ)`): its modulus squared is `|ζ|`, and for positive real ζ its logarithm is real. They introduce no extra regularity hypothesis.

## Finding and adversarial recheck

| ID | Severity | Anchor and quoted text | Finding / exact proposed fix | Refutation status |
|---|---|---|---|---|
| F1 | **minor** | W4:60–61, “`InnerProductSpace.toDual` is a linear isometry equivalence” | For complex scalars replace “linear” with “conjugate-linear”; preferably display `E ≃ₗᵢ⋆[ℂ] E*`. Preserve the norm formula and the rest of the proof. | Survived a separate recheck: Mathlib's definition and module documentation explicitly say conjugate-linear. At `u↦iu`, `toDual(iu)=−i·toDual(u)`, contradicting complex linearity. Conversely, an attempt to turn this into a substantive obstruction fails: the proof only uses its isometry, and `continuousLinearMapOfBilin` already composes two conjugate-linear maps to return a linear map. |

No blocking or major finding survives. Endpoint handling for the interval-integral API is an implementation detail described above, not an extra premise or an open gap. No new suspected defect in a pinned source was found; the existing source deviations outside this delta are not re-adjudicated.

## Inequalities, cycles, and consumers

Independently recomputed the small-scale comparisons using `|W|_{p,r}≤|W|_{p_+,ηr}` and output rescaling by η⁻². From `M_F≤ση²/16`:

- `8M_F/(ση²)≤1/2`, giving inverse norm ≤2.
- `λ|ΔDφ|≤16η⁻²λN₁/σ≤|ξ−ζ|`, giving inverse difference ≤`4|ξ−ζ|`.
- `λ|Δφ|_{p,ηr}≤2η⁻²M_F|ξ−ζ|≤(σ/8)|ξ−ζ|`.
- The transport term contributes `2·(2/σ)·(σ/8)|Y|=(1/2)|Y|`. Adding the inverse-difference term `4|Y|`, direct parameter term `2λ|Y|^L`, and sup `2|Y|` gives `13/2`, then 7. The repairs neither divide by zero nor assume λ>0 to divide by λ.

Refutation attempts checked misplaced conjugation in the complex Riesz construction, swapping matrix indices, a missing parameter-distance factor, doubling the preparatory displacement, and recurrence of the W7 admissibility cycle. None refutes the repaired claims. For Borel recursion, frequency continuity follows from the already proved Lipschitz estimates, not from the desired admissibility; countable relative-open removal then supplies domains. The direct divisor argument similarly uses only definitions and the unperturbed affine maps.

**Consumer statement change:** literally, yes: W6 `freq-lip` replaces the overbroad “all ≤α” by the three epsilon bounds and `θ≤θ₀`, and makes θ's choice order explicit. This is the intended correction of a false/ambiguous extra inequality, not a new loss at a consumer. W7 `family` at :267–275 already requires exactly epsilon∈[0,α] and θ∈[0,θ₀]; W8 `w6-general` at :213–215 explicitly uses `θ=425(1+M)max(γ,γ₁)≤θ₀`. Neither uses `θ≤α`. All other repaired result statements retain their bounds, hypotheses and quantifiers, including prep-step(iii)'s sharp `M_{F,P}` and pullback's constant 7. No frozen declaration changes. W7/W8 files themselves are byte-unchanged between the two commits (`git diff --quiet` exit 0).

Two ancillary changes in the allowed diff are sound: W5 `s-solve` now cites W4 `lie(iv)` for the derivative identification with the available weight guard, rather than `lie(ii)`; W4's separation lemma gets a supersession note pointing to W7 `sep`, without a changed mathematical assertion.

## Verification and closeout

- `git archive 5aa0e866 blueprint-W blueprint | tar -x -C .drafts/W/review-gapfix`: exit 0; compilation and reading used this export, not the live writer's files.
- `latexmk -pdf -interaction=nonstopmode blueprint.tex` in the exported `blueprint-W`: **exit 0**, `Output written on blueprint.pdf (115 pages, 1601864 bytes)`; zero `^!` errors, zero undefined references, zero multiply-defined-label warnings. The build log is `../build-gapfix.log`.
- `pdftotext -layout blueprint.pdf ../rendered.txt`: exit 0; checked rendered passages for Riesz, the three new W5 externals, pullback bounds and W6 Borel proof.
- Read P96-K printed pp.130–132 (PDF 13–15) and 140–141 (PDF 23–24) using `pdftotext -f ... -l ... -layout`. These support the surrounding pullback and modified-step context; the new constants and elementary repairs were recomputed rather than attributed to the source. Extracts are in the scratch directory.
- Mathlib verification was source inspection, not an elaboration or kernel check. No Lean result was authored, so `#print axioms` is not applicable. No lint or Lean/Lake command ran, as required by this docs-only review brief.
- All ten requested gaps classified; one minor wording fix remains for the writer. Scope excludes unchanged proof obligations, global graph revalidation, and theorem closure. Only this report and the permitted scratch export/artifacts were written; no commit or other state-changing git command ran.

## Fix verification (sub-orchestrator kam-d4, 2026-10-30)

F1 (minor): w4-homological.tex L60–61 now reads "InnerProductSpace.toDual is a conjugate-linear isometry
equivalence E ≃_{ℓi}^⋆ E* (only its isometry is used)". Edited by kam-d4. Compile: exit 0, 0 errors, 0 undefined
references, 115 pages. CLOSED. The gap repairs to W4, W5 and W6 are ACCEPTED.
