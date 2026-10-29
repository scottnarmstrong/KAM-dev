# Independent audit W-BP0-1
FAIL

Audited `/root/code/KAM-w`, branch `w`, HEAD `fd2c7ec172f80e19ba3629934830747c34182a70`, 28 October 2026, against `.drafts/briefs/W-BP0-audit.md`. This is a mathematics/source-fidelity audit, not a Lean certification. The failure is localized: the errata check contains a false mass-threshold assertion, and the headline is not a non-weakened transcription of the source's family-embedding conclusion. I found no counterexample or unpaid case in the central W0 nonresonance, cubic bound, corrected quartic coefficients, or specialized nondegeneracy proofs. Those results should be retained. The requested report is the only deliverable changed; no commit was made.

## Findings

| ID | Severity | Location | Claim | Evidence | Required fix |
|---|---|---|---|---|---|
| W-A1 | Medium | `docs/tracks/W/errata-check-W0.md:137–138`; `.drafts/handoff-W-BP0.md`, N-1 summary | The printed norm-one bound holds for all sequences iff `m ≥ 3`. | The displayed supremum is wrong: `sup_{j≥1} j/sqrt(j²+m) = 1`, not `1/sqrt(1+m)`. At `m=3`, `q=e₂`, its squared norm ratio is `4/sqrt(7)=1.511857892… > 1`. For every finite positive mass, sufficiently high modes violate the bound. | Replace the threshold sentence with: the operator norm is exactly `sqrt(2)` for every fixed `m>0`; the printed norm-one bound fails for every such mass. Keep the N-1 source-error verdict and the blueprint's corrected bound. Correct the handoff too. |
| W-A2 | Medium | `blueprint-W/parts/w-headline.tex:39–53,76–80` | The proposal represents the source specialization with all weakenings accounted for. | P96-W pp. 272–273 and 288–289 give an embedding of the entire union of parameter tori. The proposal requires continuity of the family and an embedding only on each individual torus. It never requires `K_I(θ)=K_{I'}(θ')` to imply `I=I'`. It also replaces the source's Lipschitz family by a continuous family, beyond merely dropping an extension off the Cantor family. | For a non-weakened family conclusion, require the induced map on `Γ × T²` to be an embedding of the family, with the appropriate regularity in Cartesian coordinates. Otherwise explicitly declare these additional weakenings and seek review of that weaker contract. Do not describe it as the full specialized Main Theorem. Stability and Whitney regularity remain deferred as D30 permits. |
| W-A3 | Low | `blueprint-W/PLAN.md:76` | The multiplier norm bound `(1+m)^(r/2)` is stated without restricting `r`. | It holds for `r≥0`. For `r=-1`, the norm from `ℓ^{a,p-1}` to `ℓ^{a,p}` is `sup_j j/λ_j=1`, exceeding `(1+m)^(-1/2)`. At `m=1,j=10`, the ratio is `0.995037…`, versus bound `0.707106…`. | Add `r≥0`, or state the all-real-`r` bound `(1+m)^(max(r,0)/2)`. Supply `p≥1/2` where W1 uses the present trilinear theorem; state the summability range `s>1/2` in `w1:young`. |
| W-A4 | Low | `scripts/wave/w0_checks.py:10,18`; prescribed isolated invocation | The checks are reproducible with the audit's exact command. | `python3 -I scripts/wave/w0_checks.py` exits 1: `ModuleNotFoundError: No module named 'sympy'`. Sympy is installed only in the user site, which isolation excludes. An explicitly documented fallback ran the unedited script to completion and passed. | Make dependencies available to the isolated interpreter, or document an appropriate environment/interpreter. Preserve the distinction between the failed prescribed invocation and the successful fallback. |
| W-A5 | Low | `blueprint-W/parts/w0-normalization.tex:211–214`; `blueprint-W/PLAN.md:67` | P96-W Lemma 1's compressed proof is labelled a source gap. | P96-W p. 278 explicitly invokes convergence in complex neighborhoods, termwise time differentiation, and completeness. The source does provide an analytic-curve reconstruction argument. The blueprint supplies more detail and proves a stronger `C¹`-curve version, rather than filling an absent theorem. | Label this as expansion/strengthening of the source proof. Distinguish that from genuine wrong formulas or missing premises. The additional source typo below should be recorded separately. |
| W-S1 | Low | P96-W p. 278, proof of Lemma 1, second line of the `u_tt` display (PDF p. 11 image) | Additional suspected source sign typo, not in the writer's list. | The image prints a positive `λ_j²q_j` term, whereas (6), p. 277, implies `q̈_j=-λ_j²q_j-λ_j G_q(q)_j`; the next displayed line on p. 278 already uses `-Au`. | Orchestrator should record the missing minus sign as a source typo. The blueprint at lines 196–201 correctly uses the negative sign; do not change that proof. |
| W-S2 | Low | KP96 author p. 13, first display in proof of Lemma 3 | Additional suspected source factor typo, not in the writer's list. | It writes `∂G/∂q̄_j = ∫ f(|u|²)uφ_j`. From (5), p. 11, `G=(1/2)∫g(|u|²)`, the standard derivative is half this integral. In the cubic case (7), `G=(1/4)∫|u|⁴`, gives the same missing factor directly. The equation (6) and Lemma 1 calculation on p. 11 already compensate correctly through `2i∂H/∂q̄`. | Record a candidate local factor-two typo; it affects this displayed gradient formula, not the qualitative smoothing claim. Do not propagate it into W's force interface. |

## Per-item verdicts

### 1. Conventions — PASS WITH NOTES

`w0-conventions.tex:72–151` consistently uses the real physical Hamiltonian, standard `dq∧dp`, `z=(q+ip)/sqrt(2)`, action `|z|²`, and increasing angle in `z=sqrt(I)e^{-iφ}`. Direct calculation gives `i dz∧d z̄=dq∧dp`, `ż=-iλz`, and `dq∧dp=dφ∧dI`. Setting `φ=2πθ`, `Y=2πI`, gives `dθ∧dY`; mixed divisors really are `2πk·ν+l·Ω`. There is no time scaling hidden in this conversion.

The comparison table at lines 163–171 agrees with the inspected source images: P96-W pp. 277, 279–282, 284, 287, 290–291. The p. 276 action convention is different but internally consistent in its heuristic display; its mere difference is not an additional mathematical error. The later unannounced attachments are the problem. The time-reversal repair needs conjugation/momentum reversal as described, not merely pretending the printed positive rotation solves the physical first-order system unchanged.

### 2. PDE equivalence (a) — PASS

`w0-normalization.tex:165–208` proves the stated two directions with sufficient hypotheses. In (i), bounded multipliers and `p ∈ C¹(I,ℓ^{1,0})` give `q ∈ C²(I,ℓ^{1,-1})`; exponential decay makes reconstruction bounded into every fixed `C^k` space even from that lower weight. This pays the time derivatives and joint continuity. The first force identity uses the proved cubic bound, uniform convergence, sine completeness, and continuity; equality almost everywhere therefore becomes equality everywhere, including the endpoints. The second force identity has the correct sign.

In (ii), the reconstruction identities recover the coefficients by integration. Continuity of `u_t,u_tt` on compact time-space sets pays differentiation under the integral, and two integrations by parts have vanishing boundary terms. The conclusion is coordinatewise `C¹` and the coefficient equations. It does not claim the stronger Banach-space regularity in (i) follows for every classical PDE solution. Nor does it claim every classical solution has the required exponentially decaying representation. These restrictions are explicit, appropriate typing/regularity hypotheses, not disguised assumptions of the equations.

The analytic all-time version remains W2; Lemma 1, P96-W p. 278, supports that later task. W-A5 concerns the description of the source, not validity of the new proof.

### 3. Cubic estimate (b) — PASS

`w0-normalization.tex:95–154`: the weight inequality and Young/Cauchy–Schwarz argument give the asserted, non-optimal `K_s=2^s sqrt(1+2ζ(2s))` for `s≥1`. The zero mode is included in `1+2ζ(2s)`. The signed-index majorant is even, so restricting its squared norm to positive indices costs at most half the two-sided squared norm, including when a zero convolution coefficient is present. Combined with three input factors `sqrt(2)`, this gives exactly `C_*=K_{p+1/2}²/π`, hence `C_m=8(1+2ζ(3))/π=8.668505…` at `p=1`.

Only `λ_j≥j` is used in that bound; no dependence on `m` is concealed. Reconstruction bounds and later divisors may depend on `m`. Absolute convergence also holds at `a=0` in the claimed range by the convolution majorant. Complex trilinearity is in the actual coefficients, not the absolute-value majorant; bounded trilinearity establishes polynomial analyticity. The proof does not misuse componentwise analyticity as a substitute for Banach-space analyticity.

### 4. Quartic coefficients (c) — PASS

`w0-normalization.tex:36–72`: product-to-sum followed by the cosine integral formula gives the seven Iverson brackets with the asserted `1/(2π)` factor, including zero cosine frequencies. The signed form has positive terms for one negative sign and negative terms for zero or two negative signs; the all-negative case cannot contribute to positive output index. Repeated indices are counted with multiplicity. In particular the values `g_iiii=3/(2π)`, `g_iijj=1/π` for distinct modes, and `g_1113=-1/(2π)` agree with direct integration. P96-W (10)–(11), p. 281, use the additional four square-root frequency factors exactly as the blueprint says.

### 5. Nonresonance, A/B and formal Birkhoff step (d) — PASS at the stated formal level

The new proof at `w0-normalization.tex:218–245` is complete for all index patterns, not merely for small modes or generic masses:

- Four equal frequency signs are excluded by positivity. Three against one are excluded by the spatial selection rule and strict subadditivity `λ_x+λ_y>λ_{x+y}`.
- With two frequency signs on each side, the spatial two-pair relations either coincide with that pairing (strict convexity at fixed sum) or cross it (strict monotonicity of `f(y)+f(y+t)`). Both force equal multisets, including repeated-index cases and negative `t` on its stated domain.
- A one-against-three spatial relation can be renamed `a=b+c+d`. If `d≤b`, the frequency inequality is immediate; if `d>b`, the proof compares a proper positive subinterval with a right translate of `[b,d]`. Strict positivity and monotonicity of `f'` pay both comparisons. No sign pattern is omitted.

Thus resonant projection equals independent-angle averaging. The moments and multiplicities at lines 293–302 give

`<G> = (9/(16π))Σ(I_j/λ_j)² + (3/(2π))Σ_{i<j}I_i I_j/(λ_iλ_j)`.

Consequently `A_ii=9/(8πλ_i²)` and `A_12=B_ji=3/(2πλ_iλ_j)` with the appropriate indices. The infinite sums converge for the stated phase space.

At lines 305–324 the generating coefficient `c/(-i(α-β)·λ)` has the correct sign: `X_Λ F=G^tan-Ḡ` and `X_FΛ=-X_ΛF`, so pullback by the positive time-one flow removes the nonresonant quartic part. Conjugate monomials give a real generator. Here “polynomial” is understood formally by degree; infinitely many modes do not make it a finite monomial sum. No bounded analytic generator, flow, or sixth-order norm estimate has yet been proved. The blueprint explicitly assigns those to W3 using quantitative divisors. P96-W Lemma 4, p. 283, is correctly restricted to a finite minimum index for a uniform lower bound; the qualitative lemma is not a replacement for it.

### 6. Nondegeneracy (e) — PASS

`w0-normalization.tex:339–379` proves all three claims for every fixed positive mass, independently of the script's finite search. The determinant is `-63/(64π²(1+m)(4+m))`. The normal combinations of length one or two are exhausted by positivity and strict monotonicity of `λ_j`.

For A3, vanishing of the linear coefficients gives `k_i=cλ_i` and `s=-7c/4`. If `|l|=1`, also vanishing of the constant term forces `k_i²=4λ_i²/[7(λ_1²+λ_2²)] ∈ (0,4/7)`, impossible for integers. If `|l|=2`, `|c|<8/21` and `0<λ_2-λ_1<1` force the integer `k_2-k_1` to vanish; then `c=s=0`, whereas a nonzero normal multi-index of length two cannot have `s=0`. This includes doubled indices and opposite-sign pairs.

The source's A3 at P96-W p. 288 and Lemma 6, pp. 292–293, means nonidentity of the affine resonance, not pointwise absence of all resonances for every action. The source proof itself tests simultaneous vanishing of constant and linear coefficients. The blueprint correctly makes this explicit. The mode-gap condition (4), p. 273, is `1≤1` for `{1,2}`. For later application of P96-K assumption A, pure normal nonresonance of `Ω(I)` on a sufficiently small action domain still has to be attached, rather than identified with the bare condition on `λ_N`; W8's domain shrink can supply it.

The corrected spectral difference estimate with `κ=2` is valid: differentiate the explicit smooth function `sqrt(x²+m)+c(I)/sqrt(x²+m)` to obtain `1+O(x^-2)`, uniformly for bounded actions, and integrate between normal indices. Thus the difference estimate does not depend on subtracting uncontrolled pointwise asymptotic remainders.

### 7. Duffing check (f) — PASS WITH NOTES

`w0-normalization.tex:389–410` checks the first frequency-shift coefficient correctly. With physical sine amplitude `a`, `ε=3/(2π)` and `I=λ_j a²/2` to leading order, the shift `3εa²/(8λ_j)` is `A_jj I`. The script's smallest-amplitude ratios independently reproduced `0.99976`, `0.99987`, `0.99998` for masses `0.1,1,10`.

This is a Galerkin/Duffing consistency check, not an exact invariant one-mode PDE subsystem: `g_jjj,3j` is nonzero. The text explicitly drops other-mode forcing and qualifies the action relation. For `m>0`, `λ_{3j}≠3λ_j`, so that forcing introduces no third-harmonic resonance into the first shift calculation. The numerical integrations support the coefficient, not a rigorous global remainder estimate or PDE existence theorem.

### 8. Errata — PASS for the principal verdicts; FAIL for N-1's added threshold

All formulas used in these determinations were inspected on 200-dpi page images, not just OCR.

- **E-PDE-W-1: confirmed with the writer's two-slip localization.** P96-W (9), p. 280, has `1/4`; p. 281 defines the `sqrt(2)` complex scaling; p. 282's first expansion retains `1/4` instead of `1/16`, and its following signed-index sum drops the remaining prefactor. The prime is explicitly an index convention, with no normalization weight. Counting on p. 284 is right for that prefactor-free sum; multiplying by `1/16` gives the blueprint's A/B. The printed coefficients and their attachments on pp. 290–291 really are incompatible with the physical Hamiltonian in these variables.
- **E-PDE-W-2: confirmed, with a distinction.** P96-W p. 287 uses half the squared complex modulus for actions; p. 290 attaches `α=λ`, `A=Ḡ`, and recovers real coordinates without `sqrt(2)`. These cannot all agree with p. 281. Under the p. 287 action convention, the quadratic coefficient needs `2λ`, and the quartic matrix needs `4Ḡ`, independently of E-PDE-W-1. The positive complex rotation disagrees with (6), p. 277. The p. 276 heuristic action convention is internally valid by itself, rather than a further erroneous formula.
- **E-PDE-KP-1: confirmed for the pinned author version.** KP96 (5)–(6), p. 11; (7), p. 13; Lemma 4, p. 14; and the normal-form rewrite on p. 16 force `A=4Ḡ=(4-δ)/π` when `I=|q|²/2`. Lemma 4's coefficient in complex moduli is itself correct. Remark 2, p. 5, inherits the erroneous action-coordinate coefficient. No alternate choice of action makes both the printed linear and quartic rewrites correct.
- **E-PDE-KP-2: confirmed as a premise gap, not a refutation of existence.** The all-real-mass quantifier on p. 5 and the assertion in Lemma 6, p. 20, conflict at `J={1,2},m=-9,l=e₃`. The other exceptional combinations listed by the writer likewise violate that premise. A gauge repair is not certified here; an arbitrary common shift of Diophantine frequencies cannot simply be assumed to preserve that property.
- **N-1: source error confirmed, proposed mass threshold refuted (W-A1).** P96-W pp. 279–280 use the full two-sided Fourier norm. Its exact operator norm is `sqrt(2)` at every finite fixed mass, as approached by high modes. Thus this is not merely a defect for masses below 3.
- **N-2: confirmed.** KP96 pp. 12–13 define the same normalized Fourier basis on `[-π,π]`. The odd extension of `Sq` has norm `sqrt(2)||q||`, not the norm printed on p. 13. Renormalizing this function norm would require changing the preceding definitions.
- **N-3: confirmed as a local parenthesis typo.** P96-W p. 282 places the division inside the parentheses after `4-`; p. 284 makes the intended common denominator clear. The larger factor-16 correction is a separate issue.

Additional suspected source defects W-S1 and W-S2 are reported above for the orchestrator's ledger. No ledger or source was edited.

### 9. Headline W-NLW2 — PASS as a weaker existence proposal; FAIL as a non-weakened source specialization

`w-headline.tex:39–60` has the right order of quantifiers: all family data follow fixed `m`, precede `I`, and allow a torus-dependent Diophantine constant. A common exponent `τ>1` is compatible with the source (increase the source exponent if necessary). Density is genuinely one in action space near zero, not merely positivity along a sequence or a measure assertion about arbitrary PDE data. Passing from source action normalization by a common scalar and between finite-dimensional norm balls preserves this limit. A countable shell construction supplies a Borel parameter set.

An analytic embedded phase torus with rationally independent frequency supplies two basic frequencies. Exact invariance is a conclusion, not a premise. Analyticity of `K_I` into E implies the time regularity needed by item 2, and exponential spatial decay gives joint local analytic reconstruction on smaller complex neighborhoods. Bounded reconstruction controls `u,u_x,u_t` uniformly by the phase-space norm, so the last smallness estimate is consistent. The source's linearizing parametrization and frequency limits are supported by P96-W p. 289 Remark 1 and KP96 pp. 24,29–31. One must retain an angular displacement estimate tending to zero when converting the radial parametrization back; the radial map's better exponent cannot simply be copied. The weaker `o(r)` bound leaves room for that estimate.

The omissions of linear stability and Whitney regularity are declared and match D30's staging. The declared Borel formulation and weaker closeness are also transparent. W-A2 identifies an additional family-level weakening: individual embedding plus family continuity does not assert an embedded, Lipschitz Cantor manifold. This is not a counterexample to the proposed existence theorem, but prevents calling it the full non-weakened specialized Main Theorem.

### 10. PLAN — PASS WITH NOTES

The W0 nodes and dependencies track the supplied arguments, and W1 exposes the external sequence-space facts rather than importing a PDE KAM theorem as an unexplained scalar estimate. W0-to-W1 reuse does not create a mathematical cycle: W0 presently gives the paper proof; W1 will implement its sequence algebra in Lean. Sine completeness is an explicitly named external input, used by `pde-equiv` even though that W0 row lists only local parents. Add the direct dependency on `w1:sine-completeness` when making the formal graph. W-A3 needs its missing ranges fixed before statements are drafted.

For later milestones the quantitative divisors, analytic symplectic flow, unbounded diagonal evolution, infinite-operator homological equation, iteration, parameter Lipschitz control and refined measure theorem remain substantive obligations. The coarse edges are sensible, but do not discharge these inputs. P96-K Theorem D, p. 124, has an auxiliary `0≤ϖ<min(p̄-p,1)`; the choice and the strict measure margin must be retained in W7/W8, not replaced by plugging in the endpoint. `κ=2,Δ=1,g=6` gives `6>11/2`. No additional external theorem is needed for the audited W0 proofs beyond the facts explicitly listed in their ledger; W4–W8 have not yet received a complete dependency audit.

## Independent checks and limits

Commands were run in the audited worktree. No targeted Lean build or `#print axioms` applies: this package has no Lean module or Lean result, and the brief explicitly calls for no Lean work. I did not build the library to repair missing audit infrastructure.

1. `git rev-parse HEAD` returned the hash above; initial `git status --short` was empty.
2. `python3 -I scripts/wave/w0_checks.py`: exit **1**, missing `sympy` at line 18. No dependencies were installed and the script was not edited.
3. Successful fallback, exposing the already installed user package explicitly:

   ```sh
   OPENBLAS_NUM_THREADS=1 python3 -I -B -c 'import sys,runpy; sys.path.append("/root/.local/lib/python3.12/site-packages"); runpy.run_path("scripts/wave/w0_checks.py",run_name="__main__")'
   ```

   Exit **0**, final output `ALL CHECKS PASS`. All nine sections ran. The nonresonance scan's smallest divisor at `m=0.01` was `4.105e-07`; A3 scan minima at masses `0.1,1,10,43` matched the writer's receipt; random cubic ratio maximum was `2.9836`, against `8.668505`. Finite scans are supplementary checks, not proofs of quantified inequalities.
4. Independent elementary counterexamples: N-1 squared ratios `1.5118578920369088` at `(m,j)=(3,2)` and `1.414213562373095` at `(100,10)`; negative-multiplier ratio `0.9950371902099892` versus asserted bound `0.7071067811865475` at `r=-1,m=1,j=10`.
5. `LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: exit **1**. It printed `check_lean_modules: PASS (417 Lean files, 0 comparator configurations)` and `FROZEN-ANCHOR GUARD OK`, then the ABI scratch check failed with `error: unknown module prefix 'KAM'` and no `KAM.olean` on its search path. Lake also materialized dependencies as a side effect of that required lint. This is an infrastructure failure, not a W0 proof failure or a lint PASS. No subsequent build was attempted.
6. Source images were rendered using `pdftoppm -r 200 -f N -l N -singlefile -png`, into the brief-authorized `.drafts/audit-img/`. Inspected P96-W printed pp. **272–273,276–284,287–293**, KP96 author pp. **5,11–14,16,19–20,24,29–31**, P96-K printed pp. **120–122,124**. No copyrighted PDF was copied or committed.
7. `pdfinfo blueprint-W/blueprint.pdf` reports **13 pages**, whereas the handoff says 12. Text extraction confirms the compiled PDF contains the nonresonance lemma, nondegeneracy section and proposed headline. No recompilation was performed because the audit is read-only outside the report and authorized image scratch. This is not a byte-for-byte certification that the PDF matches every current TeX line.
8. `git diff --check` and `git diff --no-index --check /dev/null /root/code/KAM-w/docs/tracks/W/audits/W-BP0-audit-1.md` both exited **0**, with no output. `git diff --name-only` was empty; `git status --short` showed only the new `docs/tracks/W/audits/` directory. Branch remained `w`. Thus no pre-existing tracked file was changed. Audit images and tool-generated dependency/ABI scratch are ignored working artifacts, not deliverables.

What I could not certify: the isolated script invocation as supplied; repository ABI hashes without built KAM artifacts; the KP96 journal printing (only author v2.1 is pinned); a full independent proof audit of P96-K's infinite-operator and measure arguments or all of KP96's shell assembly; analytic Birkhoff realization and all future W1–W8 Lean work. W0's formal transformation and numerical receipts do not certify those later results. No frozen declaration was changed, no axiom claim is made, and no source normalization was silently repaired by this audit.
