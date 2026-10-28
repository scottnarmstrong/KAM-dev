# PDE KAM and perpetual leapfrogging

Research exploration, 28 October 2026. This is a proposed extension, not an approved statement, a source audit PASS, or a formalization receipt. The scope is the brief `.drafts/briefs/explore-pde-kam.md`: this report and downloaded PDFs only. No Lean, source registry, manifest, existing report, or generated file was edited; no commit or Lean build was made.

**Recommendation: GO for a bounded, smoothing, one-dimensional wave track; GO-LATER for leapfrogging.** Start with the autonomous equation

    u_tt = u_xx − m u − u³,     0 < x < π,
    u(t,0) = u(t,π) = 0,       m > 0,

and two temporal frequencies arising from modes 1 and 2. The parameters to be excluded are the two small internal actions, not the mass. Pöschel's wave theorem permits every fixed positive mass for this mode choice. The most economical alternative is cubic NLS: its quadratic spectral growth makes the measure argument easier. Nevertheless, the wave target is a sound first choice that follows the owner's preference and develops the linear-growth spectral machinery needed later.

There is one immediate qualification. **The wave paper contains apparent normalization inconsistencies in its printed Birkhoff calculation.** The first milestone must independently fix the original PDE Hamiltonian, real/complex coordinate conversion, quartic coefficients, and time convention. Exact candidates and replacement calculations appear in §4. They do not constitute a counterexample to the qualitative existence theorem, but its printed constants must not be copied into frozen declarations.

## 1. Sources, versions, and verification boundary

The following short identifiers are local to this report; they do not register new campaign sources.

| ID | Source and precise version used | Local file under `sources/pdf/` |
|---|---|---|
| P96-K | J. Pöschel, *A KAM-theorem for some nonlinear partial differential equations*, Ann. Scuola Norm. Sup. Pisa (4) 23 (1996), 119–148; published Numdam scan | `poschel1996_numdam_ASNSP_23_119.pdf` |
| P96-W | J. Pöschel, *Quasi-periodic solutions for a nonlinear wave equation*, Comment. Math. Helv. 71 (1996), 269–296; published ETH E-Periodica scan | `poschel1996_wave_CMH_71_269.pdf` |
| KP96 | S. Kuksin and J. Pöschel, *Invariant Cantor manifolds of quasi-periodic oscillations for a nonlinear Schrödinger equation*, Ann. of Math. 143 (1996), 149–179; **author version 2.1, August 1994**, typeset 12 January 2002 | `kuksin_poschel1996_NLS_author_v2_1.pdf` |
| HHM23 | Z. Hassainia, T. Hmidi, N. Masmoudi, *Rigorous derivation of the leapfrogging motion for planar Euler equations*, **arXiv:2311.15765v2**, 5 December 2023 | `arxiv_2311.15765v2_HHM_leapfrogging.pdf` |
| AS26 | T. Alazard and C. Shao, *KAM via Standard Fixed Point Theorems*, **arXiv:2312.13971v3**, 27 March 2025; existing context pin AS26 | `arxiv_2312.13971.pdf` |

Links: [P96-K scan](https://numdam.org/item/ASNSP_1996_4_23_1_119_0.pdf), [P96-W scan](https://www.e-periodica.ch/cntmng?bot=1&pid=com-001%3A1996%3A71%3A%3A18), [P96-W bibliographic DOI](https://doi.org/10.1007/BF02566420), [KP96 author PDF](https://webusers.imj-prg.fr/~sergei.kuksin/p/96_Annals.pdf), [KP96 journal record](https://annals.math.princeton.edu/articles/13219), [HHM23 v2](https://arxiv.org/abs/2311.15765v2), [AS26 v3](https://arxiv.org/abs/2312.13971v3).

SHA-256, computed from the actual local bytes:

```text
3fac82b098ac6add2e3b336978d8bcf70166590707a997c0684b008b6df9420f  poschel1996_numdam_ASNSP_23_119.pdf
77f083dc4f3d45802460c880a588ef227065810aa93cc963ff7684714d25d6a2  poschel1996_wave_CMH_71_269.pdf
d05ec70b6308d99bf2e6d2e1d22299791cb58bd2aefc8aee29c4a21f1ff2dc7e  kuksin_poschel1996_NLS_author_v2_1.pdf
5c3ecff79051ab5bff9baebe2a634c00b5cd46f6045adf65337911aca9ad0afe  arxiv_2311.15765v2_HHM_leapfrogging.pdf
5e2e6563bc0128e665ed744b11a9a7b87635745c5322a061d1a4073ca5c62a0d  arxiv_2312.13971.pdf
```

The first four files were downloaded for this task. The Numdam download is byte-identical to the pre-existing `poschel1996.pdf`; both have the first hash. AS26 was already present, its version was checked on the title page and against the versioned arXiv record, and its hash matches `docs/sources.json`. The P96-W download contains a newly generated ETH cover sheet, so a later download may have a different hash. The pin here is the actual 29-page file. P96-K has 31 PDF pages, KP96 35, HHM23 81, and AS26 40. The HHM abstract page's “80 pages” comment does not override the PDF count.

**Locator convention.** For P96-K, printed page = one-based PDF page + 117. For P96-W, printed page = one-based PDF page + 267. KP96 references below are to the author PDF's own printed pages, equal to PDF pages, **not** to journal pages 149–179. HHM23 and AS26 references use their printed/PDF page numbers. Numbered equations, theorem names, and paragraph positions disambiguate locations. Critical scanned formulas were checked on page images; OCR alone loses inequality signs and entire equations.

This exploration inspected the headline statements, analytic setup, principal proof steps, measure mechanism, and the normalization passages identified below. It is not a line-by-line certification of all five proofs. Kuksin's original monograph/erratum and the original Craig–Wayne–Bourgain papers were not independently pinned or audited; comments about them below are limited to the comparisons made in the inspected primary papers. Nothing depends on an uninspected theorem from those works.

## 2. First target and proposed mathematical freezing contract

### 2.1 Why this equation and these parameters

P96-W's Main Theorem, **pp. 272–273**, treats odd analytic nonlinearities with nonzero cubic coefficient. For a tangential set `J = {j₁ < … < jₙ}`, `n ≥ 2`, it requires

    min_{1 ≤ i < n} (jᵢ₊₁ − jᵢ) ≤ n − 1.                 (P96-W (4), p. 273)

It then gives a full-density Cantor family for **every** `m > 0`. For `J = {1,2}` the condition holds. Taking the cubic coefficient to be +1 and omitting higher terms is a specialization of the actual PDE, not an assumed perturbative input. In particular, no variable potential, inverse spectral problem, excluded mass set, external forcing, or full integrability of an auxiliary PDE is needed. “Genuinely nonlinear” here means a nonzero local cubic force in the PDE; it does not mean a quasilinear principal part.

The wave spectrum is simple under Dirichlet conditions: `λⱼ = sqrt(j²+m)`, `j ≥ 1`. Periodic spatial boundary conditions would introduce multiplicities and block problems. The massless equation is completely resonant and is excluded. General sets of modes require the source's restriction or additional mass exceptions; the statement below does not erase those quantifiers. [P96-W, pp. 271–274, Main Theorem and Remarks 1, 2, 7](https://www.e-periodica.ch/cntmng?bot=1&pid=com-001%3A1996%3A71%3A%3A18).

### 2.2 Definitions with fixed conventions

Use period-one time angles `θ : Fin 2 → ℝ`, with `ℤ²`-periodic lifts; spatial position stays in `[0,π]`. Let

    φⱼ(x) = sqrt(2/π) sin(jx),       λⱼ = sqrt(j²+m),
    ‖q‖²_{a,p} = Σ_{j≥1} |qⱼ|² j^{2p} exp(2aj),
    E_{a,p} = ℓ^{a,p}(ℝ) × ℓ^{a,p}(ℝ),
    ‖(q,p)‖_E = max(‖q‖_{a,p}, ‖p‖_{a,p}).

The symbol `p` in `ℓ^{a,p}` is the regularity exponent; the second coordinate in `E` is momentum. Fix `a = 1` and regularity exponent `p = 1` for the first headline. The source permits arbitrary positive choices; this specialization avoids needless headline parameters.

For `w = (q,p)` define the reconstruction

    U_m(w,x) = Σ_{j≥1} qⱼ φⱼ(x)/sqrt(λⱼ),
    V_m(w,x) = Σ_{j≥1} sqrt(λⱼ) pⱼ φⱼ(x).

These sums and all fixed finite orders of spatial differentiation converge uniformly on a smaller complex spatial strip. This is a theorem to prove, not a property supplied by the notation. The Hamiltonian and its real canonical equations are

    H_m(q,p) = ½Σ λⱼ(qⱼ²+pⱼ²) + ¼∫₀^π U_m(q,p,x)^4 dx,
    q̇ⱼ = λⱼpⱼ,
    ṗⱼ = −λⱼqⱼ − λⱼ^(−1/2)∫₀^π U_m(q,p,x)^3 φⱼ(x) dx.

The symplectic form is `Σ dqⱼ ∧ dpⱼ`. The equations are read coordinatewise, or in the weaker space `E_{1,0}`. The full vector field is not a bounded map `E_{1,1} → E_{1,1}`: its linear part loses one spatial weight. P96-W explicitly distinguishes this from the one-smoothing nonlinear field (**pp. 277–280, (6)–(9), Lemmas 1–3**).

For `I ∈ (0,∞)²`, put `r(I) = sqrt(I₁+I₂)` and define the linear torus

    Q⁰ⱼ(I,θ) = sqrt(2Iⱼ) cos(2πθⱼ),
    P⁰ⱼ(I,θ) = −sqrt(2Iⱼ) sin(2πθⱼ)                  (j = 1,2),
    Q⁰ⱼ = P⁰ⱼ = 0                                    (j ≥ 3).

Thus `Iⱼ = (Q⁰ⱼ²+P⁰ⱼ²)/2` is the standard oscillator action. This deliberately fixes the action normalization independently of the inconsistent complex-coordinate passages in §4.

An analytic embedding `K_I : ℝ²/ℤ² → E_{1,1}` means that its periodic lift is real analytic, is injective modulo integer translations, and has injective derivative at every point. The induced quotient map is a homeomorphism onto its image; compactness of the finite torus supplies that topological conclusion. This is a new PDE embedding definition, not the finite ambient type in the existing frozen torus definition.

### 2.3 Proposed headline `W-NLW2`

**For every `m > 0`, there exist** `r₀ > 0`, `C > 0`, `τ > 1`, a nonnegative function `η : (0,r₀) → ℝ` with `η(r) → 0` as `r ↓ 0`, a Borel set

    Γ ⊂ { I ∈ (0,∞)² : r(I) < r₀ },

a continuous frequency map `ν : Γ → ℝ²`, and a continuous family of embeddings `K_I`, such that:

1. **Full density in actions:** for the positive quadrant `P = (0,∞)²` and the max-norm ball `B_h ⊂ ℝ²`,

       lim_{h↓0} Leb₂(Γ ∩ B_h) / Leb₂(P ∩ B_h) = 1.

2. **Two independent temporal frequencies:** for every `I ∈ Γ` there exists `γ_I > 0` such that

       |k·ν(I)| ≥ γ_I |k|₁^(−τ)       for every k ∈ ℤ² \ {0}.

   The exponent `τ` is chosen before `I`; `γ_I` may tend to zero at the origin. Also `ν(I) → (λ₁,λ₂)/(2π)` as `I → 0` within `Γ`.

3. **Small embedded tori:** each `K_I = (Q_I,P_I)` is the analytic embedding defined above, and

       sup_θ ‖K_I(θ) − K⁰_I(θ)‖_E ≤ η(r(I)) r(I),
       sup_θ ‖K_I(θ)‖_E ≤ C r(I).

   Continuity of the family means continuity of `(I,θ) ↦ K_I(θ)` on `Γ × (ℝ²/ℤ²)`. No global Lipschitz bound uniform down to zero in the singular action coordinates is imposed.

4. **Exact invariance, with no assumed flow:** for every `I ∈ Γ`, real `θ`, and `j ≥ 1`,

       D_{ν(I)}Q_{I,j}(θ) = λⱼ P_{I,j}(θ),
       D_{ν(I)}P_{I,j}(θ) = −λⱼ Q_{I,j}(θ)
          − λⱼ^(−1/2) ∫₀^π U_m(K_I(θ),x)^3 φⱼ(x) dx.

5. **PDE conclusion:** for every `θ₀` the function

       u(t,x) = U_m(K_I(θ₀+tν(I)),x)

   is real analytic locally in `(t,x)` around every point of `ℝ × [0,π]`, solves the displayed nonlinear Dirichlet equation classically for **every** real time, and satisfies `u_t(t,x) = V_m(K_I(θ₀+tν(I)),x)`. After enlarging `C`,

       sup_{t∈ℝ, x∈[0,π]} (|u| + |u_x| + |u_t|) ≤ C r(I).

All existential data are chosen after the fixed mass and before the action and phase. No uniformity as `m → 0`, `m → ∞`, or the number of excited modes increases is claimed. The bound on the family, rather than smallness of an arbitrary input perturbation, is the meaning of “small.” It gives nonzero solutions with arbitrarily small amplitude. The embedding and rational independence prevent disguising a one-frequency orbit as a two-frequency hull: a dense two-torus orbit cannot lie on a smaller closed torus in the phase space.

This is a **proposed specialization and repackaging**, deliberately weaker than the source's linear-stability and stronger regularity conclusions. The source basis is P96-W **Main Theorem, pp. 272–273; Lemma 1, p. 278; Cantor Manifold Theorem and Remark 1, p. 289; assembly pp. 290–291**, together with **KP96 Theorem 2, p. 19, and §7, pp. 25–31** for the parameter construction and linearizing parametrization. The little-o closeness formulation avoids assigning the better radial-map exponent to the linearizing parametrization: KP96 §7 Step 7 distinguishes the two. A formal statement audit must still check this translation and the normalization repair before owner approval.

The density statement concerns a finite-dimensional **action parameter set**. It is not Lebesgue measure in an infinite-dimensional Hilbert space, where no analogous locally finite translation-invariant volume exists. It is not a probability on generic PDE initial data. “Cantor” is used descriptively: the proposed contract requires Borel measurability and density, not perfectness or absence of isolated points. KP96 **p. 24, Remark 2** explicitly warns about isolated points.

**Period conversion:** if a source torus has angular frequency `ω` with period `2π`, the campaign frequency is `ν = ω/(2π)`. In canonical action-angle coordinates `φ = 2πθ`, the conjugate action is `Y = 2πI`, so `I dφ = Y dθ`. The divisor in campaign coordinates is `2πk·ν + ℓ·Ω`, not `k·ν + ℓ·Ω`. One cannot rescale only the tangential frequencies or forget this factor in a normal-mode equation.

### 2.4 Alternatives

| Candidate | Benefit | Added cost or boundary | Judgment |
|---|---|---|---|
| Fixed-mass cubic Dirichlet wave, `J={1,2}` | Real scalar nonlinear PDE; every fixed positive mass; explicit modes; nonlinear field gains one weight | Linear normal spectrum needs the refined measure theorem | Recommended owner-facing first target |
| Cubic Dirichlet NLS, `iu_t=u_xx−mu−|u|²u`, fixed `m>0` | `λⱼ=j²+m`; integer quartic divisors; no smoothing required by the abstract theorem; arbitrary finite mode set | Complex scalar PDE; still infinite operators and parameter KAM; normalization audit still needed | Best fallback if minimizing proof cost dominates |
| Variable-potential NLW | External spectral parameters can simplify frequency independence | Sturm–Liouville estimates, potential parametrization, eigenfunction multiplication estimates | Defer |
| Kuksin's original route / sine-Gordon approximation | Strong historical results, including other equations | Integrable-PDE machinery or more complicated linearization; historical `d=1` measure correction | Defer |
| One periodic nonlinear mode / Lyapunov-center result | Cheaper PDE reconstruction exercise | Only one independent time frequency | Useful warm-up, does not answer the request |
| Quasilinear wave, derivative NLS, KdV | Closer to difficult PDE applications | Unbounded nonlinear perturbation and tame/derivative-loss machinery | Later track extension |

The NLS comparison is supported by **KP96 Theorem 1, p. 5; Lemmas 4–5, pp. 14–16; nondegeneracy and `d=2` verification, pp. 20–21**. In particular, quartic divisors `i²+j²−k²−l²` are integers under the selection rule. This is a real simplification compared with the wave square roots. It does not imply that the nonlinear wave theorem is a finite-dimensional corollary.

## 3. Proof route and the first genuinely new estimates

### 3.1 Sequence algebra and PDE attachment

Use a weighted Hilbert sequence space, with multiplication handled on the associated two-sided Fourier coefficients. For `a ≥ 0`, `s > 1/2`, prove

    ‖b*c‖_{a,s} ≤ C_s ‖b‖_{a,s} ‖c‖_{a,s}.

P96-W **Lemma 2, p. 279; §6, pp. 294–295**, and KP96 **Appendix A, pp. 31–32**, give the proof. Odd sine extension and two factors of `λ_j^(−1/2)` then give

    G_q : ℓ^{a,p} → ℓ^{a,p+1},       ‖G_q(q)‖_{a,p+1} ≤ C‖q‖_{a,p}³,

with a continuous trilinear realization for the cubic case. This establishes analyticity without invoking an unproved infinite-dimensional “coordinatewise analytic plus bounded” principle. The source uses that principle in **P96-W p. 280**; explicit polynomial maps are simpler here. The reconstruction lemma must recover the original pointwise PDE, boundary conditions, and time derivatives from the coefficient equations. An abstract torus in a sequence space alone is not the requested PDE theorem.

### 3.2 Partial quartic Birkhoff normal form

Transform only quartic monomials involving at least one tangential index. Keep the quartic terms containing only normal variables in the remainder. The sine-product selection rule says a nonzero interaction has a signed relation `±i±j±k±l=0`. P96-W **Main Proposition, pp. 281–282; Lemma 4, p. 283, proof pp. 285–286**, bounds the nonresonant square-root divisors for this restricted problem. The bound depends on the finite tangential cutoff and on the fixed mass; it is not a uniform bound for every quartic divisor at arbitrarily large indices.

Construct the generating Hamiltonian and its time-one map on sequence balls, with explicit displacement, analytic dependence, symplecticity, and a sixth-order remainder. Obtain

    H ∘ F = Λ + Q + R,
    Q = ½ Iᵀ A I + Σ_{j≥3}(B I)_j J_j,
    R = O(‖z_normal‖⁴) + O(‖z‖⁶).

The corrected oscillator-action coefficients computed directly from the original Hamiltonian are

    A_ii = 9/(8πλ_i²),       A_ij = 3/(2πλ_iλ_j)  (i≠j),
    B_ji = 3/(2πλ_jλ_i)      (j normal, i tangential).

Equivalently `A = (3/(8π)) D(4·11ᵀ−Id)D`, `D=diag(1/λ_i)`. Hence

    det A = (3/(8π))^n (−1)^(n−1)(4n−1) Π_i λ_i^(−2) ≠ 0.

These are **our normalization calculations**, to be independently proved before adoption; they are not represented as the literal constants printed in P96-W. The scalar factor does not change the rank-one nondegeneracy argument. The further affine-resonance nonidentity is a separate gate: `det A≠0` alone is insufficient. P96-W **Lemmas 5–6, pp. 291–293**, prove it for the permitted mode sets.

### 3.3 Abstract parameter-dependent PDE KAM

On a complex domain with finite angles/actions and infinitely many normal coordinates, write

    N(θ,y,z,z̄;ξ) = ω(ξ)·y + Σ_j Ω_j(ξ) z_j z̄_j,
    H = N + P.

This display uses the source's radian-angle convention; apply the conversion in §2 for implementation. The hypotheses of **P96-K Assumptions A–C, pp. 120–121**, include:

- a bi-Lipschitz tangential frequency map on a closed bounded finite-dimensional parameter set;
- null sets of exact mixed resonances and nonvanishing pure normal combinations for normal integer multi-indices of length at most two;
- spectral asymptotics with `d≥1`, tail exponent `δ<d−1`, and Lipschitz control of that tail in a weighted supremum norm;
- analyticity in phase variables, Lipschitz dependence on parameters, and a nonlinear vector field from regularity `p` to `p̄`, with `p̄≥p` for `d>1` and **strictly `p̄>p` for `d=1`**.

For the wave problem `d=1`, `δ=−1`, `p̄−p=1`. The source's rescaled field norm is

    |W|_r = |W_θ| + r^(−2)|W_y| + r^(−1)‖W_z‖_{a,p̄}
              + r^(−1)‖W_z̄‖_{a,p̄}.

The smallness in **Theorem A, pp. 121–122** is on

    ε = sup |X_P|_r + (α/M) Lip_ξ(X_P)_r ≤ c_* α,

with the source's frequency constants and fixed analytic data accounted for. It is not a small scalar sup norm of `P` alone, and the Lipschitz term cannot be dropped. A future abstract frozen contract must expose the fixed spectral, Lipschitz, analytic-domain, and smoothing data before choosing its constants; KP96 **p. 24** explicitly lists these dependencies. This report does not approve the entire general Theorem A as a Lean statement.

### 3.4 Homological equation and infinite operators

Truncate the perturbation to weighted degree two, where `y` has degree two and `z,z̄` degree one. Solve

    {F,N} + N̂ = R,

retaining the averages in `N̂`. The relevant scalar denominators include

    k·ω,
    k·ω ± Ω_j,
    k·ω ± Ω_j ± Ω_l.

The `k=0, j=l` difference divisor vanishes identically; its diagonal term is retained in the normal form, never inverted. The normal multi-index should be a finitely supported integer sequence, for example `ℕ+ →₀ ℤ`, with ℓ¹ size at most two. The time Fourier index remains `Fin n → ℤ`.

The difficult quadratic mixed term is an **operator** equation on the normal Hilbert space. Dividing each matrix coefficient by a nonzero number is not enough to obtain a bounded operator. P96-K **Lemma 1, pp. 125–128, especially p. 127**, conjugates weighted operators to ℓ², uses spectral separation, and invokes the infinite-matrix estimate **Appendix A, Lemma A.1, pp. 145–146**. This lemma and the Lipschitz difference-of-inverses estimate are essential new dependencies. They cannot be replaced by finite `Matrix (Fin n) (Fin n)` theorems or by entrywise bounds alone.

“No loss of derivatives” must be interpreted accurately. The nonlinearity is smoothing, so this route needs no Nash–Moser restoration of lost spatial regularity. Solving the angle equations still consumes analytic strip width and powers of the Diophantine constant. The unbounded linear diagonal operator still has to be handled on a scale or through coefficient equations.

### 3.5 Step, iteration, and parameter extension

P96-K **§3, pp. 128–132**, constructs the small symplectic flow, bounds the new remainder, and updates frequencies. **§4, pp. 132–135**, proves the iterative lemma, convergence, invariance, and the limiting normal form. Each step must maintain domain margins, reality, the stronger normal-space regularity, and weighted parameter Lipschitz estimates. The parameter sets shrink with the corrected frequencies, and frequency corrections must be extended to the common parameter domain with uniform weighted bounds. Scalar McShane extension helps with individual frequency coordinates; it is not a general Hilbert-valued extension theorem.

The abstract theorem also establishes elliptic normal form/linear stability. For the first frozen PDE headline I recommend leaving the separate stability conclusion out, while preserving whatever normal-form control the existence proof itself needs. In an infinite-dimensional Hamiltonian system, linear stability is a statement about a specified linearized evolution and norm, not merely imaginary diagonal entries written formally.

### 3.6 Measure is the decisive wave-specific step

For `Ω_j(ξ)=λ_j+(Bξ)_j`, the difference asymptotics satisfy

    (Ω_i−Ω_j)/(i−j) = 1 + O(j^(−2)),        i>j,

uniformly on bounded action domains: the relevant exponent is `κ=2`. P96-W **p. 291** verifies this. For a fixed time index, infinitely many normal pairs can have nearly the same difference. A naive sum of independent slab estimates over all pairs diverges.

P96-K **§5, pp. 135–139, Lemmas 3–8 and Theorem B** groups the normal resonances using spectral asymptotics. For `d=1`, the coarse exponent is `μ=κ/(κ+1)=2/3`. The wave application on shrinking action domains needs the stronger **Theorem D, p. 124; proof §6, pp. 140–142**. For affine original frequencies it gives

    Leb(Π \ Π_α) ≤ C diam(Π)^(n−1) α^μ,
    μ = κ/(κ+1−ϖ/4),       0 ≤ ϖ < min(p̄−p,1).

The gain is material. The Cantor-manifold argument requires a remainder exponent

    g > 4 + (4−Δ)/κ,       Δ=min(p̄−p,1).

Here `g=6`, `Δ=1`, `κ=2`, so `6>11/2`. See **P96-W pp. 289, 291**, and the proof in **KP96 §7, Steps 3–8, pp. 26–31**. With the coarse exponent alone, the relevant comparison is at the borderline and does not yield density one.

As an explicit arithmetic check of the margin, choose `ϖ=1/2`, giving `μ=16/23`, and follow KP96's auxiliary radius `r` with `λ=4/g=2/3`. Choose `α(r)=r^(47/24)`, with suitable fixed prefactors and sufficiently small `r`. Then

    r²/α = r^(1/24) → 0,
    α^μ/r^(2λ) = r^(2/69) → 0.

The first ratio pays perturbative smallness/closeness; the second pays the relative measure loss. The `r` here is the **auxiliary normal-domain radius**, not the headline oscillator amplitude. This is an exponent-feasibility calculation, not a certified density rate in the headline variable. KP96 patches disjoint shrinking action shells to obtain one measurable family with density one; a sequence of unrelated positive-measure families would not by itself prove the stated limit.

### 3.7 Comparison with other proof architectures

Craig–Wayne–Bourgain methods solve the PDE hull equation using truncations, inverse estimates, and multiscale/Newton or Nash–Moser arguments rather than diagonalizing the full normal dynamics through this second-Melnikov KAM normal form. They can avoid some classical reducibility requirements, but introduce substantial Green-function and resonance-cluster machinery. They are valuable for harder spectra; they offer no demonstrated implementation saving for this simple Dirichlet target. This comparison follows **P96-W discussion pp. 275–277** and **AS26 §1**, not an audit of their original theorems.

AS26 is a different, potentially useful route for the campaign's **finite-dimensional** torus problem. Its actual phase space is `Tⁿ×ℝⁿ` (**p. 2**); Theorems 1.1–1.2 (**p. 3**) use Sobolev hypotheses and para-linearization, with paraproduct estimates in **§3, pp. 16–22** and a Schauder fixed-point construction in **§4.3, pp. 30–33**. The PDE extensions are discussed as extensions/forthcoming work in **p. 4**. The pinned paper does not supply the infinite normal-frequency theorem needed here. Replacing P96-K with AS26 would therefore require both new PDE mathematics and a paraproduct calculus. The arXiv v3 record notes a correction to §4.1; use the pinned v3, not an earlier version. No later PDE extension was audited in this exploration. [AS26 v3](https://arxiv.org/abs/2312.13971v3).

## 4. Source quality, suspected errata, and required deviations

P96-K is a good central source: a short published proof, separate analytic and measure theorems, and appendices that identify the functional-analytic tools. P96-W supplies the PDE and normal-form verification; **it imports its Cantor Manifold Theorem from KP96**, which in turn uses P96-K. Thus the honest source chain has three papers. Neither the abstract Numdam paper alone nor the wave paper alone contains every proof leaf.

The following are **candidate errata for the orchestrator's ledger**, not edits made here. All formula locations below were read in the pinned files; the wave normalization passages were also checked visually.

**E-PDE-W-1: quartic normalization, P96-W p. 282, first Hamiltonian expansion in the proof of the Main Proposition.** The preceding definitions are `G=(1/4)ΣG_ijkl q_iq_jq_kq_l` in (9), p. 280, and `z_j=(q_j+ip_j)/√2`, p. 281. The expansion on p. 282 instead prints

    (1/4) Σ G_ijkl (z_i+z̄_i)⋯(z_l+z̄_l),

then identifies its quartic part with `Σ' G_ijkl w_iw_jw_kw_l`, with `G_i...l=G_|i|...|l|`. Direct substitution requires **1/16** in both the expanded polynomial and the signed-index sum with that coefficient definition. The displayed `Ḡ_ij=(6/π)(4−δ_ij)/(λ_iλ_j)` on pp. 282, 284 consequently gives a different quartic coefficient from the original Hamiltonian.

A one-mode check makes the discrepancy independent of operator estimates. From (9)–(11),

    G(q_i) = 3 q_i⁴/(8πλ_i²),
    average_φ G(sqrt(2I_i) cos φ) = 9 I_i²/(16πλ_i²).

Thus the oscillator-action twist is `9/(8πλ_i²)`, whereas the source's printed diagonal `Ḡ_ii` is `18/(πλ_i²)`, a factor of 16 larger. The mixed coefficient calculation gives the same factor. This is a normalization defect candidate, not evidence that nondegeneracy or the existence theorem fails. Required repair: independently derive the quartic polynomial and generating equation from the fixed real Hamiltonian; transport every downstream coefficient and smallness constant explicitly.

**E-PDE-W-2: incompatible real/complex recovery and actions.** P96-W **p. 290, paragraph immediately after `z(t)=Γ∘Ψ(e^{iω(I)t}v₀)`**, gives `q=Re z`, `p=Im z`. With the printed definition on p. 281 these should be `q=√2 Re z`, `p=√2 Im z`. Also **p. 287** defines `I_j=|z_j|²/2` but **p. 281** writes the quadratic Hamiltonian `Σλ_j|z_j|²`; **p. 290** identifies its action coefficient with `λ_j`. These cannot all hold without a declared rescaling. With the p. 281 coordinates, the standard action is `|z_j|²=(q_j²+p_j²)/2`. The sign of the rotation must also be transported from `q̇=λp`, `ṗ=−λq`: for `z=(q+ip)/√2` it is `ż=−iλz`. The headline avoids importing the inconsistent convention by retaining the real equations and specifying its phase explicitly.

**E-PDE-KP-1: author-version normal-form rewrite.** In the pinned KP96 author PDF, **Lemma 4, p. 14**, writes `Ḡ=(1/2)ΣḠ_ij|q_i|²|q_j|²`; **p. 16, first displayed normal form after the proof**, rewrites this as `(1/2)⟨AI,I⟩` with `I_j=|q_j|²/2` and `A_ij=Ḡ_ij`. Algebraically the first formula becomes `2ΣḠ_ij I_iI_j`; with that convention the matrix would be `4Ḡ`. This candidate is confined to the inspected author version; agreement with the journal printing is **unverified**. The abstract Cantor theorem can be used with a correctly computed matrix; its constants cannot be inferred from this inconsistent application rewrite.

**E-PDE-KP-2: pure-normal nonresonance for unrestricted real mass.** The author version's **Theorem 1, p. 5**, allows every real `m`, but **Lemma 6, p. 20**, asserts `⟨l,β⟩≠0` for `1≤|l|≤2`. With `J={1,2}`, `m=−9`, and `l` supported with value 1 on the normal mode 3, this pairing is `3²−9=0`. The abstract theorem's premise therefore does not follow as written. A mass/gauge reduction or modified normal-form argument could repair the application; no such repair is certified here. This is a candidate proof-attachment gap for the unrestricted-mass assertion, not a refutation of that assertion. The proposed wave theorem and the recommended NLS fallback both restrict to positive mass, so this example does not obstruct either proposal. Agreement with the NLS journal printing remains unverified.

Historical corrections already disclosed by the source also matter. **P96-K §8 Remark 2, p. 144**, reports a flaw in the measure proof of Pöschel 1989 Lemma 8.1: Lipschitz control of a directional derivative was needed. **Remark 3, p. 145**, reports incorrect `d=1` estimates in Kuksin's 1993 monograph, specifically (4.11), p. 77, and points to an erratum. These are verified *reports of corrections by Pöschel*; the earlier sources and erratum were not independently checked. This is a reason to follow the inspected 1996 measure proof.

Other proof-expansion obligations, without an identified false theorem:

- P96-W **Lemma 1, p. 278**, compresses termwise differentiation, sine completeness, and PDE identification into one paragraph. Each needs a provider.
- P96-W **p. 284** invokes analyticity from component analyticity and boundedness; polynomial/convolution construction can avoid that external analytic theorem for the cubic target.
- P96-K **p. 128** treats the remaining homological components by comparison with two model components. The graph needs every component and its operator norm, including reality and symmetry conditions.
- P96-K **Appendix A.4, p. 147**, presupposes a Banach-space flow exists on the claimed domain. Local existence, domain retention, parameter bounds, differentiability, and symplecticity are separate proof obligations.
- KP96 **§7, pp. 28–31**, uses shell patching and a radial reparametrization. The radial map need not linearize the flow. Its better exponent must not be transferred to the linearizing map without proof.
- HHM23 **p. 67, final paragraph before Appendix A**, acknowledges a measure argument written with derivatives of a merely Lipschitz function and says to justify it using the Lipschitz norm. This is an explicit proof-expansion obligation, not a newly established false claim.

Declared deviations proposed here: pure cubic only; two consecutive modes; fixed positive analytic/spatial regularity weights; standard real oscillator actions; period-one temporal angles; Borel/full-density formulation instead of strict Cantor topology; omit linear stability and Whitney regularity from the first headline; rederive normalization constants rather than silently copying the printed values. All must appear in the eventual statement audit. No frozen statement has been modified.

## 5. Reuse map from inspected code

The inventory below is based on reading current declarations and representative proof bodies, not just directory names. The checkout was observed at `4c54188f287e30462810b0f27c258139a9cb1ab7`; this is a live shared checkout, not a new frozen source snapshot. Current README/brief status takes precedence over the older Phase-0 wording still in `docs/PLAN.md`.

| PDE proof step | Existing declarations and locator | What can actually be reused; remaining work |
|---|---|---|
| Banach-valued angle Fourier expansion | `KAM/Strip/FourierSeriesVector.lean:127`, `norm_fourierSumVec_le`; `:141`, `tendstoUniformlyOn_fourierSumVec`; `:192`, `differentiableOn_fourierSumVec`; `:333`, `summableWeighted_torusCoeffW`; `:380`, `summation_forward_vec`; `:400`, `summation_converse_vec` | Already polymorphic in a complete complex normed target. Can take a weighted sequence space or bounded-operator space after constructing its instances. The angle domain remains finite-dimensional. |
| Complex Cauchy estimates | `KAM/Strip/Cauchy.lean:53`, `norm_fderiv_le_of_closedBall_bound`; `:80`, `norm_fderiv_le_of_closedBall` | These use arbitrary complex normed domain/target types, not `FiniteDimensional`; directly useful on sequence balls. Do not assume every other strip theorem has the same generality. |
| Analyticity of finite-angle hulls | `KAM/Strip/Analytic.lean:101`, `holomorphic_analytic` | Finite-dimensional domain, Banach target with completeness/second-countability requirements. Fits a finite torus into a separable sequence space; does not supply all analytic Hamiltonian calculus on infinite-dimensional domains. |
| Products/convolutions | `KAM/Fourier/Convolution.lean:124`, `KAM.Fourier.weightedNorm_convolution_le`; `KAM/Weighted/Algebra.lean:191`, `KAM.Weighted.wbound_mul` | Weighted ℓ¹ angle convolution and finite-action analytic algebra. They provide summability patterns and exponential-weight inequalities. The spatial ℓ² polynomial-weight convolution theorem is new. |
| Parameter norms | `KAM/Weighted/Norm.lean:42`, `InClass`; `:62`, `WBound`; `KAM/Weighted/Parametric.lean` | Helpful organization for Banach-valued Fourier sums, but the action domain is `Fin m → ℂ`. The full mixed finite/infinite domain and smoothing field norm are new. |
| Tangential small divisors | `KAM/Diophantine/Cohomological.lean:179`, `KAM.Diophantine.existsUnique_cohomological`; `KAM/Diophantine/FrequencyDependence.lean:99`, `solve_sub_solve`; `:122`, `weightedNorm_solve_sub_solve_le` | Reuse the `ℓ=0` logic and inverse-difference algebra. Need sequence/operator-valued extensions and all shifted normal divisors. |
| Existing matrix-valued cohomology | `KAM/Strip/CohomologicalOperator.lean:165`, `cohomological_apriori_operator`; `:286`, `norm_cohSolutionMat_le` | Actual target is `Matrix (Fin p) (Fin q) ℂ`. No infinite-matrix solver is supplied by the name. |
| Bounded-operator Neumann step | `KAM/Matrix/Neumann.lean:33`, `isUnit_add_of_inverse_norm_mul_le_half`; `:51`, `norm_inverse_add_le` | The initial section is for arbitrary complete normed rings; usable on bounded endomorphisms. Later finite-matrix specializations should not be confused with this general ring result. |
| Local flow of the small generating field | `KAM/ODE/Existence.lean:37`, `KAM.ODE.picard_lindelof_ball`; `:149`, `gen_uniform_exist` | Explicit bounded/Lipschitz ball hypotheses with `CompleteSpace E` are usable in Banach spaces. By contrast `gen_local` at `:179` assumes `ProperSpace E`; infinite Hilbert balls are not compact. |
| Canonical flows and Lie transforms | `KAM/Canonical/Flow.lean:45`, standing `FiniteDimensional ℂ E`; `:244`, `flow_a`; `:273`, `flow_d`; `KAM/Canonical/SymplecticForm.lean`; `KAM/Canonical/Lie.lean` | Formula/proof templates and finite tangential coordinate changes. The flow proof explicitly uses compact gauge balls. New uniform-ball Banach flow and weak symplectic arguments are required; this is not an instance change. |
| Measure exclusions | `KAM/Measure/Slab.lean:55`, `KAM.Measure.volume_abs_affine_lt_le`; `:150`, `slab_measure_le`; `KAM/Measure/Lattice.lean:254`, `lattice_sum` | Useful finite-parameter Fubini/slab and time-index summation tools. New normal-pair counting, asymptotic grouping, perturbed Lipschitz slabs, finite exceptional modes, and Theorem-D refinement. |
| Extensions over holes | `KAM/Measure/McShane.lean:35`, `mcshane_component`; `:71`, `mcshane_clamp` | Scalar coordinate extensions for frequencies with coordinate weights. Finite-vector extension does not automatically preserve the needed infinite sequence norm. |
| Iteration convergence | `KAM/Apost/Schedule.lean:169`, `KAM.Apost.epsSeq_le_q_pow`; `:246`, `error_decay_sum`; `KAM/Strip/Limits.lean` | Arithmetic patterns and uniform-limit lemmas. The schedule is specialized to the current a-posteriori constants, and the PDE iteration evolves normal frequencies and parameter sets. New iteration invariant/assembly. |
| Final invariant-torus theorem | Existing `KAM.aposteriori_kam`, `KAM.kam_positive_measure`, finite-dimensional torus/geometry modules | Do not apply them to an infinite type. Normal directions are not a finite Lagrangian frame, and the PDE torus has infinite codimension. New anchor/provider required. |

Tracks N/P are useful through their canonical-map and normal-form infrastructure, but not through a black-box Nekhoroshev or planetary theorem. The Kepler and planetary physical-coordinate modules do not contribute to this wave PDE. Track I's finite-dimensional continuation is likewise not a substitute for an unbounded PDE flow. The embedding route deliberately avoids formalizing the complete wave initial-value problem.

## 6. Mathlib inventory and design gaps

The installed Mathlib checkout was read at commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The statements below concern that checkout; “missing” means no ready-made API was located in the inspected/searchable modules, not a theorem about all future Mathlib releases.

| Facility | Present locally | Additional PDE work |
|---|---|---|
| ℓ² and completeness | `Mathlib/Analysis/Normed/Lp/lpSpace.lean`: `Memℓp`, `lp`, `lp.completeSpace` (`:1359`); `Analysis/InnerProductSpace/l2Space.lean`: `lp.instInnerProductSpace` (`:116`), `lp.inner_eq_tsum` (`:153`), Hilbert-basis infrastructure | Define weighted spaces by transport through `w_j ↦ e^{aj}j^p w_j`, preserving coefficient evaluation; prove embeddings, projections, tails, conjugation, and smoothing multiplier estimates. `PiLp` on a finite type is not this space. |
| Infinite sums and linear maps | `Summable`, `HasSum`, `tsum`; continuous multilinear maps; continuous linear maps and operator norms | Absolute convergence of convolution and Hamiltonian pairings; interchange of differentiation/sums; coefficient/operator realization and weighted operator ideals. |
| Analytic Banach maps | `Analysis/Analytic/Basic.lean`: `HasFPowerSeriesAt`, `AnalyticAt` (`:110`), `AnalyticOnNhd` (`:120`), based on `FormalMultilinearSeries` | The foundations already allow infinite dimensions. Build the specific cubic map, Hamiltonian class, gradient identity, Poisson closure, and quantitative Lipschitz/smoothing bounds. |
| ODE foundations | `Analysis/ODE/PicardLindelof.lean`, `ExistUnique.lean`, `Gronwall.lean`; repo Banach-ball lemma above | Quantitative holomorphic generating flows and parameter derivatives on noncompact balls. This is feasible for bounded small fields; no generic ODE theorem makes the diagonal wave generator bounded. |
| Sobolev spaces | `Analysis/Distribution/Sobolev.lean`: `TemperedDistribution.MemSobolev`, `BesselPotentialSpace`, Fourier characterization at `p=2`, derivative/laplacian membership | These are Fourier-defined spaces on finite-dimensional vector spaces. No ready-made identification with the weighted odd periodic sine space or Dirichlet trace algebra was found. Direct sequence reconstruction is smaller. |
| Spatial Fourier/PDE bridge | `Analysis/Fourier/AddCircle.lean`, Fourier/integration foundations; repo angle Fourier tools | Sine normalization, orthogonality/completeness or an equivalent direct Fourier identity, boundary compatibility, and analytic coefficient reconstruction. |
| Symplectic structure | Finite symplectic groups and bilinear-form/continuous-bilinear machinery | The physical unweighted form `Σ(q p'−p q')` is continuous and nondegenerate on weighted spaces but generally **weak**, not an isomorphism to their weighted dual. An arbitrary analytic scalar Hamiltonian need not possess a same-space Hamiltonian vector field. Bundle the actual field/gradient relation and prove it for the constructed Hamiltonians. Do not use the weighted Hilbert Riesz gradient as the physical gradient without correction. |
| Diagonal operators | Bounded operators, partially defined linear maps, spectral tools | Use `diag λ : ℓ^{a,p+1} →L ℓ^{a,p}` or its explicit domain; bounded phase rotations; commutators and the exact second-Melnikov inverse. No generic spectral theorem is needed for the explicit sine spectrum. |
| Parameter measure | Lebesgue/product measure, Fubini, countable unions, limits, Lipschitz tools | A new finite-dimensional resonance theorem with infinitely many normal labels and iteration-dependent frequencies. No infinite-dimensional Lebesgue measure construction is needed or appropriate. |
| Tame PDE calculus | Some Sobolev and multiplier foundations | No assembled Nash–Moser, paraproduct calculus, or vortex-contour KAM library was located. These belong to the leapfrogging extension, not the first wave proof. |

Keep tangential variables and Fourier indices in the repository's mandated `Fin n → ℝ/ℂ/ℤ` types. Infinite **normal** sequences require a new, explicitly documented weighted subtype/model over positive naturals. This is an extension of the ambient-type convention, not permission to replace existing finite ambient types or introduce `EuclideanSpace`. No new general infinite-dimensional manifold framework is necessary.

## 7. Milestones, cost, and campaign placement

Proposed new track **W** (wave/PDE KAM), alongside K/I/N/P. The name is provisional. Its source graph must distinguish the abstract KAM theorem, the action-family construction, and the PDE reconstruction. An edge to an abstract theorem does not discharge its spectral or smoothing hypotheses.

| Milestone / independently freezable result | Deliverable | New Lean lines, rough |
|---|---|---:|
| W0: normalization and cubic attachment | Exact sine integral coefficients; real Hamiltonian equations; cubic gradient realizes the physical force; two-mode averaged twist and its determinant | 1k–3k |
| W1: weighted sequence calculus | Complete weighted spaces, convolution theorem, diagonal/smoothing bounds, analytic cubic field | 4k–8k |
| W2: PDE reconstruction | Analytic coefficient solutions give all-time classical Dirichlet solutions; explicit smallness bounds | 2k–4k |
| W3: partial Birkhoff theorem | Actual analytic symplectic map, near-identity bound, quartic normal form, sixth-order and pure-normal remainder | 5k–10k |
| W4: normal homological theorem | Solve every degree-two component with sequence/operator and parameter Lipschitz estimates | 5k–10k |
| W5: one PDE KAM step | A small generating flow and transformed Hamiltonian with improved remainder and controlled frequencies/domains | 5k–10k |
| W6: abstract analytic iteration | Nested-parameter convergence, exact invariance, real analytic torus, frequency asymptotics | 5k–10k |
| W7: wave parameter exclusions | Infinite normal-resonance counting and refined affine-frequency measure estimate | 5k–10k |
| W8: action-family and PDE headline | Shell patching, density one, two independent frequencies, reconstruction, quantitative smallness | 2k–5k |

Combined estimate: **34k–70k additional Lean lines**, excluding commentary, blueprint, audits, and later linear stability. Confidence is **low** for the total, moderate for identifying the major modules. These are planning ranges after crediting existing reusable analysis, not measured task sizes or a calendar promise. A substantial unexpected operator/analytic API gap could exceed the range. The NLS fallback could avoid roughly 5k–10k of wave-specific divisor/measure work, but would still need most of the infinite-dimensional core. Work should be split into focused modules well below the 1500-line cap.

The first concrete mathematical milestone is **W0 together with the W1 cubic-gradient interface**. It should prove, from the fixed Hamiltonian rather than an assumed smoothing hypothesis,

    G_q : ℓ^{1,1} → ℓ^{1,2} is analytic,
    ‖G_q(q)‖_{1,2} ≤ C_m ‖q‖_{1,1}³,

and certify the quartic action coefficients in §3.2. A useful first source/design checkpoint is the one-mode Duffing-frequency consistency calculation. The first difficult operator checkpoint is P96-K Lemma A.1 plus the `z z̄` homological solve. Do not postpone that operator prototype until after building a large scalar Hamiltonian interface.

Pipeline: resolve candidate errata and write a source-backed mathematical blueprint; draft the exact headline/gate statements with all definitions; independently audit and obtain owner approval before freezing; construct the source dependency graph with explicit external leaves and consumer edges; design the sequence/operator modules; then assign proof packages and audits. W1/W2 and the operator prototype can be designed alongside the ongoing N/P campaign without changing their frozen surfaces. Every later Lean brief must reproduce the repository's hard rules verbatim; this exploration is not itself a Lean proof brief.

Main risks are the refined wave measure estimate, boundedness of the infinite homological operator, weak-symplectic flow calculus, and exact source normalization. A proof that assumes a bounded homological inverse or an already positive-measure nonresonant set as an unexplained package has missed the core work. A finite Galerkin theorem followed by an unproved limit is also insufficient: all constants and torus embeddings must be controlled uniformly in the normal cutoff, and compactness cannot be borrowed from finite dimensions.

## 8. Leapfrogging: what HHM actually proves and how far away it is

### 8.1 The result

HHM23 **Theorem 1.1, p. 4**, fixes `y₀>0` and an interval

    0 < ξ_* < ξ^* < y₀/√2.

For all sufficiently small patch radii `ε>0` it constructs a Cantor-like set `C_ε ⊂ [ξ_*,ξ^*]` with `|C_ε| → ξ^*−ξ_*`. For each `ξ₀∈C_ε`, four concentrated patches solve the planar Euler vorticity equation for all time. There are two upper positive patches and their reflected negative counterparts, with vorticity amplitudes `±ε^(−2)`. The normalized domains lie near unit discs; the physical domains are `ε O^ε_{t,k}+z_k(t)`, following the symmetric four-point-vortex configuration. The second upper patch is related to the first by a half-period time shift. See **(1.5)–(1.7), p. 4**, and the contour derivation in **§3.1**. [HHM23 v2](https://arxiv.org/abs/2311.15765v2).

The normalized patch shapes are periodic with the point-vortex period `T(ξ₀)` and are not rigidly rotating. The motion is periodic in a translating frame and leapfrogs perpetually; it is **not** a theorem about two or more independent temporal frequencies, nor about vorticity smooth across the patch boundary. These are vortex-patch solutions with regular moving boundaries and discontinuous vorticity. The translating frame may have nonconstant instantaneous speed (**p. 3, (1.4)**). The spatial contour parameter and periodic time together form the `T²` used in the proof; they are not two time frequencies.

The shape expansion in **p. 4, Remark 1** is nontrivial at order `ε²` in normalized radius, with a remainder of higher order. This establishes the desired non-rigid fluid motion. It does not concern self-gravitating fluid bodies or Euler–Poisson planets, so the earlier exploration's fluid-body discussion should not be read as ruling out this planar-vorticity result.

### 8.2 Architecture and derivative loss

1. **Point-vortex dynamics and parameter twist.** Reduce the symmetric quartet to a finite-dimensional Hamiltonian system. Show periodic leapfrogging and the necessary parameter dependence of its period/frequency. **§2, pp. 11–16; Lemma 2.1, p. 13**.
2. **Contour dynamics.** Derive a nonlinear integral equation for the boundary, with reflection symmetry and half-period delay. Use periodic Sobolev norms with parameter Lipschitz control. **§3.1–3.3, pp. 16–30**.
3. **Construct a sufficiently accurate approximate patch.** Starting from the disc leaves a residual too large compared with the inverse's `ε` loss. A higher-order approximate solution and rescaling repair that. **Lemma 3.3, pp. 31–32; §3.5, pp. 32–34**.
4. **Reduce the transport part.** A first transformation removes the problematic low-order variable coefficients; a KAM procedure then conjugates transport to constant coefficients up to a controlled error. **Propositions 4.1–4.2, pp. 34–42; Appendix A.4, pp. 71 ff.**
5. **Separate the degenerate spatial modes `±1`.** They require a coupled `4×4` differential system and monodromy analysis, including the time delay. The complement is inverted using small divisors and smoothing remainders. **§5.1–5.4, pp. 43–54**.
6. **Nash–Moser and measure.** Use an approximate right inverse with tame estimates, Fourier smoothing/truncation, and nested parameter exclusions. **Proposition 5.5, p. 53; Proposition 6.1, pp. 55–56; Corollary 6.2, pp. 63–64; Lemma 6.3, pp. 64–67**.

The leading multiplier described in the introduction is

    i[ε² ℓ ω₀(ξ₀) + ½(j−sign j)].

It is degenerate at spatial modes `j=±1`; the remaining time-space resonances are excluded. The inverse estimates in **Proposition 5.5** explicitly require higher Sobolev norms, including `‖h‖_{s+2τ}`, and powers of the small-divisor parameter. Thus **yes, there is loss of derivatives, and yes, the proof uses Nash–Moser**. KAM is used inside the transport reduction; invoking the bounded-perturbation P96-K theorem does not replace this architecture.

An advantageous feature of this *periodic-time* problem is that the exclusion weights can be placed on the spatial frequency and absorbed by spatial smoothing. HHM23 **p. 10** explains why the remaining smoothing operator need not undergo the full normal reducibility procedure used in quasiperiodic settings. The final measure estimate is stronger than a bare limit: **Lemma 6.3, p. 64**, gives `|O\C_∞| ≤ C ε^(δ/n)`, where this `n` comes from the monodromy analysis in Proposition 5.1, not from a number of temporal frequencies. Do not replace it by a universal `O(ε^δ)` estimate.

### 8.3 Distance and intermediate projects

The first wave project supplies weighted Fourier methods, infinite operator estimates, parameter Cantor bookkeeping, and disciplined source/normalization practice. It does **not** supply the contour equation, singular-integral regularity, tame changes of variables, smoothing-projector iteration, monodromy degeneracy analysis, or weak Euler reconstruction.

A realistic chain is:

- formalize the explicit four-point-vortex leapfrogging orbit, period, and frequency monotonicity;
- develop periodic Sobolev product/composition estimates and the circle Hilbert transform;
- derive contour dynamics for a single smooth patch and prove its equivalence to the Euler patch evolution;
- treat a simpler rigidly rotating or translating desingularized configuration;
- build tame transport reduction and an approximate-inverse Nash–Moser theorem with parameter exclusions;
- prove the nondegenerate normal inverse and the special delayed `±1`-mode monodromy result;
- assemble the HHM approximate patch, full iteration, parameter measure, non-rigidity, and all-time Euler reconstruction.

Indicative incremental budget **after** W: approximately **70k–160k Lean lines**, with **very low confidence**, and potentially more if the contour/PDE reconstruction or tame calculus must be built from scratch. This is a separate substantial research-formalization campaign, not an application package for the wave theorem. It is realistic as a later published-theorem target with dedicated infrastructure and source audits. It is not a responsible near-term promise alongside completion of N/P.

## 9. Decision and owner questions

**GO** for a source/design phase of track W, beginning with the exact cubic-gradient/normalization milestone. **Do not freeze the printed normal-form constants before independent audit.** Proceed to the wave headline if the bounded-operator homological prototype and refined measure blueprint both close without added conclusion-shaped hypotheses. **GO-LATER** for HHM leapfrogging, with the point-vortex theorem as its first inexpensive independent milestone.

Questions for the owner at the normal statement-review stage:

1. Adopt the recommended real scalar wave equation with `J={1,2}` and every fixed `m>0`, or prioritize the somewhat cheaper cubic NLS route?
2. Approve action-parameter density one as the first measure conclusion, with no claim about a probability on general PDE initial data?
3. Keep the first headline to analytic existence, independent frequencies, exact PDE reconstruction, and smallness, leaving linear stability/Whitney regularity as later gates?
4. Authorize a separate normalization repair in the blueprint after independent checking of E-PDE-W-1/2 and E-PDE-KP-1, rather than freezing literal inconsistent formulas?

Recommendations are the first alternatives in each question. These are questions recorded for future owner review, not a request that blocks completion of this exploration. No new statement was frozen or implicitly approved here.

## 10. Checks and handoff

Files authored: this report. PDFs added: P96-K duplicate download, P96-W, KP96 author version, HHM23 v2, as listed in §1. Existing AS26 and the earlier P96-K pin were read and hash-verified. Failed author-site/PDF requests produced no saved HTML or bogus PDF. Extracted text and rendered page images were processed in memory; no extra evidence files were created.

Checks performed: PDF magic/`pdfinfo`, SHA-256 computation, direct source-page inspection, source/code locator checks, exact rational checks of the twist factor and exponent margin, report whitespace/link checks, and scoped `git diff --check`.

Executed check results:

```text
python3 -IB scripts/check_lean_modules.py --root /root/code/KAM
  exit 0: check_lean_modules: PASS (415 Lean files, 0 comparator configurations)
python3 -IB scripts/check_frozen_anchors.py --root /root/code/KAM --manifest /root/code/KAM/manifest/frozen-anchors.json
  exit 0: FROZEN-ANCHOR GUARD OK
python3 -IB scripts/gen_root_imports.py --check
  exit 0, no output
python3 -IB scripts/render_errata.py --check
  exit 0, no output
git diff --check -- docs/explorations/pde-kam-and-leapfrogging.md
  exit 0, no output; supplemented by direct checks because the report is untracked
In-memory report checks
  all five listed PDF hashes match; no missing referenced local paths;
  no trailing whitespace or replacement characters; table declaration locators match
In-memory symbolic/rational checks
  sine fourth integral = 3/(2*pi); mixed sine-square integral = 1/pi;
  mean cos^4 = 3/8; two-mode twist determinant times pi^2*lambda_1^2*lambda_2^2 = -63/64;
  printed/derived diagonal-twist ratio = 16;
  refined measure exponent = 16/23; relative-loss exponent = 2/69;
  smallness exponent = 1/24
```

No Lean modules were changed, so there are no new Lean results or `#print axioms` outputs. The task-specific **no-build / report-only** rule governs this handoff. The full `scripts/lint_sources.sh` was inspected but not executed: its final `abi_hashes.py --check` stage invokes Lean and creates an ABI probe file. Static source/module checks can be run separately; none is presented as a kernel replay or proof receipt.

Uncertainties: the normalization repairs need independent review; the abstract proof and all component estimates have not received a complete refute-first audit; the KP96 journal printing has not been compared with its author version; size estimates are low-confidence. Suspected errata and deviations are enumerated in §4 for orchestrator action. The first unpaid mathematical gate is the normalized cubic/partial-Birkhoff attachment, followed by the bounded infinite homological operator and refined wave measure estimate—not the already-proved finite-dimensional KAM theorem.
