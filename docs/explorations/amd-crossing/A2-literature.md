> Source: `RESEARCH/LITERATURE.md` in the exploration workspace `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`. Paths `_sources/…` refer to `RESEARCH/_sources/` in the workspace.
> Date: 2026-10-31.
> Independent analysis produced for the orchestrator; not audited. Copy lightly edited: co-author naming neutralized, internal labels made neutral, cross-references pointed to the appendix files.

# Sources and novelty: strong AMD and exponential safety

Research date: 2026-10-31. Scope: the unaveraged Newtonian planetary problem, fixed mass ratios, a compact set of ordered positive semimajor axes, a **fixed positive margin below the strong Laskar–Petit threshold**, and uniformity over every permitted secular state and fast phase. This is an upgrade of the existing planar KAM development, not a claim that a new theorem has been proved in this research turn. Repository inspected read-only at `f5625f197c621ccc8045e8392a07e23fe0cb10fc`; no Lean/build verification was performed.

## 1. Laskar–Petit: precisely what is conjectured

J. Laskar and A. C. Petit, *AMD-stability and the classification of planetary systems*, A&A **605**, A72 (2017), [DOI 10.1051/0004-6361/201630022](https://doi.org/10.1051/0004-6361/201630022), [published PDF](https://www.aanda.org/articles/aa/pdf/2017/09/aa30022-16.pdf), [arXiv:1703.07125v2](https://arxiv.org/abs/1703.07125v2), submitted 22 March 2017. The published paper has 16 pages; this arXiv PDF has 18. The downloaded v2 is `_sources/LP17-arxiv-v2.pdf`, SHA256 `6b3c7aad2c2bf69612c0e0a65a5409f40a03e330253f8b3880f8e53d40f09361`. The published text was checked through the web PDF extraction; direct local download returned HTTP 403.

The following **single quotation is the identical clause in both versions**, published §3, A72 p.3, and arXiv v2 §3, p.4:

> we conjecture that in absence of short period resonances, the AMD-stability ensures the practical long-term stability of the system.

Line-break hyphenation is joined and the superscript footnote marker after “practical” is omitted. The footnote defines a time very long compared with the central star's expected lifetime. Thus the conjecture is present in the March arXiv v2, not only in the published version. Neither text supplies the quantitative uniform theorem proposed here; in particular, fixed AMD margin, compact parameter domain, arithmetic constants, and the mass threshold must be specified independently.

Exact working pins:

| Item | Published locator | arXiv v2 locator | Content to use |
|---|---|---|---|
| Canonical heliocentric split | §2.1, p.2, (2)–(8) | §2.1, p.2, (2)–(8) | Canonical momenta, including recoil, rather than independent two-body velocities |
| Angular momentum and AMD | §2.2, p.2, (9)–(11) | §2.2, p.2, (9)–(11) | (C=\sum_i\Lambda_i-|L|=\sum_i\Lambda_i(1-\sqrt{1-e_i^2}\cos i_i)), relative to the invariable plane |
| Pair contact/minimization | §3–3.1, pp.3–4, (26)–(34) | §3–3.1, p.4, (26)–(34) | Minimize the two eccentricity deficits subject to (a(1+e)=a'(1-e')), (0\le e,e'\le1) |
| Critical pair value | §3.2, p.4, (35)–(39) | §3.2, p.5, (35)–(39) | Unique critical eccentricity; (C_c(\alpha,\gamma)) is a **relative**, outer-action-normalized threshold |
| Catalogue coefficient | §5 opening, p.7, (58) | §5 opening, p.8, (58) | (\beta=C/(\Lambda' C_c)); the numerator is the **whole system's** AMD |
| Inclination proxy | §5.1, p.7, (61) | §5.1, p.9, (61) | Doubling eccentricity AMD is an equipartition assumption, not measured inclination information |
| Strong/weak | §5.3, p.8; §5.3.1–2 | §5.3, p.10; §5.3.1–2 | Planet-pair safety plus (\beta_S=C/\Lambda_1<1) is strong; weak permits stellar collision |
| Solar System qualification | §5.4.1, p.9; Figs.8–9, p.12 | §5.4.1, p.10; Figs.8–9, p.14 | Giants supply enough AMD to destabilize the inner system; subsystem classification is different |

For this campaign use the **absolute** compact minimum \(B_{ij}=\min[\Lambda_iD(u)+\Lambda_jD(v)]\), (D(u)=1-\sqrt{1-u^2}), over (u,v\in[0,1]) with (a_i(1+u)\ge a_j(1-v)). Equality of this minimum with the contact minimum is an elementary monotonicity lemma to prove. It avoids dependence on the critical-root solver and makes attainment transparent. The strong threshold is the minimum of adjacent (B_{i,i+1}) and all \(\Lambda_i\). This agrees with LP's innermost-star condition: (B_{i,i+1}<\Lambda_{i+1}), so adding the other stellar thresholds does not alter the minimum. These are campaign adaptations, not quotations of an LP theorem.

## 2. Niederman 1996: significant prior art, unresolved source pin

L. Niederman, *Stability over exponentially long times in the planetary problem*, Nonlinearity **9** (1996), 1703–1751, [DOI 10.1088/0951-7715/9/6/017](https://doi.org/10.1088/0951-7715/9/6/017). Searches by title, DOI, author, author HDR, and citations did **not** produce an inspectable original article here. A similarly titled 1995 proceedings item is not a substitute.

What could be verified from primary research papers discussing it:

* Clarke–Féjoz–Guardia, arXiv:2303.05979v1, §1.3, p.5, explain the conditional exponential stability of fast actions while secular coordinates remain in a bounded domain, and angular-momentum confinement in the near-circular/coplanar setting. This is the same basic mechanism the campaign uses.
* Barbieri–Niederman, arXiv:1810.05987v1, introduction p.2 and §5.1 p.41, attribute a roughly (4\times10^9)-year Sun–Jupiter–Saturn-model estimate at mass ratio below (10^{-13}) to Niederman. Their own theorem is local near a periodic torus.
* Niederman's [HDR](https://www.imcce.fr/content/medias/publications/publications-recherche/theses-habilitations/docs/Niederman_HDR.pdf) is accessible, but is not the 1996 theorem text.

**Not verified:** the original theorem number, exact quantified parameter domain, constants, exponents, spatial/planar distinctions of each original theorem, and whether an abstract result there already directly contains the whole strong-LP sublevel corollary. Do not fill these blanks from the project's Nek77 exponents, or cite a guessed “Theorem 1.” Acquiring the original is a literature gate for any novelty claim, not a blocker to the independent proof route specified below.

## 3. The normal-form sources

### Pöschel 1993 — original statement checked

J. Pöschel, *Nekhoroshev estimates for quasi-convex Hamiltonian systems*, Math. Z. **213** (1993), 187–216, [DOI 10.1007/BF03025718](https://doi.org/10.1007/BF03025718). The **unnumbered Normal Form Lemma, printed p.192**, was visually checked in the repository's original GDZ scan, `sources/incoming-N/poschel1993_gdz.pdf` (SHA256 `27568ec63af069ab6d6c02e0327aa2d822998be47888f20dea0c6418552dc869`); the inspected image is `_sources/poschel-p192.png`. Bibliography was cross-checked by web search. Proof: pp.193–196; analytic estimates: Appendix A, pp.211–213.

In his radian-angle conventions, (D) is \((\alpha,K)\)-nonresonant modulo a symmetric set \(\mathcal L\), (1/p+1/q=1), and

\[
 \varepsilon\le {\alpha r\over2^7qK},\qquad
 r\le\min\{\alpha/(pMK),r_0\},\qquad Ks\ge6.
\]

There is a real analytic symplectic map from widths \((r/2,s/6)\) to \((r,s)\), with

\[
 H\circ\Psi=h+g+f_*,\quad
 \|g-P_{\mathcal L}T_K f\|\le16c\varepsilon^2,\quad
 \|f_*\|\le\varepsilon e^{-Ks/6},\quad
 \|\Pi_I\Psi-I\|\le c\varepsilon r,
 \quad c={2qK\over\alpha r}.
\]

For \(\mathcal L=\{0\}\), (g) is independent of the fast angles. This published statement does **not** include additional canonical secular pairs. Treating those pairs as passive parameters would omit their Poisson-bracket derivatives. The repository's extended theorem explicitly supplies that missing part.

### Barbieri–Marco–Massetti 2022

S. Barbieri, J.-P. Marco, J. E. Massetti, *Analytic Smoothing and Nekhoroshev Estimates for Hölder Steep Hamiltonians*, CMP **396**, 349–381, [DOI 10.1007/s00220-022-04464-0](https://doi.org/10.1007/s00220-022-04464-0). Published PDF checked, `_sources/BMM22.pdf`. **Appendix B, Lemma B.1, p.380, (B.1)–(B.5)** states a Pöschel form with

\[
 \varepsilon\le{\alpha\rho'\over256\xi K},\quad
 \rho'\le\min\{\rho,\alpha/(2\xi MK)\},\quad K\sigma\ge6,\quad\xi>1.
\]

The remainder is \(\varepsilon e^{-K\sigma/6}\); the correction to the resonant truncation is at most \(64K\varepsilon^2/(\alpha\rho')\). Its action-angle domain has no extra secular pairs. Equation (B.3) prints \(\{h,g\}=0\); for a general resonance module, Fourier support alone does not imply that identity on a whole thick domain. The present use is only the zero module, where angle-independence suffices. No general-module commutation claim is imported.

### Pinzari–Liu 2023

G. Pinzari and X. Liu, *Quantitative KAM theory, with an application to the three-body problem*, J. Nonlinear Sci. **33**, 90, [DOI 10.1007/s00332-023-09948-4](https://doi.org/10.1007/s00332-023-09948-4), [arXiv:2302.00279v2](https://arxiv.org/abs/2302.00279v2), 1 August 2023. Checked **§3.4, Proposition 3.2, pp.30–31; Lemma 3.3, p.31; (85)–(87); iteration pp.32–34**.

This is a useful independent slow-variable normal-form source: the analytic cost uses \(\delta=\min\{\hat r\hat s,\hat\varepsilon^2\}\), reflecting both fast and slow brackets. Its mixed Fourier–Taylor nonresonance hypothesis must be preserved. In a specialization with zero unperturbed slow frequencies, pure slow monomials must belong to the retained module; one cannot require their divisors to be nonzero. The exact constants used in PROOF-PLAN ([A4](A4-proof-plan.md)) are instead those of the already implemented Track N extension.

### The directly reusable extended theorem in KAM

`KAM/Nekhoroshev/Partial/Setting.lean:ExtNFHyp`, `Partial/NormalForm.lean:nf` (line 604), and `Partial/Nonresonant.lean:nonresonant` (line 341) are the decisive finds. The source is `blueprint-N/parts/p11b-partial-nf.tex`, node `bpN:p11:nf`, and `p11c-partial-stability.tex`, node `bpN:p11:nonresonant`, recorded in `docs/graph/N/DEPGRAPH.md`. They permit an **arbitrary real secular set S**, thickened in complex space, and bound the slow bracket through (64\pi ksr\le w^2). They are stronger for this task than an ordinary action-angle normal form. This research inspected their statements and proof route; it did not rerun a kernel or source audit.

## 4. Planetary analytic domains and angular-momentum closure

T. Castan, *Stability in the plane planetary three-body problem*, thesis, UPMC/Observatoire de Paris, 2017, [HAL tel-01597143](https://theses.hal.science/tel-01597143), deposited 28 September 2017. Checked `_sources/Castan2017.pdf`:

* §1.2, **Proposition 1.3, printed p.25 / PDF p.36**, complex Kepler equation on an explicit domain;
* **Proposition 1.5, printed p.28 / PDF p.39**, and **(1.31)**, positive image strip for its inverse;
* §1.3, **Proposition 1.8, printed p.39 / PDF p.50**, complex distance/Legendre bounds;
* **Theorem 1.9, printed p.40 / PDF p.51, (1.43)**, a disturbing-function bound under explicitly listed widths and separation inequalities.

These give a route to numerical constants. They are not a ready-made uniform theorem on every strong-AMD sublevel. For qualitative existence, `KAM/Planetary/Exponential/ComplexTube.lean:tube` already supplies periodic holomorphic extension from a compact safe real set; the new work is proving the strong-LP set lies there with a collar.

S. Barbieri and L. Niederman, *Sharp Nekhoroshev estimates for the three body problem around periodic orbits*, JDE **268** (2020), 3749–3780, [DOI 10.1016/j.jde.2019.10.013](https://doi.org/10.1016/j.jde.2019.10.013), checked [arXiv:1810.05987v1](https://arxiv.org/abs/1810.05987v1), 14 October 2018. Exact pins: **§3.3.2, Theorem 7, pp.30–32, (93)–(102)**; **§3.3.3, p.32**. Theorem 7 bounds eccentricities through angular momentum, the available action drift, and a strict secular-domain inequality. Its proof introduces a secular first-exit time and excludes exit. The final theorem is explicitly local near an unperturbed periodic torus; it is not a whole-LP-sublevel theorem. These are preprint locators; no unverified published renumbering is asserted.

## 5. Large secular domains and the instability boundary

G. Pinzari, *Perihelia reduction and global Kolmogorov tori in the planetary problem*, Memoirs AMS **255** (1218), 2018, [arXiv:1501.04470v4](https://arxiv.org/abs/1501.04470v4), 20 September 2016. Checked PDF: **Proposition 5.1, printed pp.37–38 / PDF pp.41–42, (5.2)–(5.4)**, averaging the fast angles with exponential remainder; **Appendix D, Proposition D.1, printed pp.77–78 / PDF pp.81–82**, and **Lemma D.2, p.79 / PDF p.83**. This genuinely allows eccentricities not close to zero and appreciable inclinations, but uses hierarchical axis separation and structured coordinate domains; its headline eccentricity range approaches the Levi-Civita limit, not all (e<1). It does not establish uniformity on an arbitrary strong-LP sublevel.

G. Pinzari, *Aspects of the Planetary Birkhoff Normal Form*, RCD **18** (2013), 860–906, [DOI 10.1134/S1560354713060178](https://doi.org/10.1134/S1560354713060178): the [publisher abstract](https://rcd.ics.org.ru/S1560354713060178/) explicitly reports planar exponential stability of planetary actions outside mean-motion resonances. This is relevant prior art. Its exact full theorem/domain was not inspected here, so it is a further novelty-review item, not an exact supplier in the proof graph.

A. Clarke, J. Féjoz, M. Guardia, *A counterexample to the theorem of Laplace–Lagrange on the stability of semimajor axes*, ARMA **248**, 19 (2024), [DOI 10.1007/s00205-024-01960-6](https://doi.org/10.1007/s00205-024-01960-6), checked [arXiv:2303.05979v1](https://arxiv.org/abs/2303.05979v1), 10 March 2023. **Theorem 1, p.4; (3)–(4), p.4; §1.3, p.5; §8.1**: hierarchical spatial four-body solutions realize prescribed eccentricity/angular-momentum and outer-axis itineraries; in planetary scalings the diffusion time can be polynomial. These families are not confined to one mass-independent compact set of axes with a fixed strong-AMD margin. This prevents an overbroad theorem, but is not a counterexample to the proposed quantified statement.

## 6. Search result and recommended novelty language

Searches included the exact Niederman title/DOI; combinations of “AMD-stability”, “angular momentum deficit”, “exponential”, “Nekhoroshev”, “rigorous theorem”; large-eccentricity planetary averaging; and source chaining through the papers above. Results also included resonance-overlap criteria (e.g. Hadden–Lithwick, [arXiv:2106.14863](https://arxiv.org/abs/2106.14863)) and numerical classification. An overlap criterion or empirical stability classifier is not the required unaveraged finite-time theorem.

**Verdict: the mechanism is known; the proposed sharp uniform-domain corollary is plausibly new as a packaged statement, but novelty is unverified.** Angular momentum plus exponentially small fast-action drift is already explicit in Nekhoroshev/Niederman and BN20, and already implemented in this repository with a cruder box. No inspected source states the entire spatial strong-LP-sublevel theorem with uniform constants, a fixed positive threshold margin, arbitrary secular dynamics, and the specified Diophantine exponent. Absence from this search is not proof of novelty, especially with the original Ni96 and the full Pinzari13 theorem still unpaid source checks.

Safe campaign description: “A formalized strong-AMD refinement of planetary exponential safety, with a nonresonant rate and a spatial extension.” Do not advertise a new normal-form theorem, a proof of perpetual stability, a practical actual-mass result, or complete resolution of the informal LP conjecture. The practical lifetime and numerical smallness questions are additional obligations.
