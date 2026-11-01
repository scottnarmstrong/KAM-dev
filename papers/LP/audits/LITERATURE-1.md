# LITERATURE-1: literature and quotation audit of papers/LP

Auditor: independent, refute-first (wrote none of the text). Date 2026-11-01, 10:01 UTC.
Target: commit `cda28701`, worktree `/mnt/HC_Volume_106379410/kam-paper/KAM-paper-lp`, `papers/LP/` (main.pdf, 23 pp, ModDate 09:56 UTC).

```
f3ff73e5d17bc33caf1b7b2208ff88bd9cb03afc1804b23ba9a6fe81cf7018f7  papers/LP/sections/abstract.tex
ada83f3d7164acae9789f09af5b1f7f12c14c89976fa433fd8d809971660e9b6  papers/LP/sections/barrier.tex
a181b6562a9f7227abbf3108d53db74e5f23fd7fbf3e07c8acfd13c473f2da8e  papers/LP/sections/formal.tex
80434fbe44a19b4cbc64237446be9a3302097858d31365048a2e7d3260f3726a  papers/LP/sections/intro.tex
5959168e64b3799604c8f027d25f618d884e4b770ee7df2548d474a8a7c1e3c5  papers/LP/sections/outlook.tex
b2ac9581303d74a1e4b2e1b7378c02e68ddd75795445bbdcaa1c5dbcea1295f9  papers/LP/sections/planar.tex
971762711fd9c61e45f1358b2ddaeef31e343aaaf91d97717bf20daf93091736  papers/LP/sections/resonant.tex
be293bf790dea4e255f293b3afb4d54d4d0ac283c490ec066eac4314c313d347  papers/LP/sections/results.tex
fcadf891d3ac3ae65c274041ab3c30be77c98ecce7726aff1b89a3d10e4698a3  papers/LP/sections/spatial.tex
057db74fbcd16f4ac5b2b980240889e37d2e532ec8de168b2fa74e43fe649ae0  papers/LP/refs-A.bib
3a88dd6af1066cc7fccf5cfd945f0b3c6cf89a46f1b73f5b8ad719ffd0a94e4c  papers/LP/refs-B.bib
1bf44ca0117c6090621b13ae211c6e47f8760ede56695a51700a97ca4e77d81a  papers/LP/refs.bib
38c1f4e2786e90d5b5b4e8a42a612b430b3aac2e33af6fbe3377e1e72eb7874f  papers/LP/refs-C.bib
```

Sources inspected: LP17 arXiv:1703.07125v2 (pdftotext); Nekhoroshev 1977 English (pdftotext and rendered pp. 9, 28–31, 55–56);
Pöschel 1993 GDZ scan (rendered printed pp. 191–192); BN arXiv:1810.05987v1 (the two local copies are byte-identical);
CFG arXiv:2303.05979v1; Pinzari arXiv:1501.04470v4. I did not inspect Niederman 1996.

## Verdict: **PASS WITH NOTES**

Every locator I checked exists and says what the paper says it says (LP17 §2.2 and (11), §3 and footnote 1, §§3.1–3.2,
§5.3, §5.3.2, §5.4.1; Nek77 §1.11 p.9, §1.18, (4.1), (4.4), (4.5), Thm 4.4 p.30, Rem. 4.5.A, §12.2, Thm 12.3
pp.55–56, (12.3)–(12.5); Pöschel's Normal Form Lemma on printed p.192; BN p.2, §3.3.2 Thm 7, §3.3.3, §5.1; CFG §1.3,
Thm 1; Pinzari Prop. 5.1). The one quotation is verbatim. The exponents check out: with all steepness indices 1, (4.1)
gives ζ = s(s−1)/2, and (4.4)–(4.5) then give a = 2/(6n²−3n+14) and b = 3/(6n²−3n+14) = (3/2)a, which match (12.4)–(12.5).
Scope language follows the binding rules. The text uses no "first", "new" or "novel" claim and hedges novelty ("to our
knowledge"). It explicitly says the mechanism and the normal form are not new, says nothing about the Solar System, and
calls the results "a rigorous asymptotic form of the mechanism … not resolve the conjecture". One MAJOR finding remains
(F1): the comparison with Nekhoroshev's Theorem 12.3 undersells that theorem, so the "what is added" claims for
Theorem E are stated unfairly. The paper does not fail on any citation.

## Findings

### F1 — MAJOR — Comparison with Nekhoroshev Thm 12.3 understates prior work; "what is added" for Theorem E is overclaimed

Locations:
- intro.tex:30: "Theorem~\ref{thm:resonant} has the same exponents; its hypothesis is the pointwise strong AMD condition $C(0)\leq B(\Lambda(0))-\delta$ at the initial axes, rather than a threshold uniform over a box, and its conclusions add …"
- intro.tex:32: "What we add is the form of the statement: the hypothesis is exactly the strong AMD-stability condition at the initial actions, with only a fixed margin; the constants are uniform over the whole corresponding sublevel set, including large eccentricities and, in space, arbitrary inclinations; … To our knowledge, the statement in this sharp form has not appeared."
- resonant.tex:7–8: "What is added is the sharp hypothesis $C(0)\le B(\Lambda(0))-\delta$ on the whole curved sublevel."

Evidence (Nek77 p.55, §12.2, rendered): the domain is B(α,β,γ) = {α_i ≤ a_i ≤ β_i, |N| ≥ γ}, where N is the total angular
momentum of the unperturbed system divided by μ. "Another critical value of γ is the largest value for which the
boundary … of B(α,β,γ) contains points corresponding to collisions of the planets, either with one another **or with the
centre of attraction O**. We denote this value by γ₀(α,β)." Definition 12.2.A requires γ₀ < γ < γ_m. Theorem 12.3
(pp.55–56): no collision on [0,T] with T = M⁻¹exp(M^{−a}), M = C₁μ, and |a_i(t)−a_i(0)| < C₂μ^b.
A lower bound |N| ≥ γ is the same as an upper bound on the AMD, ΣΛ_i − C ≥ γ. And γ₀ is by definition the collision
threshold over the box, including collision with the star, which is exactly the strong threshold. Nekhoroshev's domains
therefore already are strong-AMD sublevels over a box of axes. They also already allow large eccentricities and arbitrary
mutual inclinations, since nothing restricts the domain beyond |N| ≥ γ. B is continuous (Lemma 3.4), and a compact
𝒜 is covered by finitely many small boxes with finitely many γ levels. So the hypothesis C(0) ≤ B(Λ(0)) − δ appears to be
reachable from Theorem 12.3 by bookkeeping: on a box of width w, γ₀ ≤ ΣΛ(0) − B(Λ(0)) + o_w(1). This is essentially what
§6 does with Nek77 Thm 4.4. The resulting "pointwise vs. uniform over a box" distinction therefore does not strengthen
the hypothesis, up to the arbitrary margin δ. The same applies to "uniform over the whole sublevel, including large
eccentricities and arbitrary inclinations" as a distinguishing feature, at least for Theorem E.
What is genuinely different for Theorem E is narrower. Theorem E identifies the hypothesis with the LP17 threshold, adds
the annulus-ordering and osculating conclusions, covers both directions of time and well-posedness, and has a formal
proof. Note that Nekhoroshev's own text says "collisions or even close approaches … are impossible" (p.55).
For Theorems B–D, the O(√μ) drift and the exponent 1/(2(τ+1)) under a Diophantine condition do differ from Nek77, and the
hedged novelty sentence is acceptable for them.
Smallest repair:
1. In intro.tex:30, replace "rather than a threshold uniform over a box" by a sentence along the lines of: "Since |N| ≥ γ
   is an upper bound on the AMD and γ₀ is the collision threshold over the box (including collision with the star),
   Nekhoroshev's domains are strong-AMD sublevels over boxes of axes, and covering 𝒜 by finitely many small boxes gives a
   statement of the type of Theorem E under the same hypothesis up to the margin."
2. Restrict intro.tex:32 "What we add" to Theorems B–D, and add a separate, more modest sentence for Theorem E (LP
   identification, annuli and osculating conclusions, formal proof).
3. Change resonant.tex:7–8 to something like "What is added is the identification of Nekhoroshev's collision threshold
   with the strong AMD threshold of Laskar and Petit and the conclusions on the orbital annuli."

If the authors believe there is a real gap between Theorem 12.3 and Theorem E, for example in the coordinates (barycentric
velocities versus canonical heliocentric momenta) or in the backward time direction, the paper must state that gap
explicitly.

### F2 — MINOR — "with a threshold that is sharp" without qualification

Location: intro.tex:3 ("…an elementary conserved quantity bounds this growth for an exponentially long time, with a threshold that is sharp."). The abstract (abstract.tex:2, "up to the sharp strong threshold") and Theorem A's title "Sharp barrier" have the same problem.
Evidence: barrier.tex:69 itself says "This is sharpness of the geometric condition only, not a claim that motion above the threshold must collide." The intro sentence reads as dynamical sharpness.
Repair: write "with a threshold that is geometrically sharp (orbits can touch at the threshold)", or drop "sharp" in intro.tex:3.

### F3 — MINOR — LP17 locators for the definitions of AMD-stability and strong AMD-stability are imprecise

Location: intro.tex:5 "They call a system AMD-stable if its AMD is below this value for every adjacent pair, and strongly AMD-stable if, moreover, it is below the value Λ₁ at which the innermost planet can reach the star~\cite[\S5.3]{LP17}."
Evidence (LP17 arXiv v2, p.8, untitled preamble of §5 just before §5.1): "A system is AMD-stable if every adjacent pair is AMD-stable … We define βS … For this pair, we have α = 0 and thus Cc = 1. With this simplification βS = C/Λ, where Λ is the circular momentum of the innermost planet." §5.3 (p.10) then defines "strong AMD-stable" as max β < 1 and βS < 1. The content is correct; the adjacent-pair definition and βS = C/Λ₁ are in §5, not §5.3.
Repair: cite "\S5 and \S5.3" (likewise results.tex:28).

### F4 — MINOR — Outlook overstates what BN20 §5.1 obtains at 10⁻¹¹

Location: outlook.tex:15–18 "\cite[\S5.1]{BN20} reaches times comparable to the age of the Solar System for perturbations of size about $10^{-11}$ in their normalization".
Evidence (BN arXiv v1 p.40, Table 1, exactly at the 5:2 resonance): log ε = −11.25 gives t̄ = 5.75×10¹⁰ y, but log ε = −11.00 gives t̄ = 3.08×10⁷ y. Table 3 (off resonance): log ε = −11.5 gives 1.04×10⁹ y. On p.41 the authors summarise their result as "good times of stability (i.e. greater or equal, say, than 1×10⁹ years) for values of ε which are almost 100 times greater than those in [30]", i.e. about 10⁻¹¹ for ≥10⁹ years, not for the age of the Solar System (≈5×10⁹ y).
Repair: "for perturbations of size about $10^{-11.25}$ exactly at the resonance (about $10^{-11.5}$ for nearby initial actions) \cite[\S5.1, Tables 1 and 3]{BN20}".

### F5 — MINOR — BN p.2 attribution drops the resonance qualifier

Location: intro.tex:30 "…give stability for a time comparable with the age of the Solar System when the mass ratio is below $10^{-13}$~\cite[p.~2]{BN20}."
Evidence (BN p.2): "In the case of the 5 : 2 resonance, stability holds for a time comparable with the age of the Solar System if the ratio for the mass of the greater planet on the Sun mass does not exceed 10⁻¹³". BN p.41 gives the figure as "t̄ ∼ 4×10⁹ years for ε < 10⁻¹³".
Repair: insert "for a Sun–Jupiter–Saturn model near the $5{:}2$ resonance" and "the mass of the larger planet".

### F6 — MINOR — Solar-System AMD-instability attributed to LP17 as their finding

Location: outlook.tex:23–24 "Laskar and Petit find it AMD-unstable, because of the AMD carried by the giant planets \cite[\S5.4.1]{LP17}".
Evidence (LP17 §5.4.1): "Owing to the large amount of AMD created by the giant planets, the inner system is not AMD-stable (Laskar 1997)." The Conclusion says "The solar system is AMD-unstable".
Repair: "Laskar and Petit classify it as AMD-unstable (following Laskar 1997) …". The logical consequence the paper draws (the hypothesis fails for the eight-planet model) is fine.

### F7 — MINOR — Niederman's prior work is characterised only through CFG, and that description is used as a contrast

Location: intro.tex:30 (Niederman via \cite[\S1.3]{CFG24}) together with intro.tex:32 ("including large eccentricities and, in space, arbitrary inclinations").
Evidence: CFG §1.3, p.5, is quoted accurately: "provided that the actions in the degenerate (i.e. secular) directions remain in some bounded region, the actions conjugate to the fast angles are stable … In the neighborhood of coplanar and circular ellipses … the conservation of the angular momentum prevents the degenerate actions … to undergo any substantial instability". But Nie96 was not inspected (outlook.tex:38–39 says so honestly). The contrast "including large eccentricities" therefore rests on a secondary summary, and per F1 it is not a distinguishing feature against Nek77 Thm 12.3 either.
Repair: in intro.tex:32, either drop the large-eccentricity and inclination clause as a point of difference, or add "(in contrast with the near-circular regime described in \cite[\S1.3]{CFG24}; we have not inspected \cite{Nie96})".

### F8 — MINOR — The abstract says "the same holds" for Theorem E, but the drift is different

Location: abstract.tex:2 "Without arithmetic conditions the same holds with Nekhoroshev's exponents."
Evidence: Theorem E (results.tex:90) has drift μ^{b} in place of √μ; the abstract's preceding sentence asserts O(√μ).
Repair: "Without arithmetic conditions the same holds, with drift $O(\mu^{b})$ and time exponent $a$ given by Nekhoroshev's exponents."

### F9 — MINOR — Formal-verification status is stated inconsistently (overclaim risk)

Locations:
- abstract.tex:2: "The results under the Diophantine condition are formally verified in the Lean proof assistant."
- intro.tex:34: "A formal proof of Theorem~E is in preparation".
- formal.tex:104–110: "The same is reported for the development version of the formal proof of Theorem~E … Theorem~E is proved on a development version; its independent review is in progress. The exact statement texts of all results are under final review."

Evidence: these sentences disagree. "In preparation" and "proved on a development version" are different claims. "Statement texts … under final review" qualifies the abstract's unqualified "formally verified".
Repair: use one status sentence everywhere, and qualify the abstract until the statements are frozen.
Checked, no issue: the Proposition 6.1 file, `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean` at `a994efdf`, contains no `sorry`; its body delegates to the provider.

### F10 — MINOR — Bibliography metadata not verifiable locally; repository citations may be inaccessible

- BN20 (JDE 268 (2020) 3749–3780, doi 10.1016/j.jde.2019.10.013): the arXiv v1 title matches. The journal data matches the A2 survey pin but not a published PDF, so it is unverified.
- CFG24 (ARMA 248 (2024) art. 19, doi 10.1007/s00205-024-01960-6): the title and authors match arXiv v1. The DOI matches `docs/sources.json`, which gives the first author as "J. Clarke" (an error in the registry; the paper's "Andrew Clarke" is correct per the arXiv PDF). The volume and article number are unverified.
- Pin18 (Mem. AMS 255, no. 1218, 2018): the arXiv v4 title "Perihelia Reduction and Global Kolmogorov Tori in the Planetary Problem" matches. The journal data is unverified.
- Pos93 (Math. Z. 213, 187–216): the volume and year are confirmed by the GDZ cover, and the scan has 30 pages after the cover, consistent with 187–216. The DOI BF03025718 agrees with `sources.json` but is not independently verified.
- Nie96 (Nonlinearity 9(6), 1703–1751): this agrees with the reference lists of CFG [51] and BN [30]. The DOI is unverified.
- Nek77 (Russian Math. Surveys 32(6), 1–65): this is consistent with the English PDF (65 pp., running heads p.1–65).
- LP17 (A&A 605, A72, doi …/201630022): the arXiv header "manuscript no. 30022" is consistent with the DOI. The volume and article number are unverified. The paper asserts no published page number (good).
- Lean4 (CADE-28, LNCS 12699, 625–635) and Mathlib (CPP 2020, 367–381): unverified locally.
- KAMnotes and KAMrepo point to `github.com/scottnarmstrong/KAM-dev` at `a994efdf`. The files `docs/tracks/LP/source/MAIN.md` and `AMENDMENTS.md` exist at that commit. I cannot tell whether the repository is public. If it is not, "Complete proofs … are written out in~\cite{KAMnotes}" (intro.tex:34, planar.tex:36, 81, spatial.tex:47) cites an inaccessible source.

Repair: verify the flagged fields against the publishers' pages before submission. Make sure the cited repository and commit are public, or point to an archived copy.

## Locators checked and found correct (no action)

- intro.tex:5–9, LP17: §2.2 AMD definition and (11) Σ Λ_k(1−√(1−e_k²)cos i_k) with Λ_k = m_k√(μa_k), μ = Gm₀. §3: least AMD for contact of two planets. "conserved in the secular system at all orders". The quotation, "we conjecture that in absence of short period resonances, the AMD-stability ensures the practical long-term stability of the system.", is verbatim except for the footnote mark. Footnote 1 reads "practical stability means stability over a very long time compared to the expected life of the central star".
- results.tex:28 and barrier.tex:55, 66: C_c(α,γ) as the minimum of the relative AMD on αe + e′ − 1 + α = 0, 0 ≤ e, e′ ≤ 1 (LP17 (28)–(30), §§3.1–3.2), normalised by Λ′ of the outer planet. This is correct.
- outlook.tex:34–35: weak AMD-stability allows the innermost planet to reach e = 1 and collide with the star (LP17 §5.3.2). Correct.
- resonant.tex:5–6, 34–38: §1.18 (convex, hence quasiconvex, hence steep, with the planetary example), §1.11 p.9 (quasiconvex implies all steepness indices are 1), Thm 4.4 p.30, Rem. 4.5.A (sup|H₁| allowed), (4.1)/(4.4)/(4.5). The Euclidean norms are fixed in §4.1 and §4.3.A rather than §4.2 (§4.2 defines X−ε), which is a negligible point. The "slightly weaker form" description is accurate: a max-norm erosion is a stronger hypothesis, a stopped slow condition is equivalent to applying Thm 4.4 with C := t, and the max-norm conclusion is weaker.
- intro.tex:28 and planar.tex:81, 175: Pöschel's "Normal Form Lemma" is on printed p.192. It has no slow variables; "of the type of" and "in the form of" are acceptable, and the text disclaims novelty.
- intro.tex:30: BN §3.3.2 Theorem 7 ("Stability of the cartesian variables", confinement via angular momentum, pp.30–32). §3.3.3: "Such result is strictly local since it has been constructed in the neighborhood of a periodic torus". Correct.
- intro.tex:30: CFG Theorem 1 (4-body problem with three planets; itinerary of a₃ ∈ [1,∞)). §1.3: "In the planetary regime, the conservation of the angular momentum does not prevent secular variables from drifting because of the high inclination of the two inner planets." Correct. Note that Theorem 1 itself is stated in the hierarchical regime with fixed masses, and the planetary-regime version is Thm 3/§8.1. The paper's wording ("orbits of the problem with three planets") is not wrong.
- intro.tex:30: Pinzari Prop. 5.1 (normalisation of fast angles, remainder bounded by e^{−ĉK̄s}/…, (5.6)). Correct.
- outlook.tex:31–32 (Nek Thm 12.3 exponents) and outlook.tex:38–39 (Nie96 not inspected) are honest and correct.

## Overclaim and novelty scan

The text contains no "first", "novel" or "new result" claim. "New" appears only in negations ("The mechanism is not new"; "We do not present the normal form as new"; "we do not claim them as new"). There is no Solar-System claim (outlook.tex:23–25, results.tex:97, intro.tex:26). The relation to the conjecture is framed correctly (abstract; intro.tex:26). The remaining overclaims are F1 (main), F2, F8 and F9.
