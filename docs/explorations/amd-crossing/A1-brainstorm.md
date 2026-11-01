> Source: `BRAINSTORM-1.md` in the exploration workspace `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`.
> Date: 2026-10-31.
> Independent analysis produced for the orchestrator; not audited. Copy lightly edited: co-author naming neutralized, internal labels made neutral, cross-references pointed to the appendix files.

**Independent brainstorm of the proposed AMD theorem — 31 October 2026**

**Verdict.** There is a very plausible and worthwhile theorem here, but the sentence is not yet a theorem statement. Its most promising interpretation is an exponential-time consequence of **nonresonant averaging, exact angular-momentum conservation, and the AMD geometric barrier**. It need not require integrability, steepness, or regularity of the secular trajectories. However, quantitative nonresonance, a positive safety margin, a specified convention for orbital elements, and protection against stellar collision are essential to the proposed proof. The exponent \(1/(2n+1)\) is defensible under a particular Diophantine hypothesis; it is neither automatic from “nonresonant” nor a canonical exponent determined just by counting planets.

The qualitative idea has clear prior art. In the published Laskar–Petit paper, §3 explicitly says “we conjecture that in absence of short period resonances” before asserting practical long-term stability from AMD stability. Thus a rigorous, quantified version would address an existing conjectural principle. I did not find a source stating exactly the fully specified theorem proposed below; that is not evidence that the result is new. [Laskar–Petit, 2017, published article](https://doi.org/10.1051/0004-6361/201630022).

**Scope and method.** The frozen input is the co-author's message (input file, lines 3–7), SHA-256 04a2c8c4f0abe1db597e83416599eced31543fbec914d30bf5499d3db9c6cd25. I first reconstructed the mechanism independently, then searched the literature and checked relevant statements, formulas, and limitations. This is an independent mathematical brainstorm with a self-refutation pass, not a complete proof audit or a Lean source audit. No source files, repository history, or Lean artifacts were changed, and no builds were run; this report is the sole written artifact. The exponent notation in the message is ambiguous; throughout I use the interpretation requested by the owner, \(\mu^{-1/(2n+1)}\).

**1. Is it plausibly true? The mechanism and its actual obligations.**

My answer is **yes for a quantitatively specified, uniformly separated, strongly AMD-stable family; not established as literally written**. “Strongly” here includes a barrier against point-star collision, defined below. If only planet–planet crossing is intended, the weaker version needs a stopping condition or an independent stellar-distance bound.

Before consulting the literature, the decisive observation was
\[
C(t)-C(0)=\sum_{i=1}^n\bigl(\Lambda_i(t)-\Lambda_i(0)\bigr),
\tag{1}
\]
where \(\Lambda_i\) are the correctly normalized Kepler actions and the AMD is \(C=\sum_i\Lambda_i-|\mathbf L|\). The total angular momentum \(\mathbf L\) is exactly conserved by the full Newtonian system. Consequently, slow drift of the fast actions controls the **total** AMD even if individual eccentricities and inclinations change substantially.

The natural proof has the following steps.

| Step | Mathematical content | Assessment |
|---|---|---|
| 1 | Write the exact translation-reduced Newtonian Hamiltonian as \(h(\Lambda)+\mu f(\Lambda,\lambda,z)\), with \(n\) fast angles and secular variables \(z\). | Standard, but mass scaling and element conventions must be exact. |
| 2 | Prove that an AMD margin below every relevant pair threshold gives disjoint radial annuli; add a star barrier for positive perihelia. | Elementary geometric core. It controls every angular configuration compatible with the AMD budget. |
| 3 | Enlarge the safe set and construct a complex analytic neighborhood with bounds on the exact Hamiltonian and coordinate maps. | Delicate. Real separation alone is not a numerical complex-width estimate. Large eccentricities worsen the constants. |
| 4 | Impose finite-order nonresonance near the initial fast actions and average the fast angles to exponential accuracy. | Standard normal-form technology; the version with evolving secular variables must be pinned and checked. |
| 5 | Integrate the exponentially small derivative of each fast action in normal-form coordinates. Include both coordinate changes. | Standard once the correct normal form exists. No secular trajectory shadowing is required. |
| 6 | Transfer to the original canonical elements, use (1), and control the moving collision threshold. | Essential; a threshold evaluated only at \(t=0\) is insufficient. |
| 7 | Close a first-exit argument excluding action-domain exit, loss of the AMD margin, and collision. | The main logical assembly. It removes an otherwise circular assumption that secular variables remain safe. |
| 8 | Deduce actual separation and, if requested, compare genuinely osculating heliocentric ellipses. | Compact-domain estimates, but a separate coordinate bridge. |

The relevant normal form is
\[
H_\mu\circ\Phi
=h(J)+Z_\mu(J,z)+R_\mu(J,\theta,z),
\qquad \partial_\theta Z_\mu=0.
\tag{2}
\]
The function \(Z_\mu\) may define complicated, nonintegrable secular dynamics. Nevertheless,
\[
\dot J=-\partial_\theta R_\mu.
\tag{3}
\]
If \(\|\partial_\theta R_\mu\|\le M_R\mu e^{-\kappa K}\), then, while the orbit stays in the normal-form domain,
\[
\|J(t)-J(0)\|_\infty
\le M_R\mu |t|e^{-\kappa K}.
\tag{4}
\]
An exponential time with a smaller exponent leaves this drift tiny. Add the displacement of \(\Phi\) and \(\Phi^{-1}\), then use the geometric barrier to justify continued residence in the domain.

**A crucial distinction:** do not try to show that the full solution follows one particular secular solution throughout the claimed time. A Gronwall estimate in a chaotic secular system can destroy that comparison much earlier. Equations (3)–(4) instead estimate almost conserved quantities along the actual transformed orbit. They do not contain a secular Lyapunov exponent. This is precisely why chaotic secular dynamics can coexist with the conclusion.

There is also a useful coordinate fact. After rotating the reference plane so that its normal is \(\mathbf L(0)\), spatial Poincaré variables satisfy
\[
C=\frac12\sum_i(\eta_i^2+\xi_i^2+u_i^2+v_i^2)
\tag{5}
\]
along the exact trajectory. A strong AMD margin therefore supplies a whole bounded secular region, not merely a neighborhood of the initial secular point. Construct averaging on an enlarged version of that region. This avoids assuming that chaotic trajectories remain near their starting eccentricities. The angular-momentum formula can be checked against [Chierchia’s planetary-problem treatment, §3.6](https://upcommons.upc.edu/server/api/core/bitstreams/e4d6ade3-07a2-43b1-9edc-c19a8c3e4b50/content).

**What could fail?** The argument fails if the normal form is valid only near the initial secular state, if the orbit can approach the star, if arithmetic constants deteriorate without accounting for them, or if the AMD gap is smaller than coordinate and action errors. None is cured by saying that the Kepler Hamiltonian is convex up to sign.

**2. Exact meanings, normalizations, and the exponent.**

**The unaveraged problem and \(\mu\).** Choose units with gravitational constant \(G=1\) and stellar mass \(m_0=1\), and write
\[
m_i=\mu\nu_i,\qquad 0<\nu_i\le1,\qquad \max_i\nu_i=1.
\tag{6}
\]
Thus \(\mu\) is the largest planet/star mass ratio, while the positive relative masses \(\nu_i\) are fixed as \(\mu\to0\). Total planetary mass divided by stellar mass is an equivalent parameter for fixed \(n,\nu\), with changed constants. A massless limit is separate: AMD cannot constrain an exactly massless body through a positive mass-weighted deficit.

Let \(q_i=x_i-x_0\) be heliocentric positions, and \(p_i=P_i/\mu\), where \(P_i\) is the planet’s barycentric momentum in the zero-total-momentum frame. After translation reduction, dividing the physical Hamiltonian by \(\mu\) gives the exact Hamiltonian
\[
\begin{aligned}
H_\mu(q,p)
&=\sum_i\left(\frac{|p_i|^2}{2\nu_i}-\frac{\nu_i}{|q_i|}\right)\\
&\quad+\mu\left(\frac12\left|\sum_i p_i\right|^2
-\sum_{i<j}\frac{\nu_i\nu_j}{|q_i-q_j|}\right).
\end{aligned}
\tag{7}
\]
The scaled equations have the same time variable as the physical equations. The star’s recoil is included; the star is not held fixed dynamically. There is no truncation in eccentricity, inclination, separation, or powers of \(\mu\) in (7).

For this splitting, define canonical Kepler elements using position \(q_i\), Kepler velocity \(p_i/\nu_i\), and gravitational parameter \(1\). Then
\[
\Lambda_i=\nu_i\sqrt{a_i},\qquad
h(\Lambda)=-\sum_i\frac{\nu_i^3}{2\Lambda_i^2},\qquad
\omega_i(\Lambda)=\frac{\nu_i^3}{\Lambda_i^3}=a_i^{-3/2}.
\tag{8}
\]
Here \(h,\omega\), and the normalized action definitions do not depend on \(\mu\). This is the fixed-central-mass splitting in the AMD paper, after scaling. Another standard exact splitting absorbs diagonal recoil into reduced masses \(b_i=\nu_i/(1+\mu\nu_i)\) and Kepler parameters \(k_i=1+\mu\nu_i\), and uses \(\Lambda_i=b_i\sqrt{k_i a_i}\). Both are legitimate, but elements and thresholds cannot be exchanged silently. Compare [Laskar–Petit, §2.1](https://arxiv.org/pdf/1703.07125) and [Pinzari, 2013, equations (1)–(3)](https://arxiv.org/pdf/1310.0181).

The symbol \(\mu\) in some astronomical AMD formulas denotes \(Gm_0\), not a small planetary mass ratio. Rename it during any source-to-Lean translation.

**AMD.** In our convention,
\[
\mathbf L=\sum_i q_i\times p_i,\qquad
C=\sum_i\Lambda_i-|\mathbf L|
=\sum_i\Lambda_i\left(1-\sqrt{1-e_i^2}\cos i_i\right).
\tag{9}
\]
The inclinations \(i_i\) are relative to the invariable plane perpendicular to nonzero total angular momentum. They are not sky-plane inclinations or the pairwise mutual inclinations themselves. The vector formula is preferable as the fundamental definition.

Physical AMD is \(\mu C\), and physical circular angular momenta are \(\mu\Lambda_i\). A fixed normalized margin \(\delta\) means physical margin \(\mu\delta\). Relative AMD, such as \(C/\Lambda_j\) or \(C/\sum_i\Lambda_i\), is a different normalization and must be named.

AMD is exactly conserved when both the \(\Lambda_i\) and angular momentum are conserved, as in the secular model. For the full system, (1) is the useful identity. Conservation in an all-orders *formal* secular normal form does not establish convergence of an infinite averaging transformation or infinite-time conservation of physical AMD.

**The pair collision threshold.** Set \(D(e)=1-\sqrt{1-e^2}\). For \(a_i<a_j\), define
\[
\begin{aligned}
\mathcal C_{ij}(\Lambda)
=\min\{&\Lambda_iD(u)+\Lambda_jD(v):\\
&0\le u,v\le1,\quad a_i(1+u)\ge a_j(1-v)\}.
\end{aligned}
\tag{10}
\]
Here \(a_k=(\Lambda_k/\nu_k)^2\). Including endpoints makes the minimizing set compact. The minimum occurs at radial contact, with equality in the constraint. It is the least eccentricity AMD capable of making inner aphelion reach outer perihelion. Coplanar, suitably oriented ellipses realize the limiting geometry; inclination cannot lower the necessary budget.

Writing \(\alpha=a_i/a_j\), \(\gamma_m=\nu_i/\nu_j\), the normalized Laskar–Petit expression is
\[
\frac{\mathcal C_{ij}}{\Lambda_j}
=\min_{\substack{0\le u,v\le1\\\alpha(1+u)\ge1-v}}
\left[\gamma_m\sqrt\alpha\,D(u)+D(v)\right].
\tag{11}
\]
This specifies the factor multiplying the relative threshold. A compact-minimum definition suffices for the barrier theorem; an equation for the optimizer is optional.

Here is the elementary argument independently. Since \(\cos i_k\le1\),
\[
C\ge\sum_k\Lambda_kD(e_k)
\ge\Lambda_iD(e_i)+\Lambda_jD(e_j).
\tag{12}
\]
If the radial annuli overlap, the actual eccentricities are feasible in (10), so \(C\ge\mathcal C_{ij}\). Take the contrapositive.

**A whole-system threshold.** For ordered semimajor axes, use
\[
\mathcal C_{\rm cross}(\Lambda)
=\min_{1\le i<n}\mathcal C_{i,i+1}(\Lambda).
\tag{13}
\]
Compare the **entire system’s** AMD with each adjacent-pair threshold. Comparing only the AMD currently carried by a pair is inadequate when secular interactions transfer AMD from other planets. Checking all adjacent radial gaps orders every annulus and separates every pair. Protecting one specified pair is a different conclusion from protecting the system.

The criterion is sufficient, not necessary, for geometric nonintersection. Radial intervals may overlap while the actual inclined or apsidally oriented ellipses remain disjoint. Above threshold there is no automatic instability theorem.

**The star threshold.** Since \(D(1)=1\), the least eccentricity AMD permitting the \(i\)-th Kepler orbit to become radial is \(\Lambda_i\). Define
\[
\mathcal C_\star(\Lambda)=\min_i\Lambda_i,\qquad
\mathcal B(\Lambda)=\min\{\mathcal C_{\rm cross}(\Lambda),
                              \mathcal C_\star(\Lambda)\}.
\tag{14}
\]
Under the pair condition, only the innermost planet needs an additional star test: for \(j>1\), taking \(u=0\), \(v=1-a_{j-1}/a_j\) in (10) gives \(\mathcal C_{j-1,j}<\Lambda_j\). Thus \(\mathcal B=\min(\mathcal C_{\rm cross},\Lambda_1)\). Formula (14) is convenient for proofs.

For a finite-radius star, prevent \(a_i(1-e_i)\le R_\star\), not merely \(e_i=1\). Equation (7) describes point masses.

**“No orbit crossing.”** Distinguish:

1. Canonical instantaneous Kepler ellipses have disjoint radial annuli:
   \[
   a_i(t)(1+e_i(t))<a_{i+1}(t)(1-e_{i+1}(t)).
   \tag{15}
   \]
2. Genuinely osculating heliocentric ellipses, tangent to actual relative velocities, have disjoint radial annuli.
3. Actual interplanetary distances stay positive, preferably uniformly bounded below.

Conclusion 1 directly implies 3: each current position lies on its canonical ellipse even when the ellipse is not tangent to actual motion, and
\[
|q_j-q_i|\ge\big||q_j|-|q_i|\big|.
\tag{16}
\]
Conclusion 2 needs a comparison. In convention (7),
\[
\dot q_i=\frac{p_i}{\nu_i}+\mu\sum_jp_j.
\tag{17}
\]
Canonical elements therefore differ from ordinary velocity-osculating heliocentric elements. The latter may also use gravitational parameter \(1+\mu\nu_i\). On a compact elliptic region away from radial orbits, semimajor axes and eccentricity vectors differ by \(O(\mu)\), uniformly. A fixed positive annulus margin absorbs this error after reducing \(\mu_0\). The map and its estimate belong in the proof. Jacobi elements need their own bridge.

Actual collision avoidance is weaker than noncrossing of instantaneous ellipses. Resonant phase protection can prevent collisions when osculating ellipses cross. Our candidate establishes radial ordering in a nonresonant regime.

**Quantitative nonresonance.** A useful hypothesis is
\[
|k\cdot\omega(\Lambda^0)|
\ge\gamma_D |k|_1^{-\tau}
\quad(k\in\mathbb Z^n\setminus\{0\}),\qquad
\gamma_D>0,\quad\tau>n-1.
\tag{18}
\]
The constants precede \(\mu\) in a uniform asymptotic theorem. For fixed \(\tau>n-1\), the union over \(\gamma_D>0\) has full measure; a fixed \(\gamma_D\) is a quantitative restriction.

Pairwise irrational period ratios do not suffice. Frequencies \((1+\sqrt2,\sqrt2,1)\) have irrational pairwise ratios but obey \(\omega_1-\omega_2-\omega_3=0\). Multiplanet resonances matter. Mere rational independence of the full vector gives no power-law control of small divisors: Liouville vectors obstruct that arithmetic inference.

Only a finite cutoff \(K=K(\mu)\) is needed. An alternative is
\[
|k\cdot\omega(\Lambda^0)|\ge\alpha_K
\quad(0<|k|_1\le K),
\tag{19}
\]
with explicit relations between \(\alpha_K,K,\mu\), and domain width. Excluding a fixed list of low-order resonances does not by itself justify a cutoff tending to infinity.

**Where the proposed exponent can come from.** This is a sufficient scaling calculation reconstructed here, not an attribution of the AMD theorem to a source. Let \(M_2\) bound the derivative of \(\omega\), and \(\varepsilon=\mu M_f\), with \(M_f\) an analytic perturbation bound. To preserve (19) in an action tube of radius \(r\), require
\[
M_2Kr\lesssim\alpha_K.
\tag{20}
\]
A standard analytic averaging smallness condition, absorbing fixed angular and secular complex widths into constants, is
\[
\frac{\varepsilon K}{\alpha_K r}\lesssim1.
\tag{21}
\]
Under (18), set \(\alpha_K=\gamma_DK^{-\tau}\). Combining gives
\[
\varepsilon M_2K^{2\tau+2}\lesssim\gamma_D^2,\qquad
K\asymp\left(\frac{\gamma_D^2}{\varepsilon M_2}\right)^{1/(2\tau+2)},
\qquad r\asymp\sqrt\varepsilon,
\tag{22}
\]
with comparison constants depending on fixed geometry and widths. Exponential Fourier tails then suggest
\[
|t|\le T_0\exp\!\left(c\mu^{-1/[2(\tau+1)]}\right),\qquad
\|\Lambda(t)-\Lambda(0)\|_\infty\le A\sqrt\mu.
\tag{23}
\]

The action-angle inequalities can be checked in Pöschel’s normal form as reproduced in [Barbieri–Marco–Massetti, Appendix B, especially (B.1)–(B.2)](https://link.springer.com/article/10.1007/s00220-022-04464-0). Secular canonical pairs add Poisson-bracket estimates and a domain obligation; they need not change the power in (22) when their widths are fixed. For related estimates with extra pairs, see [Pinzari–Liu, §3.4](https://link.springer.com/article/10.1007/s00332-023-09948-4). Neither citation alone verifies our full specialization.

In particular,
\[
\tau=n-\tfrac12
\quad\Longrightarrow\quad
\frac1{2(\tau+1)}=\frac1{2n+1}.
\tag{24}
\]
This is an admissible Diophantine exponent. More generally \(\tau=n-1+\eta\) gives \(1/(2n+2\eta)\). If only a bound with \(\tau=n\) is assumed, this argument gives \(1/(2n+2)\), not \(1/(2n+1)\). A stronger arithmetic bound might hold, but does not follow from the weaker one.

For a merely nonresonant vector define \(\Psi_\omega(K)=\max_{0<|k|_1\le K}|k\cdot\omega|^{-1}\). This construction is governed by \(\mu K^2\Psi_\omega(K)^2\lesssim1\), without a universal stretched-exponential power. This is a limitation of the inference, not a proof that every Liouville planetary system is unstable.

Partial-convexity Nekhoroshev theory is another possible route. The Kepler Hamiltonian has negative-definite Hessian in its \(n\) fast actions but is flat in secular directions. A full convex or steep theorem must be specialized through an appropriate *degenerate* result. One cannot insert \(n\), \(3n\), or \(3n-2\) into a generic exponent by inspection. The nonresonant route avoids this ambiguity and needs no secular steepness. No optimality claim for (24) is justified.

**3. Hidden hypotheses and attempted failure modes.**

**Margins and quantifiers.** A fixed initial architecture strictly below threshold has a positive gap. Thus “any AMD below threshold” can mean: for each such gap, there are sufficiently small masses and suitable time constants. It cannot silently mean that one mass threshold and exponential constant work uniformly as the gap tends to zero. A clean hypothesis is
\[
C(0)\le\mathcal B(\Lambda(0))-\delta,\qquad
\delta>0\text{ fixed before }\mu.
\tag{25}
\]
Both coordinate error and action drift must fit inside \(\delta\). If the gap shrinks with \(\mu\), recalculate complex widths, perturbation norms, and times. I have not constructed a full Newtonian counterexample to every no-margin interpretation; the justified criticism is the lack of stated support for a uniform conclusion.

**The threshold moves.** Bounding \(|C(t)-C(0)|\) alone is insufficient. Control \(|\mathcal B(\Lambda(t))-\mathcal B(\Lambda(0))|\) too. Continuity suffices existentially; a Lipschitz modulus is useful quantitatively.

**Pair AMD stability does not exclude the star.** Take \(a_1/a_2=0.1\), \(\Lambda_1=0.01\), \(\Lambda_2=1\). Pair contact requires \(e_2\ge0.8\), since \(e_1\le1\). Thus \(\mathcal C_{12}\ge1-\sqrt{1-0.8^2}=0.4\). AMD \(0.02\) is below this but above inner star threshold \(0.01\). Allowed configurations can approach \(e_1=1\). This proves insufficiency of the budget for excluding the star, not an exact collisional trajectory. The weak/strong distinction is explicit in [Laskar–Petit, §5.3](https://arxiv.org/pdf/1703.07125).

**Large eccentricity is not intrinsically fatal; uniformity near one is.** On any fixed safe compact region with \(e_i\le e_*<1\), the exact Kepler map has a complex analytic neighborhood. Small-eccentricity expansions are not conceptually required. Constants deteriorate as \(e_*\to1\), perihelia vanish, or annuli approach contact. An existential theorem can allow high eccentricities with geometry-dependent constants; it should not promise realistic masses or uniformity up to \(e=1\).

**Inclinations consume AMD.** Ignoring inclination underestimates excitation. Conversely (12) works in space without a small-inclination expansion. Strong AMD nevertheless constrains inclinations: \(C<\min_i\Lambda_i\) forces each orbit’s angular momentum to have positive projection on \(\mathbf L\). “No extra small-inclination hypothesis” does not mean arbitrary retrograde configurations qualify. Circular and coplanar configurations also require regular coordinates, since classical orbital angles are singular there.

**Proper degeneracy is real.** The full Keplerian Hessian has zero secular directions. Repairing this by proving a steep secular Birkhoff form changes the project and can introduce exactly the secular hypotheses the proposal avoids. Fast-angle averaging with a bounded secular domain is the alternative.

**Later resonances require a finite-order argument.** An all-orders Diophantine set has no open action neighborhood. For \(|k|_1\le K\), however,
\[
|k\cdot\omega(\Lambda(t))|
\ge\gamma_DK^{-\tau}
-M_2K\|\Lambda(t)-\Lambda(0)\|_\infty.
\tag{26}
\]
A sufficiently narrow tube preserves the divisors used. Higher-order resonances are covered by the small remainder. Do not assume all-orders nonresonance at every later time. Secular resonances are allowed: they are not divisors inverted in fast-angle averaging.

**The architecture must be fixed in the limit.** Uniform constants require bounded positive semimajor axes, distinct ordering, and fixed positive relative masses. If spacings shrink with \(\mu\), perturbations near conjunction may cease to be uniformly small. If outer semimajor axes diverge, fast frequencies and other constants deteriorate. “Small planetary masses” does not control these competing limits.

**Two literature stress tests.** Resonant AMD extensions address the failure of unrestricted secular averaging near mean-motion resonances. Clarke–Féjoz–Guardia construct polynomial-time semimajor-axis instability in a hierarchical four-body regime. That does not refute our fixed-geometry, quantitatively nonresonant, strong-AMD candidate; it does rule out unrestricted semimajor-axis stability slogans. [Petit–Laskar–Boué, 2017](https://www.aanda.org/articles/aa/pdf/2017/11/aa31196-17.pdf); [Clarke–Féjoz–Guardia, especially §1.3](https://arxiv.org/abs/2303.05979).

**Permitting chaos is not proving chaos.** Absence of a regularity hypothesis does not establish a chaotic trajectory in the admitted region. Positive entropy, a horseshoe, or positive Lyapunov exponents would be an additional result. The reduced planar two-planet secular problem has one degree of freedom and is integrable. A pilot in that setting would not demonstrate secular chaos; planar three-planet or spatial two-planet dynamics is more relevant.

**No crossing is not a complete stability classification.** The theorem does not predict ephemerides, establish infinite-time confinement, or describe behavior after its time horizon. The stronger candidate below also prevents escape on its interval through compact elliptic bounds. State these conclusions explicitly instead of hiding them in “stable.”


**4. Literature and the likely novelty boundary.**

These references have different logical roles. None substitutes for matching its hypotheses to the exact domain. The descriptions distinguish established results from models, heuristics, and the proposed application.

| Reference | Contribution and limitation |
|---|---|
| **J. Laskar, “On the Spacing of Planetary Systems,” Phys. Rev. Lett. 84, 3240–3243 (2000).** [Publisher](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.84.3240) | Early AMD-stability and accretion-model formulation. Prior art for the safety principle, not the requested quantitative unaveraged theorem. |
| **J. Laskar and A. C. Petit, “AMD-stability and the classification of planetary systems,” A&A 605, A72 (2017).** [Published version](https://doi.org/10.1051/0004-6361/201630022), [preprint](https://arxiv.org/abs/1703.07125) | Central source for threshold geometry and formal secular conservation. Published §3 labels the nonresonant practical-stability extension conjectural. The March preprint and published wording are not identical. |
| **A. C. Petit, J. Laskar and G. Boué, “AMD-stability in the presence of first-order mean motion resonances,” A&A 607, A35 (2017).** [Paper](https://www.aanda.org/articles/aa/pdf/2017/11/aa31196-17.pdf) | A first-order resonance-overlap extension, relevant to compact systems. It is not a rigorous general \(n\)-planet exponential-time theorem. |
| **A. C. Petit, J. Laskar and G. Boué, “Hill stability in the AMD framework,” A&A 617, A93 (2018).** [Preprint](https://arxiv.org/abs/1806.08869) | Relates two-planet Hill stability to AMD, energy, and masses, building on Marchal–Bozis. Exact-integral Hill criteria give a different nonencounter conclusion and need not exclude ejection or stellar collision. Distinguish exact inequalities from their small-mass expansions. |
| **L. Niederman, “Stability over exponentially long times in the planetary problem,” Nonlinearity 9, 1703–1751 (1996).** [DOI](https://doi.org/10.1088/0951-7715/9/6/017) | Foundational planetary fast-action stability in a properly degenerate setting. I could not inspect the complete original theorem through available publisher access; this report does not verify its exact exponents or maximal domain. The bounded-secular-domain mechanism and near-circular planetary application are described in the later research papers below. |
| **S. Barbieri and L. Niederman, “Sharp Nekhoroshev estimates for the three-body problem around periodic orbits,” Journal of Differential Equations 268(7), 3749–3780 (2020), preprint 2018.** [Full preprint](https://arxiv.org/abs/1810.05987); [DOI](https://doi.org/10.1016/j.jde.2019.10.013) | Rigorous local planetary/restricted three-body stability using periodic averaging. §3.3.2 bounds secular Cartesian variables through angular momentum; §3.3.3 explicitly states locality around a periodic torus. Useful for the bootstrap, but not a theorem for every AMD-safe \(n\)-planet configuration. |
| **J. Pöschel, “Nekhoroshev estimates for quasi-convex Hamiltonian systems,” Math. Z. 213, 187–216 (1993).** [DOI](https://doi.org/10.1007/BF03025718) | Quantitative normal-form and confinement machinery. Its nonresonant normal-form component is especially relevant. Applying full quasi-convexity directly to all planetary actions ignores proper degeneracy. |
| **S. Barbieri, J.-P. Marco and J. E. Massetti, “Analytic Smoothing and Nekhoroshev Estimates for Hölder Steep Hamiltonians,” Comm. Math. Phys. 396, 349–381 (2022).** [Open article](https://link.springer.com/article/10.1007/s00220-022-04464-0) | Appendix B gives an accessible quantitative Pöschel normal form. The Hölder theorem itself is not needed here. |
| **M. Guzzo, L. Chierchia and G. Benettin, “The Steep Nekhoroshev’s Theorem,” Comm. Math. Phys. 342, 569–601 (2016).** [DOI](https://doi.org/10.1007/s00220-015-2555-x), [institutional record](https://www.research.unipd.it/handle/11577/3187109) | Constructive steep Nekhoroshev theory with exponents depending on dimension and steepness indices. It does not make the unreduced degenerate Kepler Hamiltonian steep. |
| **M. Guzzo, “The Nekhoroshev theorem and long-term stabilities in the Solar System,” Serbian Astronomical Journal 190, 1–10 (2015).** [Review](https://doiserbia.nb.rs/img/doi/1450-698X/2015/1450-698X1590001G.pdf) | Context on effective stability and stable chaos. A guide to the literature, not a proof of this AMD proposition. |
| **J. Féjoz, “Démonstration du ‘théorème d’Arnold’ sur la stabilité du système planétaire (d’après Herman),” ETDS 24, 1521–1582 (2004).** [DOI](https://doi.org/10.1017/S0143385704000410); **“On ‘Arnold’s theorem’ on the stability of the solar system” (2013).** [Author’s comparison](https://www.aimsciences.org/article/doi/10.3934/dcds.2013.33.3555) | Planetary KAM establishes positive-measure quasiperiodic families with the required treatment of degeneracy. This is an all-time existence result for selected initial data, not finite-time safety for every point in an AMD sublevel. |
| **L. Chierchia and G. Pinzari, “The planetary \(N\)-body problem: Symplectic foliation, reductions and invariant tori,” Invent. Math. 186, 1–77 (2011).** [DOI](https://doi.org/10.1007/s00222-011-0313-z); **“Planetary Birkhoff normal forms,” J. Mod. Dyn. 5, 623–664 (2011).** [Article](https://www.aimsciences.org/article/doi/10.3934/jmd.2011.5.623) | Symmetries, reduction, torsion, and secular Birkhoff forms. These are central for KAM and secular-action stability. Our fast-action barrier route should not import their stronger secular-normal-form obligations unnecessarily. |
| **G. Pinzari, “Aspects of the planetary Birkhoff normal form,” Regular and Chaotic Dynamics 18, 860–906 (2013).** [Full preprint](https://arxiv.org/abs/1310.0181) | Theorem B / Theorem 4.1 gives exponential stability of all planetary actions for the planar three-body problem on a small-eccentricity domain with separation and finite-order mean-motion exclusions. The text discusses obstacles to spatial steepness. It is not the arbitrary-AMD theorem here. |
| **G. Pinzari, “Perihelia reduction and global Kolmogorov tori in the planetary problem,” Memoirs AMS 255, no. 1218 (2018).** [Preprint](https://arxiv.org/abs/1501.04470) | Extends planetary KAM beyond nearly circular, nearly coplanar regimes under its own hypotheses. It constructs quasiperiodic families, not protection of every AMD-safe trajectory. |
| **G. Pinzari and X. Liu, “Quantitative KAM Theory, with an Application to the Three-Body Problem,” J. Nonlinear Science 33, 90 (2023).** [Open article](https://link.springer.com/article/10.1007/s00332-023-09948-4) | §3.4 contains normal forms with extra canonical pairs and independently controlled analytic widths. Useful technology to examine, not a ready-made AMD theorem. |
| **P. Robutel, L. Niederman and A. Pousse, “Rigorous treatment of the averaging process for co-orbital motions in the planetary problem,” Computational and Applied Mathematics 35, 675–699 (2016).** [Full preprint](https://arxiv.org/abs/1506.02870) | Rigorous averaging with collision-distance-dependent domains. Illustrates why analyticity estimates are substantive; its resonant three-body setting differs from the fully nonresonant \(n\)-planet problem. |
| **L. Niederman, A. Pousse and P. Robutel, “On the co-orbital motion in the three-body problem: existence of quasi-periodic horseshoe-shaped orbits” (2020 version).** [Paper](https://arxiv.org/abs/1806.07262) | Rigorous quasiperiodic co-orbital motion shows that resonance can protect orbits. Nonresonance is sufficient for our chosen mechanism, not necessary for planetary safety. |
| **T. Castan, “Stability in the plane planetary three-body problem,” doctoral thesis (2017).** [Institutional PDF](https://www.imcce.fr/content/medias/publications/publications-recherche/theses-habilitations/docs/Castan_These.pdf), [HAL](https://theses.hal.science/tel-01597143) | Detailed complex Kepler-equation and disturbing-function estimates followed by quantitative KAM. Particularly relevant to analytic domains. Its very small sufficient mass ratios concern that construction, not a universal obstruction or this candidate’s mass threshold. |
| **A. Clarke, J. Féjoz and M. Guardia, “A counterexample to the theorem of Laplace–Lagrange on the stability of semimajor axes,” Arch. Rational Mech. Anal. 248, article 19 (2024).** [Paper](https://arxiv.org/abs/2303.05979), [DOI](https://doi.org/10.1007/s00205-024-01960-6) | Large semimajor-axis changes in polynomial time in a hierarchical four-body regime. §1.3 explains the failure of confinement/convexity hypotheses behind unrestricted use of Niederman’s method. A mandatory stress test, not a counterexample to the repaired candidate. |
| **A. Yalinewich and C. Petrovich, “Nekhoroshev Estimates for the Survival Time of Tightly Packed Planetary Systems,” ApJ Letters (2020).** [Preprint](https://arxiv.org/abs/1907.06660) | A heuristic, numerically compared survival-time scaling motivated by Nekhoroshev theory. Not the rigorous exponential-time lower bound sought here. |

**Novelty assessment.** Collision geometry is known. The distinction between chaotic motion and slow diffusion is established Hamiltonian theory. Exponential fast-action stability in planetary and properly degenerate settings has substantial prior art. The potentially useful contribution is a clean theorem assembling these ingredients with an explicit AMD margin, complete quantifiers, and a physical conclusion, perhaps on a larger safe region than older near-circular applications. Whether that corollary has already been stated, or is immediately contained in a version of Niederman’s theorem, requires checking the original theorem in full. I would call this **an established principle with a plausible rigorous quantitative formulation; novelty unverified**, rather than either “new theorem” or “already proved exactly as written.”

**5. Candidate statements with explicit quantifiers and dependence.**

Separate an elementary deterministic theorem from the analytic stability theorem. This makes a useful formalization possible before exponential averaging is available.

**Candidate A: robust AMD barrier under a supplied action bound.** Fix \(n\ge2\), positive relative masses \(\nu\), an initial ordered action vector \(\Lambda^0\), \(C_0\ge0\), and \(r>0\). Assume the closed box
\[
Q_r=\{\Lambda:\|\Lambda-\Lambda^0\|_\infty\le r\}
\tag{27}
\]
has positive actions and strictly ordered semimajor axes, and
\[
\Delta_r:=\min_{\Lambda\in Q_r}\mathcal B(\Lambda)-C_0-nr>0.
\tag{28}
\]
Then every elliptic canonical configuration with these masses, total angular-momentum magnitude \(\sum_i\Lambda_i^0-C_0\), and actions in \(Q_r\), has positive perihelia and disjoint adjacent radial annuli. On this entire set there are positive lower bounds for perihelia and annulus gaps depending only on \((n,\nu,\Lambda^0,C_0,r)\). Every exact Newtonian trajectory whose actions remain in \(Q_r\) has these properties throughout its interval of existence. If the action bound is supplied up to a first exit, the separation bounds provide continuation through any proposed finite endpoint.

Once the orbital identities are established, the proof uses (1), (10)–(16), and compactness:
\[
C(t)\le C_0+nr
<\min_{Q_r}\mathcal B
\le\mathcal B(\Lambda(t)).
\tag{29}
\]
For the star, \(C\le\Lambda_i-\Delta_r\) implies
\[
\sqrt{1-e_i^2}\ge\frac{\Delta_r}{\Lambda_i}.
\tag{30}
\]
Positive bounded actions then prevent radial degeneration and bound momenta and positions. Together with pair separation, the Newtonian vector field remains on a compact nonsingular set. This is a continuation argument, not an assumption of global existence.

Replacing \(\mathcal B\) by \(\mathcal C_{\rm cross}\) gives only the pair barrier on the elliptic nonsingular interval; the same unconditional continuation needs a separate stellar-distance bound.

**Candidate B: nonresonant exponential-time safety for the exact spatial planetary problem.** This is the theorem I believe plausible and recommend proving on paper before freezing a Lean signature. **This report does not claim to prove it.**

Choose units \(G=m_0=1\). For every:

- integer \(n\ge2\);
- vector \(\nu\in(0,1]^n\) with \(\max_i\nu_i=1\);
- nonempty compact \(\mathcal A\subset\{a\in\mathbb R^n:0<a_1<\cdots<a_n\}\);
- Diophantine parameters \(\gamma_D>0\), \(\tau>n-1\);
- margin \(0<\delta<\min_{a\in\mathcal A}\mathcal B(\Lambda(a))\),

there exist
\[
\mu_0>0,\quad A_\Lambda>0,\quad A_a>0,\quad
c>0,\quad T_0>0,\quad d_\star>0,\quad d_{\rm pair}>0
\tag{31}
\]
depending **only** on \((n,\nu,\mathcal A,\delta,\gamma_D,\tau)\), with the following property.

For every \(0<\mu\le\mu_0\), and every initial state of exact Hamiltonian (7) whose canonical Kepler elements are elliptic and satisfy
\[
\begin{gathered}
a(0)\in\mathcal A,\qquad
|k\cdot\omega(\Lambda(0))|\ge\gamma_D|k|_1^{-\tau}
\quad(k\in\mathbb Z^n\setminus\{0\}),\\
C(0)\le\mathcal B(\Lambda(0))-\delta,
\end{gathered}
\tag{32}
\]
the unique maximal Newtonian solution is defined at least on \([-T_\mu,T_\mu]\), where
\[
T_\mu=T_0\exp\!\left(c\mu^{-1/[2(\tau+1)]}\right).
\tag{33}
\]
For every \(|t|\le T_\mu\), it remains elliptic, the semimajor axes keep their ordering, and
\[
\begin{gathered}
\|\Lambda(t)-\Lambda(0)\|_\infty\le A_\Lambda\sqrt\mu,\qquad
\|a(t)-a(0)\|_\infty\le A_a\sqrt\mu,\\
|C(t)-C(0)|\le nA_\Lambda\sqrt\mu,\qquad
C(t)\le\mathcal B(\Lambda(t))-\delta/2,\\
a_i(t)(1-e_i(t))\ge d_\star\quad(1\le i\le n),\\
a_{i+1}(t)(1-e_{i+1}(t))-a_i(t)(1+e_i(t))
\ge d_{\rm pair}\quad(1\le i<n).
\end{gathered}
\tag{34}
\]
Actual star–planet distances are at least \(d_\star\); actual planet–planet distances are at least \(d_{\rm pair}\). There are **no additional hypotheses on secular frequencies, secular integrability, secular steepness, or Lyapunov exponents**. Constants are uniform over all initial fast phases and all eccentricity, inclination, and orientation data satisfying (32).

For the requested exponent, specialize to \(\tau=n-\tfrac12\). A pointwise statement for any fixed admissible AMD follows by choosing a positive \(\delta\) below its strong-threshold gap; the constants depend on that choice. The \(\sqrt\mu\) action radius is a plausible output of route (22), not a claim about every planetary Nekhoroshev theorem.

**Making the dependence operational.** Let \(\mathcal L=\{\Lambda(a):a\in\mathcal A\}\). Choose a compact neighborhood \(U\) of \(\mathcal L\) inside the positive ordered action chamber, small enough that \(\min_U\mathcal B>\delta\). Define
\[
\Omega_B(r)=\sup\{|\mathcal B(\Lambda)-\mathcal B(\Lambda')|:
\Lambda,\Lambda'\in U,\ \|\Lambda-\Lambda'\|_\infty\le r\}.
\tag{35}
\]
Choose \(r_\delta>0\), smaller than the distance from \(\mathcal L\) to the boundary of \(U\), such that
\[
nr_\delta+\Omega_B(r_\delta)\le\delta/2.
\tag{36}
\]
Continuity supplies this radius. If a Lipschitz constant \(L_B\) is proved, \(r_\delta\le\delta/[2(n+L_B)]\) suffices together with the boundary condition.

Build the analytic domain using a weaker margin, such as \(\delta/4\), to leave room for the normal-form maps. The action width, angular strip, secular complex width, perturbation norm, and coordinate bounds depend on \((n,\nu,\mathcal A,\delta)\). Apply the normal-form lemma with \((\gamma_D,\tau)\). Reduce its mass threshold to ensure
\[
A_\Lambda\sqrt{\mu_0}<r_\delta.
\tag{37}
\]
If the construction gives threshold \(\mu_{\rm NF}\), an appropriately strict choice satisfies
\[
\mu_0\le\min\{\mu_{\rm NF},\ (r_\delta/(2A_\Lambda))^2,\ 1\}.
\tag{38}
\]
The annulus constant is the minimum radial gap over the compact set of actions in \(U\) and eccentricities in \([0,1]^n\) satisfying
\[
\sum_i\Lambda_iD(e_i)\le\mathcal B(\Lambda)-\delta/2.
\tag{39}
\]
Every gap is positive by (10), hence so is the compact minimum. If \(\Lambda_i\le\Lambda_{\max}\) and \(a_i\ge a_{\min}>0\) on \(U\), the perihelia satisfy the explicit bound
\[
a_i(1-e_i)\ge
a_{\min}\left(1-\sqrt{1-(\delta/(2\Lambda_{\max}))^2}\right)
\ge\frac{a_{\min}\delta^2}{8\Lambda_{\max}^2}.
\tag{40}
\]
One may choose the rightmost expression as \(d_\star\).

These formulas specify dependencies and the error budget, not numerical values for analytic normal-form constants. Numerical constants are another task if the theorem is to apply at particular astronomical masses. Restoring physical units also restores a fixed reference time multiplying (33); the mass ratio \(\mu\) is dimensionless.

A final corollary can use velocity-osculating heliocentric ellipses. Prove a uniform \(A_{\rm osc}\mu\) bound on changes in perihelion and aphelion radii over the safe compact set. Require, for example, \(2A_{\rm osc}\mu_0<d_{\rm pair}/2\) and the analogous stellar inequality. Osculating gaps then retain half the canonical bounds. \(A_{\rm osc}\) depends only on the same fixed data. A separate corollary prevents a coordinate convention from disappearing inside the theorem’s name.

**Other variants worth considering.**

| Variant | Benefit and limitation |
|---|---|
| Exact secular theorem | Fixed \(\Lambda\), conserved angular momentum, and \(C<\mathcal B\) give permanent safety for a complete secular flow, whatever its detailed dynamics. Clear small formalization; not unaveraged dynamics. |
| Deterministic Candidate A | Reusable interface for analytic or computer-assisted action bounds. Keep that bound as a visible hypothesis. |
| Finite-order averaging | Once a controlled normal form supplies an \(O(\mu^{N+1})\) fast-action derivative and \(O(\mu)\) coordinate errors, it yields \(O(\mu^{-N})\) time with \(O(\mu)\) drift, subject to its domain conditions. Constants depend on fixed order \(N\), geometry, and arithmetic. A useful intermediate target. |
| Finite-cutoff exponential statement | State (19)–(21), a margin, and a time proportional to \(\exp(cK)\). Exposes numerical hypotheses without prematurely freezing a Diophantine exponent. |
| Weak AMD stability | Protect pairs until first exit from a specified star-safe elliptic domain. Closer to the literal pair threshold, but conditional in time. |
| Near-circular, nearly coplanar theorem | Easier domains and closer comparison with older stability results. Sacrifices breadth but may be the first unaveraged target. |
| Resonance-tolerant fast-action theorem | Appropriate partial-convexity/periodic-averaging theorem plus AMD. Potentially admits some mean-motion resonances; substantially more geometric work. |
| Two-planet Hill theorem | Exact energy and angular momentum can yield an infinite-time nonencounter result of a different kind. Not a replacement for the general no-crossing statement. |
| KAM or superexponential-near-torus theorem | Longer or infinite times for restricted initial data with additional hypotheses; different scope. |
| Existence of chaotic but safe motion | Add a rigorously constructed chaotic invariant set inside the safety domain. Neither theorem automatically supplies the other. |

**6. Verdict as a Lean formalization target.**

**A good research direction, but the current sentence is not a safe frozen target.** The attractive feature is modularity: fast-action stability is analytic; AMD is a geometric barrier; exact angular momentum connects them. Each stage is useful mathematics. The last analytic stage is a substantial undertaking, not a short invocation of “KAM” or of convex Hamiltonian stability.

I would use the following order, with honest intermediate endpoints:

1. **Freeze the physical and coordinate definitions.** Newtonian equations, translation reduction, mass scaling, canonical elements, exact angular momentum, identities (8)–(9), and distinction (17).
2. **Formalize the geometric barrier.** Define the threshold by a compact minimum, prove (12)–(16), distinguish pair from system, and add the star threshold. This is independently valuable.
3. **Prove Candidate A.** Include threshold continuity/moduli and ODE continuation. This does not yet prove an exponential-time result.
4. **Prove quantitative analytic averaging.** Start with a finite cutoff and explicit domain loss, coordinate displacement, inverse map, and remainder. Allow evolving secular pairs; do not assume their confinement in a way that already implies the conclusion.
5. **Specialize the analytic domain to the planetary problem.** Use the safe secular region to control the complex Kepler map and every Newtonian denominator, for all permitted phases.
6. **Optimize the cutoff and close the bootstrap.** Derive the exponent from inequalities and attach the result to the exact Newtonian solution. Prove the osculating corollary separately.

The hardest parts are likely:

- **Analytic infrastructure:** several-complex-variable domains, Fourier norms and tails, Cauchy estimates, Poisson brackets, generating-function flows, and quantitative composition/inverse estimates. Formal normal-form algebra without controlled remainders is insufficient.
- **The Kepler map:** symplecticity, regularity at circular/coplanar configurations, complex inversion of Kepler’s equation, and the singular set. These are major celestial-mechanics ingredients.
- **Uniform domain control:** room for the secular trajectory to explore its permitted AMD region while both coordinate transformations stay valid. Here an unconditional theorem can accidentally become conditional on stability.
- **Quantifiers and interpretation:** constants must precede \(\mu\) and initial data; ratios and spacings cannot vary silently; thresholds move with actions; the exported theorem must concern actual Newtonian solutions and a specified crossing notion.

The constrained optimization defining \(\mathcal C_{ij}\) is not the dominant obstacle. A closed formula for its optimizer is unnecessary for the first theorem. Full planetary KAM, a high-order secular Birkhoff form, and general steep Nekhoroshev theory could add enormous cost without being needed for the nonresonant route. This report makes no claim about which infrastructure already exists in any Lean repository.

Before a large campaign, the most valuable paper-level deliverable is a complete proof of Candidate B using one exact normal-form lemma, with secular-domain assumptions discharged and all coordinate changes included. The first unresolved analytic obligation here is **a uniform exponential fast-angle normal form on the entire enlarged strong-AMD sublevel, with the bounds needed by the first-exit argument**. References make this plausible; citing them has not discharged it.

I recommend proceeding with the robust barrier and a finite-cutoff averaging interface while treating the full exponential planetary theorem as a candidate requiring that paper proof. A successful result would formalize a meaningful distinction between safety and dynamical regularity. Its wording alone would not establish new chaotic trajectories or certify stability at Solar-System mass ratios.

**Closeout and limits.** All six requested topics are addressed. The original proposal is preserved and repairs are explicit. This is not a counterexample to Candidate B, an optimal-exponent claim, a verified novelty result, a complete audit of Niederman’s original theorem, or a completed analytic proof. Searches covered the named authors, the AMD/exponential-stability combination, quantitative averaging, resonant variants, and semimajor-axis instability. Search coverage cannot prove absence from the literature. The input hash was recorded before analysis and verified unchanged at delivery.

