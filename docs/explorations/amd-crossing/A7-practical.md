> Source: `RESEARCH/PRACTICAL.md` in the exploration workspace `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`. Paths `_sources/…` refer to `RESEARCH/_sources/` in the workspace.
> Date: 2026-10-31.
> Independent analysis produced for the orchestrator; not audited. Copy lightly edited: co-author naming neutralized, internal labels made neutral, cross-references pointed to the appendix files.

# Practical applicability: constants, Solar System, targets and certificates

Assessment date: 2026-10-31. **A practical campaign is worth a bounded numerical pilot, but neither P-EXP-SAFE nor the proposed qualitative Candidate B currently certifies a real planetary system at its actual masses.** The highest-value first experiment is a two-planet published model with a large AMD margin. A finite-cutoff certificate is a better practical interface than attempting to prove an infinite Diophantine condition from observations.

Repository inspected read-only at `/root/code/KAM`, commit `f5625f197c621ccc8045e8392a07e23fe0cb10fc`; no build or code changes. Numerical screening below is ordinary floating-point calculation, explicitly not interval or Lean certification. Sources and scripts are retained under `_sources/`.

## 1. What existential constants leave unpaid

P-EXP-SAFE (`KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean:planetaryExponentialSafety`) gives \(\exists\mu_*,c,C>0\). The construction of the analytic tube and perturbation normalization uses compactness and gives no usable numerical \(\mu_*\). The proposed Candidate B has the same issue even though its normal-form engine already has explicit constants.

An explicit version must provide certified values for:

1. **Physical input and units:** star mass, G, length/time normalization, true masses or a bounded inclination-dependent family, a joint initial-state enclosure, included bodies and force model. If \(a_{ref}=1\), one time unit is \(\sqrt{a_{ref}^3/(GM_*)}\), not automatically one year.
2. **AMD geometry:** a lower bound for each compact pair minimum and stellar threshold, an upper bound on total spatial AMD, an initial margin δ, and a moving-threshold bound over the action tube. The masses/axes/eccentricities must come from one consistent fit or joint uncertainty model.
3. **Real and complex domain widths:** positive real periapse/pair gaps; uniform regular Kepler chart; action width r, physical slow width w, fast angle strip s; and nonvanishing complex Newtonian denominators with a fixed square-root branch.
4. **Norms:** the Fourier-weighted disturbing-function norm \(F\), the frequency Lipschitz constant L, and all chart/scaling constants. A value on the real orbit is not a complex norm on the whole enlarged secular set.
5. **Normal form and transfer:** cutoff K, finite divisor lower bound α, all slow-bracket/smallness inequalities, preimage bounds, and the actual fast-action error at the claimed time.
6. **Final budgets:** original AMD increase, threshold motion, ODE continuation, and the \(O(\mu)\) canonical-to-actual-osculating radial error. Unmodeled perturbations cannot be added over billions of years without a new estimate.

Castan's thesis [HAL tel-01597143](https://theses.hal.science/tel-01597143), Propositions 1.3 and 1.5 (printed pp.25,28), Proposition 1.8 (p.39), and Theorem 1.9 (p.40, (1.43)), gives an explicit-domain starting point. The current repository's `Planetary/Exponential/ComplexTube.lean:tube` is useful for qualitative closure but does not itself compute those widths.

## 2. A concrete explicit certificate target

Use the period-one conventions of `Nekhoroshev/Partial/Setting.lean:ExtNFHyp`, with \(p=q=2\), \(\varepsilon=\mu F\). Certify a central finite-cutoff lower bound
\[
 \alpha\le\min_{0<|j|_1\le K}|j\cdot\omega_c/(2\pi)|.
\]
For an initial parameter box, this must hold uniformly on that box, with action-tube variation handled separately. Sufficient inequalities are
\[
 KLr\le\alpha/2,\quad \mu F\le{\alpha r\over256K},\quad
 64\pi ksr\le w^2,\quad 2\pi Ks\ge6,                  \tag{P1}
\]
\[
 nr/2+\Omega_B(r/2)\le\delta/2,\quad
 T\le {sr\over5\mu F}\exp(2\pi Ks/6),                \tag{P2}
\]
plus the fixed action/slow collar, chart, inverse and osculating inequalities. Here \(k=n\) planar or \(2n\) spatial. `Partial/Nonresonant.lean:nonresonant` supplies the stopped drift \(r/2\); the AMD bootstrap removes the stop.

This yields a **finite-time actual-mass theorem without an infinite Diophantine hypothesis**. It is not a weakening disguised as a proof of the asymptotic exponent: it is a separate explicit instance of the same normal-form/AMD mechanism. Exact rational periods are commensurable at some high order, and every open frequency uncertainty box meets high-order resonance hyperplanes. Neither a decimal fit nor an observational interval can certify the proposed all-orders Diophantine premise. Finite K avoids that obstacle.

Optimize K,r,s,w and the available margin jointly. A first implementation may use (P1)–(P2) verbatim. If it fails by many orders of magnitude, improving the Fourier norm and retaining measured low-order structure is more useful than merely increasing arithmetic precision. A tailored iteration can later replace coarse uniform majorants, but needs a new soundness proof including all tails.

## 3. How small can hand bounds be?

There is **no universal numerical \(\mu_*\)** determined by n alone. As a deliberately transparent illustration, use the conservative proof-plan choice
\[
 K=\left({\gamma_1^2\over4096L F\mu}\right)^{1/[2(\tau+1)]},
 \qquad\log T={\pi sK\over6}.
\]
For dimensionless values \(s=0.02\), \(\gamma_1=0.01\), \(L=F=1\), and \(\log T=30\), this requires \(K\simeq2865\) and

| Fast dimension and arithmetic exponent | Mass bound from these choices alone |
|---|---:|
| n=2, \(\tau=1.5\) | \(\mu\lesssim1.27\times10^{-25}\) |
| n=3, \(\tau=2.5\) | \(\mu\lesssim1.54\times10^{-32}\) |

These are **illustrative arithmetic**, not estimates for any star and not universal upper limits on what better proofs can achieve. Extra collar conditions can shrink them further. Conversely, finite-cutoff direct divisors and optimized normalizations can improve greatly on this generic Diophantine formula. A few-Gyr target for a several-day inner orbit corresponds to a dimensionless logarithmic horizon of roughly 28–30, making the illustration relevant in scale. It explains why an asymptotic theorem plus standard hand majorants is unlikely to settle actual exoplanet masses around \(10^{-5}\)–\(10^{-4}\).

Verified historical comparisons:

| Work and exact locator | Numerical result | Scope and limitation |
|---|---|---|
| Barbieri–Niederman 2020, [DOI 10.1016/j.jde.2019.10.013](https://doi.org/10.1016/j.jde.2019.10.013); checked [arXiv:1810.05987v1](https://arxiv.org/abs/1810.05987v1), §5.1, Table1 pp.40–41 | At exact 5:2 central actions: \(\varepsilon=10^{-11.25}\), time \(5.75\times10^{10}\) yr, 18 iterations; at \(10^{-11}\), \(3.08\times10^7\) yr; at \(10^{-12}\), \(1.17\times10^{29}\) yr | Reduced-mass planar Sun–Jupiter–Saturn model; epsilon is their perturbation/mass scaling, not an automatically identical normalization to this campaign |
| Same source, Table3 p.41 | \(\varepsilon=10^{-14}\), initial action radius \(1.38\times10^{-6}\max\Lambda^0\), time \(1.99\times10^{10}\) yr; \(10^{-11.5}\), radius \(8.09\times10^{-7}\max\Lambda^0\), time \(1.04\times10^9\) yr | An open initial action neighborhood, not only the exact resonant actions; still far below actual Jupiter mass ratio |
| Same source, discussion p.41 | Attributes \(\sim4\times10^9\) yr for \(\varepsilon<10^{-13}\) to Niederman 1996, and \(\sim1.3\times10^{11}\) yr at that scale to Castan | Secondary attribution in a primary research paper; the original Ni96 theorem and numerical conventions were not recovered here |
| Castan thesis, §6.1, printed p.144 / PDF p.155 | Worked KAM example uses \(m_1=m_2=10^{-85}m_0\), \(a_1=5.2\) AU, \(a_2=5.2\times10^{12}\) AU | A different, highly conservative KAM calculation, not the Nekhoroshev estimate above and not a universal necessity |
| Giorgilli–Locatelli–Sansottera 2009, [DOI 10.1007/s10569-009-9192-7](https://doi.org/10.1007/s10569-009-9192-7), [arXiv:1303.7395](https://arxiv.org/abs/1303.7395), abstract | Sun–Jupiter–Saturn computer algebra reaches a stability timescale comparable to the universe's age | Authors explicitly qualify the calculation by substantial perturbation-series truncations; not a certificate of the exact full Hamiltonian |
| Sansottera–Locatelli–Giorgilli, [arXiv:1010.2609v3](https://arxiv.org/abs/1010.2609v3), abstract; [DOI 10.1016/j.matcom.2010.11.018](https://doi.org/10.1016/j.matcom.2010.11.018) | Estimated \(10^7\) yr for observational initial data | Planar **secular** Sun–Jupiter–Saturn–Uranus model |
| Giorgilli–Locatelli–Sansottera 2017, [DOI 10.1134/S156035471701004X](https://doi.org/10.1134/S156035471701004X), [arXiv:1702.04894v1](https://arxiv.org/abs/1702.04894v1), abstract p.1, discussion p.6 and §5 pp.26–27 | Estimated stability beyond Solar System lifetime, but initial neighborhood about ten times smaller than observational uncertainties | Same secular-model scope; p.6 explicitly says the result is not supported by a rigorous computer-assisted proof |

The literature supports the usefulness of tailored computation, but does not justify saying that exact unaveraged actual-mass Solar System stability is already certified. The historical reduced-mass values \(10^{-13}\)–\(10^{-11}\) remain many orders below Jupiter's approximately \(9.55\times10^{-4}\) ratio.

There is also a useful **existing repository model result**: `KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean:secularBoxAtCitedMasses` uses exact decimal model masses \(\mu=4773/5000000=0.0009546\), \(\mu m_S=0.0002856\). It proves global safety for `exactSecularHamiltonian` in its specified input box, with fixed fast actions. This is an honest actual-scale **averaged-model** theorem. It does not pay the fast averaging remainder needed for the unaveraged moving-Sun theorem.

## 4. The Solar System and LP17's exact claim

Primary source: Laskar–Petit 2017, [published PDF](https://www.aanda.org/articles/aa/pdf/2017/09/aa30022-16.pdf), **§5.4.1, A72 p.9; Figs.8–9, p.12**, and **§6**. Equivalent arXiv v2 locators are **§5.4.1, p.10; Figs.8–9, p.14**. These locators were checked in both texts; the common conjecture itself is documented in LITERATURE ([A2](A2-literature.md)).

LP17 says the giant planets' large AMD makes the **inner part of the full Solar System AMD-unstable**. It describes the outer dynamics as mostly quasiperiodic and emphasizes that AMD transfer from outer to inner can make the inner system unstable. Figure 8 compares the angular-momentum/AMD scales. Figure 9 and §5.4.1 classify the Solar System as hierarchically AMD-stable: the outer part is AMD-stable, and the inner part becomes AMD-stable when considered alone. This is a subsystem classification, not a theorem that their coupling can be ignored.

Honest possible statements are therefore:

* An **isolated outer-planets Newtonian model**, with a verified strong margin, can be a theorem/certificate target. Its actual mass threshold remains to be checked; Jupiter–Saturn's near 5:2 and other multi-frequency divisors make it difficult.
* An **isolated terrestrial-planet model without giants**, with its own AMD and verified inputs, can also be a target. It does not describe the inner subsystem of the coupled full system for exponentially long times without a bound on the omitted interactions.
* The existing exact secular Sun–Jupiter–Saturn model theorem at the cited masses is a concrete limited result, with the scope just described.
* The **full eight-planet system does not satisfy the proposed global strong-AMD premise**. No amount of improving normal-form constants fixes that premise. Splitting it and asserting no AMD exchange would introduce exactly the secular assumption this campaign seeks to avoid.

AMD-unstable means this sufficient barrier fails; it does not assert a collision occurs. The actual Solar System also includes relativistic and other effects absent from the chosen Newtonian model. No result here is a statement about every aspect of the physical Solar System.

## 5. Exoplanet screening with reproducible margins

LP17 Fig.5 (published p.9 / arXiv v2 p.11) lists HD 1461, HD 109271, HD 11964 and HD 69830 among its strong-AMD examples. Its catalogue used 131 systems and an inclination proxy; that is not a current, observationally certified list. The live [exoplanet.eu AMD page](https://exoplanet.eu/amd_stability/) could not be retrieved reliably in this session. Instead the LP figure and primary fit papers were checked, with the official NASA archive used to locate and compare named solutions.

For each pinned model, compute
\[
 \Lambda_i=m_i\sqrt{a_i},\quad C_p=\sum_i\Lambda_i(1-\sqrt{1-e_i^2}),\quad
 \beta_p=C_p/B,\quad\text{relative margin}=1-\beta_p.
\]
Masses in Earth masses and axes in AU are sufficient for these ratios; the common \(\sqrt{GM_*}\) cancels. The script `_sources/target_margins.py` minimizes the contact cost on its exact feasible interval by golden-section search and includes a nominal finite-divisor scan. Results are in `_sources/target_margins.json`. **No outward rounding is used.** These calculations are screening, not proof that B exceeds a certified bound. Eccentricity limits, central masses and axes are not combined into a claimed joint credibility interval.

### Four concrete candidates/models, in recommended screening order

| System; pinned fit | Periods (days), inner to outer | \(m\sin i\) (Earth masses); axes (AU) | Eccentricities used | \(B; C_p\) in \(M_\oplus\sqrt{AU}\) | \(\beta_p\); margin |
|---|---|---|---|---|---|
| **HD 109271**, Lo Curto et al.2013 Table2, p.7 | 7.8543, 30.93 | 17,24; .079,.196 | .25,.15 nominal | 1.46052; .27194 | .1862; **81.4%** |
| **HD 1461**, Díaz et al.2016 Table5 | 5.77152,13.5052 | 6.44,5.59; .0634,.1117 | .131,.228: each 95% upper limit | .13016; .06318 | .4854; **51.5%** |
| Same fit, conservative eccentricity screen | same | same | .172,.305: each 99% upper limit | .13016; .11318 | .8696; **13.0%** |
| **HD 11964**, Rosenthal et al.2021 catalogue, c then b | 37.9196,1935.0 | 24.3,201; .2315,3.185 | .106,.101 nominal | 11.69181; 1.90019 | .1625; **83.7%** |
| **HD 69830**, Lovis et al.2006 discovery model | 8.667,31.56,197 | 10.2,11.8,18.1; .0785,.186,.630 | .10,.13,.07 nominal | .67565; .09275 | .1373; **86.3%** |

Primary pins and source limitations:

* **HD 109271:** [Lo Curto et al., A&A551 A59](https://doi.org/10.1051/0004-6361/201220415), [arXiv:1301.2741](https://arxiv.org/abs/1301.2741), Table2. Eccentricity uncertainties are .08 and .09; masses are \(17\pm1\), \(24\pm2\) Earth masses. Period ratio 3.93797 is near 4:1, so “no resonance problem” would be false. Its low mass and large AMD margin make it the best first numerical trial, subject to a finite-divisor check.
* **HD 1461:** [Díaz et al., A&A585 A134](https://doi.org/10.1051/0004-6361/201526729), Table5 and its dagger footnote. The paper identifies the quoted eccentricities as **95% and 99% upper limits**, not best-fit values. Period ratio 2.33997 is near 7:3 at harmonic order 10. The lowest mass scale is attractive; inclination and eccentricity uncertainty can consume the margin.
* **HD 11964:** [Rosenthal et al., ApJS255,8](https://doi.org/10.3847/1538-4365/abe23c), [planet catalogue J/ApJS/255/8](https://cdsarc.cds.unistra.fr/viz-bin/cat/J/ApJS/255/8), values cross-checked in the [NASA solution table](https://exoplanetarchive.ipac.caltech.edu/overview/HD%2011964), selecting the Rosenthal column for **both** planets. Period ratio 51.029 is far from low-order pair resonances, but the outer fast frequency is small. It is a wider-separation, larger-mass alternative, not the smallest-mass target.
* **HD 69830:** [Lovis et al., Nature441,305–309](https://doi.org/10.1038/nature04828), [arXiv:astro-ph/0703024](https://arxiv.org/abs/astro-ph/0703024), discovery orbital table. Use this as a historical benchmark, **not the preferred current target**. [Boulkaboul et al.2026](https://arxiv.org/abs/2604.23694v1), p.10, HIP40693 discussion, identifies activity correlations near the middle planet's period. A new model-selection review is needed. The three-frequency screen below is independently unfavorable.

Approximate minimum-mass ratios \(\mu\), assuming an edge-on common plane, are respectively \(6.9\times10^{-5}\), \(1.9\times10^{-5}\), \(5.4\times10^{-4}\), and \(6.3\times10^{-5}\); stellar masses used for this rough comparison are 1.047,1.02,1.12,.86 solar masses. The HD11964 stellar mass is a rounded screening value, not a certified catalogue uncertainty. These estimates are not true-mass upper bounds. For an inclined common plane, all masses scale by \(1/\sin i\); the planar beta is unchanged but perturbation size increases. Unknown mutual inclinations also add AMD, so no table row proves spatial strong stability of the observed system.

LP17's equipartition proxy doubles \(C_p\). It would give beta .3724 for HD109271, .9708 for HD1461's 95% eccentricity screen (but 1.739 for its 99% screen), .3250 for HD11964, and .2746 for the old HD69830 fit. This is a **model assumption**, not a bound inferred from RV data.

### Arithmetic screen: pair ratios are not enough

For the same periods, normalized \(\omega_i=P_1/P_i\), a floating-point enumeration of every \(0<|j|_1\le12\) gives:

| Model | Minimum nominal \(|j\cdot\omega|\) | One minimizing integer vector |
|---|---:|---|
| HD109271 | .015752 | \((-1,4)\) |
| HD1461 | .008512 | \((-3,7)\) |
| HD11964 | .019597 | \((0,-1)\), the slow outer mean motion |
| HD69830 (2006) | **.000161** | \((-1,3,4)\) |

No row establishes nonresonance to the much larger K potentially required for a Gyr certificate. In particular HD69830's adjacent ratios 3.6414 and 6.2421 conceal a small **three-frequency** combination. The measured P and a columns are only rounded screening data; an actual certificate must enforce their dynamical/coordinate relation consistently rather than treating both as independent exact inputs.

### A fifth screened system that should be rejected for this route

**HD96700** appears in LP17's 2017 strong list, but [Unger et al.2021](https://doi.org/10.1051/0004-6361/202141351), [arXiv:2108.10198v1](https://arxiv.org/abs/2108.10198v1), §5.3 and orbital table on p.10, includes a third planet. The fit has P=8.1245,19.88,103.5 d; masses 8.9,3.5,12.7 Earth masses; a=.0777,.141,.424 AU; outer e=.27±.08. Even taking **both inner eccentricities zero**, the nominal outer eccentricity gives \(C_p=.30713\), \(B=.11804\), \(\beta_p=2.602\). It fails the global strong-AMD screen. This does not prove dynamical instability, but it does prevent recycling its old catalogue label as a Candidate B premise.

The saved NASA composite query `_sources/exoplanet-archive-20261031.json` was used for discovery/cross-checking only. It mixes references and sometimes retains older planet inventories; the HD20794 rows, for example, mix 2011 masses with 2025 periods. It is intentionally **not** the source of a certified initial condition. The calculations above use the named individual fits.

## 6. Computer-assisted route analogous to the lunar certificates

The repository's relevant pattern is precise: `KAM/SpinOrbit/Graph/CertV2.lean:soRotBarrier_of_certV2` turns a passing arithmetic certificate into a mathematical barrier using `checkTorusCertificateV2_sound`; `SpinOrbit/LunarFinalR2V2.lean:lunar_barriers_65_v2` consumes checked data; `lunar_spin_confinement_65_v2` derives a dynamical conclusion. The data generator is not trusted merely because it produced plausible floats. A planetary version should copy this **soundness architecture**, not the spin-orbit theorem or its low-dimensional cost estimate.

Proposed layers:

1. **Frozen model/input record.** Rational intervals for all initial parameters, a source/epoch record, a specified plane/inclination range, and an exact Hamiltonian expression. Decide whether the claim concerns an isolated published model or an observational family. Include any relevant additional bodies or explicitly limit the model.
2. **AMD geometry checker.** Interval/root-bracketing or convex one-dimensional minimization gives rigorous **lower bounds** for every pair threshold. A sampled feasible point gives an upper bound and cannot certify safety. Prove a lower bound over the entire parameter box, then bound C above and reserve threshold-motion/bridge margins.
3. **Analytic-domain checker.** Certify complex Kepler invertibility, chart derivative bounds and nonzero central/pair denominators on the complete enlarged secular set. Use Castan-style inequalities first; subdivide the real parameter/slow domain when dependency overestimation is severe.
4. **Fourier/normal-form checker.** Enclose low modes and all derivative/norm bounds with interval arithmetic. Prove analytic tail bounds for omitted Fourier modes and any Taylor truncation. Certify all integer divisors through K, including multi-planet combinations. Check either (P1)–(P2) or a separately proved sharper iteration.
5. **Kernel soundness theorem.** A passing finite rational record implies the actual analytic hypotheses for the exact Hamiltonian, a valid original-variable action drift, and a time interval. No floating-point oracle or unbounded generated “axiom” is allowed.
6. **AMD/ODE/physical export.** Consume the proved certificate through the qualitative first-exit engine, then the actual osculating bridge. Report time in physical units with a rigorous conversion and state the admitted observational/model assumptions.

The computer should emit a ledger of inequalities with rational lower/upper endpoints and a unique failing item when unsuccessful. This permits useful results even when a Gyr actual-mass certificate fails: e.g. a certified finite horizon, a verified smaller-mass threshold, or a geometric AMD certificate alone. Each must retain its proper scope.

## 7. Cost and likely failure points

**First screening:** one numerical analyst for roughly 1–2 working weeks is a reasonable planning allowance to pin one fit, implement interval AMD/divisor checks, and optimize the coarse explicit-domain inequalities for two planets. This is an estimate, not measured performance. It should precede a large Lean implementation. A negative result with the first failed inequality is valuable.

**Reusable certificate infrastructure:** roughly 7–15k hand-written lines across analytic-domain arithmetic, Fourier/normal-form soundness and adapters, plus data and an independent emitter. With experienced proof and numerical staff, plan in months rather than days; no hardware benchmark was run here. The qualitative theorem can proceed independently.

The main numerical risks are narrow complex widths near the enlarged sublevel's collision boundary; overly large global Fourier norms; action-radius versus divisor competition; uncertainty intervals crossing a low-order resonance; unbounded true masses/mutual inclinations; and omitted Taylor/Fourier tails. HD109271's near4:1, HD1461's near7:3, and the three-body HD69830 combination are concrete examples. Higher precision only fixes rounding loss, not a genuinely false smallness inequality.

Mode count scales poorly: the number of integer modes in an \(\ell^1\) ball is about \(2K^2\) for n=2 and \((4/3)K^3\) for n=3. K=1000 already means about two million versus 1.3 billion modes before symmetry or sparse estimates. The slow-domain dimension is 2n planar and 4n spatial. Whole-domain certification is much more expensive than checking one trajectory. Sparse analytic bounds and short, independently checkable data chunks are likely necessary on the current memory-limited machine.

**Recommended practical commitment:** fund the HD109271/HD1461 finite-cutoff screening first, keep HD11964 as the wide-separation alternative, and use the historical HD69830 model as a stress test. Commit to reporting actual masses only if the full explicit ledger passes. The asymptotic theorem remains worthwhile even if this pilot exposes an impractical mass threshold; the two outcomes must not be conflated.
