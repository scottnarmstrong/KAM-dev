# Realistic KAM and bodies of finite size

Research report for the collaborator's question, 27 October 2026: *is there an improvement of KAM that makes it more
realistic? How about bodies of finite size?* It extends [planetary-and-nekhoroshev.md](planetary-and-nekhoroshev.md)
and [almost-every-shorter-times.md](almost-every-shorter-times.md). It proposes statements; it does not change any
frozen anchor.

Three independent literature surveys fed this note: point-mass realism, rigid and tidal bodies, and fluid bodies
with the point-mass limit. References were checked against arXiv, publisher or Crossref records unless marked
**[unverified]**. Statements of the form "nothing was found" mean nothing turned up in targeted searches, not that
nothing exists.

## Summary

1. **The realistic upgrade of KAM is the a-posteriori theorem plus a computer-assisted proof (CAP).** It removes
   the small parameter: fix the actual Hamiltonian, compute an approximate torus, and verify with interval
   arithmetic that its invariance error is below an explicit threshold built from computable norms. This is
   exactly the theorem the campaign freezes as G1 (HL19 Thm 3.1, GJLV05). The campaign's route is therefore
   the right one for realism, not only for formalization.
2. **For the real planets there is still no theorem.** Proved results at true masses exist only for reduced
   models (secular Sun–Jupiter–Saturn, truncated restricted problems, Trojans, exoplanet analogues). The full
   planar Sun–Jupiter–Saturn torus has been computed to invariance error about 10⁻⁵⁴ but not yet certified
   (FH 2025). For the inner planets a KAM torus through the observed data is numerically excluded.
3. **Finite size by itself costs nothing for spheres.** By the shell theorem, rigid spherically symmetric bodies
   move exactly like point masses and their spins decouple. On Arnold's tori all mutual distances stay at least
   some c > 0, so spheres of radius below c/2 never touch. This is an elementary corollary of track P.
4. **Asphericity and spin are a genuinely different problem.** Only the 1½-degree-of-freedom spin–orbit model is
   understood: KAM tori at the true parameters of the Moon and several Saturnian moons trap the synchronous
   resonance forever, in a truncated model (Celletti 1990). No Arnold-type theorem for N rigid or oblate bodies
   is known.
5. **Tides make "for all time" false and change the right theorem.** Dissipation that conserves angular momentum
   drives systems towards rigid relative equilibria, so invariant tori become attractors (conformally symplectic
   KAM, Calleja–Celletti–de la Llave 2013; that paper is already pinned as CCdlL13). For three or more bodies no
   stable end state exists (Moeckel 2017).
6. **Fluid bodies are open.** Only rigidly rotating relative equilibria of several self-gravitating fluid bodies
   exist (Lichtenstein, McCann, Campos–del Pino–Dolbeault). There is no time-periodic or quasi-periodic
   Euler–Poisson solution with separated bodies, and no derivation of the point-mass dynamics from fluid bodies
   valid even for one bound orbital period.

## A. Point masses: what makes KAM realistic

### A1. The size of the classical threshold

Hénon's estimate for Arnold's theorem gives masses below about 10⁻³³³ (two degrees of freedom), and about
10⁻¹¹³¹ for spatial Sun–Jupiter–Saturn, as reconstructed by Laskar (arXiv:1411.4930). Jupiter's ratio is about
10⁻³. Every realistic result below avoids this threshold by not using a perturbation series in ε at all.

### A2. A-posteriori KAM with interval arithmetic

- **Form of the theorem.** Given one Hamiltonian H and an approximate torus K with Diophantine frequency ω and
  invariance error E = X_H∘K − ∂_ωK: if ‖E‖_ρ is below an explicit function of (γ, τ, ρ) and of computable
  twist and non-degeneracy norms of K, a true invariant torus exists within C‖E‖ of K (dlLGJV 2005; FHL 2017;
  HL 2019).
- **Strength.** There is no near-integrability, no action-angle variables and no family in ε. FHL 2017 prove
  invariant curves of the standard map up to ε = 0.9716, essentially at Greene's critical value.
- **Degeneracies.** The iso-energetic and extra-first-integral versions (HL 2019 Thm 3.6; FH 2024) handle the
  energy and angular-momentum degeneracies of the planetary problem.
- **The real system.** FH 2025 (J. Nonlinear Sci. 35:13, arXiv:2403.10152) treat the full planar
  Sun–Jupiter–Saturn problem with real masses and orbital data. They compute a 3-torus in a 6-dimensional
  reduced phase space with invariance error about 10⁻⁵⁴, using more than 6×10⁹ Fourier coefficients. The KAM
  hypotheses are checked numerically only, so this is evidence, not yet a theorem.

### A3. Normal-form CAPs at true masses (Rome and Milan schools)

These are theorems for reduced models:
- Locatelli–Giorgilli 2000: planar **secular** Sun–Jupiter–Saturn, real masses, interval arithmetic; an invariant
  torus near the real data, so perpetual stability of that two-degree-of-freedom model.
- Celletti–Chierchia 2007 (Mem. AMS 878): Sun–Jupiter–Victoria in the planar circular restricted problem, real
  mass ratio, with the perturbation truncated to its dominant Fourier terms. The 2-tori bound the observed
  3-dimensional energy level, so the asteroid is confined forever (the track I mechanism).
- Gabern–Jorba–Locatelli 2005: Trojans; the normal form works for 23 of 34 Trojans, and the CAP was completed
  for 3.
- Exoplanets: υ And c,d secular librational torus (CLSV 2022); HD 60532 in the averaged 3:1 resonance
  (DLS 2023); υ And b with general-relativity corrections, at least 3 degrees of freedom (Mastroianni–Locatelli
  2024).
- Caracciolo–Locatelli 2025, full planar three-body problem for HD 11964, HD 142 and HD 4732: found only as a
  conference abstract and a talk **[unverified]**.

### A4. Effective stability at realistic parameters

- Near a KAM torus the drift is superexponentially slow (Morbidelli–Giorgilli 1995); this is generic for
  Diophantine tori (Bounemoura–Fayad–Niederman 2017). This is how a single certified torus becomes an
  **open-set, finite-time** statement.
- Trojans: Giorgilli–Skokos 1997 find a region stable for the age of the universe at the real Sun–Jupiter mass
  ratio that contains a few real Trojans; later improvements include Guzzo–Caracciolo–Pinzari 2026
  (arXiv:2601.18268).
- Planets: Giorgilli–Locatelli–Sansottera 2017 (planar secular Sun–Jupiter–Saturn–Uranus) combine a KAM torus
  with Nekhoroshev estimates and reach the age of the Solar System, but in a neighbourhood about 10 times
  smaller than the observational uncertainty.
- Purely analytic bounds remain far from the real masses: Niederman 1996 gives about 4×10⁹ yr only for
  ε < 10⁻¹³; Barbieri–Niederman 2020 reach the age of the Solar System only for ε ≲ 10^−11.25.

### A5. Which statements are provably false

- Laplace–Lagrange stability of semi-major axes is false for all initial data: Clarke–Féjoz–Guàrdia 2024 build
  three-planet orbits whose outer semi-major axis varies by large amounts over polynomial times.
- Arnold diffusion is proved in the planetary regime: Féjoz–Guàrdia–Kaloshin–Roldán 2016 (restricted planar,
  μ = 10⁻³ as model value); Clarke–Féjoz–Guàrdia 2025 (spatial four-body); and by CAP at physical
  Neptune–Triton masses, Capiński–Gidea 2023 and arXiv:2504.09273.
- Consequence: with three or more degrees of freedom, "every orbit in an open set is stable for all time" cannot
  hold in general. What remains provable is perpetual stability on a Cantor set, open-set stability for finite
  time, and probabilistic statements.

### A6. The real Solar System numerically (not theorems)

- Lyapunov time about 5 Myr; about 1% of observationally compatible orbits reach Mercury collisions within 5 Gyr
  (Laskar–Gastineau 2009). Leaving out general relativity raises the risk about 60-fold (Brown–Rein 2023).
- Probability about 10⁻⁴ within 2 Gyr (Abbot et al. 2021).
- The gap between the Lyapunov time and the instability time is explained by quasi-integrals of weakly broken
  symmetries (Mogavero–Hoang–Laskar 2023, PRX 13, 021018).
- Passing stars matter at the percent level: they raise the odds of Mercury instability by 50–80% (Kaib–Raymond
  2025, arXiv:2505.04737). The physically meaningful horizon is about 5–10 Gyr, not t → ∞.

### A7. Beyond Newtonian point masses

- **General relativity.** No KAM or Nekhoroshev theorem for the 1PN N-body problem was found. The only
  rigorous KAM result with GR corrections is the secular restricted model of Mastroianni–Locatelli 2024.
  Inference: the a-posteriori theorem applies unchanged to H_N + c⁻²H_1PN; nobody has done it.
- **Formal verification.** No Lean, Coq or Isabelle formalization of KAM or Nekhoroshev was found besides the
  projects listed in the README. The closest certified computation is the Isabelle/HOL verified ODE solver
  (Immler 2018).

## B. Bodies of finite size

### B1. Spherical rigid bodies: a free corollary

For spherically symmetric bodies the shell theorem makes the mutual force exactly the point-mass force, and the
spins are conserved and decouple. On the compact invariant tori of the planetary theorem every mutual distance
is bounded below by some c > 0 (planetary-and-nekhoroshev.md, "Collision exclusion"). So for radii
r_i + r_j < c the tori are motions of non-touching spheres. This is our own deduction, stated here as a
proposed corollary of P-PLANAR / P-FIXED.

### B2. Aspherical rigid bodies: spin–orbit coupling

Model: the centre of mass follows a fixed Kepler ellipse, and the spin axis is perpendicular to the orbit and is
the shortest principal axis:

    ẍ + ε (a/r)³ sin(2x − 2f(t)) = 0,       ε = (3/2)(B − A)/C.

This has 1½ degrees of freedom.
- **Proved at true parameters:** Celletti 1990 (ZAMP 41, 174–204) proves by CAP two rotational invariant tori
  bracketing the synchronous resonance, at the true e and ε of the **Moon, Rhea, Dione and Enceladus**. The
  potential is truncated to its leading terms in e. Since the extended phase space is 3-dimensional, the tori
  confine the resonance for all time.
- **Not proved:** Celletti–Chierchia 2000, "Hamiltonian stability of spin–orbit resonances", is numerical. There
  is no rigorous KAM statement for Mercury's 3:2 resonance at its true parameters.
- **Rigorous fragments with more degrees of freedom:** Nekhoroshev stability of proper rotations of a perturbed
  rigid body (Benettin–Fassò–Guzzo 2004); Arnold diffusion in a d'Alembert precession model
  (Chierchia–Gallavotti 1994).
- **Not found:** an Arnold, Herman–Féjoz or Chierchia–Pinzari theorem for N rigid or oblate bodies, or any KAM
  theorem for the full (non-Keplerian) two-rigid-body problem. Moon-stabilized obliquity of the Earth is a
  contested numerical claim, not a theorem.

### B3. Tides: dissipation replaces invariant tori by attractors

With a constant-time-lag tidal torque the spin–orbit equation gains a friction term −λ(ẋ − μ). Its time-2π map
multiplies the area form by a constant: it is **conformally symplectic**.
- **Celletti–Chierchia 2009** (ARMA 191, 311–345): for Diophantine ω and small ε, uniformly in the dissipation
  λ, there is a unique drift μ(ε, λ) and an invariant torus of frequency ω, attracting for λ > 0.
- **Calleja–Celletti–de la Llave 2013** (pinned as CCdlL13): an a-posteriori KAM theorem for conformally
  symplectic systems, with no closeness to integrability and one drift parameter tuned per frequency. This is
  the dissipative twin of G1.
- **Resonant attractors at true parameters:** Antognini–Biasco–Chierchia 2014 prove existence (not stability) of
  1:1 periodic orbits at the observed e and ε of the Moon and many satellites, and Mercury's 3:2 orbit, for
  dissipation up to 10⁻³; the physical value is about 10⁻⁸.
- **No rigorous CAP at real tidal parameters exists.** Calleja–Celletti–Gimeno–de la Llave 2022 explicitly do
  not claim one.
- **The long-time picture.** Energy decreases at fixed angular momentum, so bounded collision-free motions
  approach relative equilibria. Haus–Bambusi 2015 prove the trichotomy for one elastic body around a point
  planet: escape, fall, or convergence to synchronous circular rotation. For three or more bodies no relative
  equilibrium minimizes energy at fixed angular momentum (Moeckel 2017). Hence generic N ≥ 3 tidal evolution
  should end in collision or escape: this is a conjecture, not a theorem.
- **Physics caveat.** Realistic rheology gives non-smooth torques (Makarov–Efroimsky 2013), which leave the
  conformally symplectic class.

### B4. Self-gravitating fluid bodies

- **Exact orbiting fluid bodies exist only as rigidly rotating relative equilibria:**
  - Lichtenstein 1922 (two incompressible masses);
  - McCann 2006 (compressible binaries, as energy minimizers at fixed angular momentum);
  - Jang–Seok 2022 (orbital stability of McCann's binaries);
  - Campos–del Pino–Dolbeault 2010 (N bodies near any nondegenerate central configuration).
- **Open:** time-periodic or quasi-periodic Euler–Poisson solutions with separated bodies. The nearest analogue
  is KAM desingularization of point vortices into vortex patches (Hassainia–Hmidi–Masmoudi, Invent. Math.
  2025).
- **Point-mass limit.** Newtonian effacement is an exact identity: self-forces cancel, and the corrections are
  J₂(R/d)² from flattening and k₂(M_B/M_A)(R/d)⁵ from tidal quadrupoles. But no theorem controls the internal
  fluid dynamics along a bound orbit for even one period. The best dynamical results cover one hyperbolic
  encounter (Miao–Shahshahani, arXiv:1708.04307) or dispersing bodies (Parmeshwar, arXiv:1910.08600).
- **Contact.** For bodies of radius r > 0, Painlevé's criterion means there are no singularities before contact,
  and the set of initial data leading to contact is open, hence of positive measure. No estimate of its measure
  for N ≥ 3 was found.

## C. Proposed statements for the campaign

Ranked by value per formalization cost. These are proposals for the owner, not approved anchors.

**C1. Spheres corollary (cheap).** Proposed as an addendum to P-PLANAR / P-FIXED. Give each planet radius
rᵢ > 0. Then the positive-measure union of tori produced by the theorem consists of motions in which no two
spheres touch, provided max(rᵢ + rⱼ) is below the uniform separation bound already proved there. It needs only
the shell theorem in the form "the Newtonian Hamiltonian of spheres equals that of point masses at positive
separation", which can be imposed as the model definition. Estimate: a few hundred lines on top of track P.

**C2. Spin–orbit confinement with a certificate.** Proposed for track I.
- *Model.* The conservative spin–orbit equation of B2 with explicit (e, ε), written as an autonomous two-degree-of-
  freedom Hamiltonian in extended phase space.
- *Statement.* If two certified approximate tori satisfy the hypotheses of I-G1 (isoenergetic a-posteriori
  KAM), the synchronous resonance between them is confined for all time; this is the I-HEAD mechanism.
- *Certificate.* The numerical inputs would come from an interval-arithmetic certificate. Precedent: PlasmaLean,
  listed in the README.
- *Payoff.* This would be the first formally verified KAM statement about a real body (the Moon, in the
  truncated model of Celletti 1990), and the first finite-size statement.
- *Risks.* The time-periodic forcing needs an extended-phase-space formulation, and the certificate pipeline is
  new to the campaign.

**C3. Conformally symplectic a-posteriori KAM (track K variant).** Pinned source: CCdlL13, already in
`sources/`.
- *Statement.* For a conformally symplectic flow with constant conformal factor e^{−λt} and one drift parameter,
  an approximately invariant torus with small error and nondegenerate twist and drift-transversality lies near a
  true invariant torus, with an adjusted drift. The torus is attracting for λ > 0.
- *Reuse.* The Newton step, cohomological equations and Neumann bounds of G1 carry over almost verbatim. The
  cohomological equation becomes ∂_ω u + λu = g, which is easier (no small divisor at k = 0 when λ ≠ 0).
- *Application.* Quasi-periodic attractors in the averaged dissipative spin–orbit model (Celletti–Chierchia 2009).
- *Estimate.* 5k–10k lines beyond track K's G1.

**C4. Not recommended now.** These are open mathematics, not formalization targets:
- N rigid or oblate planets (no published theorem);
- 1PN planetary KAM (unpublished);
- any fluid-body theorem;
- a tidal "for all time" statement, which is false for N ≥ 3.

## D. References

**Point masses**
- Abbot et al., ApJ 923 (2021) 236, arXiv:2106.09091.
- Barbieri–Niederman, JDE 268 (2020) 3749, arXiv:1810.05987.
- Bounemoura–Fayad–Niederman, CMP 350 (2017) 361, arXiv:1601.01783.
- Brown–Rein, MNRAS 521 (2023) 4349, arXiv:2303.05567.
- Capiński–Gidea, CPAM 76 (2023) 616, arXiv:1812.03665; arXiv:2504.09273.
- Caracciolo–Locatelli–Sansottera–Volpi, MNRAS 510 (2022) 2147, arXiv:2108.11834.
- Celletti–Chierchia, Mem. AMS 187 (2007), no. 878.
- Clarke–Féjoz–Guàrdia, ARMA 248 (2024), arXiv:2303.05979; Publ. IHÉS 141 (2025).
- Danesi–Locatelli–Sansottera, CeMDA 135 (2023) 24, arXiv:2303.06702.
- de la Llave–González–Jorba–Villanueva, Nonlinearity 18 (2005) 855 (GJLV05).
- Féjoz–Guàrdia–Kaloshin–Roldán, JEMS 18 (2016) 2315, arXiv:1109.2892.
- Figueras–Haro, Physica D 462 (2024) 134127, arXiv:2304.10205; J. Nonlinear Sci. 35 (2025) 13,
  arXiv:2403.10152.
- Figueras–Haro–Luque, FoCM 17 (2017) 1123, arXiv:1601.00084 (FHL17).
- Gabern–Jorba–Locatelli, Nonlinearity 18 (2005) 1705.
- Giorgilli–Locatelli–Sansottera, RCD 22 (2017) 54, arXiv:1702.04894.
- Giorgilli–Skokos, A&A 317 (1997) 254.
- Guzzo–Caracciolo–Pinzari, arXiv:2601.18268.
- Haro–Luque, JDE 266 (2019) 1605, arXiv:1711.05515 (HL19).
- Immler, J. Autom. Reason. 61 (2018) 73.
- Kaib–Raymond, arXiv:2505.04737.
- Laskar, arXiv:1411.4930.
- Laskar–Gastineau, Nature 459 (2009) 817.
- Locatelli–Giorgilli, CeMDA 78 (2000) 47.
- Mastroianni–Locatelli, CNSNS 130 (2024) 107706, arXiv:2311.01938.
- Mogavero–Hoang–Laskar, PRX 13 (2023) 021018, arXiv:2305.01683.
- Morbidelli–Giorgilli, J. Stat. Phys. 78 (1995) 1607.
- Niederman, Nonlinearity 9 (1996) 1703.

**Rigid and tidal bodies**
- Antognini–Biasco–Chierchia, J. Nonlinear Sci. 24 (2014) 473, arXiv:1312.7544.
- Benettin–Fassò–Guzzo, CMP 250 (2004) 133.
- Calleja–Celletti–de la Llave, JDE 255 (2013) 978 (CCdlL13).
- Calleja–Celletti–Gimeno–de la Llave, CNSNS 106 (2022) 106099, arXiv:2107.02853.
- Celletti, ZAMP 41 (1990) 174–204 and 453–479.
- Celletti–Chierchia, CeMDA 76 (2000) 229; ARMA 191 (2009) 311.
- Chierchia–Gallavotti, Ann. IHP Phys. Théor. 60 (1994) 1.
- Haus–Bambusi, Math. Phys. Anal. Geom. 18 (2015) 14, arXiv:1212.0816.
- Makarov–Efroimsky, ApJ 764 (2013) 27, arXiv:1209.1616.
- Moeckel, CeMDA 128 (2017) 3.

**Fluid bodies and the point-mass limit**
- Campos–del Pino–Dolbeault, CMP 300 (2010) 765, arXiv:1001.4866.
- Hassainia–Hmidi–Masmoudi, Invent. Math. (2025), arXiv:2311.15765.
- Jang–Seok, ARMA 244 (2022) 443.
- Lichtenstein, Math. Z. 12 (1922) 201.
- McCann, Houston J. Math. 32 (2006) 603.
- Miao–Shahshahani, arXiv:1708.04307.
- Parmeshwar, arXiv:1910.08600.

## Checks and limits

- No Lean was written for this note.
- The literature claims come from three independent surveys. Each checked its references against primary
  records, and the items it could not confirm are marked [unverified] above or were left out.
- The corollaries C1 and C2 and the conjecture in B3 are our own deductions, not statements from the sources.
