# What is proved: plain-language accounts of each result

Each file below states exactly what one subproject proves: the setting, every hypothesis, the order of the
quantifiers, the explicit constants, and what is not claimed. The Lean statements they link to are the authority; these
accounts are written from them. Progress meters are in the [README](../../README.md#progress-by-subproject).

## KAM theory: the original project

- [Track K](K.md): positive-measure KAM for nearly-integrable analytic Hamiltonians (complement ≤ C·ε^{1/4}), the
  a-posteriori KAM theorem, local uniqueness of tori, the measure of non-Diophantine frequencies.
- [Track I](I.md): isoenergetic KAM, all-time confinement in two degrees of freedom, the restricted circular planar
  three-body problem.
- [Track N](N.md): Nekhoroshev stability for quasi-convex Hamiltonians, partial convexity, averaging.
- [Track P](P.md): properly degenerate KAM, the planar two-planet problem, n planets around a fixed Sun, AMD and
  secular-box safety.

## Extensions of the theory

- [Track R](R.md): Rüssmann's KAM theorem under weak non-degeneracy.
- [Track W](W.md): quasi-periodic solutions of the cubic wave equation (PDE KAM).
- [Track LP](LP.md): no orbit crossing for an exponentially long time below the sharp Laskar–Petit AMD threshold.
- [Track B](B.md): finite-time effective stability; the Hénon–Heiles system confined; confinement from approximate
  integrals.

## Certified numerics: the Moon

- [SO part 1](SO-1.md): the Lean checker that turns numerical KAM tori into theorems.
- [SO part 2](SO-2.md): the Moon's spin rate stays within 2.755 % of its orbital rate for all time.
- [SO part 3](SO-3.md): the Moon is locked in synchronous rotation forever.

## Certified numerics: planetary systems

- [SJSU gate 2](SJSU.md): the secular Sun–Jupiter–Saturn–Uranus model keeps its eccentricities in fixed bands for
  5·10⁹ years.
- [LG00](LG00.md) (side project): a kernel-checked KAM torus of a secular Sun–Jupiter–Saturn model.
- [HD 11964](HD11964.md) (side project, in progress): no orbit crossing for a fixed time in a real exoplanet system.

## Frozen, proof open

- [Magnetic barrier](Magnetic.md): an invariant surface that no field line of a model magnetic field crosses.
