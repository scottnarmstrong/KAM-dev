# Planetary KAM, Nekhoroshev and the "almost every" question

[← Back to the catalogue](../README.md)

Four research reports from 27 October 2026, written for Zohar Komargodski's questions about planets. The first set up
the parallel tracks I, N and P (decision D14). The three "almost every" rounds asked whether most initial conditions, or
all of them, stay safe for shorter or longer times; they produced five more milestones (D22). Round 3 is an independent
refutation audit of round 2. Every statement these reports finally recommended was frozen in a corrected form and is now
proved; see [`docs/STATEMENTS.md`](../../STATEMENTS.md).

| Document | Status | One line |
|---|---|---|
| [planetary-and-nekhoroshev](../planetary-and-nekhoroshev.md) | done (D14) | Why the headline does not apply to planets; three ranked targets |
| [almost-every-shorter-times](../almost-every-shorter-times.md) | done in part (D22, D28) | Averaging gives mean error O(√ε), not error O(√ε) off a set of size O(√ε) |
| [almost-every-round2](../almost-every-round2.md) | done, corrected by round 3 | Exponential-time safety for every low-AMD initial condition; secular SJS box |
| [almost-every-round3-refutation](../almost-every-round3-refutation.md) | audit; done (D25) | Confirms round 2 with corrections; the exponent 1/(2n) is unverified |

## Planetary KAM and open regions of long-time stability

**[planetary-and-nekhoroshev.md](../planetary-and-nekhoroshev.md)** · 27 October 2026 · research report ·
status: **done** (adopted as tracks I, N, P by D14; the recommended statements are proved)

The report states the planetary KAM theorem (Arnold 1963, Herman–Féjoz 2004, Chierchia–Pinzari 2011) with its exact
quantifiers and explains why the campaign's headline theorem does not apply to planets: the Kepler Hamiltonian depends
on only n of the 2n planar (3n spatial) actions, so its frequency map is degenerate ("proper degeneracy"). For "a region
with no collisions or escapes" it separates two mechanisms. In two degrees of freedom, two invariant tori bound a region
for all time, provided the system is isoenergetically nondegenerate. In general dimension, Nekhoroshev theory gives
exponentially long confinement for every initial condition. It ranks three formalization targets: all-time confinement in
two degrees of freedom with the restricted three-body problem; quasi-convex Nekhoroshev with exponents 1/(2n); and
properly degenerate KAM as the bridge to planets.

- **Numbers and verdicts.** For the restricted circular planar three-body problem the bordered determinant is
  3κΩ²/L⁴ > 0, which is why isoenergetic KAM works there. A fixed-Sun model is a different model from the moving Sun:
  dropping the indirect kinetic term needs its own proof. Estimates: 5–10k + 5–10k Lean lines (target 1), 20–40k
  (target 2), 15–30k (target 3), 30–60k for the planar planetary application. The 1% of 2,501 Laskar–Gastineau runs with
  large Mercury eccentricity is numerical evidence, not a proof of collision.
- **Outcome.** Proved and sealed: [`all_time_confinement`](../../STATEMENTS.md#all_time_confinement),
  [`restricted_near_circular`](../../STATEMENTS.md#restricted_near_circular),
  [`quasiConvex_nekhoroshev_complexBound`](../../STATEMENTS.md#quasiconvex_nekhoroshev_complexbound),
  [`properlyDegenerateKAM`](../../STATEMENTS.md#properlydegeneratekam),
  [`planarTwoPlanetKAM`](../../STATEMENTS.md#planartwoplanetkam) and
  [`fixedSunPlanetaryKAM`](../../STATEMENTS.md#fixedsunplanetarykam).
- **Followed by.** [almost-every-shorter-times](../almost-every-shorter-times.md) and
  [realistic-kam-and-finite-size](../realistic-kam-and-finite-size.md) extend it. [ambition](../ambition.md) still cites
  it: "proper degeneracy and quantifier order remain central".

## Most nearby initial conditions over shorter times (round 1)

**[almost-every-shorter-times.md](../almost-every-shorter-times.md)** · 27 October 2026 · research report ·
status: **done in part** (its averaging statement became N-AVERAGING, D22 and D28); emphasis superseded by round 2

The question was whether "most" initial conditions stay safe over shorter, polynomial times. The main correction to the
brief: for multifrequency averaging (Neishtadt; Arnold–Kozlov–Neishtadt, Theorem 6.11) the *mean* error over initial data
is O(√ε), so the set where the error exceeds η has measure O(√ε/η). It does not follow that the error is O(√ε) outside a
set of measure O(√ε). The report keeps five parameters apart (perturbation ε, mass ratio μ, observational radius r,
tolerated drift η, exceptional fraction δ) and surveys stickiness near KAM tori (Morbidelli–Giorgilli; Bounemoura–Fayad–
Niederman; Bounemoura–Farré, where all but a fraction exp(−c r⁻ᵃ) of a tube of radius r is stable for doubly exponential
time), prevalence results for generic Hamiltonians, and the numerical ensembles. It proposes (A) an averaging theorem on a
fixed ball and (B) a fixed-Sun planar planetary application over time L/μ with exceptional relative measure δ.

- **Numbers and verdicts.** Exception at most C_L√ε/(ηV) on a ball of volume V, for time L/ε. Estimates: A 10–20k Lean
  lines, B 15–25k. Numerically, Mogavero–Laskar 2021 find 42 secular collisions in 10,560 runs over 5 Gyr (about 0.4%):
  "at least 99% safe over 5 Gyr" is broadly compatible with the models, "all except a null set" is not.
- **Candidate errata.** BFN16 Definition 1, p. 3 (the conclusion repeats the initial time, so it is tautological);
  quantifier issues in Bounemoura–Niederman and in Morbidelli–Giorgilli 1995.
- **Outcome.** Proved: [`averaging_mean`](../../STATEMENTS.md#averaging_mean) and
  [`averaging_most`](../../STATEMENTS.md#averaging_most).
- **Disagreements.** [Round 2](../almost-every-round2.md) moves the emphasis from most data over polynomial times to all
  data over exponential times. [Round 3](../almost-every-round3-refutation.md) confirms the averaging correction and fixes
  one attribution (the slides are by Neishtadt and Okunev).

## Longer-time planetary safety: round 2

**[almost-every-round2.md](../almost-every-round2.md)** · 27 October 2026 · proposal for tracks N and P ·
status: **done, with the corrections of round 3** (milestones adopted by D22, D25, D28)

The main finding is classical: on a fixed region of the planar moving-Sun problem with low angular-momentum deficit (AMD)
and radially separated orbits, small masses give exponential-time safety for *every* initial condition, with no
exceptional set. Partial (properly degenerate) Nekhoroshev theory controls the fast Kepler actions; exact conservation of
angular momentum then bounds the AMD and hence every eccentricity, which closes the continuation argument. The report
also shows that averaging cannot simply be iterated to reach times μ⁻ᵏ, and gives an exact-average secular
Jupiter–Saturn box that is safe for all time at the actual masses. It ranks six milestones and lists refutation gates for
an independent audit.

- **Numbers and verdicts.** Proposed P-EXP-SAFE: time t₀exp(cμ^(−1/(2n))) and action drift Cμ^(1/(2n)), empty
  exceptional set; the mass threshold is not verified at μ ≈ 10⁻³. Secular box: Saturn/Jupiter mass in [0.29, 0.31],
  a_J ∈ [5.15, 5.25] au, a_S ∈ [9.45, 9.65] au, e_J ≤ 0.06, e_S ≤ 0.07 gives AMD < 0.0065492 < 0.00957, hence e < 0.15,
  a radial gap of at least 1.995 au and radii between 4.3775 and 11.0975 au, for all time in the secular model.
  Milestones: P-AMD-CONFINEMENT (3–6k lines), P-SECULAR-BOX (1–3k), N-PARTIAL-CONVEX (20–40k), P-EXP-SAFE (2–5k),
  N-NONRESONANT-MEASURE (8–15k), P-REALISTIC-CERT (unknown; feasibility study only).
- **Outcome.** Proved: [`amdConfinement`](../../STATEMENTS.md#amdconfinement),
  [`planetaryExponentialSafety`](../../STATEMENTS.md#planetaryexponentialsafety),
  [`secularBoxSafety`](../../STATEMENTS.md#secularboxsafety),
  [`secularBoxAtCitedMasses`](../../STATEMENTS.md#secularboxatcitedmasses) and
  [`partialConvex_nekhoroshev`](../../STATEMENTS.md#partialconvex_nekhoroshev).
- **Disagreements.** [Round 3](../almost-every-round3-refutation.md) finds the exponent 1/(2n) unverified and the cited
  stopped theorem (Pinzari D.1) to be a whole-interval statement that cannot close the bootstrap. The frozen theorem uses
  Nekhoroshev 1977's exponents a = 2/(6n² − 3n + 14), b = 3a/2 instead. [ambition](../ambition.md) records that the
  1/(2n) shortcut "was not established"; [program-a-plan](../program-a-plan.md) and
  [program-d-plan](../program-d-plan.md) work with the frozen exponent.

## Round 3: refutation audit of the round-2 planetary safety claims

**[almost-every-round3-refutation.md](../almost-every-round3-refutation.md)** · 27 October 2026 · independent referee
audit · status: **audit**; its corrected statements were frozen (D25) and are proved

The audit re-derives round 2's Hamiltonian, the angular-momentum and AMD identity, the AMD bootstrap, analyticity through
circular orbits and continuation, and confirms each. It recomputes the secular box in exact rational arithmetic and
confirms it (a crude form of Laskar's AMD stability; e_J ≤ 0.0759 and e_S ≤ 0.1210 separately). It finds that the cited
source theorem is not a stopped theorem and pins the right one: Nekhoroshev 1977, Theorem 4.4, with an arbitrary stopping
time. The exponent β = 1/(2n) is unverified: the proceedings page that states it attributes it wrongly, and the full Guzzo
1999 proof gives at most 1/(3n). The whole result is already Nekhoroshev 1977, §12, Theorem 12.3.

- **Verdicts.** P-EXP-SAFE: confirmed with corrections (corrected form P-EXP-SAFE′ with ∃ a, b > 0, or
  a = 2/(6n² − 3n + 14), b = 3a/2). Secular box: confirmed. Round-1 averaging correction: confirmed (AKN states the
  Markov form is best possible). Novelty: a known theorem. Two attempted counterexamples (Féjoz–Guàrdia–Kaloshin–Roldán;
  Clarke–Féjoz–Guàrdia) fail for stated reasons, which show that fixed positive masses and a low-AMD,
  μ-independent domain are needed.
- **Recommendations.** Safe to freeze: P-AMD-CONFINEMENT with a stopped hypothesis, P-SECULAR-BOX, N-PARTIAL-CONVEX in
  stopped form, P-EXP-SAFE′, and round 1's averaging statement. Not a source theorem: N-NONRESONANT-MEASURE. Feasibility
  study only: P-REALISTIC-CERT.
- **Ledger notes.** Pinzari's restatement drops "C arbitrary"; Guzzo 1999 (proceedings, p. 443) misattributes the
  exponent; the brief pointed at the wrong Pinzari file.

[← Back to the catalogue](../README.md)
