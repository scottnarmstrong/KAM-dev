# SJSU-FULL: from the secular theorem to the full planar Newtonian problem (scoping)

6 November 2026, branch `sjsu-full-scope` (off `main` at `5b61de513`). Scoping only: no Lean, no `lake build`, no
`.lake`, nothing frozen. The computations are float64/mpmath explorations under `nice` (each under 1 CPU-min, under
1 GB); their scripts and JSON outputs are in the worktree's uncommitted `.drafts/sjsu-full/`. Appendix A gives
their formulas, so they can be rerun.

**Labels.**
- **proved:** a compiled Lean theorem at the cited path.
- **measured:** computed in this task (float64 or mpmath, sampled along one orbit unless stated otherwise). A sampled
  supremum is only a lower estimate of the true supremum.
- **estimate:** this note's arithmetic or judgement; its method is stated next to it.
- **literature:** a published claim, cited.

Read first: [`sjsu-gate2.md`](sjsu-gate2.md) (gate 2 = T2-CONF), [`sjs-rigor-plan.md`](sjs-rigor-plan.md),
[`sjsu-lean-rigor-astra.md`](sjsu-lean-rigor-astra.md) §5C, [`sjsu-model-recovery.md`](sjsu-model-recovery.md),
[`hd11964-pilot.md`](hd11964-pilot.md) and [`../campaign/design/HD11964-PILOT.md`](../campaign/design/HD11964-PILOT.md).

## 0. Summary

**Gate 2's theorem does not lift to the full problem by itself.** `sjsu_secular_confinement` concerns the truncated
order-2 polynomial `SJSU18-O2`. That polynomial differs from the true averaged dynamics of the planar four-body
problem at the 10⁻²–10⁻³ level: its secular frequencies are 1.6 %, 0.35 % and 0.05 % from N-body
(`sjsu-model-recovery.md:15-16`), and its 5:2 quartic is 5–8 % off. The certified secular rates are about 10⁻²⁰ per
year.
- **Estimate:** pulled back into the full problem, gate 2's observables F_j would confine only for about 10³ yr (§2.5).
- **What is needed instead:** secular observables of a *rigorously averaged* full Hamiltonian, built at a higher
  order in the masses.
- **What gate 2 contributes:** the tube checker, the charts, the packed Fourier–Taylor layer and the method.

**The full problem has a cheaper backbone than the secular route: AMD plus fast-action drift.**
- **Measured:** SJSU is well below the planar strong-AMD collision threshold of track LP: C/B = 0.166 at the
  nominal point and at most 0.181 along 2·10⁴ yr. The binding pair is Saturn–Uranus, B = 6.04·10⁻³ against
  C = 1.00·10⁻³; the absolute margin is B − C ≥ 4.93·10⁻³.
- **Consequence:** "no orbit crossing for |t| ≤ T" needs only a certified drift bound on the three fast actions Λ_j.
  That is the HD 11964 route, `KAM/Application/LambdaDrift/`, already generic in n.
- **Free eccentricity bounds:** the AMD bound also gives upper eccentricity bounds (e_J ≤ 0.067, e_S ≤ 0.105,
  e_U ≤ 0.224 with the drift windows of §1.2). Gate 2's secular intervals add only the lower bounds and sharper upper
  bounds for Saturn and Uranus.

**But the current LP helper's budget is too tight for SJSU, and a cheaper short-horizon route exists.**
- **Λ oscillation (measured):** Λ_J and Λ_S oscillate over 3.0·10⁻⁴ and 3.8·10⁻⁴ along the orbit.
- **The budget:** `LiftData.budget` (n r + Ω_B(r) ≤ δ/4) with `DriftData.ok` (range(F − Λ) < d ≤ r/2) then needs
  about 2.3·10⁻³ against δ/4 = 1.23·10⁻³: **FAIL as stated.**
- **Fix:** an ordinary, non-frozen sharpened helper. It uses per-planet radii, bounds the range of Σ_j(Λ_j − F_j)
  jointly (measured 1.0·10⁻⁴ against 7.3·10⁻⁴ for the sum of the separate ranges), and uses the margin δ − m in place
  of δ/4. It closes the budget with room to spare (§2.3).
- **Short horizons need no AMD:** for T ≲ 10³–10⁴ yr the secular variables move little. A *joint* first exit with
  averaged Λ_j and averaged (ξ_j, η_j) on a small box then gives explicit semi-major-axis and eccentricity intervals,
  and explicit separations of at least 2.9 AU between orbits, with no AMD argument at all.

**Realistic horizons (estimate; gate SF-1 measures them).** Each order of fast averaging gains roughly 10²–10³ in T
here. That is less than HD 11964's 10³ per order, because of the 5:2 (k·n = −7.1·10⁻³), 1:−7 (6.1·10⁻³) and
three-body (2, −6, 3) (4.0·10⁻³, first degree in e) near-resonances.

| Rung | Content | Fast order | Region | Kernel CPU (estimate) | Verdict |
|---|---|---:|---|---:|---|
| FULL-A1, T = 10³ yr | no crossing, explicit a and e intervals, gaps ≥ 2.9 AU | 1 (2 if SF-1 fails) | small box around today's state | 5–75 CPU-h (order 1); 3·10³–2·10⁴ (order 2) | **go after HD 11964's rehearsal** |
| FULL-A2, T = 10⁶ yr | no crossing; AMD-ball eccentricity caps | 2–3 | whole AMD ball, 8-D modulo rotation | 10⁵–10⁷ | **no-go** locally; funded project at best |
| FULL-B, T ≥ 10⁶ yr | adds secular eccentricity intervals | 3–4 fast; secular at mass order ≥ 3 | secular tube | ≥ 10⁶ | **no-go**; a research problem |
| 5·10⁹ yr | the gate-2 headline for the full problem | ≥ 4–5; resonant normal form for 3λ_J − 5λ_S − 7λ_U | — | out of reach | **not a target** (§4.6, chaos) |

**Recommendation.**
1. Keep T2-CONF unchanged as the secular result, with its docstring's caveat.
2. Scope the first full-problem theorem as **FULL-A1 at T = 10³ yr**: the HD 11964 engine at n = 3, order-1 fast
   averaging, a small region, about 5–9k new Lean lines, most of them shared with HD 11964 and X1.
3. Run gates SF-1, SF-2, SF-4 and SF-6 (Python, under 3 CPU-h in total) before any Lean.
4. Sequence it after HD 11964's two-cell rehearsal; HD's full run is itself 400–620 CPU-h and awaits an owner decision.
5. Section 5.4 lists 9 owner decisions.

## 1. Candidate target theorems

### 1.1 Model of record (full problem)

- **Hamiltonian.** LP's frozen moving-Sun Hamiltonian `movingHamiltonian G m0 m μ`
  ([`KAM/Frozen/Planetary/Defs/MovingHamiltonian.lean:44`](../../KAM/Frozen/Planetary/Defs/MovingHamiltonian.lean)),
  with n = 3. It is the planar four-body problem in canonical heliocentric (Poincaré) variables, Féjoz (28).
  - It is exactly SLG13's eq. (1): the Kepler terms have reduced mass β_j = m0m_j/(m0 + m_j), plus the indirect
    kinetic term Σ r̃_i·r̃_j/m0 (`sjsu-model-recovery.md:62-79`).
  - LP's solution notions apply: `IsMovingSolutionOn` and `MovingUniqueOn`, and the barycentric
    `IsNewtonSolutionOn` clause used by LP1.
- **Masses.** `m_j = μν_j` with ν = (1, M_J/M_S, M_J/M_U) and μ = 1/1047.355, from the dataset's exact reciprocals
  1047.355, 3498.5 and 22902.98.
- **Units.** G·m0 = 1 in AU, so one model time unit is 1/(2π) yr.
- **Today's state z⋆.** SLG13 Table 1 read as Poincaré elements and mapped to heliocentric canonical Cartesian
  coordinates, as an exact rational literal. This is the reading of `sjsu-model-recovery.md` §5.2.
  - **Do not use the other reading.** Read as heliocentric osculating elements, Table 1 puts Jupiter–Saturn into an
    almost exact 5:2 resonance (2n_J − 5n_S = −0.0007 rad/yr), contradicting the source.
  - **So the full-problem dynamics is sensitive at 10⁻³ in momenta**, and z⋆ must be pinned by an explicit literal
    and its provenance (decision 2).
- **Initial set Q.** A sup-norm ball of radius ρ about z⋆ in (q, p). It is not a claim about the real Solar System's
  uncertainty ellipsoid (§4).

### 1.2 FULL-A1: no orbit crossing with explicit elements, T = 10³ yr (recommended first target)

In words: for every planar initial state z₀ with ‖z₀ − z⋆‖∞ ≤ ρ, the planar Newtonian four-body solution exists
and is unique on [−T, T], and for every t with |t| ≤ T and every planet j:
1. the osculating Kepler semi-major axis a_j(t) lies in [a_j^lo, a_j^hi];
2. the osculating eccentricity e_j(t) lies in [e_j^lo, e_j^hi];
3. every heliocentric distance is at least q_min, and every mutual distance satisfies
   |r_i(t) − r_j(t)| ≥ q_{j}^min − Q_{i}^max ≥ 2.9 AU for i < j (explicit, not LP0's existential `dStar`/`dPair`).

Constants (estimate, to be fixed by SF-1/SF-2):
- T = 10³ yr = 2π·10³ model units.
- ρ = 10⁻⁷ (AU and AU per model time unit).
- a_j windows of about ±0.25 % (J), ±0.7 % (S) and ±0.4 % (U): Λ windows d = (7, 8, 1)·10⁻⁴, about twice the
  measured oscillation of each Λ_j (§2.3).
- e_j windows: today's value ± the secular and great-inequality motion over 10³ yr ± the short-period oscillation.
  - **Measured:** the 200-yr-mean (ξ, η) move at most 6.4·10⁻⁶ per yr (Saturn) and 3.7·10⁻⁶ per yr (Jupiter).
  - That is 6.4·10⁻³ over 10³ yr, about 0.28 |z_S|: e_S ∈ about [0.035, 0.075], e_J ∈ about [0.04, 0.06], and e_U
    nearly frozen.
- With the AMD caps instead (no secular box), the explicit annuli of §1.3 already give gaps of 2.96 AU (J–S) and
  4.28 AU (S–U).

**Lean shape (sketch; not built; hard rules apply verbatim to any realization).** (1) Never use
`set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design
signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not elaborate at
default heartbeats, report it as a design signal. (2) No Lean file may exceed 1500 lines of code. When a file
approaches the cap, split it into focused modules, preserving public import paths as cheap facades.

```lean
/-- FULL-A1 (sketch): planar Newtonian SJSU, no orbit crossing for |t| ≤ T, explicit osculating elements. -/
theorem sjsu_full_noCrossing (z₀ : Phase (3 * 2))
    (hz₀ : ∀ k, |z₀.1 k - sjsuZStar.1 k| ≤ ρ ∧ |z₀.2 k - sjsuZStar.2 k| ≤ ρ) :
    ∃ z : ℝ → Phase (3 * 2), z 0 = z₀ ∧
      IsMovingSolutionOn sjsuNu sjsuMu (Set.Icc (-T) T) z ∧
      MovingUniqueOn sjsuNu sjsuMu (Set.Icc (-T) T) z ∧
      ∀ t ∈ Set.Icc (-T) T,
        (∀ j, aLo j ≤ keplerAxis sjsuNu (z t) j ∧ keplerAxis sjsuNu (z t) j ≤ aHi j) ∧
        (∀ j, eLo j ≤ planeLength (keplerEccVector sjsuNu (z t) j) ∧
              planeLength (keplerEccVector sjsuNu (z t) j) ≤ eHi j) ∧
        (∀ j, qMin ≤ planeLength (bodyVector (z t).1 j)) ∧
        (∀ i j, i ≠ j → gapMin ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j))
```

- **The elements** are LP's frozen heliocentric Kepler elements at mass vector ν, not SLG13's Poincaré β-elements.
  The two differ by O(μ). `ReducedElements.lean` (`keplerAxis_redMass`) switches between them exactly, if the owner
  prefers the β-elements.
- **The separation clause** follows from the element clauses through the frozen LP lemmas `PlaneLengthLeSourceKeplerApo`
  and `SourceKeplerPeriLePlaneLength`: for i < j, |r_i − r_j| ≥ |r_j| − |r_i| ≥ q_j − Q_i.
- **Kind:** a literal application, so **freeze approval is needed** (decisions 1–3). No KAM theorem enters.

### 1.3 FULL-A2: the AMD route, T = 10⁶ yr (scoped, not recommended now)

- **Same shape as FULL-A1**, with eccentricity *caps* from the AMD bound (no lower bounds) and the LP0 barrier for no
  crossing. It is the HD 11964 theorem at n = 3.
- **Measured (exact formula, float evaluation):** explicit annuli from a strong-AMD cap C ≤ C_max and absolute action
  windows ±dΛ (`annuli.json`).

  | C_max, dΛ | e_max (J, S, U) | perihelion min (AU) | aphelion max (AU) | gap J–S | gap S–U |
  |---|---|---|---|---:|---:|
  | 1.2·10⁻³, (4, 5, 0.6)·10⁻⁴ | 0.067, 0.105, 0.224 | 4.85, 8.52, 14.88 | 5.56, 10.60, 23.57 | 2.96 | 4.28 |
  | 1.5·10⁻³, (8, 10, 1.2)·10⁻⁴ | 0.075, 0.117, 0.250 | 4.80, 8.36, 14.34 | 5.61, 10.77, 24.14 | 2.75 | 3.57 |
  | 2.0·10⁻³, (16, 20, 2.4)·10⁻⁴ | 0.086, 0.135, 0.288 | 4.73, 8.11, 13.55 | 5.68, 11.05, 25.00 | 2.43 | 2.50 |

- **The drift tolerance is the lever.** With the crude bound C(t) ≤ C₀ + Σ|ΔΛ_j| and a uniform relative drift of
  5·10⁻³, the S–U gap closes (−1.2 AU). The AMD route therefore needs relative Λ-drift ≲ 10⁻³ together with joint
  bookkeeping of Σ(Λ − F) (§2.3).

### 1.4 FULL-B: adding the secular eccentricity intervals

- **What it adds:** two-sided e_j intervals in the spirit of T2-CONF, [0.026, 0.062], [0.009, 0.085] and
  [0.006, 0.063], for a horizon comparable to the secular periods (5·10⁴–6·10⁵ yr) or longer.
- **What it requires (§2.4):** secular observables of the rigorously averaged full Hamiltonian, pulled back through the
  fast normalization, in one joint first exit with the fast actions.
- **Horizon:** it only becomes more than FULL-A1 once T exceeds about 10⁴ yr, so it inherits FULL-A2's costs at least.

### 1.5 Realistic T

- **10³ yr (FULL-A1)** covers about one great-inequality period (880 yr), 84 Jupiter and 12 Uranus orbits. It is the
  realistic first rung.
- **10⁶ yr** is the realistic ceiling of a funded effort, on the HD 11964 ladder (one more order per factor
  10²–10³).
- **Gigayear horizons** need fast order ≥ 4. They also need a resonant treatment of 3λ_J − 5λ_S − 7λ_U and its
  secular subresonances, one of which is within 1·10⁻⁶ rad/yr of exact resonance in the model (§2.6). Not realistic.

## 2. The route

### 2.1 Architecture

Use one first-exit theorem with a vector of approximate integrals F = (F^Λ_J, F^Λ_S, F^Λ_U, F^sec_1, …), not two
nested theorems.
- **The engine:** `KAM.Application.Confinement.hamiltonian_approxIntegrals_confinement`
  ([`ApproxIntegral.lean:295`](../../KAM/Application/Confinement/ApproxIntegral.lean), proved).
  - W is the collision-free open set where `movingHamiltonian` is C².
  - D is the tube {|F_k − c_k| < width_k}. It has compact closure: bounded actions and eccentricities bound
    positions and momenta.
  - The conclusion supplies existence, uniqueness and drift ≤ η_k|t|.
- **Working in the Poincaré chart Ψ:** LP's `liftChartHam ν μ` = H∘Ψ
  ([`KAM/Planetary/Exponential/Lift.lean:53`](../../KAM/Planetary/Exponential/Lift.lean)) and the chart lift of
  stopped orbits (`KAM/Planetary/StrongAMD/ChartLift/`) already do this for the Λ-only bridge (`Bridge.lean`).
  The rate is the chart bracket `pb (F k) (liftChartHam ν μ)`
  ([`LambdaDrift/Poisson.lean:42`](../../KAM/Application/LambdaDrift/Poisson.lean)).
- **New ordinary Lean (A1-J):** a chart version of `hamiltonian_approxIntegrals_confinement` whose region is cut out
  by fast *and* secular observables. It generalizes `stoppedDrift_of_approxIntegrals` (Bridge.lean:85) from "Λ within
  d, chart AMD ≤ C₀ + nd" to "Λ within d, (ξ, η) within the secular box".
- **For FULL-A2:** keep the AMD clause and LP0 instead of the box.

### 2.2 Which approximate integrals, and why direct observables

**Direct truncated Lie observables, as in HD 11964 (design §6.1–6.2):**
F^Λ_j = exp(L_{−χ₁})⋯exp(L_{−χ_N}) Λ_j, truncated at μ^N, with generators χ_k solving the fast homological equations
over the actual divisors k·ω(Λ).
- **The identity layer.** `pb_approxIntegral₂` ([`LieRemainder.lean:187`](../../KAM/Application/LambdaDrift/LieRemainder.lean))
  writes the rate as five terms: Fourier-tail residuals plus brackets of order μ·tail, μ³ and μ³. Each term is bounded
  separately, so the kernel never sees an O(μ) cancellation (proved for N ≤ 2).
- **Why not an explicit canonical map Φ.** A pullback F^sec∘Φ⁻¹ through Lie time-one maps would need:
  - flow existence and symplecticity on certificate domains (`KAM/Canonical/FlowInverse.lean` and `Symplectic.lean`
    exist, but not in certificate form);
  - inverse-domain coverage;
  - Lie-series remainders with derivatives.

  The direct observable needs none of these, only the identity and the term bounds.
- **Secular observables in the full problem:** F^sec_j(full) = exp(L_{−χ₁})⋯ F^sec_j truncated, with F^sec_j a gate-2
  type near-torus observable of the averaged secular Hamiltonian H̄. Its rate splits as
  {F^sec_j(full), H} = {F^sec_j, H̄_N} + (fast residual terms) + (higher brackets):
  - the first term is a gate-2 check (`checkTube`), but on H̄_N, not on `SJSU18-O2`;
  - the others are the HD-type terms with F^sec in place of Λ.
- **Lean gap.** The identity is proved for N ≤ 2 only. Order N with N generators is new ordinary Lean (A1-L,
  1–2k lines). The pattern is fixed by `LieRemainder.lean`'s proof: antisymmetry, {I_k, G} = −D_kG, the derivation
  rule and Jacobi.

### 2.3 The bounds needed on {F, H_full}

**FULL-A1 (box route), T = 10³ yr, rates in action units per year (estimate):**
- **Fast actions: η^Λ_j·T + range(F^Λ_j − Λ_j) < d_j**, with d_j the half-width of the Λ window. For a ±0.15 % axis
  window uniform in Λ/Λ\* (7.5·10⁻⁴ relative), d would be (4.0, 1.6, 0.36)·10⁻⁴.
  - **Measured along the orbit:** the Λ ranges are 3.0·10⁻⁴, 3.8·10⁻⁴ and 4.6·10⁻⁵, i.e. 0.75×, 2.4× and 1.3× those
    windows: Saturn's oscillation (1.7·10⁻³ relative, mostly the great inequality and the J–S synodic terms) alone
    overflows a uniform window. The windows are therefore set per planet from the range of F − Λ, about twice the
    oscillation: d ≈ (7, 8, 1)·10⁻⁴, i.e. axis windows of about ±0.25 %, ±0.7 % and ±0.4 %. SF-1 measures the
    ranges over the region, not along one orbit.
  - **Budget:** η^Λ·T ≲ d/2, i.e. η^Λ ≲ (3.5, 4, 0.5)·10⁻⁷ per yr at T = 10³ yr. The raw rate (order 0, F = Λ) is **measured** at
    sup |Λ̇| = 6.1·10⁻⁵, 6.5·10⁻⁵ and 7.8·10⁻⁶ per yr, so one needs a gain of about 10²–10³: order 1 at the edge, order 2
    safely (SF-1).
- **Secular variables: η^sec·T + range(F^sec − z) < box half-width.** With order-1 averaged (ξ, η), the rate is the
  secular plus great-inequality motion: **measured** ≤ 6.4·10⁻⁶ per yr, against a raw (short-period) sup of
  4.6·10⁻⁴ per yr. Over 10³ yr that needs a box half-width of about 10⁻² in (ξ, η) units. That box also bounds the AMD
  region trivially.
- **Face condition (ApproxIntegral `hsep`):** on ∂D some |F_k − c_k| exceeds its window plus T·η_k. With box-shaped D
  in the chart variables this is the HD/gate-2 face check.

**FULL-A2 (AMD route).**
- **What `LiftData` needs:** `budget` n·r + Ω_B(r) ≤ δ/4 (`KAM/Planetary/StrongAMD/ChartLift/Stopped.lean:51`), and
  `DriftData.ok` η_iT + (hi_i − lo_i) < d ≤ r/2 (`NoCrossing.lean:61`).
- **The SJSU numbers:**
  - δ ≤ B − C = 4.93·10⁻³, so δ/4 = 1.23·10⁻³.
  - Ω_B(r) ≈ 0.1–0.3·r (**measured**, finite differences of B).
  - (hi − lo) ≥ about 3.8·10⁻⁴ (the oscillation of Λ_S), so d > 3.8·10⁻⁴, r ≥ 7.6·10⁻⁴ and n·r ≥ 2.3·10⁻³ > δ/4.
  - **FAIL as stated.**
- **Sharpened helper (new ordinary Lean, A1-S, 0.4–0.8k lines):**
  1. per-planet radii r_j, with C(t) ≤ C₀ + Σ_j|ΔΛ_j| replaced by the joint bound
     C(t) − C₀ = Σ(Λ_j(t) − Λ_j(0)) ≤ Σ(F_j drift) + range(Σ_j(Λ_j − F_j)).
     The joint range is about 7× smaller (**measured** along the orbit: 1.03·10⁻⁴ against 7.33·10⁻⁴), because
     Jupiter and Saturn exchange Λ almost conservatively;
  2. margin δ − m in place of δ/4, with m > 0 kept for LP0. The δ/4 is a proof constant of LP-CONF's generic
     helper (`StrongAMD/Confinement.lean:169`), not a physical requirement.

  It is an ordinary theorem with new names; the frozen LP0/LP1 are untouched.

**FULL-B (secular intervals).** For a tube of width δ_sec = 10⁻⁶ in Γ units (gate 2's) at horizon T, η^sec ≤ δ/(2T).
That is 5·10⁻¹⁰ per yr at 10³ yr, 5·10⁻¹³ at 10⁶ yr, and 10⁻¹⁶ at 5·10⁹ yr.
- **Fast remainder.** The fast-averaging remainder after mass order N contributes about μ^{N+1}·n·Λ/|z|, with
  μ ≈ 10⁻³ and |z| ≈ 0.03 (estimate). Hence N ≥ 3 for 10⁶ yr and N ≥ 4–5 for gigayears.
- **Secular part.** H̄_N must itself be computed to mass order N (§2.5).

### 2.4 The secular part: what replaces SJSU18-O2

- **What it would take.** H̄_N is the angle-independent part of the order-N fast normal form of `movingHamiltonian`,
  with every truncation enclosed:
  - Fourier order in λ: Laplace tails α^k with α_JS = 0.545, α_SU = 0.497, so K ≈ 25 for 10⁻⁵ relative and K ≈ 60 for
    10⁻¹⁶;
  - eccentricity degree;
  - the Λ-expansion;
  - mass order.
- **Why SLG13's truncations do not qualify.** |k| ≤ 16, degree 18, Kepler quadratic and perturbation linear in L, and
  order 2 with a hand-picked μ⁴ resonant term. At |k| ≤ 16 the pointwise truncation error is about 10⁻³
  (`sjsu-model-recovery.md:101-102`).
- **Size (estimate).** A dense global Fourier–Taylor H̄ at 3-D Fourier support K ≈ 60 and degree 18 in six complex
  secular variables would hold about 5·10⁵ modes × 7·10³ monomials per charge class, about 4·10⁹ coefficients:
  infeasible in Python, let alone the kernel. Hence the cell decomposition (§3) and low local Taylor degree, which make
  FULL-B a different engineering problem from gate 2's single global tube.

### 2.5 How far gate 2's own F_j survive in the full problem (estimate; gate SF-4)

- **The extra rate.** {F_j, H_full-averaged} = {F_j, SJSU18-O2} + {F_j, ΔH}, where ΔH is the true minus the model
  secular Hamiltonian.
- **Its integrable part** (frequency shifts) nearly commutes with F_j.
- **Its angle-dependent quartic part** is about 5 % of SJSU18-O2's quartic, |H₄| ≈ 1.8·10⁻²·|z|⁴ ≈ 7·10⁻⁹. That gives
  |{F, ΔH}| ≈ 3·10⁻¹⁰ per yr, and with gate 2's δ = 10⁻⁶, T ≈ δ/(2η) ≈ 1.5·10³ yr.
- **Consequence.** The secular theorem's 5·10⁹ yr does not survive; its F_j are as good as a crude bound at
  millennium scale.
- **Gate SF-4 measures this** with an alternative secular model: the order-3 Lie mimic (`lie_mimic.py`) or an
  N-body-fitted quadratic part.

### 2.6 Near-resonances (measured divisors, `scales.json`)

Mean motions are N-body (`applications/sjsu/validation/astar.json`). "e-degree" is the minimal eccentricity degree
|Σk| (d'Alembert).

| k = (k_J, k_S, k_U) | k·n (rad/yr) | n_J/|k·n| | e-degree | Role |
|---|---:|---:|---:|---|
| (3, −5, −7) | −1.00·10⁻³ | 529 | 9 | SLG13's resonant step; three-body, mass order 2 |
| (2, −6, 3) | +3.98·10⁻³ | 133 | 1 | **three-body, first degree in e**; not in SLG13's list (it has \|k\|₁ = 11 > K_F = 8) |
| (1, 0, −7) | +6.11·10⁻³ | 87 | 6 | 7:1 J–U |
| (2, −5, 0) | −7.11·10⁻³ | 74 | 3 | great inequality |
| (0, 1, −3) | −1.11·10⁻² | 48 | 2 | 3:1 S–U |

- **Fast normal form.** All of these are non-resonant on the fast scale. They are solved in the generators with their
  actual divisors k·ω(Λ) over the Λ window (HD's method), so they cost amplification, not a resonant normal form.
  - (2, −6, 3) enters at mass order 2 with a first-degree-in-e amplitude; it is the first term to check in SF-1's
    order-2 rate.
  - (3, −5, −7) has divisor about n_J/529 but amplitude about μ²e⁹.
- **The two-scale split fails for (3, −5, −7).** With secular frequencies g ≈ 10⁻⁵–1.1·10⁻⁴, the combinations
  k·n + p·g with Σp = 9 include (p = (9, −3, 3)) one at **+1.0·10⁻⁶ rad/yr** (e-degree 15) with the model's g and
  κ·n\*. The near-resonant tail continues with (9, −2, 2) at 9.6·10⁻⁶ and (9, −1, 1) at 1.8·10⁻⁵.
  - **The exact resonance is model-dependent.** With the N-body κ·n = −1.002·10⁻³ the same combination sits at
    −1.9·10⁻⁵, and the model's g are off by up to 1.6 %.
  - **Agreement with the literature:** these are the three-body subresonances whose overlap is reported to make the
    outer planets chaotic (Murray–Holman 2001; §6).
  - **Consequence:** fast-angle averaging cannot remove them, and they are irrelevant below about 10⁶ yr, since their
    amplitudes are of order μ²e¹⁵.
  - **Beyond about 10⁷ yr** a resonant normal form would be needed: keep the harmonic and confine by energy plus the
    transverse combinations b·Λ, b·k = 0. `ApproxIntegral` allows it (F may include the normalized energy).

## 3. Reuse of the repository

| Component (path) | Status | Reuse for SJSU-FULL | Gap |
|---|---|---|---|
| First exit `hamiltonian_approxIntegrals_confinement` (`KAM/Application/Confinement/ApproxIntegral.lean:295`) | proved | the engine of FULL-A1/B | chart version with mixed fast and secular region (A1-J) |
| Λ-drift bridge and no crossing (`KAM/Application/LambdaDrift/Bridge.lean:85`, `NoCrossing.lean:121`, `ObservableNoCrossing.lean:95`) | proved, generic n ≥ 2 | FULL-A2 directly at n = 3 | budget too tight for SJSU: sharpened helper A1-S (§2.3) |
| Order-1/2 Lie remainder identities, Poisson calculus, rotation invariance (`LieRemainder.lean`, `LieRemainderChart.lean`, `Poisson.lean`, `Rotation.lean`) | proved, generic | rate decomposition; cover modulo rotation | order N ≥ 3 (A1-L) |
| Reduced elements and ranges (`ReducedElements.lean`, `ReducedRange.lean`, `Threshold.lean`) | proved | choice of elements in the statement; threshold lower bounds | S–U pair is not star-dominated: `liftData_of_star` does not apply (B = 6.0·10⁻³ < Λ_U = 0.047) |
| LP strong AMD: LP0 barrier (`KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean`), LP-CONF, LP-LIFT, spatial mirror (`KAM/Planetary/Spatial/`) | sealed / proved | no-crossing backbone; AMD caps; spatial route exists | LP1's μ₀ is existential and needs Diophantine mean motions: it cannot be instantiated at the real masses |
| HD 11964 engine (`applications/hd11964/`, branch `hd-layer`; status `docs/campaign/side/hd11964-status.json`) | partly built: packed Taylor × Fourier, Cauchy bound, generator remainder and cell glue proved; ramp, Kepler check and production theorem in progress | **the same engine at n = 3**; the cell cover; the Kepler witness | 3 fast angles; 9 local variables; pair-structured evaluation |
| T2-CONF packages N2–N7 (`KAM/EffectiveStability/Tube/*`) | in progress / audited | tube checker for FULL-B's {F^sec, H̄_N}; Cayley rotation; polar chart; B^{±1/2} witnesses | H̄_N is no longer a literal 7,941-term polynomial |
| Track N (`KAM/Nekhoroshev/`), planetary exponential stability (`KAM/Planetary/Exponential/`) | proved, asymptotic | Lift/chart infrastructure (`liftChartHam`, `chartSafe`), analytic domains | asymptotic constants are not explicit; no numeric horizon at μ = 10⁻³ |
| Program B (`program-b-plan.md`), `KAM/Canonical/Lie.lean` `taylor_lie` | partly proved | the explicit-Φ alternative to direct observables | not recommended (§2.2) |
| v2 / packed certifier (`KAM/CertificateSharp/Packed/`) | proved (LG00) | `PEnc` products, `jChain` evaluators, inv/sqrt/exp witnesses | 3-D blocks under the `Nat` limit; shared need with X1 (SX-2) |
| SO-3 kernel lessons (`lean-kernel-nat-literal-hash.md`) | measured | whitened literals; ≤ 4–8 GB per declaration; one heavy lane; data in an opt-in library; replay sample | must be applied from the first production module |

**What does not transfer.**
- **LP1** (`planar_strongAMD_exponentialSafety`) holds for μ ≤ μ₀ with μ₀ existential and Diophantine Kepler
  frequencies. It says nothing at μ = 9.5·10⁻⁴, and SJSU's mean motions are not certified Diophantine.
- **Track N's** exponentially long times are asymptotic.
- **Gate 2's** T = 5·10⁹ yr is a statement about another Hamiltonian.

## 4. Model gaps and their cost

The full-problem theorem is still about a *model*. Each gap below is either inside the statement (paid by
certificates) or a declared modelling choice.

### 4.1 Truncation remainders (inside the statement: FULL-A, FULL-B)

- **None in FULL-A.** `movingHamiltonian` is exact; the truncations are in F, not in H. The kernel evaluates H's
  derivatives through the Kepler witness and inv/sqrt witnesses on |r_i − r_j|, so every Fourier, Taylor and degree
  tail goes into the certificate's radii.
- **Cost:** the Fourier cutoff K is driven by α_JS = 0.545.
  - K ≈ 25 suffices for the 10⁻⁵ relative accuracy of a 10³-yr rung (the tail k·α^k ≈ 10⁻⁵ at K = 25).
  - K ≈ 50–60 is needed for 10⁻¹⁵–10⁻¹⁶ (gigayear secular rates).

### 4.2 Mass-order truncation of the secular model (FULL-B only)

- **The gap:** SJSU18-O2 is strict order two. The printed three-planet quartic needs order 3
  (`sjsu-model-recovery.md:19-24`), and the frequencies are 0.05–1.6 % off.
- **For FULL-B,** H̄ must be built at mass order N ≥ 3 inside the certificate. Cost: the 3-D generators (§5.1).

### 4.3 Planarity

- **The real AMD margin barely moves.** Inclinations to the invariable plane (J 0.32°, S 0.93°, U 1.02°; literature
  values) add Σ Λ_j i_j²/2 ≈ 4.5·10⁻⁵ to the AMD, 4.5 % of C (estimate). C/B rises from 0.18 to about 0.19.
- **Lean:** the spatial LP route exists (`KAM/Planetary/Spatial/`: chart lift, first exit, spatial exponential
  safety). A spatial `movingHamiltonian` statement is a new frozen application.
- **Certificates:** three more secular pairs, i.e. 12 local variables instead of 9. Jet-pair counts rise about 3×
  at degree 3, and the secular box gains 6 dimensions.
- **Verdict:** keep the theorem planar (decision 4) and say so in the docstring; the planar subspace is invariant, so
  the planar theorem is honest about the planar model.

### 4.4 Neptune

- **Measured:** with Neptune (J2000-like a = 30.07 AU, e = 0.0086, M_N = 1/19412.24) the binding pair becomes U–N,
  with B = 2.88·10⁻³ and C/B = 0.348. Still AMD-stable, but the margin halves.
- **New near-resonance:** U–N is near 2:1 (2n_N − n_U ≈ 1.4·10⁻³ rad/yr, period about 4.5 kyr, first degree in e).
- **Cost:** a fourth fast angle, so 4-D Fourier blocks and 12 local variables, about 10–100× FULL-A's arithmetic
  (estimate).
- **Verdict:** a model choice, not an error term. SJSU without Neptune is SLG13's model; "the outer Solar System"
  needs SJSUN (decision 5).

### 4.5 General relativity and other physics

- **1PN size:** a relative correction of 3GM/(c²a) ≈ 6·10⁻⁹ at Jupiter. It causes perihelion precession of about
  0.006″ per yr against secular g of a few ″ per yr, about 0.15 % of the secular frequencies, and no Λ-drift at first
  order (estimate).
- **Irrelevant for FULL-A;** for FULL-B it is a frequency shift of the same order as the mass-order gap.
- **Lean cost to include:** a velocity-dependent 1PN term in the Hamiltonian, about 0.5–1k lines plus a new frozen
  model.
- **Out of scope:** solar oblateness, the terrestrial planets, the Galactic tide and stellar flybys. They are
  negligible at 10³ yr and modelling choices at gigayears.

### 4.6 Initial data and chaos

- **The model's "today".** z⋆ is SLG13 Table 1 under the Poincaré reading. A theorem for a ρ-ball about it is not a
  theorem about the real Solar System's uncertainty set.
- **The real-ephemeris alternative** (a JPL state projected on the invariable plane) is an owner decision (2) and a
  new provenance chain.
- **Chaos.** Outer-planet chaos (Murray–Holman 2001; Hayes 2007: whether the outer Solar System is chaotic depends on
  initial data within the observational uncertainty) means no KAM-type all-time statement should be expected near
  today's state. It does not prevent finite-time confinement: the diffusion it drives is extremely slow
  (Lecar–Franklin–Holman 2001 put outer-planet instability times far beyond the age of the Solar System), so
  FULL-A/B remain consistent with the dynamics.

## 5. Costs, gates, plan, owner decisions

### 5.1 Lean lines (estimate, overlapping with HD 11964 and T2-CONF)

| Package | Content | New lines | Shared with |
|---|---|---:|---|
| A1-D | statement, masses, z⋆ literal, constants; freeze texts | 0.2–0.4k | pattern of T2-CONF N1 |
| A1-J | chart first exit with fast and secular observables; explicit separations from element bounds | 0.6–1.2k | generalizes `Bridge.lean` |
| A1-S | sharpened LP helper (per-planet radii, joint Σ(Λ − F) range, margin δ − m) — FULL-A2 only | 0.4–0.8k | LP-CONF |
| A1-L | order-N Lie remainder identity with N generators; secular-observable variant | 1–2k | HD order 3–4 |
| A1-P | pair-structured evaluation: per-pair 2-D Fourier × 6-variable Taylor models of f_ij and χ_ij; bracket bounds by norm products (no 3-D products at order 1) | 0.5–1k | HD layer |
| A1-K | three Kepler witnesses; cover modulo rotation for n = 3 | 0.3–0.6k | HD (300–400 lines each) |
| A1-3D | 3-D packed blocks for order-2 generators (only if SF-1 needs order 2) | 1–2k | X1/M3 (SX-2) |
| A1-G | production glue, opt-in library `KAMSJSUFull` (D51), provider | 0.5–1k | T2-CONF N7 |
| **Total, FULL-A1 order 1** | | **3.5–7k** | |
| **Total, FULL-A1 order 2** | | **4.5–9k** | |
| FULL-B additions | H̄_N certificate, secular observables through the identity, tube check on H̄_N | +3–6k | T2-CONF N3–N6 |

At 100–200 lines per prover-hour (the rate `sjs-rigor-plan.md` §5 uses): 25–70 prover-hours for FULL-A1 at order 1,
plus auditing.

### 5.2 Kernel CPU and certificate size (estimate)

**Calibration (HD 11964 design §7, estimates built on the measured LG00 packed rates):**
- 0.5 s of kernel per packed 2-D product on a 51×51 to 97×97 box;
- 2–5× all-in;
- order 1: 10³ products per cell, 0.15 CPU-h; order 2: 10⁴ products per cell, 1.5 CPU-h;
- 50–200 cells over HD's AMD ball.

**FULL-A1 order 1:**
- **All 2-D objects.** Each f_ij and χ_ij depends on one pair's (λ_i, λ_j, ΔΛ_i, ΔΛ_j, z_i, z_j): 2-D Fourier × 6
  Taylor variables, HD's own shape. The order-1 bracket term {D_kχ₁, P} is bounded by Σ sup|∂D_kχ| · sup|∂P| over
  pair models, so no 3-D product is formed.
- **Per cell:** about 3 pairs × 0.15 = 0.5 CPU-h kernel, plus three Kepler witnesses.
- **Cells:** the small box (8-D modulo rotation, thin) needs 5–30.
- **Total:** **3–15 CPU-h kernel, 6–75 all-in.**
- **Ledger:** about 1–10 GB (HD node sizes, 0.125 GB per node held, streamed).
- Fits the local box with one heavy lane.

**FULL-A1 order 2:**
- **3-D objects.** χ₂ couples pairs through {χ_JS, f_SU}: 3-D boxes of about 51³ = 1.3·10⁵ slots, 14× LG00's full box;
  jets in 9 variables.
- **Per cell:** about 10² CPU-h kernel (HD order 2 × 3 pairs × 14 × 2–3 for the jets).
- **Total over 5–30 cells:** **3·10³–2·10⁴ CPU-h kernel.** Rented hardware; above HD's whole 10³-yr run.

**FULL-A2 (AMD ball, order 2–3):** cells grow 10–100× over HD's region (8-D against 5-D modulo rotation): **10⁵–10⁷
CPU-h. No-go.**

**FULL-B:** adds the secular H̄_N at mass order ≥ 3 with K ≈ 50–60: **≥ 10⁶ CPU-h. No-go.**

### 5.3 Go/no-go gates (before any Lean)

E1-report style: literal criteria; report the failing term; never shrink Q silently.

- **SF-0 AMD-MARGIN.** Done here (**measured**): C/B ≤ 0.181 along 2·10⁴ yr; B − C ≥ 4.93·10⁻³; binding pair S–U.
  PASS.
- **SF-1 RATE-LADDER** (≤ 30 CPU-min, ≤ 4 GB). Extend `applications/hd11964/scripts/normal_form.py` to n = 3 and
  measure on the FULL-A1 box (cells sampled, not just the orbit): sup|{F^{(N)}_Λ, H}| for N = 0, 1, 2, and the range of
  F − Λ, against the exact gradient of `movingHamiltonian`.
  - PASS iff order 1 closes T = 2·10³ yr at margin 2.
  - FAIL: order 2, with SF-3 deciding the price.
- **SF-2 SECULAR-BOX** (≤ 20 CPU-min). The same for the order-1 averaged (ξ_j, η_j): rates, ranges, the box
  half-widths and the resulting e_j intervals.
  - PASS iff every e-interval has width ≤ 0.05 and the gaps are ≥ 2 AU.
- **SF-3 3-D-PRODUCT** (≤ 1 CPU-h; one targeted throwaway kernel build, shared with X1's SX-2). One real-size 51³
  product. Only if SF-1 fails.
- **SF-4 MODEL-GAP** (≤ 30 CPU-min). {F_j^{gate2}, H_alt} on gate 2's tube, with H_alt the order-3 Lie-mimic secular
  model or a quadratic part fitted to N-body.
  - Reports the horizon for which gate 2's observables would survive the model change (estimate here: about 10³ yr).
  - Informs FULL-B only.
- **SF-5 JOINT-RANGE** (≤ 30 CPU-min; FULL-A2 only). range(Σ_j(Λ_j − F_j)) over the AMD-ball region, not along one
  orbit.
  - PASS iff the sharpened budget closes with margin 2.
- **SF-6 RESONANCE-CENSUS** (≤ 10 CPU-min). Divisors k·ω(Λ) over the Λ window for |k|₁ ≤ 20, the generator amplitudes
  of (2, −6, 3) and (3, −5, −7), and their subresonances against the model's and N-body's secular frequencies.

### 5.4 Staged plan

| Stage | Content | Effort | CPU | Calendar |
|---|---|---|---:|---|
| S-0 | owner decisions 1–9 | — | — | — |
| S-1 | SF-1, SF-2, SF-4, SF-6 (Python) | one numerics worker | ≤ 3 CPU-h | 1–2 weeks |
| S-2 | wait for HD 11964's two-cell rehearsal; reuse its measured per-cell cost | — | — | HD's calendar |
| S-3 | A1-D statement; statement audit; freeze | 5–10 prover-h | — | 1 week |
| S-4 | A1-J, A1-L, A1-P, A1-K (and A1-3D if order 2) | 25–70 (order 1) or 35–90 (order 2) prover-h | builds | 3–6 weeks |
| S-5 | production run, opt-in library | — | 6–75 (order 1) or 3·10³–2·10⁴ (order 2) CPU-h | 1–2 weeks (order 1) |
| S-6 | seal audits, `#print axioms`, replay sample | auditor | ≤ 10 CPU-h | 1 week |

FULL-A2 and FULL-B are re-scoped only after S-5 reports measured per-cell costs.

### 5.5 OWNER DECISIONS

1. **First full-problem target.** (a) FULL-A1 at T = 10³ yr, with no crossing and explicit a, e intervals and gaps;
   (b) FULL-A2 at 10⁶ yr through AMD; (c) FULL-B; (d) none until HD 11964 completes.
   **Recommended: (a), sequenced after HD 11964's rehearsal (≈ (d) for the Lean, (a) for the gates).**
2. **Initial point of record.** (a) SLG13 Table 1 under the Poincaré reading, as for SJSU18-O2; (b) a JPL state
   projected on the invariable plane, with a new provenance chain.
   **Recommended: (a)**, with the docstring saying it is the model's initial datum.
3. **Initial set and elements.** (a) a sup-norm ρ-ball in heliocentric canonical (q, p), with LP's frozen heliocentric
   elements in the conclusion; (b) the same with reduced (Poincaré β) elements through `ReducedElements.lean`.
   **Recommended: (a)**; the docstring names the elements.
4. **Planar.** Keep planar (recommended) or go spatial on `KAM/Planetary/Spatial/`, at about 3× the certificate cost.
5. **Neptune.** (a) SJSU (SLG13's model; recommended for the first rung); (b) SJSUN, 10–100× the arithmetic and a
   halved AMD margin.
6. **Sharpened LP helper (A1-S).** Approve the ordinary non-frozen theorem now (cheap, also useful for other
   exoplanet systems), or defer it with FULL-A2. **Recommended: defer**; FULL-A1 does not need it.
7. **Direct observables versus an explicit canonical Φ.** **Recommended: direct observables** (HD's identity route);
   Φ only if FT observables become too dense.
8. **Compute envelope.** Gates ≤ 3 CPU-h now; production ≤ 100 CPU-h local for order 1; order 2 only with an explicit
   allocation and rented hardware.
9. **Wording.** T2-CONF stays a secular-model theorem. No README or headline may say "the Solar System" or "the full
   problem" before an S-5 theorem is sealed, and even then "the planar Newtonian SJSU model".

## 6. Literature context and honest novelty

- **Secular SJSU and SJS.**
  - Sansottera–Locatelli–Giorgilli 2013 (SLG13; Math. Comput. Simul. 88, 1–14) and Giorgilli–Locatelli–Sansottera
    2017 (GLS17; RCD 22, 54–77) construct the secular SJSU model
    through Kolmogorov-like fast averaging at order two in the masses and estimate effective stability of the secular
    dynamics through Kolmogorov and Nekhoroshev normal forms.
  - Their stability statements concern the secular model and are computer-assisted estimates, not claims about
    `movingHamiltonian`'s orbits. GLS17 also notes the order-two approximation (`sjsu-effective-stability.md:40-60`).
  - Locatelli–Giorgilli 2000 (CMDA 78, 47–74) and 2007 treat secular and planetary SJS tori.
- **Laskar.**
  - Long-term numerical integrations and the chaotic inner Solar System (Laskar 1989, 1994; Laskar–Gastineau 2009).
  - The AMD and AMD-stability (Laskar 1997, 2000; Laskar–Petit 2017, A&A 605 A72). Laskar–Petit classify systems as
    AMD-stable when the AMD cannot allow collisions, a secular criterion that assumes no mean-motion resonance.
  - LP's strong AMD threshold (this repository's track LP) is a sharpened planar form. The SJSU computation of §0 is
    ours (Appendix A); Laskar–Petit's own Solar System classification was not re-checked here.
- **Outer-planet chaos.**
  - Sussman–Wisdom 1992 (the Jovian subsystem is chaotic).
  - Murray–Holman 2001 (Nature 410, 773–779): chaos from overlapping three-body mean-motion resonances among Jupiter,
    Saturn and Uranus.
  - Hayes 2007 (Nature Physics 3, 689–691): whether the outer Solar System is chaotic depends on initial data within
    the observational uncertainty.
  - The (9, −3, 3) subresonance of §2.6 is consistent with that picture. Neither 2001 paper's exact resonance list was
    re-read for this note (decision 9 keeps the wording neutral).
- **Rigorous computer-assisted celestial mechanics.**
  - Celletti–Chierchia 2007 (Memoirs AMS 187): KAM for a restricted three-body model with realistic parameters.
  - Caracciolo–Locatelli 2020 (JCD 7): rigorous finite normal-form remainder estimates.
  - Rigorous KAM tori in secular exoplanet models: Locatelli and co-authors, recalled and not re-verified here.
  - Interval-arithmetic secular SJS work: Locatelli–Giorgilli 2000.
  - Asymptotic theorems: Arnold, Herman–Féjoz, Chierchia–Pinzari, Niederman's planetary Nekhoroshev, Pinzari; see
    `planetary-and-nekhoroshev.md`.
- **Novelty, honestly.** As far as this scoped (not exhaustive) search goes, no published result, machine-checked or
  interval-validated, bounds the orbits of the *full* (unaveraged) Newtonian planar SJSU problem with explicit
  constants over any stated horizon.
  - A sealed FULL-A1 would be a modest but genuine first: a kernel-checked, explicit-constant, finite-time no-crossing
    theorem for a four-body planetary model at real masses.
  - Its horizon (10³ yr) is short by astronomical standards, and numerical integrations show far longer stability.
  - The value is the rigour and the reusable engine, not a new astronomical fact.
  - HD 11964 (three bodies) would precede it in this repository.
  - Do not claim "first proof of Solar System stability", "Nekhoroshev for the Solar System", or any gigayear statement
    for the full problem.

## 7. Uncertainties, errata, deviations

**Uncertainties.**
- **Orbit samples, not region sups.** Every measured rate and range is sampled along one orbit (Table 1, 2·10⁴ yr,
  dt = 0.5 yr). Region sups are larger: HD saw 3–5× at the high-e end of its region.
- **Gain per order.** The 10²–10³ gain per averaging order is a judgement from HD's measured 10³ and SJSU's divisors;
  SF-1 replaces it.
- **Cost scaling.** The 3-D cost factor (14× per product) and the cell counts (5–30, 10–100× HD) are scalings, not
  measurements.
- **§2.5's** 10³ yr horizon for gate 2's observables is an order-of-magnitude estimate.
- **Literature recalled but not re-fetched:** inclinations, Neptune's elements and the novelty survey; flagged in the
  text.

**Suspected errata (pinned sources).** None new.
- Not an erratum: SLG13's list of handled near-resonances (5:2, 7:1, 3:−5:−7) omits the three-body (2, −6, 3) with
  k·n = 4.0·10⁻³ and first degree in e. It is a mass-order-2 combination outside SLG13's K_F = 8 and is legitimately
  absent from a first-order generator. It matters for a full-problem order-2 certificate (SF-6).
- Already recorded elsewhere: SJSU-E1–E4 and the "3λ₁ − 5λ₅ − 7λ₃" typo (`sjsu-model-recovery.md` §6.3).

**Non-source observation.** `LiftData.budget`'s δ/4 and `DriftData.ok`'s d ≤ r/2 are LP-CONF proof constants. For
SJSU they are binding (§2.3), but they are not defects. The fix is the additive helper A1-S; no frozen statement
changes.

**Deviations from the brief.**
- §0 calls the AMD route "cheaper than the secular route" and recommends FULL-A1 without the secular F_j: the brief's
  suggested route (secular F_j pulled back plus Λ_j) is scoped as FULL-B and judged out of reach.
- The scratch scripts reuse `applications/sjsu/scripts/nbody.py` (run with sys.path, not `-I`, since mpmath and numpy
  are user-site packages); they read but do not modify it.

## Appendix A. Computations of this note (reproducible formulas)

All under `nice -n 10`, each under 1 CPU-min and under 1 GB, in `.drafts/sjsu-full/` (uncommitted):
- `amd_threshold.py` → `amd_threshold.json`;
- `lambda_osc.py` → `lambda_osc_2e4.json`;
- `scales.py` → `scales.json`;
- `annuli.py` → `annuli.json`.

1. **Strong AMD threshold** (mpmath, 30 digits), with LP's definitions.
   - B(I) = min(min_j I_j, min over adjacent (i, j) of min over u, v ∈ [0, 1] with a_i(1 + u) ≥ a_j(1 − v) of
     I_iD(u) + I_jD(v)), where D(e) = 1 − √(1 − e²) and a_j = (I_j/ν_j)².
   - The minimum lies on the boundary v = 1 − a_i(1 + u)/a_j: a 4,001-point scan, then golden section.
   - With I = Λ\* and a = a\* (dataset): B_JS = 2.110·10⁻², B_SU = 6.039·10⁻³, min Λ = Λ_U = 4.747·10⁻²; B = 6.039·10⁻³.
   - C = 1.0015·10⁻³ (raw Table 1 AMD, `sjsu-model-recovery.md:181-183`), so C/B = 0.166.
   - AMD-ball eccentricity caps at Λ\*: 0.0609, 0.0955, 0.2043.
   - With Neptune: B_UN = 2.88·10⁻³ and C/B = 0.348.
2. **Orbit sampling.** Planar N-body flow from Table 1 (Poincaré reading), WH democratic-heliocentric, 4th order,
   dt = 0.5 yr, 2·10⁴ yr (the repository's `nbody.py` integrator). Along it:
   - Λ_j = β_j√(μ_ja_j) (Poincaré) and the LP heliocentric Λ_j = m_j√(m₀a_j) with v = p/m_j;
   - strong AMD C(t) = ΣΛ_j − |L|, with |L| conserved to 3.7·10⁻¹⁴;
   - B(Λ(t)) − C(t) ≥ 4.93·10⁻³ and C/B ≤ 0.181;
   - Λ ranges 3.03·10⁻⁴, 3.79·10⁻⁴, 4.60·10⁻⁵; the range of ΣΛ_j is 1.03·10⁻⁴;
   - sup|Λ̇_j| = 6.05·10⁻⁵, 6.45·10⁻⁵, 7.84·10⁻⁶ per yr (finite differences);
   - sup|d(ξ, η)/dt| ≤ 4.65·10⁻⁴ per yr, with 200-yr-mean rates ≤ 6.4·10⁻⁶ per yr;
   - e ranges J [0.0475, 0.0607], S [0.0107, 0.0574], U [0.0436, 0.0490].
3. **Divisors.** k·n for primitive k ∈ [−8, 8]³ with the N-body mean motions of `astar.json`. Subresonances
   κ·n\* + p·g, Σp = 9, |p_j| ≤ 12, with the SJSU18-O2 frequencies |ν| = (1.1212·10⁻⁴, 1.9677·10⁻⁵, 1.1134·10⁻⁵).
4. **Annuli.**
   - e_max = √(1 − (1 − C_max/(Λ\* − dΛ))²);
   - a ∈ a\*((Λ\* ± dΛ)/Λ\*)²;
   - perihelion a_lo(1 − e_max), aphelion a_hi(1 + e_max).
