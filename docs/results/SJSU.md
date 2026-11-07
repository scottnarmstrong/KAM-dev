# Five billion years of confinement in a secular Sun–Jupiter–Saturn–Uranus model (SJSU gate 2, T2-CONF)

**Status:** proved; freeze and seal in progress (2026-11-07) · proved theorem
`KAM.EffectiveStability.SJSU.sjsu_secular_confinement_proof` (on `main` since 2026-11-07) · approved frozen statement
`KAM.EffectiveStability.sjsu_secular_confinement` with data `KAM.EffectiveStability.sjsu18O2` (D76; staged on branch
`inp-sjsu-g2`, not yet on `main`) · axioms of the proved theorem: standard only (`propext`, `Classical.choice`,
`Quot.sound`)

## In brief

Secular models of the planets average out the fast orbital motion and keep the slow evolution of eccentricities.
`SJSU18-O2` is such a model for the planar Sun–Jupiter–Saturn–Uranus system: an explicit polynomial Hamiltonian in
three degrees of freedom, with 7,941 exact rational coefficients. The theorem says that every initial state within
10⁻⁶ of the nominal present-day secular state has a unique solution of this model for at least 5·10⁹ years in both
time directions, and that along it the model's eccentricities of Jupiter, Saturn and Uranus stay in explicit
intervals. It is a theorem about this truncated secular model, not about the full Newtonian solar system.

## Exactly what is proved

Lean: [`sjsu_secular_confinement_proof`](../../KAM/EffectiveStability/SJSU/Confinement/Proof.lean). The approved frozen
statement `sjsu_secular_confinement` has the same type (the Lean expressions are checked equal; the proved copy is only
reflowed to 100 columns). Its text is in
[`docs/explorations/sjsu-g2-t2conf-proposal.md`](../explorations/sjsu-g2-t2conf-proposal.md); at the freeze it goes to
`KAM/Frozen/EffectiveStability/SJSU/SecularConfinement.lean` in the opt-in library `KAMSJSU`.

### The model

Lean: [`sjsu18O2`](../../KAM/EffectiveStability/SJSU/Model/SJSU18O2.lean), with rows in
[`KAM/EffectiveStability/SJSU/Model/`](../../KAM/EffectiveStability/SJSU/Model/) (development copies, byte-identical to
the approved text; at the freeze they become facades of `KAM/Frozen/EffectiveStability/SJSU/`).

- **Phase space.** x = (η, ξ) ∈ ℝ³ × ℝ³, index j = 0, 1, 2 for Jupiter, Saturn, Uranus. η = x.1 are the coordinates and
  ξ = x.2 the momenta: η̇_j = ∂H/∂ξ_j, ξ̇_j = −∂H/∂η_j. These are Poincaré secular variables; Γ_j = (ξ_j² + η_j²)/2
  below is the j-th planet's angular-momentum deficit. Units: AU, year, G = 1; time t is in years.
- **Hamiltonian.** With z_j = (ξ_j − i η_j)/√2,

  H(η, ξ) = Re Σ_rows c · z_J^{a_J} z̄_J^{b_J} z_S^{a_S} z̄_S^{b_S} z_U^{a_U} z̄_U^{b_U},

  a sum over 7,941 rows (a_J, b_J, a_S, b_S, a_U, b_U, c) with natural exponents and coefficients c ∈ ℚ, read exactly
  from 25-significant-digit decimals. The rows are pinned in six parts by SHA-256 of their definition text. The total
  degrees are even, from 2 to 18, and each row has Σ(a − b) = 0, so H is invariant under the common rotation
  z ↦ e^{is}z. The sum is real; Re only fixes the type.

### The theorem

Let ξ* = (0.03446271128616895, −0.0014352339355918572, −0.010122263133599879) and
η* = (−0.009080669615926963, −0.025602508346796338, −0.0016540224121661881) (exact decimals), and let
Λ* = (0.53993226066969503769, 0.21912825008425995084, 0.047474331515411474555), the dataset's reference actions of
Jupiter, Saturn and Uranus. For a state x set

  Γ_j(x) = (ξ_j² + η_j²)/2,  e_j(x) = √(1 − (1 − Γ_j(x)/Λ*_j)²),

which inverts Γ_j = Λ*_j (1 − √(1 − e_j²)).

**Hypothesis.** z₀ = (η⁰, ξ⁰) ∈ ℝ³ × ℝ³ with |ξ⁰_j − ξ*_j| ≤ 10⁻⁶ and |η⁰_j − η*_j| ≤ 10⁻⁶ for j = 0, 1, 2 (the closed
sup-norm ball of radius 10⁻⁶ about z* = (η*, ξ*)).

**Conclusion.** There exist T₁ > 5·10⁹ and z : ℝ → ℝ³ × ℝ³ such that

- z(0) = z₀ and ż(t) = X_H(z(t)) for every t ∈ (−T₁, T₁);
- **uniqueness:** every y defined on an order-connected set I ∋ 0 with y(0) = z₀ and ẏ = X_H(y) on I equals z on
  I ∩ (−T₁, T₁);
- **eccentricity bands:** for every |t| ≤ 5·10⁹ years,

  | Planet | j | Λ*_j | band for e_j(z(t)) |
  |---|---|---|---|
  | Jupiter | 0 | 0.53993226066969503769 | [0.026, 0.062] |
  | Saturn | 1 | 0.21912825008425995084 | [0.009, 0.085] |
  | Uranus | 2 | 0.047474331515411474555 | [0.006, 0.063] |

The only premise is z₀ in the ball. Everything else (the tube, the observables, the rates) is internal to the proof.

## What is assumed and what is not claimed

- **A truncated secular model, not the solar system.** `SJSU18-O2` is planar, averaged over the fast orbital angles,
  restricted to four bodies, and truncated: strictly second order in the planetary masses, expanded to degree 18 in the
  secular variables, built along the published recipe (first-order expansion, two Kolmogorov-like steps, a resonant
  normalization step). It is a reconstruction published in
  [`applications/sjsu/`](../../applications/sjsu/), not the original authors' file. Nothing is asserted about the
  osculating elements of the full Newtonian problem, about the effect of the neglected terms, or about the inner planets.
- **Meaning of e_j.** e_j is a fixed-reference secular-model observable computed from Γ_j with constant Λ*_j (at fast
  action L = 0), as the frozen docstring states.
- **Model of record** (D75): the 7,941-term rotation-invariant complex form. The 38,466-term real form was not chosen
  because its independently rounded coefficients break rotation invariance at about 2·10⁻³⁴.
- **Nominal point.** z* is a published Table 1 state read as Poincaré elements and mapped to secular variables; the
  radius 10⁻⁶ is not a claim about observational uncertainty.
- **Finite time.** 5·10⁹ years, both directions. No all-time statement and no invariant torus is asserted.
- **Kernel replay pending.** Building the library checks every declaration in Lean's kernel, including the 4,687
  modules of `KAMSJSU` (generated certificate data and checkers). The separate full independent kernel replay of those
  modules, part of the seal procedure, has not been completed yet.

## Sources and proof

The model follows M. Sansottera, U. Locatelli, A. Giorgilli, *On the stability of the secular evolution of the planar
Sun–Jupiter–Saturn–Uranus system* (Math. Comput. Simulation 88 (2013); arXiv:1010.2609, Tables 1–2, §§2–3), and
A. Giorgilli, U. Locatelli, M. Sansottera (2017; arXiv:1702.04894), §2. Its regeneration and the deviations from the
printed data are recorded in [`docs/explorations/sjsu-model-recovery.md`](../explorations/sjsu-model-recovery.md).

The proof is a confinement-from-approximate-integrals argument
([`hamiltonian_approxIntegrals_confinement`](../../KAM/Application/Confinement/ApproxIntegral.lean); see [B.md](B.md)),
with no KAM theorem. In a modal polar chart, shifted by a numerically computed near-invariant torus graph, the proof
uses a tube of action half-width 2·10⁻⁶ and three observables f_j close to the shifted actions. Kernel-checked
exact computations (packed trigonometric and Taylor models, a bracket ledger of generated modules) bound the drift
rates |{f_j, H}| by η = (6, 23, 22)·10⁻¹⁹ per year on the tube, so T·η_j ≤ 1.15·10⁻⁸ < δ/2 = 5·10⁻⁷ at T = 5·10⁹. The
generic tube theorem `tubeChart_confinement`
([`Tube/Check/TubeChart.lean`](../../KAM/EffectiveStability/Tube/Check/TubeChart.lean)) turns these checks, the face
bounds and the initial-ball bounds into the conclusion. A separate grid enclosure proves the two-sided eccentricity
bands on the whole tube (owner ruling (a) of D75). The proof is assembled in
[`Confinement/Statement.lean`](../../KAM/EffectiveStability/SJSU/Confinement/Statement.lean) and
[`Confinement/Proof.lean`](../../KAM/EffectiveStability/SJSU/Confinement/Proof.lean).

Decisions D74–D76 in [`docs/DECISIONS.md`](../DECISIONS.md); program overview
[`docs/explorations/sjsu-gate2.md`](../explorations/sjsu-gate2.md); scoping plan
[`docs/explorations/sjs-rigor-plan.md`](../explorations/sjs-rigor-plan.md); decision log
[`docs/explorations/sjsu-g2-decisions.md`](../explorations/sjsu-g2-decisions.md).
