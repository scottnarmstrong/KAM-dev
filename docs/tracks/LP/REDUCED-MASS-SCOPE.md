# Track LP: scope of a reduced-mass Kepler split (scoping note)

Date 2026-11-02. Branch `lp-redmass-scope` (off main `067f57f6d`). Documents only: no Lean, no
freeze, no build. *est.* marks an estimate. The handoffs `HD11964-COVER-D.md` and `HD11964-CELLS.md`
named in the brief are on no ref of this clone (`b69013057` carries P2A/P2B only). Their figures
(`F_b − Λ_b ≈ 2–5·10⁻⁴`, a ~7× cut, 10³-yr margin 5.9 → ~15) are quoted as theirs. They agree with
`docs/campaign/design/HD11964-PILOT.md:225-228` and
`docs/campaign/handoffs/HD11964-PILOT.md:101-106`.

**Short answer.** The reduced-mass elements are already the frozen elements at another mass vector.
No frozen definition changes, and a successor would change no frozen statement's content. The gain
lives in two non-frozen quantitative lemmas; an application bridge of 300–500 lines (*est.*)
captures it.

## 0. The key identity (hand algebra, not yet checked in Lean)

Put `s_i = √(1+μν_i)` and `ν'_i = ν_i/s_i`. The Kepler summand of `movingHamiltonian 1 1 ν μ`
(`KAM/Frozen/Planetary/Defs/MovingHamiltonian.lean:46-47`) is `E^red_i = (1/ν_i + μ)|p_i|²/2 −
ν_i/|q_i|`: the split of MAIN (1) (`source/MAIN.md:19-23`) with the diagonal `μ|p_i|²/2` of `f`
moved into Kepler. MAIN:39 fixes "central Kepler parameter one". The frozen bodies
(`Defs/KeplerEnergy.lean:35-36`, `KeplerAxis.lean:36-37`, `KeplerAction.lean:36-37`,
`KeplerEccVector.lean:36-40`) give:

- `keplerEnergy ν' z i = s_i|p|²/(2ν_i) − ν_i/(s_i|q|) = E^red_i / s_i`;
- `keplerAxis ν' z i = −ν_i/(2E^red_i)`, the semi-axis of Kepler with mass `β_i = ν_i/s_i²` and
  central parameter `s_i²`;
- `keplerAction ν' z i = β_i·s_i·√a_i = Λ^red_i`, the reduced Delaunay action;
- `keplerEccVector ν' z i` is the reduced eccentricity vector (its coefficient is `s²/ν² =
  1/(β²M)`).

`totalMomentum` (`TotalMomentum.lean:36-37`) is split-free, so `strongAMD ν' z = ΣΛ^red − |L|` has
the AMD structure of MAIN (2). The spatial bodies have the same form
(`Spatial/Defs/SpatialKeplerAxis.lean:29`, `SpatialKeplerAction.lean:29`,
`SpatialKeplerEccVector.lean:32`).

**Consistency check.** To first order, `Λ^red_i − Λ_i = μν_iΛ_i(a_i/|q_i| − 1) + O(μ²)`. This has
mean zero along the orbit and range `≈ 2μν_iΛ_ie_i`: for b, `2·5.23·10⁻⁴·1.79·0.1 ≈ 1.9·10⁻⁴`,
against the measured 2.1·10⁻⁴. The cap is this genuine oscillation of the heliocentric `Λ_b`.

## (1) Which frozen declarations would change

- **Track P definitions (D20/D25): no successor.** The dynamics is split-free: `movingHamiltonian`,
  `IsMovingSolutionOn`, `MovingUniqueOn`, `IsNewtonSolutionOn`, `actualMasses`, the barycentric
  maps, `bodyVector`, `plane*`, `NoCollision`, `totalMomentum`, the exponents.
  `keplerEnergy/Axis/Action/EccVector` (and `physicalAMD`, track P only) are parametric in the mass
  vector; the reduced version is their instantiation at `ν'`.
- **LP definitions (D62, 89): no successor body.** The element side is instantiated at `ν'`:
  - planar: `strongAMD`, `keplerPeri/Apo`, `SourceCanonicalPhase` (`E < 0` at `ν'` ⇔ `E^red < 0`),
    `sourceStrongAMD`, `sourceKeplerPeri/Apo`;
  - spatial: `spatialKepler{Energy,Axis,Action,EccVector,Peri,Apo}`, `SpatialNegativeEnergy`,
    `SpatialElliptic`, `SpatialSourceCanonicalPhase` and the
    `SpatialSource{Kepler*,PlanetAngularMomentum,AngularMomentum,StrongAMD}` carriers;
  - the 34 characterization theorems quantify over every `ν > 0`, so they hold at `ν'` at no cost.
- **Unchanged under any reading.**
  - The actual-velocity osculating family `osc*`/`sourceOsc*`/`spatialOsc*` and its carriers. It is
    already physical (`OscVelocity.lean:29-30`; `OscParam.lean:28`, `k = 1+μν`).
  - Every threshold: `actionAxis`, `chamber`, `eccDeficit`, `pairFeasible/Objective/Threshold`,
    `AdjIdx`, `upperIdx`, `OrderedActions`, `ordered{Pair,Cross,Strong}Threshold`. Each is a
    function of `(ν, I)` only, and `a^red = (Λ^red/ν')²`: the reduced threshold is the same formula
    at `ν'`.
- **Anchors.**
  - **LP0** (`StrongAMD/Theorems/PlanarStrongAMDBarrier.lean:47-73`) is static and holds for every
    `ν > 0`, so the reduced-mass LP0 *is* LP0 at `ν'`.
  - **LP1, LP1-H, LP2, LP2-H** (D62) and **LP3 planar/spatial `_noArith`** (D64,
    `PlanarStrongAMDExponentialSafetyNoArith.lean:68-113`) bind one `ν` to both the dynamics and the
    elements, and assume `∃ i, ν i = 1`, `ν ≤ 1` (`PlanarStrongAMDExponentialSafety.lean:62`), which
    `ν'` violates. A reduced-mass version needs **6 v2 anchors** (dynamics at `ν`, elements at
    `redMass ν μ`) and **1 new definition** `redMass ν μ i = ν i / √(1 + μ ν i)`. That is the
    complete successor set, out of the 130 D62/D64 entries.

## (2) Proof transfer

- **Route (a): successors from the v1 anchors plus a comparison.** Bound `‖Λ^red − Λ‖∞`, `‖a^red −
  a‖∞` and `|e^red − e|` by `C_K μ` on compacts of physical states (*est.* 200–300 lines, from §0).
  This transfers the drift (`O(μ) ≤ μ^{b_n}`, absorbed in `A_Λ`, `A_a`), the barriers (LP0 at `ν'`),
  and the premise `C^red(0) ≤ B_{ν'}(Λ^red) − δ` ⇒ `C(0) ≤ B_ν(Λ) − δ + O(μ) + Ω_B(O(μ))`. Two
  obstructions remain:
  - **(i) the exact `δ/2` conclusion.** A black box gives `δ/2 − O(μ)`, and re-instancing `δ` cannot
    recover it. Prove from the implementation's `3δ/4` core instead
    (`StrongAMD/Confinement.lean:59`).
  - **(ii) the Diophantine premise of LP1/LP2 at `ω(I⁰)`.** It is not stable under the `O(μ)` shift
    of `I⁰`. Reopen the finite-cutoff step (`NonresonantAdapter*`, `NonresonantReuse`,
    `DiophantineBridge`), or keep the premise at heliocentric actions (a hybrid). LP3 has no such
    premise.
- **Route (b): re-run with the reduced split as the chart Hamiltonian.** The `ν'` chart gives
  `h^red(Λ) = −Σν³/(2(1+μν)Λ²)` (μ-dependent frequencies) and an `f` without the diagonal `|p_i|²`.
  - Re-prove or retarget: `PlanarDictionary`, `ChartLift` (518 lines), `AnalyticDomain` (1465; new
    `f`), `NonresonantAdapter/Rescale/Scale/Reuse` (~930; ω depends on μ), `Nek` (2156),
    `Confinement` (270; two mass vectors), `Osculating` (974), `PlanarSafety` (1359), and the
    `Spatial/*` mirror (~11.9k).
  - Reused at `ν'`: `Threshold`, `Momentum`, `Orbital`, `Geometry`, `Modulus`.
- **Does either route improve a frozen statement? No.** Every dynamic anchor states existential
  constants (`μ₀, c, T₀, A_Λ, …`) with drift `A_Λ μ^{b_n}`. The split moves only unstated constants,
  and the `O(μ)` oscillation lies below the stated drift scale. The HD 11964 margin is the explicit
  budget of two **non-frozen** lemmas: `strongFirstExit_of_stopped_drift`
  (`Confinement.lean:170-188`) and `stoppedDrift_of_approxIntegrals`
  (`KAM/Application/LambdaDrift/Bridge.lean:85-99`). The latter needs `η_i T + (hi_i − lo_i) < d ≤
  r/2`, and `hi − lo`, the range of `F_i − Λ_i`, contains the genuine oscillation.

## (3) Cost against payoff (*est.*)

| | Route (a) successor | Route (b) | Bridge (§4) |
|---|---|---|---|
| Lean lines | 1,000–2,000 | 5–10k touched | 300–500 |
| Time | 2–4 days, 2 provers | 2–4 weeks | 1–2 prover-days |
| Audits | 4–6 (statement, seal, 2–3 package, deviation) | ≥ 8 | 1 |
| Freeze/seal | proposal 0.5–1 day; ~2.5 h after approval (D62/D64) | same | none |

- **Payoff of (a)/(b):** nothing in the frozen statements, plus a deliberate deviation from the
  pinned source's split (MAIN:39) that would need a source amendment.
- **Payoff of the bridge:** the HD 11964 gain (theirs: 5.9 → ~15 at 10³ yr), and the same for
  compact or eccentric systems, where `2μνΛe` grows against `d`.

## (4) Recommendation: no successor (unless a source revision asks for one); land a bridge

Add `KAM/Application/LambdaDrift/ObservableBridge.lean` (non-frozen). The inner first exit is driven
by an observable `G` (here `G_i = keplerAction (redMass ν μ) ∘ lpChart`), and the range of `G − Λ`
is charged against `r/2 − d`, not against `d`.

```lean
theorem stoppedDrift_of_approxIntegrals_obs (hd : LiftData ν U z₀ δ r) {μ T d ε : ℝ}
    (G F : Fin n → Phase (n + n) → ℝ) (R O : Set (Phase (n + n))) (η lo hi loG hiG : Fin n → ℝ)
    (hO : IsOpen O) (hRO : R ⊆ O) (hF : ∀ i, DifferentiableOn ℝ (F i) O)
    (hGc : ∀ i, ContinuousOn (G i) (chartSafe ν))
    (hGΛ : ∀ i, ∀ w ∈ chartSafe ν, ‖fast w.2 - actionVector ν z₀‖ < r →   -- the stopped tube
      loG i ≤ G i w - fast w.2 i ∧ G i w - fast w.2 i ≤ hiG i)
    (hR : ∀ w ∈ chartSafe ν, (∀ i, |G i w - G i w₀| ≤ d) →               -- w₀ : the lift of z₀
      chartAMD w ≤ strongAMD ν z₀ + n * (d + ε) → w ∈ R)
    (hη : ∀ i, ∀ w ∈ R, |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ η i)
    (hFG : ∀ i, ∀ w ∈ R, lo i ≤ F i w - G i w ∧ F i w - G i w ≤ hi i)
    (hd0 : 0 < d) (hT : ∀ i, η i * T + (hi i - lo i) < d) (hε : ∀ i, hiG i - loG i ≤ ε)
    (hdr : d + ε ≤ r / 2) :
    <the hstop conclusion of stoppedDrift_of_approxIntegrals, verbatim>
```

- **Proof:** Bridge's first exit with `y = G(w u) − G(w 0)`. While `|y| < d`, the Λ-drift is `< d +
  ε < r`, the AMD stays `≤ C₀ + n(d+ε)` (`strongAMD_sub_eq_sum`), and `w ∈ R`. The mean value step
  gives `|y| ≤ ηT + (hi − lo) < d`. Finally the Λ-drift is `≤ d + ε ≤ r/2`.
- **Size (*est.*):** 250–350 lines; plus `ReducedElements.lean` (80–150: `redMass`, the §0 identity,
  positivity, optionally an analytic `hGΛ` bound); plus a `noCrossing_…_obs` corollary (60–100).
- **Conclusions:** exactly LP0's heliocentric form, via the unchanged
  `strongFirstExit_of_stopped_drift`. The reduced-element barrier comes free as LP0 at `ν'`.
- **Certificate side:** cells (or the analytic lemma) also bound `G − Λ` on the stopped tube, which
  is explicit and needs no normal form. `F` is built from `Λ^red`, and the bracket stays against the
  original `H`.
- **Other options:** raise `d` toward `r/2 = 2·10⁻³` (no Lean; enlarges `R`; design:223), or the
  weighted per-planet helper (small Lean; design:229-231, owner question 5).

**Uncertainties.** §0 is hand algebra; checking it in Lean is the bridge's first item. The 7× and
the margins are the campaign's figures. Whether a `G`-defined `R` is cheaper to cover than a raised
`d` is a certificate question. Obstruction (i) assumes no frozen statement exposes the `3δ/4` slack.

**Errata and deviations.** None found. MAIN:39 is a deliberate convention, not a defect.

Rules for any Lean follow-up (verbatim):

1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat
   elaboration failure is a design signal to refactor or split the proof, not something to mask with
   a larger budget. If a proof will not elaborate at default heartbeats, report it as a design
   signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused
   modules, preserving public import paths as cheap facades.
