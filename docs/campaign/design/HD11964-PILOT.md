# HD11964-PILOT: design of a certified no-crossing time for HD 11964 (Λ-only route)

Date: 1 November 2026. Branch `hd11964` (worker HD11964-PILOT, phase 1). Status: **design only**. No Lean
is written in this phase; every Lean name below is proposed. The numbers come from the numerical gate,
[`docs/explorations/hd11964-pilot.md`](../../explorations/hd11964-pilot.md), and carry its labels:
*proved* (a Lean theorem on main), *checked* (a finite statement decided in exact rationals in Python; Lean
pending), *measured* (computed here, floating point, sampled), *estimated* (a judgement or an extrapolation),
*literature*.

## 0. Summary

- **Target theorem.** In the planar Newtonian three-body model of HD 11964 (minimum masses, coplanar), every
  solution that starts in an explicit set of initial states around the nominal one exists and is unique on
  `[-T, T]`. Along it the orbits never cross, in the exact form of LP0's conclusion (perihelion and annulus
  separations `d⋆`, `d_pair`). The initial set allows all phases and all perihelion orientations.
- **Route.**
  - The proof certifies only the drift of the two semi-major-axis actions `Λ`. Exact conservation of `L` turns
    that drift into an AMD bound (`strongAMD_sub_eq_sum`, *proved*).
  - `strongFirstExit_of_stopped_drift` (*proved*, LP lane) and LP0 (`planar_strongAMD_barrier`, *sealed*)
    then give existence, uniqueness and the barrier.
  - The drift is certified by approximate integrals `F_i ≈ Λ_i`: a fast-angle Lie normal form, with its bracket
    `{F_i, H}` bounded against the **original** Hamiltonian on the whole region.
- **The AMD margin is cheap here.** For HD 11964 the strong threshold is `B(Λ) = Λ_c`: planet c falling into the
  star binds, not the pair. The pair threshold is at least 0.79 on the whole action box (0.858 at the nominal
  point), against `Λ_c ≤ 0.0625`. A two-line monotone lower bound on the pair threshold establishes this
  (*checked* in exact rationals, `validation/threshold.json`; Lean pending); no contact problem has to be
  solved. The margin is `δ = 0.0483` (normalized), `C/B = 0.162`.
- **Gate (measured, sampled).** Whole AMD ball, `e_c` up to 0.612. The worst sampled drift rate falls by
  ≈ 10³ per order:
  - orders 0–3: `5.4·10⁻⁴, 4.2·10⁻⁷, 3.7·10⁻¹⁰, 3.3·10⁻¹³`;
  - order 4: ≈ 7·10⁻¹⁵ sampled, which is the float64 floor and bounds the true rate in neither direction;
    ≈ 3·10⁻¹⁶ extrapolated from orders 2–3.
  With margin 2 the rungs close at order 2 (10³ yr) and order 3 (10⁶ yr). Both margins (4.7) are set by the
  oscillation of `Λ_b`, not by the rate: they stay ≥ 2 with the rate multiplied by up to ≈ 180 (10³ yr) and
  ≈ 210 (10⁶ yr). The 10⁹ yr rung at order 4 is **provisional**. It closes on the float64 floor values
  (margin 3.8), and with a ×5 rigorous-design factor on the extrapolated rate or with `d = 1.5·10⁻³`, but
  order 4 is not resolved in float64.
- **Cost (estimated).** The cost is set by the order and by a cover of the slow region by 50–200 cells. With
  the packed engine, kernel time only, then all-in CPU (kernel × 2–5: per-process fixed cost and node I/O, as
  on LG00):
  - 10³ yr (order 2): 70–300 CPU-h kernel, 140–1,500 CPU-h all-in;
  - 10⁶ yr (order 3): 500–2,000 kernel, 10³–10⁴ all-in;
  - 10⁹ yr (order 4): 2.5–10·10³ kernel, 5·10³–5·10⁴ all-in, before pruning.
  Without the packed layer only order 1 (about 10² yr) is within reach: whole chains on the landed list
  arithmetic cost 8–36× the packed all-in on LG00, and from order 2 a product no longer fits 4 GB. Section 7
  gives the derivation.

## 1. Model, data and what is claimed

**Data** (`applications/hd11964/data/hd11964-pilot.json`, exact decimal rationals). The fit is Rosenthal et al.
2021 (ApJS 255, 8), as rows of the NASA Exoplanet Archive. The archive extract is committed with its SHA-256.

| | HD 11964 c (index 0, inner) | HD 11964 b (index 1, outer) |
|---|---:|---:|
| period (d) | 37.9196 ± 0.0083 | 1935.0 +9.4/−9.0 |
| e | 0.106 +0.088/−0.071 | 0.101 +0.044/−0.046 |
| ω⋆ (deg, stellar) | −30 ± 86 | 26 ± 19 |
| m sin i (M⊕) | 24.34565598 ± 1.97 | 200.54972482 ± 8.58 |
| t_c (BJD) | 2455199.94 | 2455803.0 |

The stellar mass is 1.151343 M☉, the archive value of the Rosenthal rows; M☉/M⊕ = 332946.0487 (IAU 2015).

**Model.**
- The frozen `movingHamiltonian 1 1 ν μ`: heliocentric positions, rescaled barycentric momenta, `G = 1`, star mass 1.
- `μ = m_b/M⋆ = 2005497248200/3833351025484041 ≈ 5.2317·10⁻⁴` and
  `ν = (1217282799/10027486241, 1) ≈ (0.121395, 1)`, exact rationals.
- Planet masses are the minimum masses: a common orbital plane seen edge-on, zero mutual inclination.
- The time unit is `1 yr/(2π√1.151343) = 0.148326 yr` (Gaussian `G M☉ = 4π² AU³ yr⁻²`).

**Nominal state** (*measured*, `scripts/hd11964_model.py`).
- Axes from the periods: `a = (0.231518, 3.185142)` AU.
- `Λ̂ = (0.0584106, 1.7846965)`, `Γ̂ = (3.29·10⁻⁴, 9.126·10⁻³)`, `Ĉ = 9.455·10⁻³`.
- Mean motions `(8.9769, 0.17592)` per unit, ratio 51.029.
- Phases from `t_c` (radvel convention) at the epoch BJD 2455500.0. They are irrelevant to the claim, which
  covers all phases.

**What is claimed** (when phase 2 succeeds), and what is not.
- Claimed: a theorem about the stated Newtonian point-mass model with these exact parameters.
- Not claimed:
  - true masses (`1/sin i` unknown);
  - mutual inclination (planar model);
  - tides, relativity, the stellar radius, other bodies;
  - anything about the observational uncertainty beyond the explicit initial set.
- The initial set is chosen in §2; its size is an owner question.

## 2. The Lean statement (shape)

The statement is proposed in the application package (D51: `applications/hd11964/`, namespace `HD11964`).
Only frozen definitions appear in it. `ν`, `μ`, `T`, `Λlo`, `Λhi` and `Cbar` are explicit rational literals
(`@[expose] def`s).

```lean
theorem HD11964.no_crossing :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
    ∀ z₀ : Phase (2 * 2),
      (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
      0 < totalMomentum z₀ →
      (∀ i, Λlo i ≤ keplerAction ν z₀ i ∧ keplerAction ν z₀ i ≤ Λhi i) →
      strongAMD ν z₀ ≤ Cbar →
      ∃ z : ℝ → Phase (2 * 2), z 0 = z₀ ∧ IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
        MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
        ∀ t ∈ Set.Icc (-T) T,
          (∀ i, dStar ≤ keplerAxis ν (z t) i * (1 - planeLength (keplerEccVector ν (z t) i))) ∧
          (∀ a : AdjIdx 2, dPair ≤
              keplerAxis ν (z t) a.upperIdx * (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
              keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
          (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
          (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j))
```

- **Conclusion.** It is LP0's separations, verbatim, along the solution: the osculating perihelion, the annulus
  gap, the star distance and the pair distance. `dStar` and `dPair` are existential, as in LP0. Explicit values
  would need `perihelionFloor` (`Geometry.lean`) and are optional.
- **Hypotheses.** Only typing data and source premises: physical, positive orientation, the action box and the
  AMD bound. The nominal state satisfies them for every choice of phases and perihelia: `Λ̂ ∈ [Λlo, Λhi]`
  and `Ĉ ≤ Cbar` are statements about `(a_i, e_i)` alone. A corollary states it for the elements of §1.
- **Time.** `T` is in model units. A companion lemma `HD11964.T_years` gives a rational lower bound on `T` in
  Julian years, from `π < 3.1415927` and a rational upper bound on `√1.151343`.
- **Baseline constants** (*estimated*; owner questions 1–2):
  - `Cbar = 1/100`, which covers the nominal `Ĉ = 0.009455` with 6 % to spare;
  - `Λlo, Λhi = Λ̂ ∓ (10⁻⁴, 3·10⁻³)`, which covers the 1σ period uncertainty of b (3·10⁻³ in `Λ_b`);
  - the rung `T = 6742` units (≥ 1000.0 yr), then `6.742·10⁶` and `6.742·10⁹`.

## 3. Proof architecture

```
initial set (Λ box, C ≤ Cbar, L > 0)
  │ HD11964.threshold: B = Λ_c on U, Ω_B(r) ≤ r, C(z₀) ≤ B(Λ z₀) − δ           [new, small, rational checks]
  ▼
LiftData ν U z₀ δ r  (LP-LIFT's structure: budget 2r + Ω_B(r) ≤ δ/4)             [proved structure, LP]
  │ hstop ⇐ lambdaDrift_of_certificate                                          [new: §4]
  │      ⇐ lpChartLift_of_stopped (chart solution w, Ψ ∘ w = z)                   [proved, LP-LIFT]
  │      ⇐ cellOk / coverOk (Bool) + soundness: |{F_i, H∘Ψ}| ≤ η_i, F_i − Λ_i ∈ [lo_i, hi_i] on R(d)
  ▼
strongFirstExit_of_stopped_drift: existence, MovingUniqueOn, BarrierState ν U (δ/2)   [proved, LP-CONF]
  │ planar_strongAMD_barrier (LP0) on barrier states                              [sealed]
  ▼
HD11964.no_crossing
```

**Regions.**
- `U = [Λlo − r, Λhi + r]` (a closed box) is compact and lies in the chamber (`a_c < a_b` on it, a rational check).
- The certificate region in chart coordinates is
  `R(d) = {w ∈ poincareProdDom 2 : Λ(w) ∈ [Λlo − d, Λhi + d], Γ_c(w) + Γ_b(w) ≤ Cbar + 2d}`, at every fast angle.
  - It holds every chart point a trajectory can reach while `|Λ − Λ(z₀)| ≤ d`: by `strongAMD_sub_eq_sum`
    (*proved*), `C = C(z₀) + ΣΔΛ`; by `lpChart_strongAMD`, `C = ΣΓ` on prograde states.
  - Baseline `d = 10⁻³`: `Cmax = 0.012`, `e_c ≤ 0.612`, `e_b ≤ 0.116`.
- **Two radii.**
  - `r ≤ δ/12` is the helper's tube (`n r + Ω_B(r) ≤ δ/4` with `Ω_B(r) ≤ r`, `n = 2`). With
    `δ = Λlo_c − Cbar = 0.0483`, `r ≤ 4.03·10⁻³`.
  - `d ≤ r/2` is the certified drift.
  - The certificate region is built on `d`, not on `r`: a nested first exit inside the bridge (§4) keeps the
    trajectory in `R(d)`. With `r` itself the region would reach `Cmax = 0.018` and `e_c = 0.75`, past the
    Laplace limit 0.6627, where the Fourier tails of c become long (`σ(0.75) = 0.13`).

## 4. The Λ-drift bridge (new core Lean, `KAM/Application/LambdaDrift/`)

```lean
/-- From an approximate-integral certificate on a chart region to the stopped drift of LP-CONF. -/
theorem stoppedDrift_of_approxIntegrals (hd : LiftData ν U z₀ δ r) {μ T d : ℝ}
    (F : Fin n → Phase (n + n) → ℝ) (R : Set (Phase (n + n))) (η lo hi : Fin n → ℝ)
    (O : Set (Phase (n + n))) (hO : IsOpen O) (hRO : R ⊆ O) (hOsafe : O ⊆ chartSafe ν)
    (hF : ∀ i, ContDiffOn ℝ 1 (F i) O)
    (hper : ∀ i w (k : Fin n → ℤ), F i (w + fastShift k) = F i w)
    (hR : ∀ w ∈ chartSafe ν, (∀ i, |fast w.2 i - actionVector ν z₀ i| ≤ d) →
        chartAMD w ≤ strongAMD ν z₀ + n * d → w ∈ R)
    (hη : ∀ i, ∀ w ∈ R, |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ η i)
    (hG : ∀ i, ∀ w ∈ R, lo i ≤ F i w - fast w.2 i ∧ F i w - fast w.2 i ≤ hi i)
    (hT : ∀ i, η i * T + (hi i - lo i) < d) (hdr : d ≤ r / 2) :
    <the hstop hypothesis of strongFirstExit_of_stopped_drift, with μ, T, r, z₀>
```

**Proof.**
1. On the stopped interval, `lpChartLift_of_stopped` (*proved*) gives a chart solution `w` of
   `X_{liftChartHam ν μ}` with `Ψ ∘ w = z` and `Λ(w 0) = Λ(z₀)`.
2. Let `s` be the first time `w` leaves `{|Λ − Λ(z₀)| ≤ d}`. Before `s`:
   - `hR` puts `w` in `R`;
   - the mean value inequality along `w` gives `|F_i(w u) − F_i(w 0)| ≤ η_i |u|`;
   - hence `|Λ_i(w u) − Λ_i(w 0)| ≤ η_i |u| + (hi_i − lo_i) < d`.
   By continuity `s` does not exist (a one-dimensional first exit; `gen_exit` or a direct `IsClosed`
   argument). So `‖Λ(z t) − Λ(z₀)‖ ≤ d ≤ r/2`.
3. Periodicity (`hper`) makes `F ∘ w` independent of the lift's branch. It is needed only to extend cell checks
   on a fundamental domain of the angles to all angles.

**The domain of `hF`.** `F` is `C¹` only near `R`, not on all of `chartSafe ν`. Where the orbit annuli of c and
b cross, the angle averages of `1/|q_c − q_b|` that define `F` (§6.1) are singular in the slow variables. So
`hF` is stated on an open `O` with `R ⊆ O ⊆ chartSafe ν`. The mean value step of item 2 uses it only along
the path, which stays in `R`.

**Size** (*estimated*): 500–900 lines. **Reuse:**
- `lpChartLift_of_stopped`, `StoppedOn`, `LiftData`, `chartSafe` (ChartLift, LP-LIFT);
- `strongAMD_sub_eq_sum`, `lpChart_strongAMD`, `chartAMD_eq_sum_lpGamma`;
- `abs_sub_le_of_convex`-type mean value lemmas (`KAM/Application/Observables.lean`);
- `KAM/ODE/Exit.lean`.

## 5. The AMD margin: `B` is an attained minimum, enclosed by a monotone bound

`strongThreshold ν I = min (crossThreshold ν I) (min_i I_i)`, and for `n = 2`,
`crossThreshold = pairThreshold ν I 0 1`, the `sInf` of `I_0 D(u) + I_1 D(v)` over the feasible set
`a_1(1 − v) ≤ a_0(1 + u)`, `u, v ∈ [0, 1]`.
- **Lemma** (new, `HD11964.pairThreshold_ge`).
  - `pairThreshold` is a literal `sInf`, and `sInf ∅ = 0` in ℝ. The lower bound therefore goes through
    `le_csInf` and needs the feasible set nonempty: `pairFeasible_nonempty` (the point `(1, 1)`,
    `KAM/Planetary/StrongAMD/Threshold/Pair.lean`).
  - Every feasible `(u, v)` has `v ≥ v_min = 1 − 2 a_0/a_1`.
  - `D` is increasing on `[0, 1]`.
  - So `pairThreshold ν I 0 1 ≥ I_1 D(v_min)`.
  - On all of `U`: `v_min ≥ 0.832` and `pairThreshold ≥ 0.792`, decided in exact rationals by
    `threshold_ok` (`scripts/hd11964_model.py`, `validation/threshold.json`). The Lean check is the same: a
    rational `s` with `s² ≥ 1 − v_min²` bounds the square root. Against `Λ_c ≤ 0.0625` on `U`, the slack is
    12.7×. At the nominal point the values are 0.854 and 0.858.
- **Consequence.** On `U`, `B(I) = I_0`:
  - `I_1 ≥ I_0` is a rational check;
  - the infimum is attained by the star term, and no contact equation is solved;
  - `Ω_B(r) = sup |I_0 − J_0| ≤ r`, so the budget is `3r ≤ δ/4`.
- **Margin.** `C(z₀) ≤ Cbar ≤ Λlo_0 − δ ≤ B(Λ z₀) − δ` with `δ = Λlo_0 − Cbar`.
- **Size** (*estimated*): 250–400 lines.

**The per-planet budget issue (flagged by LP-QUANT §5.2).** For HD 11964 it is benign.
- `B − C = I_0 − (I_0 + I_1 − |L|) = |L| − Λ_b`, so the margin erodes **only through `Λ_b`**. The drift of `Λ_c`
  matters only to keep `B = Λ_c`, which has a 12.7× slack.
- The helper's sup-norm budget `n r + Ω_B(r) ≤ δ/4` charges both drifts three times over. This "signed" loss
  is a factor 3 in `r` (LP-QUANT's `r_signed = 2.4·10⁻²` against `r = 8·10⁻³`).
- It is not binding: the certified drift needed is `d ≲ 10⁻³`, against `r/2 = 2·10⁻³`.
- **What does cost.** LP's Kepler split puts the reduced-mass term `μ|p_b|²/2` into the perturbation. So `Λ_b`
  itself oscillates at `O(μ ν_b √a_b e_b)`: `F_b − Λ_b` ranges over 1.5–2.1·10⁻⁴ (*measured*). That is 40 % of
  `d/2` at the baseline.
- A weighted (per-planet) helper, a new additive variant of `strongFirstExit_of_stopped_drift` in
  `KAM/Application/**`, would allow `d_b` up to `δ/8 = 6·10⁻³`. It is not needed for the rungs below.
  Recorded as owner question 5.

## 6. The approximate integrals and the certificate checks

### 6.1 Which `F`

- **Definition.** `F^{(N)}_i = exp(L_{−χ_1}) ⋯ exp(L_{−χ_N}) Λ_i`, truncated at order `μ^N` (`L_χ G = {G, χ}`).
  - Each generator solves `ω(Λ)·∂_λ χ_j = Π_S H^{(j−1)}_j` exactly.
  - `Π_S` is the **exact** Fourier projection onto a finite mode set `S` (integrals, not a DFT).
  - `ω = ν³/Λ³` are the Kepler frequencies at the actual `Λ`.
  - `H^{(j−1)}_j` is the order-`j` part of the transformed Hamiltonian.
- **The slow variables are not frozen.** The brackets include the `(ξ, η)` pairs. This is what the gate
  measures, and it differs from LP-QUANT's frozen-slow Newton steps.
- **Why exact projections.** `F` is then one global real-analytic function on `R(d)`, defined without cells.
  It is exactly invariant under the common rotation, so the cover may be cut modulo rotation. A DFT on a fixed
  grid would break rotation invariance at the aliasing level.
- **Mode set.** The non-resonance is generous. Every mode of the filter box has `|k·ω| ≥ ω_b = 0.176`, since
  `|k_c·51.03 + k_b| ≥ 30` for `k_c ≠ 0, |k_b| ≤ 21`. So `S` is the whole box: `|k_c| ≤ K_c` (40–140 with
  `e_c`), `|k_b| ≤ 20`. The 51:1 near-commensurability `(1, −51)` (divisor 0.0052) is outside `S`; its
  coefficient is below 10⁻³⁰ (*estimated*).

### 6.2 The exact identity (why the check needs no cancellation in the kernel)

The bracket is computed through an identity, never as a difference of large terms.
- **Order 1.** Since `ω·∂_λ χ_1 = μ Π_S f` holds for every `(Λ, ξ, η)`:
  ```
  {F^{(1)}_i, H∘Ψ} = −μ ∂_{λ_i} (f − Π_S f)  +  μ {∂_{λ_i} χ_1, f}
  ```
  - The first term is a Fourier tail. It is bounded from a sup bound of `f∘Ψ` on a complex strip `T_ρ` by
    Cauchy: `|f_k| ≤ M_ρ e^{−ρ|k|}`.
  - The second term is the true `O(μ²)` rate. It only needs relative accuracy `O(1)`.
- **General order.** `{F^{(N)}_i, H∘Ψ}` equals a finite explicit sum:
  - tail terms `−∂_λ(1 − Π_S)` of each order-`j` piece;
  - nested brackets of total order `N + 1`: the Lie-series remainder.
  This is an algebraic identity in the Poisson algebra (bilinearity, Leibniz, Jacobi), proved once in Lean,
  generically in `N`.
  - **Without it**, a kernel evaluation of `{F, H}` from models would cancel two `O(μ)` terms down to
    `O(μ^{N+1})`. Model errors would then have to be below `10⁻¹²` relative, i.e. Taylor degree ≈ 20 in
    6 variables: infeasible.
  - **With it**, every term needs only `O(1)` relative accuracy. That is what makes low-degree cells possible.
- **Size** (*estimated*). Orders 1–2 written out explicitly: 800–1,500 lines. Generic `N`, as a truncated
  Lie-transform remainder theorem over `ContDiff` functions with the canonical bracket: 2–4 k lines.
  `KAM/Canonical/CompositionSeries.lean` gives exact Lie series and may shorten it.

### 6.3 The Bool checks and their soundness lemmas

| check | decides | soundness lemma (new) |
|---|---|---|
| `thresholdOk` | rational: `U` in the chamber, `I_1 ≥ I_0` on `U`, `pairThreshold ≥ I_1 D(v_min) > Λhi_0 + r`, `3r ≤ δ/4`, `2d ≤ r` | `HD11964.threshold_sound` → `LiftData` for every `z₀` of the initial set |
| `cellOk c` | on the cell `c` (a box in `u = (ΔΛ, ξ_c, η_c, ξ_b)`, all fast angles), the identity terms of §6.2 are bounded by `η_i`, and `F_i − Λ_i ∈ [lo_i, hi_i]` | `cellOk_sound` → `hη`, `hG` on `c` |
| `coverOk` | the cells cover `R(d)` modulo rotation (`η_b = 0` after rotation; half-open rational boxes) | `cover_sound` + `rotation_invariant` (`F`, `H∘Ψ` and `R(d)` invariant) |
| `driftOk` | `η_i T + (hi_i − lo_i) < d` | arithmetic |

`cellOk` is the expensive part. Inside it:
- **Taylor–Fourier models.** Each function is a family of packed Fourier models, indexed by the monomials in
  `u` up to degree `D = N + 1`, with a remainder valid on the complex polydisc of the cell × `T_ρ`.
  `u`-derivatives are exact coefficient shifts. Their remainders come by Cauchy from a sup bound on a polydisc
  twice the cell.
- **The chart as a straight-line program.** Per planet it runs in one angle, so it is cheap: `Γ`, `b_e`, `v`,
  then the Kepler equation, then `q`, `p`. Then the pair function
  `f = |p_c + p_b|²/2 − ν_c/|q_c − q_b|`, with `sqrt` and `inv` witnesses.
- **The Kepler witness** (new). A candidate `φ` for `F = λ + φ` is checked by its residual
  `ρ_K = sup|φ − v_0 sin(λ + φ) + v_1 cos(λ + φ)|`. The map is a contraction with constant `|v| = e < 1`, so
  `|φ_true − φ| ≤ ρ_K/(1 − e)`. `sin` and `cos` of the model come by the packed `exp` Taylor block (JetChar).
- **The homological witness.**
  - Candidate models of `χ_j` and `∂_{λ}χ_j` are validated by the residual `ω·∂_λχ_j − Π_S(…)`.
  - The error is then at most `residual / min_{k∈S} |k·ω|`, with `min = 0.176`.
  - This needs a packed multiplication of each slot by its key (the "axis ramp" of V2-PACKED §2). It is
    designed, not built.
- **Bounds.** Each identity term is bounded by a packed weighted norm plus radii (`Norm.lean`); `F − Λ` by
  norm ± radius.

## 7. Kernel engine: what the packed arithmetic on main can do here

**What exists on main** (`KAM/CertificateSharp/Packed/`, V2-PACKED §1–§12; landed with v2-packed-jet).
- `PEnc`: a packed Fourier model of a function on the complex strip `T_ρ` (Kronecker packing on a box), with
  scale, load, radius and norm bound.
- Exact packed products `PEnc.mul`, and the kernel-computed reduce `PEnc.reduceZ` (StageZ: round, box-mask,
  validate by `boxOk`, residual norm into the radius).
- Sums and scalars (`jAdd`, `jUp`).
- Weighted `ℓ¹` norms by one product (`Norm.lean`: `packNorm`, `slotSum_le_packNorm`), and zero modes
  (`PEnc.average`).
- The straight-line jet evaluator: nodes, segments, ledger and the chain theorem `jChainW_slot`/`jChainT_slot`.
- Witnesses: `inv` and `sqrt` in residual form (`JetWit`: `inv_sub_le`, `sqrtE_sub_le`), `exp` as a Taylor sum
  with remainder and characters (`JetChar`, `JetStage`).
- **Measured on LG00:**
  - Low box 51 × 51: 0.20 s kernel per heavy step;
  - Full box 97 × 97, 400-bit slots: 1.04 s per heavy step;
  - about 20 CPU-s fixed cost per process, and ≤ 4 GB per process at ≤ 15 nodes held.

**What it can evaluate here, unchanged:**
- every two-angle Fourier product, sum and scalar of the cell computation, as `jMul`/`jAdd` on boxes
  `(2K_c + 1) × (2K_b + 1)`. That is 81 × 41 (low `e_c`) to 281 × 41 (`e_c = 0.61`), 3.3k–11.5k slots, the
  size of LG00's Full box;
- the norm bounds of §6.3 (`packNorm`) and `F − Λ` (norm ± radius);
- `sqrt`, `inv` and `exp` (hence `sin`/`cos` of the Kepler phase) through the existing witnesses.

**The new layer it needs:**
1. **Taylor × Fourier models.** A family of `PEnc` indexed by the monomials of `u` (degree ≤ `D`), with a
   semantic predicate on `T_ρ × polydisc(h)`.
   - Jet product: for each pair of monomials with `|m| + |m'| ≤ D`, one packed product.
   - The degree truncation goes into the radius (the weight `h^m`).
   - Derivatives in `u` are exact coefficient shifts; Cauchy on a larger polydisc controls the remainders.
   - Kronecker packing of the monomial axes as well is **rejected**. A box `[0, D]⁶` wastes 74× at `D = 4`,
     and the window would pass the 16.8 Mbit numeral cap.
   - Size: about 1–1.5 k lines.
2. **The axis ramp** (multiply each slot by its key `k_j`): `∂_λ` and `ω·∂_λ` of generator candidates.
   Options:
   - a list walk at the boundary, `O(slots)` at about 1 ms each, so 3–12 s per call (*estimated*);
   - ramps propagated by Leibniz through products (V2-PACKED §2).
   Size: 300–600 lines.
3. **The Kepler witness** (§6.3): 300–400 lines.
4. **The identity of §6.2 on models, and the per-cell assembly** (`cellOk`, `cellOk_sound`): 1–1.5 k lines.
5. **The cover and rotation reduction:** 400–700 lines.

**Kernel cost** (*estimated* from the measured census and the LG00 rates).
- **Census** (*measured*, `validation/product-census.json`). Two-angle Fourier products per cell, i.e. the
  monomial pairs of every jet product of the chart, `f` and the Lie series, unpruned:
  - order 1: 1.0·10³; order 2: 1.0·10⁴; order 3: 7.2·10⁴; order 4: 3.8·10⁵.
- **Per packed product:** 0.2–1.3 s **kernel time** per heavy step by box size; 0.5 s on average.
- **All-in against kernel: 2–5×.** On main the all-in CPU of LG00's packed chains was 4.4× (Low) and 4.6×
  (Full) the kernel time (V2-PACKED §12.11–12.12). At Full about 20 CPU-s per process is fixed (imports, the
  probe's copy of the program, node literals), and a process holds ≤ 8 heavy steps and ≤ 15 nodes
  (0.125 GB each). A Taylor × Fourier jet here is 28–462 packed nodes (`M` in the census), so node I/O and
  per-process overhead dominate unless the shared data module and node streaming are built; with them the
  factor should approach 2.
- **Cells:** 50–200 (§8).

| rung (margin 2, sampled sup) | order | per cell, packed: kernel / all-in | whole cover, packed: kernel / all-in | whole cover, landed list arithmetic (all-in) |
|---|---:|---:|---:|---:|
| ≈ 10² yr | 1 | 0.15 / 0.3–0.75 CPU-h | 8–30 / 16–150 CPU-h | 1.3·10²–5·10³ CPU-h |
| 10³ yr (up to ≈ 10⁵) | 2 | 1.5 / 3–7.5 CPU-h | 70–300 / 140–1,500 CPU-h | 10³–5·10⁴ CPU-h, and OOM per product at 4 GB |
| 10⁶ yr (up to ≈ 10⁸) | 3 | 10 / 20–50 CPU-h | 500–2,000 / 10³–10⁴ CPU-h | infeasible |
| 10⁹ yr (provisional) | 4 | 50 / 100–250 CPU-h | 2.5–10·10³ / 5·10³–5·10⁴ CPU-h | infeasible |

- **The kernel columns** are kernel time only: per-process fixed cost, node I/O and production assembly are
  excluded. The all-in columns multiply them by 2–5.
- **The landed column.** Per product, the landed list product costs ≈ 70 CPU-s per 8k-slot product (V2-PACKED
  §8, sum of pieces), about 100× the packed kernel product. Whole chains are closer: measured 8.4× (LG00 Full)
  to 35.6× (Low) the packed all-in (V2-PACKED §12.11–12.12). The column is the packed all-in × 8–36. From
  order 2 one product no longer fits 4 GB on the landed route.
- **Pruning** (*estimated*, unmeasured): dropping monomial-pair products whose norm product is below 10⁻³ of
  the target, with the bound added to the radius, should save 3–10×, most at orders 3–4.
- **Not in the table.**
  - The Python producer at the precision the models need: radii below 10⁻¹⁶ of `f`, so 128–192-bit
    mantissas. Python big-integer arithmetic, or a GMP-backed numpy replacement.
  - Production assembly: data modules and the chain theorems per cell.
- **Comparison.** LG00 costs 30.1 CPU-h in all on the landed route (V2-PACKED §12.1). The 10³ yr rung is about
  5–50 LG00 runs all-in; the 10⁹ yr rung needs pruning or structure (next paragraph) to be practical.

**Structure that would cut the cost further** (*estimated*; to be measured in phase 2, step 1).
- `f`'s chart parts are one-angle, and their products are cheap. Only the pair function and the Lie brackets
  are two-angle.
- `ΔΛ` ranges over ≤ 2·10⁻² of the analyticity radius in `Λ` (`R_Λ ≈ 0.04–0.06`, *measured*), so degree 1 in
  `ΔΛ` may do. That roughly halves the monomial count.
- The hierarchical structure (`α ≤ 0.14`) lets the pair harmonics in `λ_b` be cut at `|k_b| ≤ 20`.

## 8. Cover of the region and cell count

- **Variables.** After the rotation reduction (`ϖ_b = 0`):
  - `(ξ_c, η_c)` in the disc of radius `√(2 Cmax) = 0.155`;
  - `ξ_b ∈ [0, 0.155]`;
  - `ΔΛ` in the box;
  - the AMD constraint `Γ_c + Γ_b ≤ Cmax`.
- **Analyticity radii** of the chart in c's slow variables (*measured* by the root test on degree-12 jets,
  `validation/slow-radius.json`):

  | `e_c` | 0.1 | 0.3 | 0.45 | 0.55 | 0.61 |
  |---|---:|---:|---:|---:|---:|
  | `R_ξ` | 0.159 | 0.145 | 0.128 | 0.114 | 0.105 |
  | `R_η` | 0.142 | 0.105 | 0.078 | 0.061 | 0.051 |

  Planet b's radii are ≥ 0.5, against a range of 0.155, so one or two cells.
- **Cell size.** Polydisc radius `h ≈ 0.3 R`. The Taylor remainder is then `(0.3)^{D+1} ≤ 10⁻²` relative,
  which suffices because of §6.2. That gives about 35 cells for c's disc and × 2 for b, i.e. 50–200 cells
  allowing for the AMD-coupled shapes and safety (*estimated*).

## 9. What is new Lean, what is reused

| piece | where | status | size (*estimated*) |
|---|---|---|---:|
| threshold and margin for `B = Λ_c` | `applications/hd11964` (`HD11964.Threshold`) | new | 250–400 |
| Λ-drift bridge `stoppedDrift_of_approxIntegrals` | core `KAM/Application/LambdaDrift/` (additive) | new | 500–900 |
| rotation invariance (chart, `H∘Ψ`, `F`, region) | core `KAM/Application/LambdaDrift/` | new | 300–600 |
| Lie remainder identity (§6.2) | core, generic | new | 800–1,500 (`N ≤ 2`), 2–4 k (any `N`) |
| Taylor × Fourier packed models, ramp, Kepler witness, `cellOk` | new modules beside `KAM/CertificateSharp/Packed/` (no edit there) | new | 3–5 k |
| cover and assembly; headline | `applications/hd11964` | new | 0.6–1.2 k |
| LP0, `strongFirstExit_of_stopped_drift`, `lpChartLift_of_stopped`, `LiftData`, AMD identity, chart dictionary | LP lane | **proved/sealed; read only** | — |
| `PEnc`, products, reduce, norms, witnesses, jet chain | `KAM/CertificateSharp/Packed/` | **proved; reused unchanged** | — |

Total new Lean: about 6–12 k lines, consistent with A7 §7's 7–15 k. No existing file changes; the LP lane and
the Moon track are untouched.

## 10. Phase 2 plan (waits for the gate and the owner's go)

1. **Measured shard first.** One cell at order 2, at `e_c ≈ 0.6`, in the packed kernel, before any cover. This
   tests the per-product rates of §7 and the producer precision. Program C's rule applies: quote kernel costs
   only after a measured shard.
2. The bridge (§4) and the threshold lemmas (§5) in Lean. They are small and independent of the numbers.
3. The order-2 identity and `cellOk`, then the order-2 cover: the 10³ yr rung.
4. The generic identity and order 3: the 10⁶ yr rung. Order 4 only after pruning is measured.

## 11. Risks

- **Sampled, not certified.** The gate's sup is over 48 centres × full fast-angle grids. The rigorous-design
  factor (report §5.4) is estimated at 1.5–5×, of which 1.7× is measured. The 10⁹ yr rung at order 4 then has
  margin 1.8–3.2, depending on the true order-4 rate, which float64 does not resolve: it is provisional.
- **Region edge.** The rates grow with `e_c`, about 5× from `e_c = 0` to 0.61 at order 2. A larger `Cbar`, or
  the 1σ eccentricities (`C = 0.020`, `e_c` up to 0.76), crosses the Laplace limit and lengthens the tails
  quickly. Owner question 1.
- **Producer precision.** The float64 gate resolves rates down to about 10⁻¹⁷. Certificate data need
  ≥ 128-bit coefficients.
- **The ramp primitive** (§7 item 2) is designed, not built; its list-walk fallback is slower but bounded.
- **Lie remainder identity.** It is the one genuinely new mathematical Lean component. Done explicitly it grows
  fast with `N`.

## 12. Owner questions (conservative option taken; nothing blocked)

1. **Initial set.** Baseline `Cbar = 0.0100` (nominal AMD + 6 %), `Λ` box = 1σ period of b.
   - Covering the 1σ eccentricities (`C ≤ 0.020`) puts `e_c` past the Laplace limit, at about 3–10× the cost
     per order.
   - Taken: the baseline.
2. **T target.** The ladder 10³ → 10⁶ → 10⁹ yr. Taken: build to 10³ yr (order 2) first.
3. **Masses.** `m sin i` with edge-on coplanar orbits (the model is exact for these masses).
   - True masses scale `μ` by `1/sin i`. Each order's rate scales roughly like `μ^{N+1}`, so `sin i = 0.5`
     costs about one order of the normal form (*estimated*).
   - Taken: `m sin i`, stated in the theorem's docstring.
4. **Where the headline is anchored.** In the application package's manifest or in the core manifest
   (APPLICATIONS.md: open for the first package). Taken: undecided; nothing is frozen in phase 1.
5. **A weighted or signed variant of the LP helper** (§5). Not needed for the planned rungs. Taken: none.
