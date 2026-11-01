# LP3: sharp strong Laskar–Petit safety with no arithmetic hypothesis (proof plan)

Status: 2026-11-01. Design phase of package LP3-DESIGN ([brief](../packages/LP3-DESIGN.md)); owner decision
OD-12 (FYI, [OWNER-DECISIONS.md:20](../OWNER-DECISIONS.md)). **This is a plan, not a proof certificate. Nothing in
it is frozen, and no Lean code is written.** Before any Lean package starts, the plan gets an independent
refute-first review.

Source: [`source/MAIN.md`](../source/MAIN.md) as amended by [`source/AMENDMENTS.md`](../source/AMENDMENTS.md),
cited as `LP:MAIN L<k> (lines)`. Sketch: `/root/code/KAM/docs/explorations/amd-crossing/A4-proof-plan.md` §7
(lines 244–254), cited as `A4:<line>`. Repository paths are relative to the worktree root. Spatial modules exist
only on branch `inp-lp-spsafe` (commit `c9553935`); they are cited as `spsafe:<path>:<line>`.

Labels: **[REUSED]** an existing proved LP or track-P declaration, used unchanged; **[ADAPTED]** an existing
declaration re-typed or generalized, with the same proof; **[NEW]** an argument supplied here; **[FROZEN]** the
sealed source-facing theorem, consumed as a black box; **[RISK]** an obligation not yet checked in Lean.

---


> **Review 1 (PASS WITH NOTES) applied** — `LP3-PLAN-REVIEW-1.md`. C1: the import ruling is recorded in
> `OWNER-DECISIONS.md` (OD-13) and in the LP prover brief. C2: §1.4 says "not comparable". C3: packages LP3-SRC and
> LP3-SP-SRC added (§5); LP3 branches start from current `inp-lp`. C4: the scalar small parameter `B₀μ` is written `ε`
> (the mass vector is `ν`); occurrences elsewhere in the text that still read `ν` for `B₀μ` mean `ε`. C5: the headline
> `μ₀` is the minimum of `ε₀/(2B₀)` and LP1/LP2's osculating and separation limits (`μ₂`, `dS₁/(2A_osc)`,
> `dP₁/(4A_osc)`, as in `PlanarSafety/Prograde.lean:83-104`). The NOTEs are folded into the package briefs.

## 0. Summary

1. **Only the drift supplier changes.** LP1/LP2 prove safety by the first-exit argument of MAIN Lemma 14
   (`LP:MAIN L14 (468–500)`). In Lean, LP-CONF implements it with the stopped drift as an explicit hypothesis
   `hstop`: action drift at most `r/2` on the stopped tube of radius `r`
   (`KAM/Planetary/StrongAMD/Confinement.lean:170-182`; spatial `spsafe:KAM/Planetary/Spatial/Confinement.lean:223`).
   LP1 discharges `hstop` with the Diophantine engine (MAIN Lemma 13, `r = √μ`; the call is at
   `KAM/Planetary/StrongAMD/PlanarSafety/Prograde.lean:132-147`). LP3 discharges the same `hstop`, with radius
   `r = (B₀μ)^{b_n}`, from the sealed `KAM.Nekhoroshev.partialConvex_nekhoroshev`
   (`KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:48-77`). That theorem's conclusion is exactly
   "drift `≤ ν^{b_n}/2`" on a stopped interval (line 76-77).
2. **The sharp curved sublevel enters through a finite cover.** The frozen theorem works on a product domain
   `G′ × D`, and its threshold `μ₀` depends on `(G, G′, D)` (line 62). The sharp region
   `{(I, y) : |y|²/2 < B(I) − δ/4}` is not a product, so we cover the compact level set `𝓛_δ` by finitely many small
   balls `G_j`. Each cell gets its own round slow ball `D_j = {|y|²/2 < B(c_j) − 5δ/16}`, at the **local** sharp
   level. The frozen theorem is applied twice per cell (forward with `(h, P)`, backward with `(−h, −P)`), and `μ₀` is
   the minimum of finitely many thresholds.
3. **One perturbation serves every cell.** `P = fc/B₀` uses the uniform holomorphic extension `fc` of the LP
   whole-sublevel domain (`exists_strongTube`, `KAM/Planetary/StrongAMD/AnalyticDomain/Extension.lean:35`; spatial
   `exists_spatialStrongTube`, `spsafe:…/AnalyticDomain/Extension.lean:66`), with `B₀ = max M 1` and `ε = B₀μ`.
   The containment theorem (`AnalyticDomain/Containment.lean:39`) places every cell's complex domain inside the
   tube where `|fc| ≤ M`.
4. **No conversion of time or period.** The frozen theorem uses radian angles (`fastShift` = `2π`-lattice,
   `KAM/Frozen/Planetary/Defs/FastShift.lean:38-39`), the standard field `KAM.hamiltonianVectorField`, and the
   physical time variable. These are exactly the conventions of the LP chart lift
   (`ChartLift/Lift.lean:148-149`). The only change of parameter is `ε = B₀μ`.
5. **Import policy.** Following the root-b8 ruling of 2026-11-01 (§4), an LP implementation module may import the
   sealed frozen anchor, as track P's `Stopped.lean:9` does. It must never import the provider.
6. **Lean size.** About 2,100 new lines in 12 files (§5). None of the LP1/LP2 geometry, chart, domain,
   first-exit, osculating or reconstruction code changes. The one exception is a small generalization of the safe-state
   predicates, so that the drift scale can be a parameter instead of the hard-coded `√μ`.

---

## 1. Target statements

### 1.1 Exponents (frozen definitions)

For `n ≥ 2` planets (the number of **fast** actions; the slow dimension does not enter):

| symbol | frozen definition | value |
|---|---|---|
| `a_n` | `KAM.Nekhoroshev.partialTimeExponent n` (`KAM/Frozen/Nekhoroshev/Defs/PartialTimeExponent.lean:32`) = `KAM.Planetary.planetaryTimeExponent n` (`KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean:35`) | `2/(6n² − 3n + 14)` |
| `b_n` | `KAM.Nekhoroshev.partialDriftExponent n` (`…/Defs/PartialDriftExponent.lean:31`) = `KAM.Planetary.planetaryDriftExponent n` (`…/Defs/PlanetaryDriftExponent.lean:36`) | `3/(6n² − 3n + 14)` |

The bridges `planetaryTimeExponent_eq_partial` and `planetaryDriftExponent_eq_partial` are already proved
(`KAM/Planetary/Exponential/Stopped.lean:76-84`). **Recommendation:** the LP3 headline uses the `planetary*` names,
for parity with the frozen `planetaryExponentialSafety`
(`KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean`). Either choice is definitionally the same number;
this is a candidate owner decision (§6, O-1).

| `n` | `a_n` | `b_n` | LP1 time exponent at `τ = n − 1/2` (`1/(2n+1)`) | LP1 drift |
|---|---|---|---|---|
| 2 | 1/16 | 3/32 | 1/5 | `√μ` |
| 3 | 2/59 | 3/59 | 1/7 | `√μ` |
| 4 | 1/49 | 3/98 | 1/9 | `√μ` |
| 5 | 2/149 | 3/149 | 1/11 | `√μ` |

### 1.2 LP3-1 (planar)

The text of LP1 (`KAM/Planetary/StrongAMD/PlanarSafety/Main.lean:44-91`; normalized form `:137-185`;
FREEZE-PROPOSAL §3), with the following changes:

* **removed:** the data `γ τ`, the premises `hγ hτ`, and the Diophantine premise
  `∀ k ≠ 0, γ·|k|₁^{−τ} ≤ |Σ kᵢ νᵢ³/Λᵢ(z₀)³|` (`Main.lean:55-57`);
* **time:** `T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))` instead of `μ^(−1/(2(τ+1)))`;
* **drift:** `AΛ * μ ^ planetaryDriftExponent n` instead of `AΛ * Real.sqrt μ`. The same change applies to the
  action, axis and AMD lines (`Main.lean:71-73`);
* **unchanged:** all other premises (physical initial state, `a(0) ∈ 𝒜`, chamber membership,
  `strongAMD ν z₀ ≤ orderedStrongThreshold − δ`) and all other conclusions: existence and uniqueness on `[−T, T]`,
  Newtonian reconstruction, ellipticity, margin `δ/2`, the separations `dStar`/`dPair`, osculating elements.

```lean
theorem lp3_planar_strongAMD_safety (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
        ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
          IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧ MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
            (fun t => barycentricPositions 1 ν μ (z t).1)
            (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            -- identical to Main.lean:68-91, except the three drift lines:
            ‖Λ(z t) - Λ z₀‖ ≤ AΛ * μ ^ planetaryDriftExponent n ∧
            ‖a(z t) - a z₀‖ ≤ Aa * μ ^ planetaryDriftExponent n ∧
            |strongAMD ν (z t) - strongAMD ν z₀| ≤ n * AΛ * μ ^ planetaryDriftExponent n ∧ …
```

The normalized variant (with the unused `hνmax`, `hνle`, as in `Main.lean:137-139`) is a corollary, as for LP1.

### 1.3 LP3-2 (spatial)

The text of LP2 (FREEZE-PROPOSAL §3c, lines 309-363; Lean `spsafe:KAM/Planetary/Spatial/SpatialSafety/Main.lean:43`
and `:153`), with the same three changes as §1.2: no `γ τ` or Diophantine premise, time
`T₀ exp(c μ^{−a_n})`, and drift `μ^{b_n}` in the action, axis and AMD lines. There is still no prograde, inclination,
alignment or secular premise. The fast dimension is `n`, so the exponents are the planar `a_n`, `b_n`; the `2n`
slow pairs change only the constants. This is the same observation as `LP:MAIN T19 (603)`.

### 1.4 What is weaker and what is stronger

| | LP1 / LP2 | LP3-1 / LP3-2 |
|---|---|---|
| arithmetic premise | Diophantine `(γ, τ)` at `ω(I⁰)` (`LP:MAIN (5)`, line 64) | **none**: every initial state of the sharp sublevel, including resonant mean motions |
| constants depend on | `(n, ν, 𝒜, δ, γ, τ)` | `(n, ν, 𝒜, δ)`, uniform over the whole compact sublevel |
| time | `T₀ exp(c μ^{−1/(2(τ+1))})`, best `1/(2n+1)` | `T₀ exp(c μ^{−a_n})`, `a_n = 2/(6n²−3n+14)` (**weaker**) |
| action / axis / AMD drift | `O(√μ)` | `O(μ^{b_n})`, `b_n = 3/(6n²−3n+14) < 1/2` (**weaker**) |
| threshold, margin, separations, osculating, uniqueness, reconstruction | sharp `B`, margin `δ/2` | identical |

Neither result implies the other. LP3 is **not comparable** with track P's `planetaryExponentialSafety` (review C2): it has
the same exponents and covers the sharp curved sublevel instead of an `AMDBox` (`A4:254`, `LP:MAIN 616`), and it adds
the separation and osculating conclusions, but P states conclusions LP3 does not (and conversely).

---

## 2. What replaces L12/L13: the partial-convex drift supplier

### 2.1 The frozen interface, read exactly

`partialConvex_nekhoroshev` (`PartialConvexNekhoroshev.lean:48-77`):

* **Data** (lines 49-61): `n ≥ 2` fast and `k ≥ 1` slow pairs. Open convex `G ⊆ G′ ⊆ ℝⁿ` and an open `D ⊆ Phase k`;
  **`D` need not be convex** (only `hD : IsOpen D`, line 52). A width `ρ > 0` with the collar `closedBall I ρ ⊆ G′`
  for `I ∈ G` (line 55). A fixed `h : ℂⁿ → ℂ` that is holomorphic, `C²`, real on real points, with Hessian bound
  `Mcomplex` on `actionNbhd G′ ρ` (lines 56-60), and `HasDefiniteFastPart G′ ρ g m h` (line 61).
* **Order of quantifiers** (lines 62-64): `∃ μ₀` comes **after** `G, G′, D, ρ, h` and **before** the perturbation
  `P`, the duration `C`, and the solution. So `μ₀` depends on the domains and is uniform in `P`.
* **Premises on the orbit** (lines 66-75): `z` solves the field of
  `degenerateHamiltonian (realPart h) (fun _ w => (P (complexifyPhase w)).re) μ`, i.e. `h(fast) + μ·Re P`, on
  `Icc 0 C`, with fast actions in `G` there. Its initial fast action lies in `innerCore G (μ^{b_n})`. Up to the
  queried time `t ≤ min C (μ⁻¹ exp(μ^{−a_n}))`, its slow pair stays in `innerCore D (μ^{b_n})`.
* **Conclusion** (lines 76-77): `‖fast (z t).2 − fast (z 0).2‖ ≤ μ^{b_n}/2`.

Definitions: `HasDefiniteFastPart` allows **either sign** `σ = ±1` of a definite real Hessian, with `|ω| ≥ g`
(`KAM/Frozen/Nekhoroshev/Defs/HasDefiniteFastPart.lean:33-39`). `IsPartialPerturbation G′ D ρ P` asks for holomorphy,
`‖P‖ ≤ 1`, reality and `2π`-fast-periodicity on `partialComplexDomain G′ D ρ` (`IsPartialPerturbation.lean:34-42`).
That set is the product `{Re fast-action ∈ G′, Re slow ∈ D, |Im| < ρ in every coordinate}`
(`PartialComplexDomain.lean:32-38`, `KAM/Frozen/Defs/ComplexStrip.lean:23-24`). `innerCore U d` is the closed
max-norm erosion `{x ∈ U : closedBall x d ⊆ U}` (`InnerCore.lean:32-33`).

### 2.2 Fixed data, chosen before `μ` and the initial state

Everything below depends only on `(n, ν, 𝒜, δ)`.

* **(F1) Shared tube.** `r_g > 0` from `exists_isSharedTube` (`AnalyticDomain/Core.lean:98`) **[REUSED]**.
  `U := cthickening (4 r_g) 𝓛_δ` (`Core.lean:128-130`) is compact and inside the chamber, and
  `Ω_B(4r_g) ≤ δ/16` (`Core.lean:83-88`).
* **(F2) Uniform extension.** `R, M, fc` from `exists_strongTube` (`AnalyticDomain/Extension.lean:35-48`)
  **[REUSED]**. `fc` is holomorphic and `2π`-shift-periodic on `complexTube (strongCore ν 𝓛 δ r_g) R`; it equals
  `fMov 1 1 ν ∘ poincareProd ν 1` at real points, which lie in `chartSafe ν`; and `‖fc‖ ≤ M` on the `R/2` tube.
  Put `B₀ := max M 1`, the same normalization as track P's `Perturbation.lean:226` (pt-rho).
* **(F3) Widths.** `rs := min (4 r_g) (R/4)`, `s = b := rs/4` (so `max(rs, 4s, 4b) = rs < R/2` and `rs ≤ 4r_g`, the
  hypotheses of `strongCore_containment`, `AnalyticDomain/Containment.lean:39-40`). `η := rs/4`, `ρ := rs/8`.
* **(F4) Finite cover [NEW].** `𝓛_δ` is compact (`isCompact_strongLevelSet`, `Core.lean:69`). Choose a finite
  `{c_j} ⊆ 𝓛_δ` with `𝓛_δ ⊆ ⋃_j ball(c_j, η/2)` (max norm). If `𝓛_δ = ∅` the theorem is vacuous: no initial state
  satisfies the premises, because `0 ≤ C` forces `δ ≤ B(I⁰)` (`Prograde.lean:119-122`). Take any positive
  constants in that case.
* **(F5) Cells [NEW].** For each `j`:
  `G_j := ball(c_j, η)`, `G′_j := ball(c_j, 2η)` (open sup-norm balls, hence open and convex),
  `A_j := B(c_j) − 5δ/16`, `D_j := slowBall n A_j` (track P's `slowBall`, `KAM/Planetary/Exponential/Setting.lean:45-46`;
  open by `isOpen_slowBall`, `Stopped.lean:62`).
* **(F6) Kepler constants.** `a_min := min_{I∈U,i} I_i > 0`, `I_max := max_{I∈U,i} I_i`,
  `g := min_i ν_i³/(I_max + rs)³`, `m := min_i 3ν_i³/(I_max + rs)⁴`, `Mc := Σ_i 3ν_i³/a_min⁴`.
* **(F7) Slow erosion gap.** `ε_D := min_j (√(2A_j) − √(2A_j′))/√(2n)` with `A_j′ := B(c_j) − 3δ/8`. This is positive
  because `A_j′ ≥ 5δ/8 > 0` and `A_j′ < A_j`, and the minimum is over a finite set.

### 2.3 Discharging the premises of the frozen theorem, cell by cell

Fix `j`. Write `h := planetaryKeplerC ν` (`Setting.lean:70-71`, `h(I) = −Σ νᵢ³/(2Iᵢ²)`).

* **Collar** (`hcollar`). If `I ∈ G_j` and `‖x − I‖ ≤ ρ`, then `‖x − c_j‖ < η + η/2 < 2η`.
* **Kepler data** (`hhol hC2 hreal hHess`). A complex `z ∈ actionNbhd G′_j ρ` has `‖z − c_j‖ < 2η + ρ < rs`. The
  closed real `rs`-ball about `c_j` lies in `U` because `rs ≤ 4r_g`. So `Re zᵢ > c_{j,i} − rs ≥ a_min > 0`
  (the real point `c_j − rs·eᵢ` is in `U`) and `|zᵢ| < I_max + rs`. Holomorphy and `C²` follow from
  `keplerSumGen_contDiffOn` (`KAM/Planetary/Exponential/KeplerData.lean:48`). The Hessian bound `Mc` follows from
  `keplerSumGen_hess_norm_le` (`KeplerData.lean:134`). Reality follows from `planetaryKeplerC_ofReal` (`:212`).
  **[ADAPTED]** from track P's `h_data` (`KeplerData.lean:238`), which proves the same facts for `fastBox`: only the
  margin lemma `keplerData_margin` (`:156`) changes, from boxes to balls.
* **Definiteness** (`hdef`). On real points of `actionNbhd G′_j ρ`: `ωᵢ = νᵢ³/Iᵢ³ > 0`, so `‖ω‖_∞ ≥ g`. The Hessian is
  `diag(−3νᵢ³/Iᵢ⁴)`, so `−D²h(v,v) ≥ m|v|²`. This is `σ = −1`; **no sign adapter is needed**, because the frozen
  definition allows `σ = ±1` (`HasDefiniteFastPart.lean:37`). For `−h`, `hasDefiniteFastPart_neg`
  (`KeplerData.lean:181`) **[REUSED]** flips `σ`.
* **The normalized perturbation** (`IsPartialPerturbation`) **[ADAPTED from `Perturbation.lean:226-323`]**. Define
  `P z := fc z / B₀` on `T := complexTube (strongCore ν 𝓛 δ r_g) R` and `0` elsewhere (the pt-def of track P).
  **One `P` serves every cell.** The key containment is
  `partialComplexDomain G′_j D_j ρ ⊆ complexTube (strongCore …) (R/2)`. It holds by `strongCore_containment`
  (`Containment.lean:39-48`) with centre `I0 := c_j ∈ 𝓛_δ`:
  * the fast action satisfies `‖z − c_j‖ ≤ ‖Re z − c_j‖ + ‖Im z‖ < 2η + ρ < rs`;
  * the fast angles satisfy `|Im| < ρ < 4s`;
  * the slow part has the witness `y := Re(slow z)`, with `y ∈ D_j ⊆ secularBall ν δ c_j` (since
    `A_j = B(c_j) − 5δ/16 ≤ B(c_j) − δ/4`; `Containment.lean:35-36`) and `‖slow z − y‖ = ‖Im‖ < ρ < 4b`.

  The four clauses then follow:
  * holomorphy, since `fc` is holomorphic on `T ⊇ R/2`-tube;
  * `‖P‖ ≤ M/B₀ ≤ 1`;
  * reality from clause 2 of `exists_strongTube`;
  * periodicity from its clause 3 (the tube is shift-invariant).

  For `−P`, `isPartialPerturbation_neg_of` (`Perturbation.lean:199`) **[REUSED]**.
* **The Hamiltonian identity on an open real set [ADAPTED].** Let
  `V_j := {w : Phase (n+n) | fast w.2 ∈ G′_j ∧ (slow w.1, slow w.2) ∈ D_j}`, which is open. For `w ∈ V_j`,
  `complexifyPhase w` lies in `partialComplexDomain G′_j D_j ρ` (imaginary parts `0 < ρ`), hence in `T`. So
  `w ∈ chartSafe ν` and `P (complexifyPhase w) = fMov(Ψ w)/B₀`. With `ε := B₀μ`:
  `degenerateHamiltonian (realPart h) (Re P ∘ complexify) ν w = −Σ νᵢ³/(2 Iᵢ²) + μ·fMov(Ψ w) = liftChartHam ν μ w`.
  This uses `realPart_planetaryKeplerC` (`KeplerData.lean:216`), `movingHamiltonian_poincareProd_split`
  (`Extension.lean:87`) and `liftChartHam` (`KAM/Planetary/Exponential/Lift.lean:53-54`). Equality on an open set gives
  equal `fderiv` and equal fields: `fderiv_eq_of_eqOn_open`, `hamiltonianVectorField_eq_of_eqOn_open`
  (`KAM/Planetary/Exponential/Hamiltonian.lean:75`, `:81`) **[REUSED]**. Differentiability comes from
  `analyticOnNhd_liftChartHam` (`Lift.lean:109`). This is the `V_j`-version of track P's
  `differentiableAt_hnu_field` (`Hamiltonian.lean:89-101`), which is typed for `workingCylinder` only.

Applying the frozen theorem to `(h, P)` and to `(−h, −P)` for each `j` gives thresholds `ν_j^+, ν_j^− > 0`. Set
`ν₀ := min{1, ν_j^±, (η/4)^{1/b}, ε_D^{1/b}, r₁^{1/b}, (4r_g)^{1/b}}`, using the minimum over the finite cover and
strict inequalities where the frozen theorem needs `<`. Here `r₁` is the budget radius of `exists_budget_radius`
(`PlanarSafety/Constants.lean:35-40`) **[REUSED]**. Then put `μ₀ := ε₀/(2B₀)`, `ε := B₀μ < ε₀`, and

```
r(μ) := ν^{b_n} = (B₀μ)^{b_n},      T(μ) := exp(B₀^{−a_n} μ^{−a_n}),      c := B₀^{−a_n},  T₀ := 1.
```

**Time check.** Since `ν ≤ 1`, `T(μ) = exp(ν^{−a_n}) ≤ ν⁻¹ exp(ν^{−a_n})`, the frozen horizon (line 72).

### 2.4 The drift supplier in the exact `hstop` shape [NEW]

**Statement (`lp_stopped_drift_nek`, planar).** Fix the data above and `0 < μ ≤ μ₀`. Take `LiftData ν U z₀ δ r`
with `r = r(μ)` (`ChartLift/Stopped.lean:44-56`; budget and ball follow from `r ≤ r₁` and `r ≤ 4r_g`). Take an
`OrdConnected J ∋ 0`, a moving solution `z` on `J` with `z 0 = z₀`, and `t ∈ J` with `|t| ≤ T(μ)` and
`StoppedOn ν z₀ δ r z t` (`ChartLift/Stopped.lean:60-63`). Then `‖Λ(z t) − Λ(z₀)‖ ≤ r/2`. This is literally the
`hstop` of `strongFirstExit_of_stopped_drift` (`Confinement.lean:177-182`).

**Proof.**

1. **Lift [REUSED].** `lpChartLift_of_stopped` (`ChartLift/Lift.lean:143-151`) gives `w : ℝ → Phase (n+n)` on an
   open interval `⊇ uIcc 0 t`. It satisfies `w u ∈ chartSafe ν`,
   `HasDerivAt w (hamiltonianVectorField (liftChartHam ν μ) (w u)) u` (two-sided),
   `poincareProd ν 1 (w u) = z u` and `fast (w 0).2 = Λ(z₀) =: I⁰`. The dictionary gives
   `fast (w u).2 = Λ(z u)` (`lpChart_action`, `PlanarDictionary.lean:64`) and `chartAMD (w u) = C(z u)`
   (`lpChart_strongAMD`, `:156`). The lift uses only `LiftData` and `StoppedOn`, and both are drift-agnostic.
2. **Cell.** `I⁰ ∈ 𝓛_δ` (as in `Prograde.lean:119-122`), so pick `j` with `‖I⁰ − c_j‖ < η/2`.
3. **Fast premises.** Since `r = ν^{b_n} ≤ η/4`, `closedBall(I⁰, ν^{b_n}) ⊆ ball(c_j, 3η/4) ⊆ G_j`. So
   `fast (w 0).2 ∈ innerCore G_j (ν^{b_n})`. On `uIcc 0 t`, `‖Λ(z u) − I⁰‖ < r`, so `fast (w u).2 ∈ G_j`.
4. **Sharp slow bound [NEW, the curvature step].** On `uIcc 0 t`, `StoppedOn` gives `C(z u) < B(Λ(z u)) − δ/2`.
   Then:
   * `Λ(z u), I⁰ ∈ U` and `‖Λ(z u) − I⁰‖ < r ≤ 4r_g`, so `B(Λ(z u)) ≤ B(I⁰) + Ω_B(4r_g) ≤ B(I⁰) + δ/16`
     (`abs_strongThreshold_sub_le_modulus`, `KAM/Planetary/StrongAMD/Modulus.lean:58`; monotonicity `:64`;
     `IsSharedTube.modulus`, `Core.lean:87`);
   * `I⁰, c_j ∈ 𝓛_δ ⊆ U` and `‖I⁰ − c_j‖ < η/2 ≤ 4r_g`, so `B(I⁰) ≤ B(c_j) + δ/16`.

   Hence `chartAMD (w u) = C(z u) < B(c_j) − 3δ/8 = A_j′`. The plain whole-ball bound `C ≤ B(I⁰) − δ/4` of
   `strongAMD_le_of_stopped` (`ChartLift/Stopped.lean:98`) is **not** sufficient here, because it leaves no collar
   below `A_j`. The sharpened bound is a new two-line lemma from the same data.
5. **Slow premise.** By `stopped_slow_erosion` (`Stopped.lean:111-114`) **[REUSED]** with `A₁ := A_j′`, `A := A_j`,
   and `ν^{b_n} < ε_D`: `(slow (w u).1, slow (w u).2) ∈ innerCore D_j (ν^{b_n})`.
6. **Solution premise.** On `[0, t]` (case `t > 0`), `w u ∈ V_j` (steps 3–4), so the field of `liftChartHam ν μ`
   equals the N-field of `(h, P)` with parameter `ν` (§2.3). Hence
   `IsSolutionOn (…) {I | fast I ∈ G_j} (Icc 0 t) w` (`KAM/Frozen/Nekhoroshev/Defs/IsSolutionOn.lean:31-35`), with
   `C := t`. This is the `V_j`-form of `stopped_isSolutionOn_forward` (`Stopped.lean:193-212`).
7. **Forward conclusion.** The frozen theorem for cell `j` and `(h, P)`, at `t ≤ min t (ν⁻¹e^{ν^{−a}})`, gives
   `‖fast (w t).2 − fast (w 0).2‖ ≤ ν^{b_n}/2 = r/2`, which is `‖Λ(z t) − I⁰‖ ≤ r/2`.
8. **Backward times** (`t < 0`). The reversed curve `s ↦ w(−s)` on `[0, −t]` solves the field of `(−h, −P)`:
   `hamiltonianVectorField_neg` (`Hamiltonian.lean:116`), `stopped_hamiltonian_neg` (`Stopped.lean:180-189`), and the
   pattern of `stopped_isSolutionOn_reverse` (`Stopped.lean:216-241`), all **[REUSED]**. The erosion premises are the
   same sets. Apply the frozen theorem for `(−h, −P)` exactly as track P does (`Stopped.lean:353-365`). For `t = 0`
   the bound is trivial.

**Uniformity.** The constants `μ₀, c, T₀, B₀` and the cover depend only on `(n, ν, 𝒜, δ)`. The cell index `j` and the
lift depend on the orbit, but every threshold was minimized over the finite cover beforehand.

### 2.5 Spatial version (`k = 2n`, `Phase (n + (n + n))`)

The argument is identical. Only the following changes:

* The frozen theorem is instantiated with `k := n + n`, so `Phase (n + k) = Phase (n + (n + n))` and
  `D : Set (Phase (n + n))`. The spatial chart is natively typed this way
  (`spsafe:KAM/Planetary/Spatial/Product/Defs.lean:66`).
* `D_j := slowBall (n + n) A_j`. Its defining sum `Σ_{k : Fin (n+n)} (y.1 k² + y.2 k²)/2` is literally
  `spatialChartAMD` (`spsafe:…/ChartLift/Setting.lean:42-43`). It equals `spatialSlowDeficit`
  (`spsafe:…/AnalyticDomain/Core.lean:42-43`) after `Finset.sum_add_distrib`.
* The extension is `exists_spatialStrongTube` (`spsafe:…/AnalyticDomain/Extension.lean:66`), on the re-typed
  `complexTubeNM` (`spsafe:…/ComplexTube.lean:36`, amendment N12). Containment is `spatialStrongCore_containment`
  (`spsafe:…/AnalyticDomain/Containment.lean:40`), with `spatialSecularBall` (`:36`).
* The chart Hamiltonian is `spLiftChartHam ν μ = spatialHProd ν + μ·fSpatial ∘ Ψ` (`spsafe:…/ChartLift/Setting.lean:54-55`).
  `spatialHProd ν w = −Σ νᵢ³/(2 (fast w.2)ᵢ²)` (`spsafe:…/Product/Split.lean:46-47`), which matches
  `realPart (planetaryKeplerC ν) (fast w.2)`. `spLiftChartSafe` (`Setting.lean:46-47`) and `spatialChartSafe`
  (`spsafe:…/AnalyticDomain/Safety.lean:36-37`) have the **same body**, so the identification is `rfl`.
* The lift is `spatialChartLift_of_stopped` (`spsafe:…/ChartLift/Lift.lean:163`), under `SpatialLiftData` (with the
  alignment field) and `SpatialStoppedOn` (`spsafe:…/ChartLift/Stopped.lean:52-75`). The chart AMD equals the
  physical AMD along the aligned orbit by `spatialChartAMD_eq_of_aligned` (`spsafe:…/ChartLift/Lift.lean:47`).
* The slow erosion constant is `√(2·2n)` instead of `√(2n)`: `stopped_slow_erosion` is generic in its dimension
  (`Stopped.lean:111`, `{x : Phase n}`).
* The Kepler data and the fast cover are **the same** as in the planar case. `h` depends only on the `n` fast actions.

---

## 3. How the whole sharp sublevel enters

* **No `AMDBox`.** Track P's `slowBall n A` has one level `A` for a whole box. `EnlargedData` bounds that level by a
  box-wide common eccentricity and pair-gap worst case (`Setting.lean:58-67`, fields `deficit`, `radii`, `gaps`).
  That level is generally far below `B(I)`. Here each cell has its own level `A_j = B(c_j) − 5δ/16`, within `δ/8`
  of the local sharp threshold. Collision safety of the whole product `G′_j × D_j` (all phases, all slow points, even
  off the physical angular-momentum level) is not re-proved. It is inherited from the containment in `strongCore`,
  whose real points lie in `chartSafe` (`AnalyticDomain/Safety.lean:47`). That containment rests on MAIN Lemmas 5
  and 8: every point with `Σ Γᵢ ≤ B(I⁰) − δ/4` and `‖I − I⁰‖ ≤ 4r_g` is safe (`LP:MAIN L8 (257-261)`).
* **Why `D` may be the sharp ball.** The frozen theorem asks only `IsOpen D` (line 52), not convexity or any
  relation to `G`. Its analytic premise is on `partialComplexDomain G′ D ρ` (strip width `ρ` in every coordinate).
  A **fixed** `ρ` suffices, because the slow imaginary width needed by `strongCore_containment` (`< 4b`) is fixed.
  The curvature of the true region `{|y|²/2 < B(I) − δ/4}` in the `(I, y)` space is absorbed by the cover. Within a
  cell, `B` varies by at most `δ/16` (`Ω_B(4r_g) ≤ δ/16`), and the four levels used are ordered with fixed gaps:

  ```
  stopped states:  C < B(c_j) − 3δ/8   <   D_j: < B(c_j) − 5δ/16   ≤   secularBall(c_j): ≤ B(c_j) − δ/4
  ```

  The first gap (`δ/16` in AMD) is the reserved collar that pays for `innerCore D_j (ν^{b_n})`. The second gap
  places `D_j` inside the analytic domain.
* **The stopped first exit (L14 / LP-CONF).** `strongFirstExit_of_stopped_drift` (`Confinement.lean:170-188`)
  **[REUSED, unchanged]** with:
  * `U` = the shared tube;
  * `r := (B₀μ)^{b_n}`;
  * `T := T(μ)`;
  * the budget `n r + Ω_B(r) ≤ δ/4`, from `r ≤ r₁` (`exists_budget_radius`);
  * `hball` from `r ≤ 4r_g`;
  * `hstop` := §2.4.

  The improvement is from `< r` to `≤ r/2`, so the frozen drift `ν^{b_n}/2` meets it with no slack and no loss. The
  AMD margin improves to `3δ/4` exactly as in `LP:MAIN L14 (485-487)` and amendment N6.
* **Assembly.** Copy `planar_safety_of_prograde` (`PlanarSafety/Prograde.lean:43-200`) with the drift supplier
  swapped (lines 71-72 and 132-145). The radius `1·√μ` becomes `(B₀μ)^{b_n}`, so `AΛ := B₀^{b_n}/2`. The axis and AMD
  lines use the same lemmas: `norm_axis_sub_le` (`Constants.lean:64`) and `strongAMD_sub_eq_sum`
  (`Momentum.lean:67`). The orientation reduction (`Main.lean:116-134`) and the spatial rotation reduction (LP2 Main)
  are reused verbatim. The only edit to existing code is to the safe-state predicates `PlanarSafeState`/`PlanarSafeSol`
  (`PlanarSafety/Orientation.lean:100-130`) and their spatial twins (`spsafe:…/SpatialSafety/Orientation.lean:131`,
  `:161`). They hard-code `AΛ * Real.sqrt μ` (`Orientation.lean:105-107`), so §5 proposes a drift-scale parameter.

---

## 4. Provider chain and import policy

**Ruling (root-b8 ruling, 2026-11-01).** An LP implementation module **may** import the **sealed** frozen anchor
`KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` (`KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean`)
and apply `KAM.Nekhoroshev.partialConvex_nekhoroshev`. The reasons given:

* AGENTS.md rule 9 quarantines only providers and `DRAFT_SORRY` anchors (`AGENTS.md`, hard rule 9);
* the manifest records `nekhoroshev.d25.partialConvex_nekhoroshev.v1` as `SEALED` (`manifest/frozen-anchors.json:8914`,
  `"state": "SEALED"` at `:9020`; implementation `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` at `:9016-9018`),
  together with its definitions;
* track P is the precedent: `KAM/Planetary/Exponential/Stopped.lean:9` public-imports the anchor and applies it at
  `:260` and `:265`;
* consuming the sealed, audited source-facing statement is preferable to consuming an implementation.

**LP modules must never import `KAM/Provider/Nekhoroshev/…` directly.** The anchor imports its provider privately
(`PartialConvexNekhoroshev.lean:22`, non-`public` `import`), and that is the only permitted path. The approval of
the frozen statement is D25 (`docs/DECISIONS.md:153-166`). The quarantine of providers until sealing is D11
(`docs/DECISIONS.md:45-51`).

**Brief conflict to fix before phase 2.** The common prover brief `/root/code/KAM-inp/.drafts/briefs/inp-prover-common.md`
("Quarantine" bullet) still says *"never import a frozen THEOREM anchor (`KAM/Frozen/*/Theorems/*`) … from your
implementation files"*. That is stricter than AGENTS.md rule 9 and contradicts both the ruling and the track-P
precedent. Every LP3 Lean brief must quote the root-b8 ruling explicitly (sealed anchor yes, provider never), or the
prover will either refuse or route around it.

**Chain used by LP3:**

```
partialConvex_nekhoroshev  [FROZEN, sealed; provider behind it, not imported]
  ├─ Kepler data on balls (LP3-KEP)  ← KeplerData.lean calculus [REUSED]
  ├─ P = fc/B₀ on every cell (LP3-PERT) ← exists_strongTube (LP-DOM/DOMX) + strongCore_containment [REUSED]
  └─ cells, thresholds, erosions (LP3-COVER, LP3-DRIFT) ← stopped_slow_erosion, *_neg lemmas (track P) [REUSED]
        ↓ hstop
strongFirstExit_of_stopped_drift (LP-CONF) [REUSED] ← lpChartLift_of_stopped (LP-LIFT) [REUSED]
        ↓
planar assembly (LP3-PS) ← barrier/osculating (GEOMOD, OSC), orientation (PS), reconstruction [REUSED]
```

The nonresonant chain (LP-NRR, LP-NRS, `NonresonantAdapter*`, `NonresonantReuse/*`, `lp_stopped_drift`
`NonresonantReuse/Drift.lean:59`) is **not used** by LP3. It stays as the LP1/LP2 supplier. `Partial/Nonresonant.lean`
and `ExtNFHyp` are not needed, so the period-one rescaling of `LP:MAIN L13 (435-441)` and amendment N6 does not
arise.

**Compliant alternative (only if the ruling were withdrawn).** The track-N implementation theorem behind the provider
(the export named in the manifest, `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev`) has the identical
signature (the sealed body at `PartialConvexNekhoroshev.lean:79-80` applies it to the binders verbatim). Importing
a provider is forbidden (rule 9), so the alternative would be the implementation module that the provider re-exports.
**Not recommended:** the ruling makes it unnecessary, and the sealed statement is the audited interface.

---

## 5. Lean package list

All modules are core library (no application root; AGENTS rule 8). Planar modules go under
`KAM/Planetary/StrongAMD/Nek/`, spatial ones under `KAM/Planetary/Spatial/Nek/`. The spatial packages start after
LP-SP-SAFE lands. Sizes are estimates in lines of code; every file stays far below the 1,500-line cap.

| Package | Files | Content | Reuses | Size |
|---|---|---|---|---|
| **LP3-KEP** | `Nek/Kepler.lean` | Kepler data on `actionNbhd (ball c 2η) ρ` inside a compact `U ⊆ chamber`: positivity margin; hol/`C²`/real/Hessian `Mc`; `HasDefiniteFastPart` for `±h` | `KeplerData.lean:48,134,181,212,216` | 180 |
| **LP3-COVER** | `Nek/Cover.lean` | (F3)–(F7): widths, finite cover of `𝓛_δ`, cells `(G_j,G′_j,D_j)`, openness/convexity/collar, the cell containment `partialComplexDomain ⊆ complexTube(core,R/2)`, the per-cell threshold bound `|B(I⁰)−B(c_j)| ≤ δ/16`, `ε_D > 0` | `Containment.lean:39`, `Core.lean:69,98`, `Modulus.lean:58,64` | 220 |
| **LP3-PERT** | `Nek/Perturbation.lean` | global `P = fc/B₀`; `IsPartialPerturbation` on every cell for `±P`; the `V_j` Hamiltonian identity and field equality | `Extension.lean:35,87`, `Perturbation.lean:199`, `Hamiltonian.lean:75,81` | 200 |
| **LP3-ONE** (early test) | `Nek/OneCell.lean` | the frozen theorem applied to **one** cell, forward and backward, with all premises discharged: the riskiest interface, built first (as AMENDMENTS recommended order item 2 did for Lemma 13) | the three above + frozen anchor | 150 |
| **LP3-DRIFT** | `Nek/Drift.lean`, `Nek/Drift/Stopped.lean` | thresholds `ν_j^±` over the cover, `ν₀, μ₀, r(μ), T(μ)`; the sharpened slow bound (§2.4 step 4); `lp_stopped_drift_nek` in the `hstop` shape | `ChartLift/Lift.lean:143`, `Stopped.lean:111,180,193,216` | 320 |
| **LP3-PS** | `Nek/Orientation.lean`, `Nek/PlanarSafety.lean` | drift-scale generalization of the safe-state predicates (or a parallel pair); `planar_safety_nek_of_prograde`; `lp3_planar_strongAMD_safety` (+ normalized) | `Prograde.lean`, `Main.lean`, `Confinement.lean:170` | 360 |
| **LP3-SP-COVER** | `Spatial/Nek/Cover.lean` | `D_j = slowBall (n+n) A_j`; spatial containment; spatial `P`; `V_j` identity for `spLiftChartHam` | `spsafe` Extension `:66,123`, Containment `:40`, Setting `:42,54` | 240 |
| **LP3-SP-DRIFT** | `Spatial/Nek/Drift.lean` | spatial `hstop` supplier | `spsafe` Lift `:47,163`, Stopped `:52,68` | 260 |
| **LP3-SP-SAFE** | `Spatial/Nek/Orientation.lean`, `Spatial/Nek/SpatialSafety.lean` | aligned theorem, rotation reduction, `lp3_spatial_strongAMD_safety` (+ normalized) | `spsafe` Aligned `:46`, Main `:43`, Confinement `:223` | 380 |

Total: about 2,300 lines in 12 files.

**Option (recommended): share the cellwise application.** A generic theorem in `k` saves about 150 lines of spatial
duplication. It would state: given the Kepler `h`, a finite cell family, a `P` with `IsPartialPerturbation` on every
cell, and curves solving the N-field with the erosion premises, the drift is `≤ ν^{b_n}/2` for all `ν < ν₀`. LP3-DRIFT
and LP3-SP-DRIFT then shrink to chart adapters.

**Recommended order:**

1. LP3-KEP, LP3-COVER and LP3-PERT, in parallel;
2. LP3-ONE;
3. LP3-DRIFT;
4. LP3-PS;
5. the spatial packages, after LP-SP-SAFE has landed.

Every Lean brief repeats AGENTS hard rules 1–11 verbatim and the §4 ruling.

---

Additional packages (review C3): **LP3-SRC** and **LP3-SP-SRC**, the LP3-1/LP3-2 statements restated through the
source carriers (OD-11 (b)), as LP-SRC/LP-SP-SRCB did for LP1/LP2 (≈ 150 lines each).

## 6. Risks and open points (honest)

| # | Risk | Assessment and mitigation |
|---|---|---|
| R1 | **`μ₀` is not uniform in the domain.** The frozen `μ₀` depends on `(G, G′, D, ρ, h, g, m, Mcomplex)` with no quantitative control (line 62). | This is resolved only by finiteness: the cover is fixed before `μ`, with two applications per cell, and the minimum is taken over finitely many. A continuum of centres (one `D` per `I⁰`) would **not** work. Lean: a `Finset` from `IsCompact.finite_cover_balls`, choice per element, then `Finset.inf'` (empty case separate). |
| R2 | **`innerCore` erosion vs the reserved collar.** The fast and slow erosions have radius `ν^{b_n} → 0`, but they need fixed collars. | Fast: `‖I⁰−c_j‖ < η/2` and `ν^{b_n} ≤ η/4`. Slow: the AMD gap `δ/16` between `A_j′` and `A_j`, through `stopped_slow_erosion` with `ε_D > 0`. **The plain `C ≤ B(I⁰) − δ/4` bound used by LP1 is too weak** (§2.4 step 4); the sharpened `C < B(c_j) − 3δ/8` uses `Ω_B(4r_g) ≤ δ/16` twice. Paper-checked here; Lean-checked in LP3-ONE. |
| R3 | **Sign and time reversal.** | `h` is negative definite (`σ = −1`), which the frozen definition allows directly. Only `t < 0` needs an adapter: `(−h, −P)` and the reversed curve, as in track P (`Stopped.lean:216-241`, `:353-365`). The two-sided `HasDerivAt` of the LP lift (`ChartLift/Lift.lean:149`) is what the reversal needs at the endpoint `s = 0`. |
| R4 | **`IsSolutionOn` on `[0, C]` needs fast actions in `G` and `DifferentiableAt H` everywhere on the interval.** | Take `C := t`. The stopped tube keeps the fast actions in `ball(I⁰, r) ⊆ G_j`, and `V_j` is open with `H_N = liftChartHam` there. Endpoints are covered because the lift lives on an open interval `⊇ uIcc 0 t` (`ChartLift/Lift.lean:147`). |
| R5 | **Time conversion.** | `T(μ) = exp(B₀^{−a}μ^{−a}) ≤ ν⁻¹exp(ν^{−a})` needs `ν ≤ 1`, which holds since `μ₀ = ν₀/(2B₀)` and `ν₀ ≤ 1`. The statement keeps LP1's `T₀ * exp(c μ^{−a})` shape with `T₀ = 1`, `c = B₀^{−a_n}`. There is no period or time rescaling (radian angles, physical time). |
| R6 | **Strict vs non-strict `μ`.** | The frozen theorem needs `μ < μ₀`; LP statements use `μ ≤ μ₀`. The factor 2 in `μ₀ = ν₀/(2B₀)` absorbs this. |
| R7 | **Containment uses one centre per cell.** `strongCore_containment` needs an `I0 ∈ 𝓛_δ`. | The cover centres `c_j` are taken **in** `𝓛_δ` (F4), so `I0 := c_j` works for the whole cell. A cover by arbitrary points would fail this. |
| R8 | **Spatial typing.** | `Phase (n + (n + n))` is native to the spatial chart. `slowBall (n+n)` and `spatialChartAMD` coincide up to `Finset` reindexing. `spLiftChartSafe` and `spatialChartSafe` agree by `rfl`. To check: that `spatialHProd` rewrites to `realPart (planetaryKeplerC ν) ∘ fast`, which should be a two-line lemma. |
| R9 | **Elaboration.** | The frozen call has 20 explicit arguments; track P makes exactly such calls (`Stopped.lean:260-272`) at default heartbeats. The finite minimum over the cover is the only new combinatorial step; keep it in its own lemma. Never raise heartbeats: report a failure as a design signal. |
| R10 | **Axioms.** | The axioms of LP3 include those of the provider behind the sealed anchor. Expect `[propext, Classical.choice, Quot.sound]`; the LP3 handoff must check with `#print axioms`. |
| R11 | **Safe-state predicates hard-code `√μ`.** | Either generalize `PlanarSafeState`/`SpatialSafeState` with a drift-scale argument and keep the old names as the `√μ` instance (a non-frozen refactor whose reflection and rotation proofs do not use the drift form; verify in LP3-PS), or add parallel predicates. The first is cleaner; the second touches no LP1/LP2 file. Orchestrator's choice (O-2). |
| R12 | **Brief conflict on importing frozen theorems** (§4). | Must be stated in every LP3 brief. |
| R13 | **Spatial dependency.** | LP3-2 depends on unlanded LP2 modules (`inp-lp-spsafe`, audit pending, FREEZE-PROPOSAL `:31`). Any change to their statements during the LP2 audit propagates here. |
| R14 | **Statement scope.** | LP3 says nothing about `γ, τ`. Its constants are uniform over the whole sublevel, so there is no "for all `γ`" family. This is stronger than "LP1 for every Diophantine state" in uniformity and weaker in exponent; §1.4 records both. |

**Candidate owner decisions:**

* **O-1.** Exponent names in the headline: `planetaryTimeExponent`/`planetaryDriftExponent` (recommended) or the
  `partial*` names.
* **O-2.** Generalize the safe-state predicates, or add parallel ones.
* **O-3.** Whether LP3-1 and LP3-2 enter the freeze proposal as anchors next to LP1/LP2 or stay as non-frozen
  corollary-level results until LP1/LP2 are frozen.

## 7. Source and sketch remarks (errata candidates; none blocking)

* **A4 §7, line 246.** "The Kepler Hessian is definite; the existing sign/time-reversal adapter applies." This is
  imprecise: no **sign** adapter is needed, since `HasDefiniteFastPart` allows `σ = ±1`
  (`HasDefiniteFastPart.lean:37`). The adapter is for **time reversal** only (negative times). This is a
  clarification, not a defect.
* **A4 §7, line 251.** "uniform enlarged slow levels with reserved margins". If "uniform" means one common slow level
  for all boxes, the construction loses sharpness: it is then the `AMDBox` problem of `A4:254`. The levels must be
  per cell (`A_j = B(c_j) − 5δ/16`); only the **margins** (`δ/16` gaps, `ε_D`) are uniform. This is a clarification.
* **A4 §7, line 252.** "The erosion `innerCore D` … supplied by the reserved physical slow collar". Correct, but the
  collar must be measured against the **sharpened** stopped bound (§2.4 step 4). The LP1 whole-ball bound
  (`ChartLift/Stopped.lean:98`) leaves none. This is a completion, not a defect.
* **MAIN `LP:MAIN 616`** correctly notes that `partialConvex_nekhoroshev` keeps a stopped slow-domain condition, so
  Lemma 14 is still needed. Consistent with this plan.
* **Deviations introduced here.** None from MAIN's L2–L8, L14, L16–L18. The drift supplier L12/L13 is replaced (by
  design), and the conclusion exponents change (§1.4).
