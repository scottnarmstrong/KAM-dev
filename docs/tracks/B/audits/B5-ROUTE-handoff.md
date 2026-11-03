# Handoff B5-ROUTE (branch `inp-b5route`, worktree `/root/code/KAM-inp-b5route`)

Status: **complete** — the full route (steps 1–5, including the Cauchy third-derivative estimate that
discharges `hG` and `hD3`) is proved. No `sorry`, no axioms beyond `propext, Classical.choice, Quot.sound`.
B5-NF was not changed.

## Files (all new, all under `KAM/EffectiveStability/`)
| file | lines | content |
|---|---|---|
| `CauchyThird.lean` | ~215 | one Cauchy step on nested balls; `D³` Cauchy estimate on a ball; real-slice transfer |
| `TorusRoute/Matrix.lean` | ~110 | holomorphy of matrix inverse entries; `Aᵀ` invertible / `‖(Aᵀ)⁻¹J‖ ≤ ‖J‖/(1-nκ)` |
| `TorusRoute/Chart.lean` | ~125 | `torusCxJac`, `torusCxChart` (= `Ψ_ℂ`), holomorphy, `‖Ψ_ℂ(θ,J) - K θ‖` bound |
| `TorusRoute/Real.lean` | ~85 | `Ψ_ℂ ∘ ι₂ = ι₂ ∘ Ψ` (`torusCxChart_realInclusion`) |
| `TorusRoute/Strip.lean` | ~100 | strip Cauchy estimates at complex points; `‖D(K∞^θ - id)(θ)‖ ≤ κc + disp/δ` |
| `TorusRoute/Data.lean` | ~110 | `certifiedTorus_chartData` (item 1), `certifiedTorus_nfTorus` (item 2) |
| `TorusRoute/Bound.lean` | ~145 | `RouteChecks`, `routeDomain`, image in `D`, holomorphy of `c.H ∘ Ψ_ℂ`, derived sup bound |
| `CertifiedTorusRoute/Glue.lean` | ~125 | real/complex gluing, `hG`-smoothness lemma, Cauchy ball in the domain |
| `CertifiedTorusRoute.lean` | ~125 | `routeC3`, `certifiedTorus_confinement` |

## Main statement (exact)
```lean
def routeC3 (c : TorusCertificate n α) (r : ℝ) : ℝ :=
  64 * ((c.params.M : ℝ) * ((c.params.μ : ℝ) / 2)) / r ^ 3

structure RouteChecks (c : TorusCertificate n α) (κc δ δφ ρJ : ℝ) : Prop where
  hδ : 0 < δ
  hδφ : 0 < δφ
  hδφρ : δφ + δ ≤ (c.params.rhoInf : ℝ)
  hκc : ∀ θ ∈ complexStrip n δφ, ‖fderiv ℂ (fun θ => (c.K θ).1 - θ) θ‖ ≤ κc
  hκ : (n : ℝ) * (κc + (c.params.disp : ℝ) / δ) < 1
  hρJ0 : 0 < ρJ
  hρJ : ρJ ≤ (1 - n * (κc + (c.params.disp : ℝ) / δ)) * ((c.params.μ : ℝ) / 2)

theorem certifiedTorus_confinement (hG : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (hT : CertifiedTorusAt c ωstar Kinf sinf) (h : RouteChecks c κc δ δφ ρJ)
    {r : ℝ} (hr : 0 < r) (hrφ : r ≤ δφ)
    (a b η : Fin n → ℝ) (ε Tt : ℝ) (hε : 0 < ε) (hTt : 0 ≤ Tt)
    (hmargin : ∀ j, a j + Tt * η j < b j) (hrJ : ∀ j, b j + ε + r ≤ ρJ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ j, b j ≤ B) (hηB : ∀ j, routeC3 c r * B ^ 2 / 2 ≤ η j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, Tt < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      z 0 = torusChartMap (torusRealU Kinf) (torusRealV Kinf) w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ {y | realInclusion₂ n y ∈ c.D} ∧
        HasDerivAt z (hamiltonianVectorField (realHam c.H) (z t)) t) ∧
      (uniqueness on ordconnected I ∋ 0, as in torus_confinement) ∧
      ∀ t, |t| ≤ Tt → Ψ (Ψinv (z t)) = z t ∧ ∀ j, |(Ψinv (z t)).2 j - w₀.2 j| ≤ η j * |t| ∧
          |(Ψinv (z t)).2 j| ≤ a j + η j * Tt
```
(`Ψ = torusChartMap (torusRealU Kinf) (torusRealV Kinf)`, `Ψinv = torusChartInvMap …`, frequency
`ω' = sinf • ωstar` inside, energy `E0`.) V is the real slice `{y | realInclusion₂ n y ∈ c.D}`.
Other main lemmas, exact signatures in the files: `norm_fderiv3_ball_le`, `abs_fderiv3_realPart_le`
(`CauchyThird`); `certifiedTorus_chartData`, `certifiedTorus_nfTorus` (`Data`);
`torusCxChart_realInclusion` (`Real`); `RouteChecks.ham_sub_le`, `RouteChecks.chart_mem_D`,
`RouteChecks.ham_differentiableOn` (`Bound`).

## Approach
* `Ψ_ℂ(θ,J) = ((K∞ θ).1, (K∞ θ).2 + (A(θ)ᵀ)⁻¹ J)`, `A(θ)_{ij} = (DK∞^θ(θ) e_j)_i`. On the strip
  `T_{δφ}`: `‖D(K∞^θ - id)‖ ≤ κ := κc + disp/δ` (Cauchy on the displacement, `norm_fderiv_angle_le_cx`),
  hence entries of `A - 1` are `≤ κ`; with `nκ < 1` the transpose is invertible and
  `‖(Aᵀ)⁻¹J‖ ≤ ‖J‖/(1-nκ)` (direct, no Neumann series). Inverse entries are holomorphic by Cramer.
* `Ψ_ℂ ∘ ι₂ = ι₂ ∘ Ψ` exactly, so `realHam c.H ∘ Ψ = (Re (c.H ∘ Ψ_ℂ)) ∘ ι₂` as functions: `hG` (C³) follows
  from holomorphy of `c.H ∘ Ψ_ℂ` on `T_{δφ} × {‖J‖<ρJ}` (image lies in `ball (K∞ θ) (μ/2) ⊆ D`); `hD3` from
  `abs_fderiv3_realPart_le` (three nested Cauchy steps on balls of radii r, 3r/4, r/2, r/4; real slice via
  `iteratedFDeriv` + `restrictScalars`).
* **No new sup-bound premise:** `‖c.H(Ψ_ℂ w) - E₀‖ ≤ M μ/2` is derived by the mean value theorem on
  the convex ball `ball (K∞ θ) (μ/2) ⊆ D` from `‖DH‖ ≤ M` (`G1Hyps.hbd`) and `c.H (K∞ θ) = E₀`
  (`CertifiedTorusAt`). The Cauchy bound is applied to `c.H ∘ Ψ_ℂ - E₀` (D³ unaffected).

## Deviations from the brief (report)
1. **`C₃ = 64 (Mμ/2)/r³`**, not `c₃ M/min(δφ,ρJ)³`: `M` is the derived oscillation bound `Mμ/2`; the constant 64
   comes from three Cauchy steps of width `r/4`. The Cauchy radius `r` is a separate parameter with
   `r ≤ δφ` and `b j + ε + r ≤ ρJ` (the ball about a point of the cylinder of radius `b+ε` must stay inside
   `|J| < ρJ`; `min(δφ, ρJ)` alone would not be correct).
2. **Transpose norm costs a factor `n`:** the sup-norm of `Aᵀ` is the column-sum norm of `A`, so the finite check
   is `n(κc + disp/δ) < 1` (stronger than the `κ < 1` of B5-LAG; implies it for `n ≥ 1`).
3. The reference-embedding hypothesis `hκc` is on the whole complex strip `T_{δφ}` (a check on
   `∂_θ(c.K^θ - id)`), not only at real points, because holomorphy of `Ψ_ℂ` needs invertibility of `A` on the strip.
   It contains the real-point hypothesis of `certifiedTorusAt_projection`.
4. `RouteChecks` bundles the finite checks into a structure (all fields are numerical/inequality checks plus
   `hκc`; none is conclusion-shaped).

## Checks
* Builds: each module built with `b_build.sh` in import order (CauchyThird, TorusRoute.{Matrix,Chart,Strip,Real,
  Data,Bound}, CertifiedTorusRoute.Glue, CertifiedTorusRoute): all succeed; per-file `b_lean.sh` run prints no
  warning for any of my files.
* `#print axioms` (scratch `.drafts/axioms_scratch.lean`) for `certifiedTorus_confinement`,
  `abs_fderiv3_realPart_le`, `norm_fderiv3_ball_le`, `torusCxChart_realInclusion`, `RouteChecks.ham_sub_le`,
  `certifiedTorus_chartData`, `certifiedTorus_nfTorus`: all `[propext, Classical.choice, Quot.sound]`.
* Line-length check (>100 chars): `[]`.
* `scripts/lint_sources.sh` and `main_shortname_check.py`: see the final lines appended below.

## Design signals / uncertainties
* No heartbeat problems; all files elaborate in a few seconds; all files < 220 lines.
* B5-NF's `hD3` is in the operator form used by `torusNormalForm_confinement`; the Cauchy estimate delivers
  it for all directions (no adaptation of B5-NF needed).
* `RouteChecks.hκc` is an unproven finite check about the approximate embedding `c.K^θ`; it is not derivable
  from `checkEmbedding` as stated (that checks `‖DK‖ ≤ σK - μ`, not `‖D(K^θ-id)‖ < 1/n`). A certificate-level check
  of it is a follow-up for the checker side.

## Errata
None found in pinned sources.

* After renaming three short-name collisions: `main_shortname_check.py` exits 0; `scripts/lint_sources.sh` passes (check_lean_modules PASS, guards OK); rebuilt all modules OK.

## AUDIT FOCUS (kam-b1)
Track B, program B5 (overnight D71; nothing frozen; OD-B13..B15; design docs/tracks/B/B5-DESIGN.md). The B5 headline:
certifiedTorus_confinement turns the v2 output (CertifiedTorusAt, with the soundness premises G1Hyps and IsDiophantine of
checkTorusCertificate_sound) plus finite checks into torus_confinement's conclusion near the certified torus (plan §3.4,
/root/code/KAM/docs/explorations/program-b-plan.md lines 426-457). Built on audited B5-CHART, B5-LAG (landed), B5-NF (PASS).
Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B5-ROUTE.md and brief-B1-common.md. Scope: prover commit d18be78b3 (nine
modules) and merges. Check: (1) every premise is a certificate soundness premise, the CertifiedTorusAt witness, or a finite
numeric check (RouteChecks fields, radii, margins) — nothing chart-, normal-form-, Lagrangian- or confinement-shaped;
hκc is a quantitative check on the certificate's approximate embedding (state whether it is finite-checkable from
certificate majorants); (2) the complexified chart Ψ_ℂ restricts EXACTLY to Ψ on reals, is holomorphic on the stated domain,
and maps into c.D (μ/2 ball, the transpose-inverse bound with the n factor); (3) hG and hD3 of B5-NF are genuinely
discharged: C³ from holomorphy, C₃ = 64 (Mμ/2)/r³ from three nested Cauchy steps (check the radii bookkeeping and the
real-slice transfer of the third derivative); the oscillation bound Mμ/2 from G1Hyps.hbd by the mean value theorem;
(4) the conclusion is torus_confinement's with V = real slice of c.D, ω' = sinf ω*, E0; (5) hygiene (AGENTS rules 3, 4,
7; widths ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
