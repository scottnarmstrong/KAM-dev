# Package LP-DICT: planar chart dictionary (MAIN L7) and the one-centre L13 adapter test

Wave 1/2. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).
The audit (PROOF-AUDIT-1 §6) asks for an EARLY test of the Lemma 13 interface (physical orbit → rescaled chart →
`KAM.Nekhoroshev.nonresonant`), the riskiest interface of the campaign. Part B is that test.

## Source

- `docs/tracks/LP/source/MAIN.md` Lemma 7 (lines 193–242; N1 fixed at 238) and Lemma 13 (lines 429–464), with
  `source/AMENDMENTS.md` (**N6** is binding for Part B: `2πs₁ < 4s`, `w < 4b`, `D₀√μ < r_*`,
  `F = realWfield b.c (realHamiltonianExt b b.rB (liftFast h + f))`, `realDom` open, stopped radius `r = D₀√μ`,
  improvement to `r/2`).
- Roadmap §1 (period one: `θ = λ/(2π)`, `Ĥ = H/(2π)`, `ℓ = w/r`, bracket `2π/ℓ²`; MAIN `(x, y)` = repository
  `(ξ, −η)`), §3 rows 7 and 13, §5.

## Existing code to reuse (do NOT build a second chart or a second engine)

- Chart: `KAM/Planetary/Poincare/{Chart,Symplectic,Bijective,Product}.lean` (`poincare`, `poincare_elements`,
  `poincare_image`, `poincareInv`, `poincareProd`, `poincareProdDom`, `regionProd`, `poincareProd_symplectic`,
  `analyticOnNhd_poincareProd`, `movingHamiltonian_poincareProd`).
- Dictionary already proved for track P: `KAM/Planetary/Exponential/Dictionary.lean`
  (`sec_domain_chart_facts`: prograde, `keplerAction = fast w.2 i`, axis, `L_i = Λ_i − Γ_i`,
  `physicalAMD = chartAMD w`; `poincareProd_image_prograde`), `Exponential/Setting.lean` (`chartAMD`,
  `chartSafe`), `Exponential/Lift.lean` (`liftChartHam`, `liftPhysicalDeriv`, chart lift of a physical
  solution), `Exponential/Hamiltonian.lean` (`fderiv_eq_of_eqOn_open`, `hamiltonianVectorField_eq_of_eqOn_open`).
  Read them first; most of Part A is restatement. Import implementation modules only (never
  `KAM/Frozen/*/Theorems/*`; `Exponential/Stopped.lean` imports a frozen theorem anchor, so do NOT import it).
- Engine: `KAM/Nekhoroshev/Partial/{Setting,Nonresonant}.lean` (`PartialBlock`, `ER`, `EC`, `fastAction`,
  `slowPair`, `realWfield`, `realHamiltonianExt`, `PartialBlock.realDom`, `ExtNFHyp`, `nonresonant`).

## Owned files

`KAM/Planetary/StrongAMD/PlanarDictionary.lean` (Part A) and `KAM/Planetary/StrongAMD/NonresonantAdapter.lean`
(Part B); split with facades if needed. Nothing else.

## Part A: MAIN Lemma 7 dictionary (premises `∀ i, 0 < ν i`, `κ = 1`)

1. **Region.** `poincareProd ν 1 '' poincareProdDom n` = `{z | ProgradeElliptic ν z}` (MAIN line 195), reusing
   `poincareProd_image_prograde`.
2. **Per-planet dictionary** on `poincareProdDom n`: `I = Λ`, energy `−ν³/(2I²)`, `L_i = I_i − Γ_i`,
   `keplerEccVector ν z i = poincareV (planetBlock w i)`, `e² = 1 − (1 − Γ/I)²`, and MAIN's
   `(k, l) = b_e (x, −y)` versus the repository `poincareV = b_e (ξ, η)` stated as an explicit identity under
   `(ξ, η) = (x, −y)` (MAIN line 199).
3. **AMD in the chart:** `physicalAMD ν (poincareProd ν 1 w) = chartAMD w` (exists) and the same for MAIN's
   `C = (∑ i, keplerAction ν z i) - |totalMomentum z|` (write it literally; package LP-MOM defines it as
   `strongAMD` and the names are joined at landing).
4. **One-line MAIN-facing corollaries** at `κ = 1`: the chart Hamiltonian identity, symplecticity, analyticity,
   fast-angle periodicity and the inverse on the prograde region (MAIN L7 "real analytic symplectic
   diffeomorphism … onto"). Do not reprove what exists.

## Part B: the L13 adapter, one centre (MAIN lines 437–441 and N6)

5. **Rescaling.** Define the period-one rescaling `lpRescale (ℓ : ℝ) : Phase (n + n) → ER n n`
   (`θ = λ/(2π)`, fast action `= Λ`, slow pair `= (ξ, η)/ℓ`, with whatever slot order and sign the engine's
   `fastAction`/`slowPair`/`realWfield` use) and its inverse; prove both are continuous linear (affine) maps and
   mutually inverse.
6. **Field conversion (physical time unchanged).** For `G : Phase (n + n) → ℝ` differentiable at `w` and
   `Ĝ := (1/(2π)) • (G ∘ lpRescale⁻¹)`: if `HasDerivAt w (hamiltonianVectorField G (w t)) t` (the chart
   convention used by `Exponential/Lift.lean`), then
   `HasDerivAt (lpRescale ℓ ∘ w) (realWfield (2π/ℓ²) Ĝ (lpRescale ℓ (w t))) t`. This is where period, time
   and bracket conventions are checked: if they do NOT match (a sign or a factor), STOP and report the exact
   mismatch; do not adjust the engine's statement.
7. **Indicator Hamiltonian.** If `PartialBlock.realDom b R` is open (prove it, or report) and
   `((liftFast h + f) (extCx y)).re = Ĝ y` on it, then
   `realWfield b.c (realHamiltonianExt b R (liftFast h + f)) = realWfield b.c Ĝ` on `b.realDom R`, when
   `b.lam = ℓ` (so `b.c = 2π/ℓ²`).
8. **Physical orbit → engine orbit.** For a moving solution `z` on an `OrdConnected` `J ∋ 0` whose chart lift `w`
   (`z = poincareProd ν 1 ∘ w`, from `Lift.lean` or a direct local-diffeomorphism argument) stays where item 7's
   trace identity holds, `y := lpRescale ℓ ∘ w` satisfies the `hy` premise of `nonresonant` with `F` as in N6.
9. **Conditional one-centre composition** (a helper with a DISTINCT name, e.g.
   `nonresonant_drift_of_chartData`, docstring "conditional on the analytic data of MAIN L8; not a source
   result"): from `ExtNFHyp b s K α L p ε {0} h f`, the smallness premise, the trace identity, the moving
   solution, `fastAction (y 0) = b.Ic` and the stopped slow-membership premise, conclude
   `‖(fun i => keplerAction ν (z u) i) − b.Ic‖ ≤ b.rB / 2` for `u ∈ uIcc 0 t1`,
   `|t1| ≤ s * b.rB / (5 * ε) * exp (2π K s / 6)`. Its premises are exactly the engine's inputs plus the
   physical solution; it must not assume any drift, confinement or AMD bound.

Out of scope: the existence of the analytic data (MAIN L8), the scale arithmetic (37) (package NonresonantScale),
and the first-exit argument (L14).

## Checks and stop condition

`lp_build.sh` on each new module (import order); `lp_lint.sh` exits 0; `#print axioms` of items 1–9. Stop when
done or blocked; a convention mismatch in item 6 is a valid, valuable stopping result (report it precisely).
Expected size 600–1,400 lines.

## Handoff

`docs/tracks/LP/audits/LP-DICT-handoff.md` (committed) and `.drafts/handoff-LP-DICT.md`, then
`touch .drafts/READY-LP-DICT`.
