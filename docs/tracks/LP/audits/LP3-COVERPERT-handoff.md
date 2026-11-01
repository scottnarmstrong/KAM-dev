# LP3-COVERPERT handoff (LP3-COVER + LP3-PERT)

Branch `inp-lp-lp3cp`. Track LP, non-frozen. No `sorry`, no heartbeat overrides, no existing file edited
(except the generated `KAM/Root/Planetary.lean`, two import lines from `scripts/gen_root_imports.py`).

## Files
- `KAM/Planetary/StrongAMD/Nek/Cover.lean` (329 lines): LP3-COVER.
- `KAM/Planetary/StrongAMD/Nek/Perturbation.lean` (261 lines): LP3-PERT.
Imports: `AnalyticDomain.Containment`, `AnalyticDomain.Extension`, track P `Exponential.{Stopped,Hamiltonian,Lift}`
(Stopped public-imports the SEALED anchor, OD-13; no provider is imported).

## Declarations
All in `KAM.Planetary.StrongAMD`. Let `rs = nekWidth rg R = min (4 rg) (R/4)`, `η = rs/4`, `ρ = rs/8`.

LP3-COVER (plan (F3)-(F7)):
- `nekWidth, nekEta, nekRho` and lemmas `nekWidth_pos`, `nekWidth_le_four_mul`, `nekWidth_lt_half`,
  `nekEta_pos`, `nekRho_pos`, `nekRho_le_eta`, `four_mul_nekEta`, `nekEta_le` (η ≤ r_g).
- Cells: `nekCellInner c = ball c η` (G_j), `nekCellOuter c = ball c (2η)` (G'_j),
  `nekCellLevel ν δ c = B(c) - 5δ/16`, `nekCellSlow ν δ c = slowBall n (nekCellLevel ν δ c)` (D_j);
  `isOpen_/convex_nekCellInner/Outer`, `isOpen_nekCellSlow`, `nekCellInner_subset_outer`.
- `nekCell_collar : I ∈ G_j → closedBall I ρ ⊆ G'_j`.
- `IsNekCover ν L δ rg R s` (centres in `strongLevelSet`, every point of 𝓛_δ within `η/2` of a centre) and
  `exists_isNekCover` (compactness; `s : Finset`).
- `nekCell_mem_of_close`, `nekCell_mem_innerCore`, `IsNekCover.mem_innerCore`: `‖I0-c‖<η/2`, `0≤r≤η/4`
  gives `I0 ∈ innerCore (G_j) r`, and stopped actions within `r` of `I0` stay in `G_j`.
- `nekCell_threshold_bound` (`‖I0-c‖ ≤ 4 rg` ⟹ `|B I0 - B c| ≤ δ/16`) and `nekCell_threshold_bound_of_close`.
- `nekCell_containment : partialComplexDomain G'_j D_j ρ ⊆ complexTube (strongCore ν L δ rg) (R/2)`
  (via `strongCore_containment`, s = b = η, centre c_j).
- `nekCell_slowGap_pos`, `exists_nekSlowGap`: ∃ εD > 0, ∀ c ∈ s, ∀ 0 ≤ ε < εD,
  `√(2(B c - 3δ/8)) + √(2n) ε < √(2 (nekCellLevel c))` (the hypothesis of `stopped_slow_erosion`).

LP3-PERT:
- `IsStrongExtension ν L δ rg R M fc` (the four clauses of `exists_strongTube`), `exists_isStrongExtension`.
- `nekNormalizedPerturbation ν L δ rg R fc B0 z = if z ∈ complexTube core R then fc z / B0 else 0`.
- `isPartialPerturbation_nekCell`, `isPartialPerturbation_neg_nekCell` (for `-P`): hypotheses `0<rg`, `0<R`,
  `0<δ`, `0<B0`, `M ≤ B0`, `c ∈ strongLevelSet ν L δ`.
- `nekCellRegion` (V_j), `isOpen_nekCellRegion`, `complexifyPhase_mem_nekCell`, `nekCell_region_trace`.
- `nekCell_hamiltonian_eq`: on V_j, `degenerateHamiltonian (realPart (planetaryKeplerC ν)) (Re P ∘ cx) (B0*μ) w = liftChartHam ν μ w`.
- `nekCell_field_eq`: differentiability and equality of `KAM.hamiltonianVectorField` on V_j.
- `exists_nekPerturbation` (bundled): ∃ R>0, ∃ B0 ≥ 1, ∃ P, (∀ c ∈ 𝓛_δ, IsPartialPerturbation ± P on (G'_c, D_c, ρ)) ∧
  (∀ c ∈ 𝓛_δ, ∀ μ, ∀ w ∈ V_c, w ∈ chartSafe ∧ identity ∧ DifferentiableAt ∧ field equality).

## Not done / notes
- Cell statements hold for every centre in 𝓛_δ, not only for the finite cover (stronger and simpler).
- The brief says the identity is "the chart Hamiltonian divided by B0"; the plan (§2.3) has no division: with
  ε = B0 μ the N-Hamiltonian equals `liftChartHam ν μ` exactly. I followed the plan (no time rescaling).
- The `-h`/Kepler data on balls is LP3-KEP; the sharpened stopped bound (plan §2.4 step 4) and the finite
  minimum of thresholds are LP3-DRIFT. Not touched here.
- Tooling: `lp_lean.sh` runs with autoImplicit enabled (it hid a missing `{ν}` binder that `lp_build.sh` caught).
  Use `lp_build.sh` as the real check.

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-lp3cp KAM.Planetary.StrongAMD.Nek.Cover` : Built (9325 jobs), no warnings in my file.
- `lp_build.sh ... KAM.Planetary.StrongAMD.Nek.Perturbation` : `✔ Built KAM.Planetary.StrongAMD.Nek.Perturbation`, Build completed successfully (9327 jobs).
- `lp_lint.sh` exit 0 (after `gen_root_imports.py`): `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- `main_shortname_check.py ... Cover.lean Perturbation.lean` exit 0: `short-name check OK`.
- `#print axioms` (scratch `.drafts/ax_coverpert.lean`): `exists_isNekCover, nekCell_containment, nekCell_collar,
  nekCell_threshold_bound, exists_nekSlowGap, IsNekCover.mem_innerCore, isPartialPerturbation_nekCell,
  nekCell_hamiltonian_eq, nekCell_field_eq, exists_nekPerturbation`: all `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
1. Widths: `hmax` in `nekCell_containment` (`4η = rs ≤ R/4 < R/2`), `hact` bound `2η + ρ < 4η = rs`.
2. `nekCellLevel = B(c) - 5δ/16 ≤ B(c) - δ/4` (needs δ>0) so `D_j ⊆ secularBall`.
3. Slow gap: positivity uses `B(c) ≥ δ` (c ∈ 𝓛_δ) so `A'_j = B(c) - 3δ/8 ≥ 5δ/8 > 0`.
4. `nekCell_hamiltonian_eq`: sign/scale (`B0 * μ`, no division), `realPart_planetaryKeplerC`.
5. `nekNormalizedPerturbation` is `0` off the tube; only values on the cell's complex domain (inside the tube) matter.
6. `exists_nekPerturbation` quantifier order: R, B0, P depend only on (ν, L, δ, rg); cells quantified after.

## Errata / deviations / design signals
No source defects found. Deviation: bundled cell statements for all centres in 𝓛_δ. No heartbeat issues
(each file builds in under 10 s); files 329 and 261 lines.
