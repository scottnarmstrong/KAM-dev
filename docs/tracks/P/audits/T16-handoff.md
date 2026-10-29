# T16 prover handoff (branch inp-p11c-t16, f62f2b53; contains T10, T11, T13 (all passed), T14, T15; offloaded package run by the main orchestrator)


## Result
`KAM.Planetary.birkhoff_form` and `KAM.Planetary.PlanarBirkhoffResult` (and the signed `p11c_phi4`) are
proved/defined **verbatim from `.drafts/design/P11CSignatures.lean`**, with no `sorry`, no `axiom`, no
heartbeat/recursion override, no `EuclideanSpace`. All new files are `module`s (copyright, `module`, imports,
docstring, `public section`/`@[expose]`), lines <= 100 columns, each file far below 1500 lines (2020 lines total).

`#print axioms KAM.Planetary.birkhoff_form` -> `[propext, Classical.choice, Quot.sound]`
(also `p11cB_estimate`: the same).

## Files (all new)
`KAM/Planetary/PlanarTorsion/Birkhoff.lean` (facade + `birkhoff_form`) and under `Birkhoff/`:
`Defs` (signed `p11c_phi4`, `PlanarBirkhoffResult`), `Domain`, `Family`, `Diag`, `Jets`, `Choice`, `Chi`,
`Map`, `Compose`, `Average`, `BetaAvg`, `Estimate`, `FhatClause`, `Result`, `Constants`.
(`KAM.lean` NOT edited; see below.)

## Graph nodes (all are *local* steps of `birkhoff_form`; no unsigned node export is introduced)
- `bt-rot` / `bt-rot#lift`: `global_planar_frame` (T14) + `p11c_rotationLift_chart` composed with `lift_map` (T11):
  `p11cB_T_props` (chart/inj/action/translation of `T = rotationLift ∘ liftFlow chi.eval`, `Compose`),
  `p11cB_T_assemble` (`T` only translates angles, `Map`).
- `bt-K`: `p11cB_K/C/R` (`Jets`): joint analyticity `p11cB_secular_analyticAt`, `p11cB_R_analyticAt`; vanishing 5-jet
  `p11cB_R_jetEq` (diagonal derivatives: `quadratic_physical_bridge`, `qe_fix_jet`, evenness `SecularForm.evenness`,
  `UᵀQU = diag σ` = `p11cB_quad_rot`); physical radius `p11cB_domain` (`Domain`: open good domain
  `p11cB_good`, circular points collision free, compactness tube lemma + lattice periodicity).
- `bt-nf`: `p11cB_family` (rotated quartic as `QuarticFamily`, via `p11cB_rotC` + `quartic_extract`), NR4 from
  `p11c_phi4 ≠ 0` (`p11cB_NR4`), `homological` (T10), `lie` (T10), `p11cB_average_beta` (`beta_formula`, T13).
- `bt-avg`: `p11cB_secular_T` (translation invariance of the radian torus average of `f̂ ∘ T`), `p11cB_secular_mov`
  (moving = fixed + `modelDelta`), `p11cB_estimate`.
- `bt-frozen`: `p11cB_fhat_clause` applies T15 `hasSecularBirkhoffForm_of_sixth_order` to the actual pullback.
- Assembly: `p11cB_result` (everything depending on `Oa`), `p11cB_main` (`Constants`: `r`, `C` chosen before `Oa`).

## Approach
1. `r`, `C` do not depend on `Oa`: take `δ0` with `thickening δ0 (closedBall a0 rho)` inside the (open, since
   `p11c_phi4` is continuous) good axis set; `Og := p11cB_O p Kc δ0`; the quartic family `F₀`, `chi` (homological) live
   on `Og`; radii of `lift_map`, `flow`, `lie` and the physical domain are taken on the compact action image `K₁`
   of the `δ0/2`-cthickening; `r := min(rL, r1, rl, δ/2)`, `C := max A 1`.
2. For a given `Oa`, `O' := p11cB_O p Kc ε'` with `ε' = min(δ0/2, δ'/2)`; families restrict (`p11cB_restrict`).
3. Everything is stated with thickenings of the compact set `closedBall a0 rho`, so `rho < 0` (empty ball) needs no case.
   The hypothesis `Oa ⊆ good` of the signed theorem is not used (the result is stronger).

## Checks (exact)
- Gate builds (`inp_lake_build.sh`, `LEAN_NUM_THREADS=1`): `KAM.Planetary.PlanarTorsion.Birkhoff` ->
  `Build completed successfully (9324 jobs).` Upstream T10/T11/T13 modules (NormalForm, Lift, Beta) were not in the
  build snapshot, so the gate also built them (9307 jobs) before my modules.
- Per-file `lake env lean` of each of the 15 `Birkhoff/*.lean` files: 0 warnings, 0 errors.
- `sh scripts/lint_sources.sh`: `check_lean_modules: PASS (1091 Lean files...)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (144 frozen declarations)`; it also prints `KAM.lean is out of date; run scripts/gen_root_imports.py`
  — expected: `KAM.lean` is generated and I must not edit it. **The orchestrator must regenerate `KAM.lean`.**
- Greps: no `maxHeartbeats`, `EuclideanSpace`, `sorry`, `axiom`, `admit` in my files.

## Design signals (heartbeats)
No override used. Several default-heartbeat `whnf`/`isDefEq` timeouts occurred while elaborating
`AnalyticAt.comp_of_eq (g := …) …` / `exact` against the unfolded `secular`/`secularAverage`/`p11c_secular` terms
(`Jets.p11cB_secular_analyticAt`, `p11cB_R_analyticAt`, `Average.p11cB_secular_T`). Fixed by splitting
(`have := … ; exact this`, naming `h1`/`h2` by `rfl`, `integral` rewriting via `congrArg`), never by a budget. Worth
noting for T20/T21: `p11c_secular`/`SecularForm.secular` must stay semi-opaque in `exact` targets.

## Uncertainties / deviations
- Location: `p11c_phi4` and `PlanarBirkhoffResult` are in the leaf module `Birkhoff/Defs.lean` (needed by the proof
  modules; the facade `Birkhoff.lean` re-exports it via `public import`, so `KAM.Planetary.PlanarTorsion.Birkhoff`
  provides every signed name). Their text is verbatim except one line-wrap (`C * (p11c_slowLength z) ^ 6`).
- `full_lift_hamiltonian` (T11) is not used: `PlanarBirkhoffResult` does not contain the Hamilton equations; (a)
  `H^Ψ∘T = h + μP` of the blueprint statement is not a clause of the signed predicate and is not proved here.
- `p11c_frameActionDomain` (T14) contains actions of arbitrary sign; positivity of actions is therefore carried
  explicitly (`p11cB_O` requires `0 < I i`; `p11cB_domain` needs positivity).
- Moving perturbation: `P0 I := p11c_secular fhat I 0` (so `C₀ + δ(I)` for `f̂_mov` by `p11cB_secular_mov`).

## Suspected errata in pinned sources
None found that affect the signed statement. Remarks: (i) blueprint `bt-rot` still uses simple connectedness (already
superseded by T14); (ii) blueprint `bt-K` obtains `ρ_K` by compactness over polydiscs; the Lean proof instead uses
the compact tube lemma around the circular torus plus lattice periodicity (equivalent, no defect).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T16 (PlanarBirkhoffResult, birkhoff_form; T10/T11/T13/T14/T15, U8b) and its node table incl. bt-* steps; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Special checks: (1) the handoff says the blueprint clause (a) H^Psi o T = h + mu P is NOT a clause of the signed PlanarBirkhoffResult and is not proved: decide whether the signed predicate deliberately narrows the node (then check every consumer, especially P1213's P12-C / P12-E (docs/tracks/P/design/P1213-LEAN-DESIGN.md) and the frozen planarTwoPlanetKAM / fixedSunPlanetaryKAM telescopes, can do without it, or obtain it from another export) or whether its absence is a completeness finding; (2) action positivity carried explicitly (p11cB_O, p11cB_domain): no added premise to the signed statement; (3) T11's lift_map and T14's rotation-lift chart are actually consumed. Audit ONLY KAM/Planetary/PlanarTorsion/Birkhoff.lean and Birkhoff/*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
