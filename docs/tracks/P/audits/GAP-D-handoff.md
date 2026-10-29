# GAP-D prover handoff (branch inp-gapd, 975b1abe; off inp with T16 (passed); offloaded gap-fill package run by the main orchestrator)


**File (new):** `KAM/Planetary/PlanarTorsion/BirkhoffClauses.lean` (185 lines). No other file touched
(KAM.lean not edited; `lint_sources.sh` reports "KAM.lean is out of date" because the new module is not yet
in the generated root: orchestrator must regenerate it).

## Node -> declaration (all in `KAM.Planetary`, unsigned, imports only `PlanarTorsion.Birkhoff`)
- `bpP:p11b:birkhoff-form` clause (a): `birkhoff_form_hamiltonian`. Same telescope as `birkhoff_form`
  (p, hp, a0, rho, hgoodK); for every good open `Oa` yields `O'`, the T = rotationLift ∘ liftFlow chi.eval
  of T16, and for both `fhat ∈ {hatFix, hatMov}`: `AnalyticOnNhd (fhat ∘ T)` on the tube, `2π`-periodicity in
  the angles (`fastShift k`), and `H^Ψ ∘ T = h(Λ) + μ (fhat ∘ T)` with `movingHamiltonian` (hatMov) /
  `fixedHamiltonian` (hatFix), `h(Λ) = hProd p.kappa p.m w`. Independence of the coupling is literal.
  Proof: consumer deduction from `movingHamiltonian_poincareProd` / `fixedHamiltonian_poincareProd`
  (helper `p11cG_split`) and `poincareProd_lattice` (helper `p11cG_periodic`), using T16's action
  preservation, angle covariance and domain clauses.
- `bpP:p11b:lift-map` explicit form: `lift_map_explicit` (any chi): `T(assemble I φ z.2 z.1) = assemble I
  (φ + g + H) (ρ Y).2 (ρ Y).1`, `g_l = ∫₀¹ ∂_{Λ_l} chi(Λ, φᵗ(Λ,z)) dt`, `H_l = ỹᵀ(ρᵀ∂ρ)x̃` with `Y = flow chi I 1 z`.
- `bpP:p11b:lift-map` properties: `lift_map_properties` (telescope of `birkhoff_form`): the explicit
  formula for the `T` of `birkhoff_form`, `IsChart 1 T tube` (analytic + symplectic), `InjOn`, action
  preservation, commutation with angle translations.
- Helpers (distinct names, grep-checked unused in KAM): `p11cG_split`, `p11cG_periodic`.

## Approach / deviations
No GAP-D entries exist in `P11CSignatures.lean`, so statements were designed from the node text. They
quantify existentially over `r, C, Oa, O'` exactly as `birkhoff_form` does and reuse its proof, so hypotheses
are T16's only. "Diffeomorphism onto its image" is rendered as `IsChart 1` (analytic + `IsSymplecticOn`)
plus `InjOn`, the form T16 delivers. Signature choices are the orchestrator's to audit.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gapd KAM.Planetary.PlanarTorsion.BirkhoffClauses`: Build completed
  successfully, no warning from this file.
- `#print axioms` for all three theorems: `[propext, Classical.choice, Quot.sound]`.
- Lines ≤ 100 (checked); no `set_option`, no sorry.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message is
  "KAM.lean is out of date" (expected, not edited by rule).

## Uncertainties / errata
- bt-rot (angle lift) not in scope. No source errata found. Blueprint's `H` uses `ỹ=Y.2`, `x̃=Y.1`, matching T14's `rotationLift`.

ORCHESTRATOR RULING (OVERNIGHT 00:10): append-only gap fill of the clauses the sub-orchestrator found unstated after T16: clause (a) of bpP:p11b:birkhoff-form and the explicit form plus properties of bpP:p11b:lift-map. stepP:p11b:bt-rot / bt-rot#lift are BYPASSED under D27 and are not findings here.

AUDIT FOCUS: read NODE: bpP:p11b:birkhoff-form and NODE: bpP:p11b:lift-map in docs/graph/P/DEPGRAPH.md (SOURCE_CONCLUSION) and blueprint p11b-planar-torsion.tex around line 208. Verdict per node: do birkhoff_form_hamiltonian, lift_map_explicit and lift_map_properties, together with T16's birkhoff_form / PlanarBirkhoffResult, state every clause of the literal node conclusions (H^Psi o T = h(Lambda) + mu P with P analytic and 2 pi-periodic, for both the moving and fixed perturbations; T = (lambda + g + H(Lambda, Y), Lambda, rho Y) with g, H as in the blueprint; the three properties) with only T16's hypotheses and no added premise? Audit ONLY KAM/Planetary/PlanarTorsion/BirkhoffClauses.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
