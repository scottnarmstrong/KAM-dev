# B16 prover handoff (branch inp-p11b-b16, 77aeaaed; contains B15 (passed); offloaded package run by the main orchestrator)


Branch `inp-p11b-b16`. All work committed (never force-added `.drafts/`).

## Files (new)
- `Tori.lean` (77 lines): verbatim `selectionHamiltonian`, `SelectionTori`, and `limit_torus` (proved).
- `ToriField.lean` (100): `toriF`, `tori_H0_field`, `tori_invariance_real` (complex field -> frozen real
  `hamiltonianVectorField (realHamiltonian h f)` via `KAM.hamiltonianVectorField_eq_of_real`).
- `ToriLimit.lean` (268): reality of `h'`, of `ω_ν(b)`, `ω_ν -> ω_*`; Cauchy-jet decay; limit point domain;
  continuity of `X_{H₀}`; `tori_invariance_C` (steps lt-field/lt-cov/lt-lim).
- `ToriReal.lean` (204): `limitC b` real on reals, `selectionEvaluation = realRestriction + (0,b)`; analyticity,
  real derivative relation, Lagrangian (limit of the zero-section pullback, `lt-lag`), immersion/embedding (`lt-emb`).
- `ToriStage.lean` (241): `toriH0`, finite-stage identity `X_{H₀}(Φ_ν z)=DΦ_ν(z)(ω_ν+∂_ηR_ν, -∂_θR_ν)` (`lt-field`,
  `lt-cov`) and Cauchy bounds `ε_ν/(s_ν/2)`, `ε_ν/(strip/4)` for the jet.
- `ToriBridge.lean` (154): one-variable directional Cauchy, `symplFormC` nondegeneracy, `dH = -Ω(X_H,·)`,
  covariance `DΦ X_{G∘Φ}=X_G∘Φ` for a symplectic near-identity `Φ`.
All files < 300 lines, lines ≤ 100 columns, no `maxHeartbeats`, no `sorry`/`axiom`/`unsafe`/`opaque`, no
`EuclideanSpace`. `Tori.lean` is the facade (imports the chain); it contains the signed declarations.

## Approach
`limit_torus`: `cx := weakBudgetCtx_of` as in `limit_map`; take `L` from `limit_map`; extend it with the new fields.
- Covariance (`lt-cov`) is proved directly with the complexified frozen form `Canonical.symplFormC` (derived from
  `composition_symplectic`), nondegeneracy of `symplFormC`, and bijectivity of `DΦ_ν` from `‖DΦ-id‖ ≤ 2⁻¹¹` (finite
  dimension). I did NOT use `chart_field` (real Phase map) — the complex route avoids restricting a composed real map
  and needs no reality of `E_ν, R_ν`; no small-holomorphic-flow theorem is invoked.
- `lt-field`: normal form differentiated at the zero section; Cauchy for `R_ν` with radii `s_ν/2` (η) and `strip/4` (θ).
- `lt-lim`: uniform value/derivative convergence from `SelectionLimit`, `frequency_uniform` for `ω_ν -> ω_*`, continuity of
  `X_{H₀}` at the limit point (`KAM.analyticOnNhd_of_differentiableOn`), then the real field from `KAM.Strip.RealRestriction`
  (`realRestriction_fderiv`, `hamiltonianVectorField_eq_of_real`, `analyticOnNhd_realRestriction`).
- `lt-lag`, `lt-emb`: as in the brief; `lt-dio` is the record's existing `diophantine` field. Orbit by chain rule.

## Checks
- Gate: `inp_lake_build.sh <wt> KAM.Planetary.WeakKAM.Tori` -> "Build completed successfully (9213 jobs)"; no warnings in Tori* files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only message is
  "KAM.lean is out of date" (generated root; not edited per rules).
- Signature diff: `selectionHamiltonian` and `SelectionTori` bodies identical to `P11BSignatures.lean`; `limit_torus` statement identical.
- `#print axioms KAM.Planetary.limit_torus`: `[propext, Classical.choice, Quot.sound]`.
- Short-name clash grep: all new public names are `tori*`/`toriH0*`/`toriF`/`toriRem`/`toriJet`; none used elsewhere in KAM.

## Uncertainties / design signals
- No heartbeat problems. `SelectionTori` inherits `limit_holo` on `d.strip/4`; I used `d.strip/4` throughout.
- Uses `cx.adm` (`SelectionAdmissibility`) only for `a.s₀ ≤ ϑ` and `Q₀ ≤ 1/2` (limit point lies in the domain of `f`).
- Builds depend on B15 (merged on the branch) being built in the overlay (I built `Limit` via the gate first).

## Suspected errata / deviations
None found. Deviation from design note: real covariance via `symplFormC` directly instead of `chart_field`
(equivalent; avoids the shared-build gate on PP1-4).

AUDIT FOCUS: design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B16 (Tori; B15, delivered P1 chart_field and real restriction, frozen dynamics) and its node table incl. lt-* steps; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean (selectionHamiltonian, SelectionTori, limit_torus). Check the invariance is for the FROZEN real Hamiltonian vector field and the Lagrangian/embedding clauses. Audit ONLY KAM/Planetary/WeakKAM/Tori*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
