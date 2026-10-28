# N11-E1 prover handoff (branch inp-n11e1, c198ff11; offloaded package run by the main orchestrator)


## Files (new)
- KAM/Nekhoroshev/Partial/Flow.lean (132 lines): `flow`, `flow_real` (+ `extImCLM`, `extImCLM_eq_zero_iff`).
- KAM/Nekhoroshev/Partial/SymplecticLinear.lean (356): helper module. Regrouping
  `(θ,(I,q,p)) ↦ ((θ,q),(I,p/c))` (`regroup c hc : EC n k ≃L[ℂ] ℂ^{n+k}×ℂ^{n+k}`), `wfieldOf_eq`,
  `extForm` (signature def, verbatim), `extForm_eq`, `canonical_at_iff`, `form_of_bracket`.
- KAM/Nekhoroshev/Partial/Symplectic.lean (400): `symplectic`, `symplectic_bracket`, `symplectic_det`,
  `symplectic_form` (signatures verbatim), `symplectic_field` (field identity
  `DΨ(wfield c (v∘Ψ)) = wfield c v ∘ Ψ`, an extra unsigned export used by `conj`), `conj`.

## Approach
- `flow`: direct from Part 5 `flow_a`, `flow_b`.
- `flow_real`: Part 5 `flow_e` Picard-iteration proof repeated with the imaginary-part CLM on `EC n k`.
- Symplectic: `ExtCanonical` pointwise is equivalent (`canonical_at_iff`) to `Y J(η∘Y)=J η` for `Y = L DΨ L⁻¹`;
  the flow part runs the variational-equation argument with `extForm c` (`extForm_const`, `flow_extForm`),
  skew-symmetry transported from `symplFormC_fderiv_field_skew`. `symplectic_bracket` and
  `symplectic_field` need no `c>0` (pure algebra on functionals). Det via `LinearMap.det_conj`.
- `conj`: complex curve `Ψ∘extCx∘y`, field identity, then `extRe`. Needed private copies of RealSystem's private
  helpers (`extCx_mem_Dom_iff`, `realWfield_cx`, ...) inside `Symplectic.lean` (private, no name clash).

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-n11e1 Flow SymplecticLinear Symplectic` -> "Build completed successfully (3235 jobs)"; no sorry, no warnings in my files.
- `main_shortname_check.py`: OK. Lines <= 100 cols. No maxHeartbeats.
- `scripts/lint_sources.sh`: PASS, frozen guard OK, ABI OK; only message "KAM.lean is out of date" (new modules; generated file, not edited by me).
- `#print axioms` flow, flow_real, symplectic, symplectic_bracket, symplectic_det, symplectic_form, conj:
  all `[propext, Classical.choice, Quot.sound]`.

## Design signals
- `fun_prop` / `Continuous.comp_continuousOn` on `symplFormC` pairs hit default-heartbeat whnf/isDefEq timeouts
  (the def unfolds a sum); replaced by explicit coordinatewise continuity lemma `continuousOn_symplFormC_curves`.

## Uncertainties / errata / deviations
- None found in sources; no signature changed. Extra public helper modules/lemmas beyond the signature list as above.
- `extForm` is defined in SymplecticLinear.lean (imported by Symplectic), same statement as signature.
- Gate queue waits were ~16 min per build; iteration used `lake env lean`.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-E1 (flow wrapper/reality, Omega_c invariance/determinant/field, conj) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Audit ONLY KAM/Nekhoroshev/Partial/{Flow,SymplecticLinear,Symplectic}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

ORCHESTRATOR RULING (OVERNIGHT 20:50): the signed name KAM.Nekhoroshev.flow clashed with Part 5's KAM.Nekhoroshev.flow (KAM/Nekhoroshev/Averaging/Flow.lean); the signature file line 213 now reads 'theorem ext_flow' (statement unchanged) and N11-E1 renamed it (c198ff11). Check ext_flow against that line; flow_real keeps its name.
