# N11-F1 prover handoff (branch inp-n11f1, adc0f148; lane N paused 2026-10-28; NOT yet independently audited)


## Files (new)
- KAM/Nekhoroshev/Partial/CompositionCoeff.lean (218): independent-dimension helpers (`*_ext`).
- KAM/Nekhoroshev/Partial/Composition.lean (590): `ExtCompose`, `extGauge`, `composition_domain`,
  `composition`, `composition_real`, Lie-series engine (`ExtCompose.lieTerm_bound`, `lieSeries_*`,
  `series_eq`, `flow_smul`, `comp_t_class_bound`).
- KAM/Nekhoroshev/Partial/TransformIntegral.lean (314): ParamHyp/Fubini engine
  (`ExtCompose.integral_inClass`, `integral_bound`, `coeff_integral_ext`).
- KAM/Nekhoroshev/Partial/Transform.lean (380): `transform`, `transform_integral`, remainder series
  (`extRemTerm`, `extRemSeries_*`), `transform_identity`.
- `extFlow` is NOT defined here: merged inp-n11f2 and imported the shared `Partial/ExtFlow.lean`
  (orchestrator note). Signed declarations copied verbatim (ExtCompose, composition, composition_domain,
  composition_real, transform, transform_integral).

## Nodes
co-field/co-series/co-remainder/composition -> `composition_domain`, `composition`, `composition_real`;
tr-taylor -> `ext_taylor_second` use inside `transform`; tr-int -> `transform_integral`, `ExtCompose.integral_*`.

## Approach
Port of Part 5 (Canonical/Composition*, TransformSeries, Transform) to EC n k with the adjoint constant
q = e²η/8 (q ≤ η, since e² < 8). Gauge `extGauge` with `norm_extGauge`; field size from `vf`; flow from
generic Part 5 `flow_a/b/d`; Taylor from N11-E2 `ext_taylor`, `ext_taylor_bound`, `ext_taylor_second`;
reality from `flow_real` and `real_system`. Remainder equals the series sum on the domain, giving the
stated class/bound.

## Checks
- Gate build of KAM.Nekhoroshev.Partial.{CompositionCoeff,Composition,TransformIntegral,Transform}:
  success, no errors, no warnings in these files, no sorry.
- #print axioms composition, composition_domain, composition_real, transform, transform_integral:
  [propext, Classical.choice, Quot.sound].
- scripts/lint_sources.sh: check_lean_modules PASS (959), FROZEN-ANCHOR GUARD OK, ABI HASHES OK;
  prints "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated; not edited by me, orchestrator to regenerate).
- Lines <= 100 columns; all files < 1500 lines. No maxHeartbeats.

## Uncertainties / errata / deviations
- No statement changes or extra hypotheses. No design signals (no heartbeat problems).
- Extra non-signed public helpers (all with `_ext`/ExtCompose-namespaced names, grepped unique):
  see files above. `q_facts_ext`, `mem_Dom_of_scaled_le`, `extGauge`, `cubeE` are public.
- Observation: `ExtCompose` hypotheses imply the transform/composition `hU`/`hW` are genuinely needed
  (kept as in the signature).

## PAUSE STATUS (lane N paused by owner)
- Done: ALL N11-F1 declarations listed above (nothing remaining in this package); all committed on inp-n11f1,
  working tree clean (git status empty apart from untracked .drafts).
- Not done: nothing in scope. (Not mine: KAM.lean regeneration; merge/landing of inp-n11f1.)
- Obstacles: none. Next steps for the receiving team: land inp-n11f1 (already contains the inp-n11f2 merge),
  regenerate KAM.lean with scripts/gen_root_imports.py, then proceed to N11-H consumers
  (`ExtCompose`, `composition`, `transform`, `transform_integral`).
- Build/lint: gate build of CompositionCoeff, Composition, TransformIntegral, Transform succeeds with no
  warnings in these files; lint_sources.sh passes (only the "KAM.lean out of date" notice).
- Note: a READY-N11-F1 marker I had created before this pause message was removed, per the instruction.
