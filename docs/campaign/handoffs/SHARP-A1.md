# SHARP-A1 handoff: the sharp Newton engine

## Files (new)
`KAM/Sharp/Engine/{Schedule,Decay,Scheme,Limit}.lean` (107/190/286/163 lines); `KAM.lean` regenerated.

## Approach
- Signatures copied verbatim from `APOST-SHARP-SIGNATURES.lean.txt` (modules now, `cohConst*` not needed).
- `Schedule`: elementary; helpers `delta0_pos`, `deltaSeq_rpow`, `rSeq_succ`, ...
- `Decay`: `ε_s ≤ 2^{-2as} e` by a direct induction (no `Q > 0`, so `C_E = 0` is covered; the Apost
  proof via `quadratic_iteration_linear` needs `Q > 0`); weighted bounds and geometric sums as in
  `KAM.Apost.Schedule`.
- `Scheme`: structures as signed; `iterate` by induction, with sums (`term_sum`, `IsNewton.sums_le`)
  proved first, then step hypotheses at every stage. `𝔠_step` of either sign is handled.
- `Limit`: reuses `KAM.Apost.lim_k/lim_dk/lim_holo/lim_primary/lim_close`; parameter limit by
  `converge_par` (Cauchy). Does not import `KAM.Sharp.Constants`.
- Note: `Limit` first timed out at default heartbeats (implicit `Ks` unification in the `KAM.Apost.lim_*`
  calls). Fixed by splitting helpers (`summable_terms`, `eps_tendsto`, `converge_par`) and passing `Ks`
  explicitly; no heartbeat option used.

## Checks
- `nice -n 5 lake build KAM.Sharp.Engine.Limit`: success (builds all four).
- `sh scripts/lint_sources.sh`: only the known ABI-scratch failure (`KAM.Frozen.Iso.Defs.BorderedHessian.olean` missing).
- `#print axioms` of `schedule`, `error_decay`, `Scheme.iterate`, `Scheme.limit`:
  `[propext, Classical.choice, Quot.sound]` each.

## Uncertainties / errata / deviations
- None: all four signatures proved exactly as given, no signature signal. No errata found.
- Extra public helper names in `KAM.Sharp.Engine` (e.g. `term_sum`, `epsSeq_le`, `converge_par`).
- `Limit.lean` imports `KAM.Apost.Limit` (heavy but generic), as the brief prescribes.

## Remaining
Nothing for A1.
