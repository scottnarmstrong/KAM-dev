# N12-12 prover handoff (branch inp-n1212, fa46131; contains inp-n1206 and inp-n1210b (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- `KAM/Nekhoroshev/Averaging/Identity.lean` — `avgCorrectionQ` (verbatim def), `identity` (verbatim signature);
  public helpers: `continuousOn_avgA/avgB/avgFreq/avgCorrectionQ/avgResidual`, `differentiableAt_avgW`,
  `mem_eIoo_of_le`, `orbit_hasDerivAt/orbit_continuousOn/orbit_mapsTo`.
- `KAM/Nekhoroshev/Averaging/PointwiseModes.lean` (helper split, imports Identity) — differentiability of `avgU k`
  and `avgQ` on the action ball, `norm_avgU_le'`, `continuousAt_avgBterm`, `mode_bound` (modewise variation via the
  right-derivative fencing theorem), `continuousOn_bterm_orbit`, `isOpen_eIoo`.
- `KAM/Nekhoroshev/Averaging/Pointwise.lean` (imports PointwiseModes) — `pointwise` (verbatim signature),
  `lambda_orbit_le` (pw-lambda), `ofReal_norm_tsum_le`, `ofReal_norm_integral_le`.
No existing file edited; KAM.lean untouched.

## Approach
- identity: `G(u)=ι I(u) − ε w(γ u)` has derivative `ε r − ε² Q` along the orbit (fbounds for the field,
  chain rule with `wreg`'s C¹, divisor identity by definition of `avgResidual`), integrated by FTC; integrands
  continuous because `ω, a, ∂_I f` are read off the C¹ fields of `avgH h f 0`, `avgH h f 1` and `fderiv w` is
  continuous on the open domain. `M₂` obtained from `avg_compact_bounds` (not in the statement).
- pointwise: real chain `|ΔI| ≤ ε(|Λu|+|Λ0|)+ε²|∫Q|+ε|∫r|`; `|Λu|` by modewise fencing + `lintegral_tsum`
  (Tonelli, only termwise AEMeasurability along the orbit); `Q,r` by `wreg` envelope bounds; regrouping into `Φ̂`
  via `le_lintegral_add` (no measurability of envelopes needed).

## Checks
- `inp_lake_build.sh … KAM.Nekhoroshev.Averaging.Identity KAM.Nekhoroshev.Averaging.PointwiseModes
  KAM.Nekhoroshev.Averaging.Pointwise`: Build completed successfully, no sorry/warnings in my files
  (only pre-existing warnings of CorrectorRegular/LocalDependence).
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only message is
  "KAM.lean is out of date" (generated; new modules PointwiseModes/Identity/Pointwise need regeneration by the
  orchestrator).
- `#print axioms KAM.Nekhoroshev.identity` / `pointwise`: `[propext, Classical.choice, Quot.sound]`.
- No heartbeat options; files ≈ 190 / 190 / 330 lines.

## Deviations / uncertainties
- One extra helper module `PointwiseModes` (DAG: Identity → PointwiseModes → Pointwise; design had
  Pointwise → Identity directly). Reason: `CorrectorRegular`'s `hasFDerivAt_avgU`/`norm_avgU_le` are private, so
  differentiability and the value bound of `avgU k` were re-proved (≈30 lines) rather than editing an audited file.
  Optionally dedupe later by making those two public.
- `hε`, `hε1`, `hκ1`, `ht` are unused in the proofs (kept as in the signatures; silenced with `have _ := …`).
- Statements unchanged; no errata found.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-12 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (identity, pointwise: max Lambda controlled by modewise variation, then Q and r integrated); (2) proofs sound (FTC; N12-06 and N12-10b consumed as designed); no added premises; (3) hygiene. Audit ONLY the Identity and Pointwise modules (compare with branch inp-n1206).
