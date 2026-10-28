# P5-BL prover handoff (branch inp-p5bl, c33e60f; contains inp-p5ex and inp-p4li (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/PGAssembly/FastComplex.lean` (~491 lines). No other file touched (KAM.lean not regenerated:
`lint_sources.sh` reports "KAM.lean is out of date" — orchestrator to regenerate).

**Declarations (signatures verbatim from P45Signatures.lean):**
- `bpP:p5:lip-complex` -> `KAM.Planetary.lip_complex`. Approach: Cauchy estimate `norm_fderiv_le_of_closedBall`
  (via `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` along lines); close pairs: every segment point is within
  `|z-z'|/2 < rho/2` of an endpoint, so the closed `rho/2`-polydisc lies in `X_{2rho}`; mean value inequality on the
  segment with constant `2A/rho`; far pairs: sup bound `2A`. `N >= 1` only used to compare `2A/rho <= 2NA/rho`.
- `complexFast` (def, verbatim), `bpP:p5:bilip` -> `KAM.Planetary.bilip`. Steps:
  - `stepP:p5:bl-real`: `real_relation` (H~0 ∘ ι = H0 and `complexFast (ι y) = ι (fastFrequency H0 y)` on the real
    part of the tube, from `h0real`, `h0holo`), `omega_hasFDerivAt` (real derivative `T`, `Dc(ι v) = ι(T v)`),
    `omega_deriv_injective` (`g ∘ ω = id` on `W` + chain rule), `fderiv_complexFast_lower` (complex derivative bounded
    below at `ι x`, `x ∈ closure V`, via real/imaginary splitting and `LinearMap.exists_antilipschitzWith`).
  - `stepP:p5:bl-comp`: `complexFast_local_lower` (local linearisation, MVT on balls, continuity of `fderiv`
    from analyticity), `lower_lip_of_local` (sequence/`IsCompact.tendsto_subseq` contradiction, cases `x ≠ x'` via real
    injectivity, `x = x'` via local bound).
  - Derivative bound: `complexFast = partialsCLM ∘ fderiv H0`, `‖partialsCLM‖ ≤ 1`, `h0bounds` (second derivative) gives
    `M0 := max 1 (pgExtension d).M0`. Radius `rho < delta/16` via `r := delta/16` in the compactness lemma.
  - Helper defs: `partialsCLM`. Helper lemmas are all in the new file; none used as hypothesis of a source result.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-p5bl KAM.Planetary.PGAssembly.FastComplex`: "Build completed successfully", no warnings in the file.
- `sh scripts/lint_sources.sh`: only "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated file, not edited); module check PASS, frozen-anchor guard OK, ABI hashes OK. No lines over 100.
- `#print axioms KAM.Planetary.lip_complex` / `KAM.Planetary.bilip`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / deviations:** none. No signature change, no extra hypotheses. `lip_complex` does not use `hN` beyond `1 ≤ N`
(the bound `2A/rho` suffices; the stated `2NA/rho` is weaker). Imports: `ExtensionTube` (for `isOpen_actionNbhd`) and `Extension`;
no provider or DRAFT_SORRY imports. No `maxHeartbeats` overrides; no design signals (each declaration elaborates quickly).

**Suspected errata:** none in the pinned source. Note (not an erratum): the source proof of `bpP:p5:lip-complex` cites `D Delta`
with polydisc of radius `rho/2`; the sup-norm Cauchy bound is `A/(rho/2)` without an `N` factor, so the stated `2NA/rho` is
conservative by a factor `N`.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-BL and its proof plan; audits DESIGN-P45-design-audit-{1,2,3,4}.md; signatures .drafts/design/P45Signatures.lean): (1) statements = design signatures (lip_complex, complexFast, bilip); (2) proofs sound (P5-EX and P4-LI consumed as designed); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/PGAssembly/FastComplex*.lean (compare with branch inp-p5ex).
