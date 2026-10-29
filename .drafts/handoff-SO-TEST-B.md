# Handoff SO-TEST-B (negative and packed tests), branch inp-sotestb

## Files
- NEW `KAM/Certificate/Tests/Negative.lean` (350 lines): the base cert and the ten §8 negatives.
- CHANGED `KAM/Certificate/Tests/Packed.lean` (340 → 394 lines): model-level packed/fallback section
  (new import `KAM.Certificate.Model.Ops`). P2–P5 and the positive/negative packed list were
  already landed (SO-POLY-B); I re-checked them, and they build unchanged.
- No landed module changed (Defs, Sound/*, Soundness untouched).

## Base certificate (hand-built; SO-PYALIGN not waited for)
`negBase : TorusCertificate 2 ℚ` is TR moved to a small strip: H = J + p²/2, K = (θ, (1/2, −1/8)), exact box (1/4, 1/2),
s = 2, σω = 3, τ = 1, ρ = 1/100, ρ∞ = 1/200, ρ_H = 1/20, w = 11/10, w_H = 3/2, μ = 1/100,
M = σK = σB = σT = 2, ν = 49/100, γ = γbar = 1, err = 0, disp = 0, B = I, S = TR's exact inverse,
and every product key advised `direct` (`negCfg`, including the invariance keys `[5,a,l]`).
`negBase_passes : checkTorusCertificate negBase = true` (decide +kernel). err = 0 makes smallness trivial,
so the margins do not depend on the size of isoC1Q. It is checker-only (resonant box), like TR.
`negDiv` (H = J + (p²/2)(p/p), Q = 2, M = 150) also passes the whole checker (`negDiv_passes`).

## Tests: each gives whole `= false` AND the intended sub-check `= false` (decide +kernel)
| # | theorem | mutation → sub-check | kernel |
|---|---|---|---|
| base | negBase_passes | — | 6.5–7.9 s |
| 1 | negResidual_fails | box centre 1/5, err 0 → checkInvariance | 1.9 s |
| 2 | negGramZero_fails / negGramTwo_fails | B = 0 / B = 2I (δ ≥ 1) → checkGram | 2.6 / 3.4 s |
| 2 | negTorsZero_fails | S = 0 → checkTorsion | 7.4 s |
| 3 | negMu_fails | μ = 0 → checkStatic | <0.01 s |
| 4 | negExp_control / negExp_fails | H = J+(p²/2)exp 0; E = 1 passes invariance at err 1/1000, E = 2 fails it | 2.0 / 2.2 s |
| 5 | negWeight_fails | w = 1: checkWeight, checkStatic | 0.02 s |
| 6 | negDiv_passes / negDivBall_fails | p ∈ 1/2 ± 1 on D → checkHamBounds | 8.3 / 1.3 s |
| 6 | negDivWit_fails | Q = 0 (δ = 1) → compose none → checkInvariance | 3.5 s |
| 7 | negBoxZero_fails / negRay_fails | box (0±1, 0±1) / ν = 6/10 → checkStatic | 0.07 / 0.08 s |
| 8 | negPi_fails | π ∈ 3.14159 ± 1e−7 → checkPiEnclosure, checkStatic | 0.13 s |
| 9 | negOne_torsion / negPerm3_selfInverse / negPerm3_fails | n = 1 toy of Tests/Defs (data copied; its bodies aren't exposed) with S = [1 0 0; 0 0 1; 0 1 0] (self-inverse, checked) → checkTorsion | 6.6 / 0.02 / 1.6 s |
| 10 | negChar_pin_fails / negChar_pin_passes | U₀ = 1/4, pin exp(2πi/4) = i (exact witness), pinHalvings 0 → Slp.compose none → checkInvariance; pinHalvings 2 → compose some, invariance passes (err 1/100) | 3.3 / 3.1 s |
Times: `profiler`, `Elab.async false`, single-threaded `lake env lean` on a scratch copy.
Notes: for items 4 and 10 the base is checked at sub-check level (checkInvariance at loose err), not the whole
checker. The exp(0) witness leaves a ~1e−4 radius at pin order 6, so err = 0 cannot pass. Item 9 is whole-false
for n = 1 anyway (checkStatic), so its evidence is the checkTorsion flip against `negOne_torsion`.

## Packed (Tests/Packed.lean, new section "Model level")
`packedTest_model_packed`: CertModel.mul with `.packed` advice at key [9] and the correct decoder → poly nonempty,
rad ≤ 64 mantissa units (= 4). `packedTest_model_fallback`: wrong decoder (+1) → mantCheck rejects → crude enclosure
(poly empty, rad > 4), so a margin of 4 relying on that product fails. Encloses.mul instances on both routes:
`packedTest_model_packed_encloses`, `packedTest_model_fallback_encloses`. This is model level only: no whole
CertFixed certificate was built for the fallback.

## Checks
- Gate build `inp_lake_build.sh … KAM.Certificate.Tests.Packed KAM.Certificate.Tests.Negative`: success (only
  pre-existing warnings in PiHigh/Expr.Basic).
- main_shortname_check.py on both modules: OK.
- lint_sources.sh: every check passes except "KAM.lean is out of date". The staleness was there before my change:
  gen_root_imports would add 14 modules, including Certificate.Defs, Sound/*, Soundness, Tests.Defs and SpinOrbit.Graph.*.
  Per rule 10 I did not commit KAM.lean, so the orchestrator should regenerate it (it now also needs Tests.Negative).
- Axioms (negBase_passes, negDiv_passes, negChar_pin_fails, negPerm3_fails, packedTest_model_*): propext,
  Classical.choice, Quot.sound only. There are no `*_torus` theorems in package B.
- No native_decide, maxHeartbeats or other forbidden constructs.

## Mirror vs Lean
- SO-TOYGEN's mirror (pre-alignment) emits no invariance advice keys `[5,a,l]`. The Lean checker needs them for exact
  products (a missing key falls back to the crude enclosure). Generators must emit them.
- Nothing else disagrees: the Lean base passes with the mirror's TR torsion inverse verbatim.

## Errata / deviations
No source errata. Deviation: the base is a TR-like n = 2 cert at ρ = 1/100, not a toy from the JSON.
Design signal: none; everything elaborates at default heartbeats.
