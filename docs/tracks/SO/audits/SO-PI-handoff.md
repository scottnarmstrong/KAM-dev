# SO-PI prover handoff (branch inp-sopi, dddf8f7b; off inp; track SO package run by the main orchestrator)


## Files
- new: `KAM/Certificate/Arith/PiHigh.lean` (~240 lines). Nothing else touched (KAM.lean is generated; lint reports it
  out of date, the orchestrator regenerates it).

## Approach
- `piLoQ`, `piUpQ`, `piLoQ_lt_pi`, `pi_lt_piUpQ` as signed (from `Real.pi_gt_d6`, `Real.pi_lt_d6`).
- `atanS x m` = rational partial sum of the arctan series; `atanS_even_lt_arctan`, `arctan_lt_atanS_odd` (strict
  alternating-series bounds for `0<x<1`, from `Real.hasSum_arctan` + Mathlib's `Antitone.*alternating_series*`).
- Machin via Mathlib's `Real.four_mul_arctan_inv_5_sub_arctan_inv_239`: `piLowRat k j < π < piUpRat k j`
  (`piLowRat_lt_pi`, `pi_lt_piUpRat`); width checks by `decide +kernel`:
  `piHigh_50` (k,j = 18,5), `piHigh_100` (36,11), `piHigh_140` (50,15): `piUpRat - piLowRat ≤ 1/10^N`.
- `e`: `eLowRat n < exp 1 < eUpRat n` (`n>0`, from `Real.exp_bound`, remainder doubled for strictness);
  `eHigh_30` (n = 40) width ≤ 10^-30 by `decide +kernel`.
- Hook for SO-ARITH: `structure PiHighCert {lo hi lo_lt lt_hi}` and `PiHighCert.ofParams k j`; wrap
  `(lo+hi)/2`, `(hi-lo)/2` into `PiEnclosure`. (`piWidthOk` is a Bool width check, unused so far.)

## Checks
- `inp_lake_build.sh . KAM.Certificate.Arith.PiHigh`: Build completed successfully, no warnings.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; only "KAM.lean is out of date" (generated).
- Kernel times (profiler "type checking", scratch file): N=50 0.36 s, N=100 0.71 s, N=140 ~1.4 s; e (30 digits) ~1.5 s
  (the last two profile lines were 1.38 s and 1.52 s, in order t140, e).
- `#print axioms` of piLoQ_lt_pi, pi_lt_piUpQ, piLowRat_lt_pi, pi_lt_piUpRat, eLowRat_lt_exp_one,
  exp_one_lt_eUpRat, piHigh_140, eHigh_30: `[propext, Classical.choice, Quot.sound]`.
- No maxHeartbeats, native_decide, axioms; lines ≤ 100.

## Uncertainties / errata
- None. `piWidthOk` / `PiHighCert.ofParams` are minimal hooks; the final `PiEnclosure` wrapper is SO-ARITH's.
- Public short names added: atanS, piLowRat, piUpRat, piHigh_*, eSum, eRem, eLowRat, eUpRat, eHigh_30,
  PiHighCert, piWidthOk (grepped, no prior use in KAM).

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; owner ruling O3: build the high-precision pi package now). Draft signatures: /root/code/KAM-inp/.drafts/design/SOSignatures.lean (piLoQ, piUpQ, piLoQ_lt_pi, pi_lt_piUpQ around lines 120-130); the PiEnclosure wrapper belongs to the later package SO-ARITH (brief /root/code/KAM-inp/.drafts/briefs/offload-main/SO-PI.md).

AUDIT FOCUS: (1) the four signed declarations match the draft signatures verbatim; (2) the arctan alternating-series bounds and the Machin assembly are sound (correct parity of the partial-sum bounds, the use of Real.four_mul_arctan_inv_5_sub_arctan_inv_239, strictness); (3) the width theorems piHigh_50/100/140 and eHigh_30 state what they claim (b - a <= 10^-N) and are proved by kernel evaluation only (decide +kernel; no native_decide); (4) the e bounds (Real.exp_bound remainder handling) are sound; (5) re-measure the kernel time of piHigh_140 if cheap. Audit ONLY KAM/Certificate/Arith/PiHigh.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
