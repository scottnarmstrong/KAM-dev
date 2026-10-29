# SO-PBASE prover handoff (branch inp-sopbase, cc2ed047; off inp-soaif, which has since landed on inp; track SO package run by the main orchestrator)


## Files (new)
- `KAM/Certificate/Poly/Basic.lean` (255 lines): CertKey, certKeyFun, CertPoly, eval, coeff,
  eval_eq_fourierSum, differentiable_eval, eval_add_int; CertRealPoly, eval, eval_real,
  differentiable_eval, eval_add_int, toPoly (via helper `certPair`), eval_toPoly,
  conjugateSymmetric, CertPoly.add, eval_add. Helpers: coeff_eq_sum, hasSum_list_coeff_mul_character,
  character_add_int, differentiable_list_sum, im_list_sum_eq_zero, character_neg_ofReal,
  certKeyFun_map_neg/nil, list_sum_flatMap_pair, pair_coeff_symm.
- `KAM/Certificate/Model/Basic.lean` (217 lines): CertWeight, checkWeight, norm_character_le_weight,
  CertModel, Encloses, supBound, norm_le_supBound. Helpers: CertWeight.rho_pos/exp_le_w/one_le_w,
  CertPoly.weightedNormUp, degFactorUp, sum_natAbs_certKeyFun_le, two_pi_zpow_le,
  weightedNormUp_bound.

All statements are verbatim from SOSignatures §B/§C (proved; no hypothesis added).

## Approach
- eval_eq_fourierSum: HasSum of the coefficient series by list induction (hasSum_ite_eq), then tsum_eq.
- toPoly = zero term (key [], im `ofInt 0`) :: flatMap of pairs (k,c),(map neg k, c.conj).
  eval_toPoly / conjugateSymmetric by induction through flatMap; coefficients via coeff_eq_sum.
- supBound = upMul (ofRatUp F) (upAdd S rad), S = Σ normUp(c)*w^{|key|₁ of stored list} rounded up,
  F = (2 piUpQ)^d (d ≥ 0) or (2 piLoQ)^d (d < 0) in ℚ. Using the whole stored list's |k|₁ is sound
  since w ≥ 1 and the denoted index truncates/pads. rad ≥ 0 is derived from Encloses at θ = 0
  (ρ > 0 by checkWeight), so no extra hypothesis.

## Checks
- Gate builds: `inp_lake_build.sh .../KAM-inp-sopbase KAM.Certificate.Poly.Basic` and
  `KAM.Certificate.Model.Basic`: "Build completed successfully (2902 jobs)", no warnings in my files
  (one pre-existing unused-simp warning in Arith/PiHigh.lean:218, not mine).
- `scripts/lint_sources.sh`: exit 0 (check_lean_modules PASS, frozen anchor guard OK, ABI OK).
  It prints "KAM.lean is out of date; run scripts/gen_root_imports.py": expected, KAM.lean is generated
  and not edited by me; the orchestrator must regenerate it (two new modules).
- `main_shortname_check.py`: OK, no reused public short names.
- No maxHeartbeats, native_decide, axiom, sorry, EuclideanSpace; all lines ≤ 100 cols.
- `#print axioms` (propext, Classical.choice, Quot.sound only) for: CertPoly.eval_eq_fourierSum,
  CertRealPoly.eval_real, CertRealPoly.eval_toPoly, CertRealPoly.conjugateSymmetric,
  CertPoly.eval_add_int, norm_character_le_weight, CertModel.norm_le_supBound.

## Not in scope / for post-gate packages
- `CertPoly.shift`, `CertPoly.conjReflect` (+ eval lemmas): Poly/Ops (SO-POLY).
- `ModelConfig`, `CertModel.add/mul/trim/toDeg/ofDeriv`, their Encloses lemmas and
  `Encloses.average`: Model/Ops (SO-MALG). I did not define ModelConfig to avoid a clash.

## Uncertainties / errata / deviations
- None found in the signed statements. Deviation: none. `supBound` body is my choice (signature
  left it `sorry`); it takes `|k|₁` from the stored key list rather than from `n`.
- Model/Basic imports Arith.Roots (for `CC.normUp`) and Arith.Transcendental (`ratExpUp`).

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 3, Revision 4 in progress for an unrelated exponential finding); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean sections B (Poly/Basic part) and C (Model/Basic part). Design audit 1 finding F2 (arithmetic reality: real Fourier denotations use mathematical conjugation and zero) applies here. The bodies of CertModel.supBound and other definitions the signature left as sorry are the prover's: check they are SOUND (norm_le_supBound) for every weight passing checkWeight, including negative derivative degree d, and that eval of the exact data equals the Fourier sum of the denoted coefficients (no truncation hidden in eval).

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to Poly/Basic and Model/Basic is complete (Poly/Ops and Model/Ops are later packages). Audit ONLY KAM/Certificate/Poly/Basic.lean and KAM/Certificate/Model/Basic.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including the namespace: fully qualified names must match); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
