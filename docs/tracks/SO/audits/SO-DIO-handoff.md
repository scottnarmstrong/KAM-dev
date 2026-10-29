# SO-DIO prover handoff (branch inp-sodio, f454a657; off inp; track SO package run by the main orchestrator)


## Files
- NEW `KAM/Certificate/QuadraticDiophantine.lean` (≈250 lines, max line width 99). Nothing else touched.
  (`KAM.lean` is stale: the orchestrator must run `scripts/gen_root_imports.py`; I did not edit it.)

## Approach
- `lunarG`, `lunarNuMinus`, `lunarNuPlus` (Real.sqrt). Closed forms ν− = (3039+√5)/3118, ν+ = (3197−√5)/3118.
- `lunarNuMinus_quadratic` (1559x²−3039x+1481=0), `lunarNuPlus_quadratic` (1559x²−3197x+1639=0); discriminant 5.
- Private `norm_bound`: for x with conjugate y (x+y=B/1559, xy=C/1559, |x−y|≤9/(4·1559), x≥1/2, x,y irrational):
  |a x+b| ≥ 1/(21(|a|+|b|)). Norm N=a²C+abB+1559b² is a nonzero integer; d·d' ≥ 1/1559, d' ≤ d+s·9/(4·1559);
  contradiction for s=|a|+|b|≥2; s=1 handled via x>1/2. Instantiated: `lunarNuMinus_lower`, `lunarNuPlus_lower`.
- Final (exact convention of frozen `IsDiophantine`, k∈Fin 2→ℤ, |k|₁, τ=1):
  `lunarNuMinus_isDiophantine`, `lunarNuPlus_isDiophantine` : `IsDiophantine (1/21) 1 ![ν±, 1]`;
  `lunarNuMinus_half_isDiophantine`, `lunarNuPlus_half_isDiophantine` : `IsDiophantine (1/42) 1 ![ν±/2, 1/2]`.
  No extra premises. Mathlib has no ready quadratic-irrational lower-bound API used here.

## Checks
- Gate build `inp_lake_build.sh /root/code/KAM-inp-sodio KAM.Certificate.QuadraticDiophantine`:
  "Built KAM.Certificate.QuadraticDiophantine (46s) / Build completed successfully (2193 jobs)", no warnings seen.
- `#print axioms` of all four IsDiophantine theorems and both quadratic theorems: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only failure is
  "KAM.lean is out of date" (new module not yet in generated root; orchestrator regenerates).
- No maxHeartbeats, native_decide, axiom, sorry, EuclideanSpace. Short names `lunarG/lunarNu*` were not present in KAM.

## Uncertainties / errata
- None. The margin in the s≥2 case is tight but proved (1/1764+9/130956 < 1/1559).

CONTEXT: track SO (owner decision D30; plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md), the lunar spin-orbit certificate project. Unfrozen helper code; no graph and no signature file exist yet for track SO, so (a) and (b) are judged against the brief /root/code/KAM-inp/.drafts/briefs/offload-main/SO-DIO.md and the pilot's §6 argument (/root/code/KAM/docs/explorations/lunar-spin-orbit-feasibility-report.md).

AUDIT FOCUS: (1) lunarNuMinus / lunarNuPlus equal 1 -/+ 1/(40 + (sqrt 5 - 1)/2) exactly (check the closed forms); (2) the four IsDiophantine statements use the frozen IsDiophantine convention (KAM/Frozen/Defs/IsDiophantine.lean) literally, with gamma 1/21 for (nu, 1) and 1/42 for (nu/2, 1/2), tau = 1, and are TRUE as stated (no hidden restriction on k); (3) the algebraic-norm proof is sound, including the tight s >= 2 margin and the s = 1 case; (4) no extra premise anywhere. Audit ONLY KAM/Certificate/QuadraticDiophantine.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
