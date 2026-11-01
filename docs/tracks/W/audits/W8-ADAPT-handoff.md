# W8-ADAPT handoff

Branch `inp-w8adapt`. Base: `730bc9e7`, which merges `inp-wprov` @ `d91269e8` (all of W8, with the nlw2 provider)
and `inp-w5aafix` @ `5831b822`. `inp` was not merged. Finished at 09:47 UTC on 2026-11-01.

## Result

**No source file needed a change.** The W5-AA-FIX guard arguments (`aaNfun`, `aaQt`, `aaGbarR`, `birkOmegaMix`,
plus `aaGbarR_aaMap`, `aaQt_congr`, `aaP_isSmoothing_of`, `summable_aaGbarR`) have no consumer outside
`KAM/Wave/KamStep/ActionAngle*.lean`, and W5-AA-FIX had already repaired those files itself. The downstream modules
use only declarations whose signatures did not change:

- `KAM/Wave/Iteration/Tori.lean:108` uses `aaConjugacy … (zero_le_one' ℝ) w6_half_le_one (aaOfReal ξ)` (unchanged).
- `KAM/Wave/Iteration/ToriBk.lean:41` uses `aaPfun m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1)` (unchanged).
- `KAM/Wave/Iteration/ToriBk.lean:61` uses `initialPerturbation` (unchanged).
- `KAM/Wave/Iteration/ToriBridge.lean` imports ActionAngleConj and Initial, but names none of the changed declarations.

A repo-wide grep for the eight changed names, outside `KamStep/ActionAngle*` and `KamStep/Initial*`, finds nothing.

**Changed files:** none under `KAM/`. The only new file is this handoff.
**Call sites repaired:** none were needed.

## No statement changed

- `git diff d91269e8 HEAD -- KAM/Wave/Iteration KAM/Wave/Assembly KAM/Provider KAM/Frozen manifest` is empty
  (0 lines). So every Tori*, Assembly and provider statement is byte-identical to W8's.
- `git diff 730bc9e7 HEAD -- KAM` is empty. This package edited no Lean file.
- The only declaration-header changes on the branch since `d91269e8` come from W5-AA-FIX itself. They are all in
  `KAM/Wave/KamStep/` and are listed in its handoff: the guard binders on `aaNfun`, `aaQt`, `aaGbarR` and `birkOmegaMix`,
  `aaGbarR_aaMap` (`hp : 1 / 2 ≤ p`), `aaQt_congr` (`hp0`), the binders dropped from `aaP_isSmoothing_of` (`hV`) and
  `summable_aaGbarR` (`i`), and six new lemmas.
- Capped probe (`w_lean.sh`, importing the frozen anchor, the provider and Initial). The run_meta check
  `(env.find? ``KAM.Wave.nlw2).type == …` prints `frozen==nlw2_proof (syntactic): true; frozen==provider: true`.

## Builds (`/root/code/KAM-inp/.drafts/W/w_build.sh`, one module per call, in import order, all rc 0)

KamStep: ActionAngle, ActionAngleDomain, ActionAngleDeriv, ActionAngleSymp, ActionAngleNormal, ActionAngleQt,
ActionAngleGbar, ActionAngleField, ActionAngleConj, InitialBound, Initial.

Iteration: ToriBridge (built in 5.9s), ToriBk (10s), Tori (9.7s), ToriPrep.

Assembly: Consts, Ext, ShellGeom, ShellData, UpstreamW6, ShellInit, ShellIter, Etor, FreqShell, Patch, NuInj,
PatchInst, Clauses, Unique, Winding, InjAssembly, ShellInv, ShellTorus (7.4s), ShellEmbed (9.8s), ShellClose (10s),
ShellFamily (3.8s), Nlw2Proof (3.4s).

Then KAM.Provider.Wave.Nlw2 (2.6s) and KAM.Frozen.Wave.Theorems.Nlw2.

Tail of the last call:
```
[w_build] slot 1: KAM.Provider.Wave.Nlw2
✔ [3796/3796] Built KAM.Provider.Wave.Nlw2 (2.6s)
Build completed successfully (3796 jobs).
[w_build] slot 1: KAM.Frozen.Wave.Theorems.Nlw2
warning: KAM/Frozen/Wave/Theorems/Nlw2.lean:43:8: declaration uses `sorry`   (expected: the anchor keeps its sorry)
Build completed successfully (3797 jobs).
```
The rebuilt Tori*, Assembly and Provider modules, and the ActionAngle*/Initial* modules, report no warnings.

## Axioms (`#print axioms`)
- `KAM.Wave.nlw2_proof`: [propext, Classical.choice, Quot.sound]
- `KAM.Provider.Wave.nlw2`: [propext, Classical.choice, Quot.sound]
- `KAM.Wave.aaConjugacy`: [propext, Classical.choice, Quot.sound]
- `KAM.Wave.initialPerturbation`: [propext, Classical.choice, Quot.sound]

## Lint (`w_lint.sh`, exit 0), tail
```
check_lean_modules: PASS (4042 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; …)
```

## Uncertainties, errata, deviations
None. No heartbeat issues: the slowest rebuilt module took 10s. No file is near the 1500-line cap; the largest
ActionAngle/Initial file has 430 lines.
