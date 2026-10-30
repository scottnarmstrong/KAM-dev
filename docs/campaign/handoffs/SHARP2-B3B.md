# SHARP2-B3B handoff: route-B step constants and small-divisor scaling

Branch `sharp-b3b` (from `sharp-v2` at ba8e923f). All six target theorems are proved with the
signatures of `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt` verbatim. No signature was
false, nothing was weakened, and no hypothesis was added.

## Files (all ≤ 466 lines, ≤ 100 characters per line, modules)
- `KAM/Sharp2/SmallDiv/Scale.lean` (111): `SDConst.of_le_gamma`, `sdConst_classical_of_le`,
  `fullBite_ratio_mono`; helpers `SDConst.of_coef`, `SDConst.of_le_const`, `zero_mem_complexStrip`.
- `KAM/Sharp2/ModConstantsB/Defs.lean` (202): `StepInB`, `StepConstsB`, `stepConstsB`, `stepCondB`,
  `StepInB.Ok`, `StepInB.Dom`, verbatim (lines wrapped only).
- `ModConstantsB/Data.lean` (278): `StepInB.OkF` (`Ok` with one field per inequality), `StepInB.Le`
  (`Dom` as rewriting equations), and one def per `let` (`sg`, `sCΩ`, ..., `sQL`, `sQ`, `sCnu`).
- `ModConstantsB/Nonneg.lean` (328), `Mono1.lean` (323), `Mono2.lean` (466): `nn_X : 0 ≤ X p`,
  `mo_X : X p ≤ X p'`, one lemma per helper (`positivity` / `gcongr`).
- `KAM/Sharp2/ModConstantsB.lean` (115): facade and the three targets `stepConstsB_nonneg`,
  `stepConstsB_mono`, `stepCondB_anti`; also `stepConstsB_eq` (`rfl`), `condH`.
- `scripts/apost_sharp/check_modconstb_v2.py`; `KAM.lean` regenerated.

## Approach
- `Scale`: `SDConst` depends on `(c, γ)` only through `c γ⁻¹`, so one lemma `of_coef` gives the
  `γ`-scaling and a larger constant. `H ≥ 0` is recovered from the hypothesis at the point `0` of the
  strip. The classical-constant statement is `sdConst_classical` at bite `b` plus the existing
  `cohConstC_mono`. The ratio monotonicity is a case split on the two `min`s.
- `ModConstantsB`: B3 pattern, one helper per `let`. The iso `Q̄_N` is now a polynomial, and monotonicity
  holds for iso, `selfcons` (L10) and the `min`/`max` branches with no extra hypothesis. The only
  nontrivial points: `CEN/CEL` is constant under `Dom` (`sCEL_eq`, `sCEN_eq`), and the
  `stage0` `min` appears only in nonnegativity (`Dom` fixes `stage0 = false`).

## Checks
- Targeted builds, one niced at a time: `KAM.Sharp2.SmallDiv.Scale`, `KAM.Sharp2.ModConstantsB.{Defs,
  Data,Nonneg,Mono1,Mono2}`, `KAM.Sharp2.ModConstantsB`: all succeed, no heartbeat or recursion option.
- Signature probe `.drafts/ProbeB3B.lean` (uncommitted): the six verbatim statements of the design file
  elaborate with the bodies `KAM.Sharp2.<name> ...`; the defs block of the design file equals
  `Defs.lean` after whitespace normalisation (`True`).
- `#print axioms` of all six targets: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: `check_lean_modules: PASS (1526 Lean files)`, `FROZEN-ANCHOR GUARD OK`;
  the only error is the known ABI-scratch missing olean
  (`KAM.Frozen.Planetary.Theorems.FixedSunPlanetaryKAM`); the generated `KAM.lean` is listed as over 1500
  lines.
- `python3 -I scripts/apost_sharp/check_modconstb_v2.py`: the Lean helper defs are parsed and evaluated
  with exact Fractions on R1 (plain/iso × L10 on/off × stage 0 on/off × two small-divisor sets = 16
  cases). Constants `CDK, C0, CxiL, QtN, QL, Q, Bloc, CBb, CNb, CNbT, Cab` (+ `Cnu` iso) and the whole
  list of step conditions (coef/bound/power, the Bloc clause excluded since the python has no local
  budget) equal `stageB` exactly in all 16 cases. Random monotonicity under `Dom`: 0 violations in 6423
  trials (plain and iso, L10 on and off).

## Uncertainties
- `ModConstantsB.Mono*` are generated (`.drafts/gen.py`, not committed); the sources are the committed
  Lean files.
- `Dom` does not fix `ePer`; this is harmless because `stage0 = false` on both sides, and `Ok` does
  not require `ePer`-dependent facts beyond `0 ≤ ePer`.
- The python cross-check compares `Bloc` to `B_loc` and omits the `Bloc` condition (no python
  counterpart).

## Suspected errata / deviations
- None found. Deviations: signature lines wrapped to 100 characters (whitespace only); `Dom.le` is
  not usable as a projection name in the helper (`Dom.toLe` is used).
