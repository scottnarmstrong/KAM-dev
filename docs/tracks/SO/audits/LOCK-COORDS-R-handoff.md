# Handoff: LOCK-COORDS-R (track SO part 3, D45)

Branch `inp-lockcoords`, worktree /root/code/KAM-inp-lockcoords.

## Files (all new)
- `KAM/SpinOrbit/Lock/Coords/Maps.lean`: `lockX`, `lockY`, `lockToRotR`,
  `lockToPhysicalR`, `lockHamiltonianR`, `lockToPhysicalR_eq`, extra `lockHamiltonianR_eq`
  (K = P₀²/2 − P₀ + P₁ + V(Q₀+Q₁, Q₁) ∘ lockToRotR, i.e. the real `soRotHC` formula),
  `lockCentre`, `lunarLockCentre`, helper `contDiff_list_sum_map`, `lockCentre_contDiff`.
- `KAM/SpinOrbit/Lock/Coords/Inverse.lean` (imports `KAM.SpinOrbit.Lock.Confine` for `libAction`): `libAction_lockToPhysicalR`, `lockToPhysicalR_surj`.
- `KAM/SpinOrbit/Lock/Coords/Conjugacy.lean` (~185 lines): partials `lockXα/lockXI/lockYα/lockYI`,
  `hasDerivAt_lockX_line`, `hasDerivAt_lockY_line`, `lockX_lockY_bracket` (X_α Y_I − X_I Y_α = 1),
  `hasDerivAt_lockHamiltonianR_line`, `hasDerivAt_lockToPhysicalR_line`,
  `differentiableAt_lockHamiltonianR`, `differentiableAt_lockToPhysicalR`, **`lock_conjugacy`**.

All names/types of the signature-file declarations in scope are byte-identical to
`.drafts/design/SOLockSignatures.lean` §2 (`libAction`) and §6 (real part). Nothing from the complex/HamExpr part
(LOCK-COORDS-C) or any checker file was touched.

## Approach
- `lock_conjugacy`: both differentials computed along lines `t ↦ z + t v` via the landed
  `soHasDerivAt_line` (KAM/SpinOrbit/Hamiltonian.lean), with `DifferentiableAt` from `fun_prop` (discharging
  `I/(πΩ) ≠ 0`, `IΩ/π ≠ 0`). C³ of `c` is unpacked with `contDiff_succ_iff_deriv` to differentiability of `c, c′, c″`.
  Final algebra: q̇ = Y·{X,Y} + (1+c′) and ṗ = c″ − (c″ + V_q){X,Y}, closed by `linear_combination` with the
  bracket `{X,Y} = 1`. Frozen convention X_K = (∂_I K, −∂_θ K) and `soRotMap` direction (rotated → physical) as in
  the corrected design §3 / audit 1 F3; `soField_eq` used for the physical side.
- Inverse: w = Y/√Ω + i√Ω X, libAction = π‖w‖², `Complex.sin_arg`/`cos_arg`.
- `lockCentre_contDiff`: induction over the list.

## Checks
- Gate builds (one at a time): `inp_lake_build.sh ... KAM.SpinOrbit.Lock.Coords.{Maps,Inverse,Conjugacy}`:
  `Build completed successfully`, no warnings in my files, no sorry.
- `sh scripts/lint_sources.sh`: only failure is
  `KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/SpinOrbit.lean)` — expected for new modules;
  rule 10 forbids me to regenerate; orchestrator to run `gen_root_imports.py` on landing. Otherwise
  `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (158 frozen declarations)`.
- `#print axioms` (scratch file, deleted) for `lock_conjugacy`, `lockToPhysicalR_surj`,
  `libAction_lockToPhysicalR`, `lockCentre_contDiff`, `lockToPhysicalR_eq`, `lockHamiltonianR_eq`,
  `lockX_lockY_bracket`: all `[propext, Classical.choice, Quot.sound]`.
- No heartbeat problems (no overrides; every file elaborates in seconds).

## Uncertainties / deviations
- `libAction`: per the ownership ruling it is owned by LOCK-CONF (`KAM/SpinOrbit/Lock/Confine.lean`). I merged
  `inp-lockpo` into `inp-lockcoords` and deleted my copy; only `Inverse.lean` uses it and now imports
  `KAM.SpinOrbit.Lock.Confine`. No cycle: Confine imports only `KAM.SpinOrbit.Barrier` and Mathlib.
- Extra public helpers beyond the signature file (listed above); none has a conclusion-shaped hypothesis.
- No signature was wrong or needed changing.

## Suspected errata
- None. Design §3 (corrected) verified: the bracket X_α Y_I − X_I Y_α = 1 (dY∧dX = dI∧dα) and
  K = H′ ∘ lockToRotR (`lockHamiltonianR_eq`) both check.

## Update after the libAction ruling
- Merged `inp-lockpo` (no conflicts); committed the removal of `libAction` from Maps (`git log -1`).
- Gate builds of Coords.Maps, Coords.Inverse and Coords.Conjugacy succeed (no warnings in my files).
- `main_shortname_check.py ... Coords.Maps Coords.Inverse Coords.Conjugacy`: `short-name check OK (no reused
  public short name)`.
- Lint: same as before. The only failure is that `KAM.lean` is out of date (generated file; the orchestrator
  regenerates it). All other checks pass.
