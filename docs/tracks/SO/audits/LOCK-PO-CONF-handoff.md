# Handoff: LOCK-PO and LOCK-CONF (branch `inp-lockpo`)

## Commits
- `e8604fdf` LOCK-PO: `KAM/SpinOrbit/Lock/PO/{Green,Contraction,Orbit}.lean`
- `0ca9d2e2` LOCK-CONF: `KAM/SpinOrbit/Lock/Confine.lean`
- `e780f59f` Short-name fix after the audit pre-check: renamed `IsSyncOrbit.hasDerivAt` → `IsSyncOrbit.hasDerivAt_orbit`, `LockBarrier.value` → `LockBarrier.barrierValue`, `prim` → `lockPrim` (and `prim_*`/`hasDerivAt_prim`/`continuous_prim` → `lockPrim_*`/`hasDerivAt_lockPrim`/`continuous_lockPrim`). All four modules were rebuilt through the gate (each `Build completed successfully`).

## Files (all new; line counts)
- `KAM/SpinOrbit/Lock/PO/Green.lean` (247)
- `KAM/SpinOrbit/Lock/PO/Contraction.lean` (226)
- `KAM/SpinOrbit/Lock/PO/Orbit.lean` (219)
- `KAM/SpinOrbit/Lock/Confine.lean` (228)

No landed, frozen, manifest, README, KAM.lean or KAM/Root file was edited.

## Declarations matching the signatures file (exact text, same names)
- `IsSyncOrbit`, `lunarSyncOrbit` (Orbit.lean): verbatim.
- `lunarSyncOrbit_spec : IsSyncOrbit lunarSyncOrbit`
- `lunarSyncOrbit_unique (ψ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit`
- `lunarSyncOrbit_bound (φ) : |ψ* φ| ≤ 17/1000000 ∧ |deriv ψ* φ| ≤ 27/200000`
- `libAction`, `LockBarrier` (Confine.lean): verbatim.
- `lock_confinement`: verbatim statement.

No signature changed; no deviation from the signatures file.

## Approach
**Green.lean.**
- `taylor_two_abs_le` proves the second-order Taylor bound from |u''| ≤ M. It uses the monotone/antitone mean-value lemmas on `M(s−x)²/2 ± R(s)`.
- `dirichlet_bound` gives |u| ≤ M/32 and |u'| ≤ M/4 when u vanishes at every half-integer. It uses Taylor from both ends of `[k/2, k/2+1/2]` with k = ⌊2x⌋, then algebra.
- `half_int_zero`: an odd one-periodic function vanishes at every n/2.
- The explicit Green operator is `green f = prim (prim f − 2∫₀^{1/2} prim f)`. Its oddness and periodicity follow from even/odd primitive lemmas (`integral_comp_neg`) and `Periodic.intervalIntegral_add_eq`.

**Contraction.lean.**
- `∂_qV` symmetries: shift (1,1) and oddness.
- Lipschitz bound with `soLip = 16π²εΣ|A_m|` (`Real.abs_sin_sub_sin_le`).
- Diagonal forcing bound with `soEta = 4πεΣ_{m≠2}|A_m|`: the m = 2 term vanishes.
- `syncForce`; `poSet`, the closed set of odd periodic functions in `ℝ →ᵇ ℝ`, which is complete.
- `syncMap d = green (syncForce d)`; `dist_syncMap_le` gives (L/32)·dist.
- `syncMap_contracting : ContractingWith (1/2) syncMap`, using the crude bound `soLip ≤ 16`.

**Orbit.lean.**
- Existence: the fixed point `ContractingWith.fixedPoint` is C², by `contDiff_succ_iff_deriv` and `contDiff_one_iff_deriv`, and solves the orbit equation.
- Uniqueness: every `IsSyncOrbit ψ` equals `green (syncForce ψ)`. This is Dirichlet uniqueness, `dirichlet_bound` with M = 0. So ψ is a fixed point of `syncMap` (via `toPoSet`), and `fixedPoint_unique` identifies it.
- Location: valid for any odd orbit. Start from the crude bound |ψ| ≤ soForceBound/32 ≤ 27/320000, then take one sharpening step with `L ≤ 3377/10⁵` and `η ≤ 5355/10⁷` (π < 3.1416, `Real.pi_lt_d4`). This gives |ψ| ≤ 1.6823·10⁻⁵ ≤ 17/10⁶, and then |ψ'| ≤ (η + L·17/10⁶)/4 = 1.3402·10⁻⁴ ≤ 27/200000. These rational bounds are proved by `norm_num` (design §1.4, audit N1 satisfied).

**Confine.lean.**
- `lockW = Y/√Ω + i√ΩX`.
- `lockW_ne_zero` holds where 𝓘 > 0.
- `LockBarrier.P_arg_neg`: P(arg w/2π) = P(arg(−w)/2π + ½), by cases on the sign of Im w and period one in α.
- `continuousOn_P_arg`: on {𝓘 > 0}, use `Complex.continuousAt_arg` on the slit plane, and the `−w` branch with eventual equality off it.
- `lockRegion = {𝓘 < Iin} ∪ {Iin/2 < 𝓘 < P}`. `isOpen_lockRegion` uses `ContinuousOn.isOpen_inter_preimage`.
- `frontier_lockRegion_subset`: the frontier lies in exactly the invariant set of `B.invariant`. The proof uses a closure argument with continuity of P∘α − 𝓘 at the frontier point.
- `lock_confinement` comes from `gen_barrier` (W = G = J = univ) plus `so_global_exists_unique`, as in `so_confinement`.

`LockBarrier.invariant` is a field of the explicitly conditional helper structure only. No source theorem assumes it.

## Checks
- Gate builds, each `Build completed successfully`, with no warnings in my files:
  - `inp_lake_build.sh … KAM.SpinOrbit.Lock.PO.Green` (2771 jobs);
  - `… KAM.SpinOrbit.Lock.PO.Contraction` (2892 jobs);
  - `… KAM.SpinOrbit.Lock.PO.Orbit` (2893 jobs);
  - `… KAM.SpinOrbit.Lock.Confine` (2890 jobs).
- `#print axioms` (scratch file, deleted afterwards). Each of the following depends on `[propext, Classical.choice, Quot.sound]`:
  - `lunarSyncOrbit_spec`, `lunarSyncOrbit_unique`, `lunarSyncOrbit_bound`;
  - `lock_confinement`, `continuousOn_P_arg`, `frontier_lockRegion_subset`.
- `sh scripts/lint_sources.sh` exits 1, for one reason only:
  `KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/SpinOrbit.lean)`.
  The generated root must pick up the 4 new modules, and rule 10 forbids me to edit or regenerate it. The orchestrator should run `scripts/gen_root_imports.py` on landing. Everything else passes: no forbidden tokens, no line over 100 characters, `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- No `maxHeartbeats` or other overrides. Every file is under 250 lines.

## Uncertainties / notes
- `abs_le_of_libAction_lt` and `sqrt_libAction_le` are not proved here. The signatures call the former a "LOCK-CONF corollary", but the design §6 package table assigns both to LOCK-ASSEMBLY, so I left them to avoid a name clash. Each is short; I can add them if wanted.
- `lunarOmega` is not defined here (it is not part of PO or CONF).
- `libAction` and `LockBarrier` live in `Lock/Confine.lean`. Later packages (ASSEMBLY, GRAPH) should import that module.
- Public helper names that other packages may reuse: `soLip`, `soEta`, `syncForce`, `poSet`, `syncMap`, `syncFixed`, `green`, `greenD`, `lockPrim`, `dirichlet_bound`, `taylor_two_abs_le`, `half_int_zero`, `lockW`, `LockBarrier.barrierValue`, `lockRegion`.

## Suspected errata / deviations
- No pinned-source errata.
- No deviations from the signatures or the design.
- The location proof uses one sharpening iteration from the crude a-priori bound instead of the contraction-distance formula η/(32 − L). It reaches the same literals.

## Short-name check (after `e780f59f`)
`main_shortname_check.py` on the four modules reports one remaining hit:
`REUSED SHORT NAME libAction (KAM/SpinOrbit/Lock/Confine.lean) already in KAM/SpinOrbit/Lock/Coords/Maps.lean on unmerged branch inp-lockcoords`.
`libAction` is a signed name, so I did not rename it. Both branches define it with the signature text. The orchestrator must keep only one definition, either on landing or by having LOCK-COORDS import `KAM.SpinOrbit.Lock.Confine` instead of redefining it. There are no Mathlib short-name hits. Lint is unchanged: the only failure is the stale generated root.
