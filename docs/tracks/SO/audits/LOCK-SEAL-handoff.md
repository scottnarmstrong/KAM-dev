# LOCK-SEAL handoff (LOCK-FREEZE Phase B: seal of the four lunar lock anchors)

Branch `inp-lockfreeze` in `/root/code/KAM-inp-lockdesign` (merged `inp` at c8dae3fee, which contains LOCK-DATA's
landing beb39ddb6). Authority: D63 (seal approved), D49 (freeze), D45 (route); brief
`/root/code/KAM-inp/.drafts/briefs/lock/PKG-LOCK-FREEZE.md` Phase B. Requested by kam-38 via kam-inp-lockdata-84.

## AUDIT FOCUS (refute first)
1. Only the four frozen proof bodies changed (between the FROZEN_ANCHOR_PROOF markers); statements byte-identical.
2. The providers' statements are the exact frozen telescopes (expr-equality below), and they assume nothing beyond
   the frozen binders: no conclusion-shaped hypothesis, no sorry/axiom.
3. The bridges in `KAM/SpinOrbit/Lock/FrozenBridge.lean` (frozen `IsSyncOrbit` ↔ landed, via `soField_eq`;
   `lunarSyncOrbit` equality; `libAction` by `rfl`) are correct and do not alter meaning; the two
   `lunarOmega` (frozen and `Lock.lunarOmega`, both `8 / 65 : ℚ`) agree definitionally in the headline `exact`.
4. D51 ownership: the headline anchor and provider now belong to `KAMLunarLock` (`scripts/build_roots.json`);
   the three orbit anchors/providers import only core and stay core. No core module imports an application.

## Changes
- `KAM/Frozen/SpinOrbit/Theorems/{LunarSyncOrbitSpec,LunarSyncOrbitUnique,LunarSyncOrbitBound,LunarSyncLock}.lean`:
  body `by sorry` → `by exact KAM.Provider.SpinOrbit.lunarSyncOrbit_spec` / `… lunarSyncOrbit_unique ψ h` /
  `… lunarSyncOrbit_bound φ` / `… lunar_sync_lock q₀ p₀ φ₀ h₀`.
- `KAM/Provider/SpinOrbit/LunarSyncLock.lean`: headline provider (the audited text of LOCK-DATA-audit-1
  §281–287) from `KAM.SpinOrbit.Data.LockN65.lunar_sync_lock_N65`.
- Already on the branch from 41934621 (audited in LOCK-DATA-audit-1): `KAM/SpinOrbit/Lock/FrozenBridge.lean` and the
  three orbit providers (from `Lock.syncOrbit_{spec,unique,bound}`).
- `manifest/frozen-anchors.json`: the four `spinorbit.lock.*` theorem entries DRAFT_SORRY → SEALED (nothing else).
- `docs/MANIFEST-CHANGES.md`: four rows. `scripts/build_roots.json`: two KAMLunarLock prefixes.
- Generated roots (`KAM.lean`, `KAM/Root/*`, `KAMLunarLock*`, lakefile block) are NOT edited (rule 10); the lander
  regenerates them.

## Build method (no `.lake/build` in this worktree, by brief)
Scratch overlay `/tmp/claude-0/-root-code-KAM-inp-lockdesign/3725f31d-b090-42aa-b100-72ad80a1344d/scratchpad/olean4`: `cp -rs /root/code/KAM-inp/.lake/build/lib/lean/KAM` (inp c8dae3fee, all up to date;
LockN65 is a symlink to `kam-data/so-lock/remote-20261105`), then each module compiled with
`lean -R . -o … -i …` (project leanOptions) under `flock …/.kernel-probe.lock systemd-run --user --scope -p
MemoryMax=10G -p MemorySwapMax=0 nice -n 10`. Nothing written into KAM-inp's build. FrozenBridge 3.8 s, orbit providers
and anchors about 2 s each, headline provider 47 s, headline anchor 36 s; no messages at all.
`lake build --no-build KAM.SpinOrbit.Data.LockN65.AssemblyN65` in KAM-inp: up to date (nothing heavy rebuilt).
**For the headline replay** use `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/claude-0/-root-code-KAM-inp-lockdesign/3725f31d-b090-42aa-b100-72ad80a1344d/scratchpad/olean4` (real-directory root last), as
LOCK-DATA-audit-1 §315–341; this worktree's own build cannot resolve AssemblyN65.

## Checks and output
- Expr-equality `example : type_of% @KAM.SpinOrbit.<n> := @KAM.Provider.SpinOrbit.<n>` for all four: elaborated,
  no messages.
- `#print axioms`: all four `KAM.SpinOrbit.{lunarSyncOrbit_spec, lunarSyncOrbit_unique, lunarSyncOrbit_bound,
  lunar_sync_lock}` depend on `[propext, Classical.choice, Quot.sound]`.
- Kernel replay, `lake env leanchecker <leaf module>` one at a time (capped, flock), the 4 providers and 4 anchors:
  all rc=0 with no output (control: a nonexistent module name prints "Could not find any oleans").
- `scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json`: FROZEN-ANCHOR GUARD OK.
- `scripts/abi_hashes.py --check`: ABI HASHES OK (315 core declarations). `lunar_sync_lock` (KAMLunarLock; the
  script's `--lib` mode needs a lake-built library) hashed by the script's exact method (pp.all `#check @`,
  same stripping): 5ccf9ade…a4dc = manifest, MATCH.
- `scripts/lint_sources.sh`: `check_lean_modules: PASS (18345 Lean files)`, `FROZEN-ANCHOR GUARD OK`; fails only on generated-root staleness (`KAM.lean`, `KAM/Root/{Frozen,Provider,SpinOrbit}.lean`, `KAMLunarLock{,/Frozen,/Provider}.lean`, lakefile block; rule 10, regenerated at landing) and its elaborated-hash step, which needs a lake build (covered by the ABI checks above).

## Uncertainties / errata / deviations
- Deviation: built in this worktree via a scratch overlay instead of a new `lockseal` worktree (worker
  instructions pin this worktree; / had 9 GB free). Agreed by kam-inp-lockdata-84.
- No suspected errata.
