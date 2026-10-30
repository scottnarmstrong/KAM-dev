# Handoff: LOCK-ASSEMBLY part 1 (glue), branch inp-lockasm

## Files
- NEW `KAM/SpinOrbit/Lock/Assembly.lean` (389 lines). Imports Lock.Confine, Lock.PO.Orbit, Lock.Coords.Maps,
  Mathlib.Analysis.Real.Pi.Bounds. No other file touched (KAM/Root not regenerated, per rule 10: the orchestrator
  must run `scripts/gen_root_imports.py`).

## Declarations
Signed, exactly as in SOLockSignatures.lean:
- `abs_le_of_libAction_lt` (CONF corollary; audit LOCK-PO-CONF note 1).
- `sqrt_libAction_le` (change of centre; audit note 1).
- `lunarOmega : ℚ := 8 / 65` (signed; not landed before).
- `lockLiteralCheck (Ω cs lo hi r₀ r₁ Iin Rψ Rp : ℚ) : Bool` — signed type needs neither `HamExpr.sqrt` nor
  `LockGraphCert`, so its body is written here. Exact ℚ arithmetic: π ∈ [3141592/10⁶, 3141593/10⁶]
  (`pi_gt_d6`/`pi_lt_d6`); square-root majorants `lockSqrtUp` (Newton with fuel, quality never used) are
  re-verified inside the check by squaring. Checks: 0<Ω, 0≤r₀, 0≤r₁, 0≤hi, root checks, tube
  `(b + a₁R + a₂R'_hi)² ≤ lo`, `R ≤ Rψ`, `hi/(πlo Ω) ≤ (Rψ−R)²`, `R' ≤ Rp`, `Ω hi/πlo ≤ (Rp−R')²`,
  `Rψ + r₀ < 1/4`, with R = r₀ + Σ|c_k|, R' = r₁ + 2πhi Σ(k+1)|c_k|.
  Design deviation: three extra sign checks (0 ≤ r₀, r₁, hi) added; harmless (all hold for the literals).
- The signed soundness `lunar_sync_lock_of_cert` needs `LockGraphCert`/`lockHamExpr` → SKIPPED as instructed.
  Instead, soundness is `lockLiteralCheck_sound` (→ `LockLiteralFacts`, real inequalities).
Unsigned helpers (distinct names): `sqrt_sq_add_sq_le`, `abs_list_sum_map_le`, `hasDerivAt_list_sum_map`,
`lockCentreAbs`, `lockCentreDAbs`, `abs_lockCentre_le`, `hasDerivAt_lockCentre`, `abs_deriv_lockCentre_le`,
`lockNatSqrt`, `lockSqrtUp`, `lockSqrtUp_nonneg`, `lockPiLo`, `lockPiHi`, `LockLiteralFacts`,
`lockLiteralCheck_sound`, `lunar_literalCheck` (the lunar literals pass, `decide +kernel`, fast).

Parametric critical path (EXPLICITLY CONDITIONAL; not the headline, not stated as `lunar_sync_lock`):
- `lunar_sync_lock_of_barrier_check`: `B : LockBarrier Ω (lockCentre cs) Iin' Iout`, `lo ≤ Iin'`, `Iout ≤ hi`,
  passing `lockLiteralCheck Ω cs lo hi (17/10⁶) (27/200000) Iin Rψ Rp` ⇒ headline shape with Rψ, Rp.
- `lunar_sync_lock_of_barrier`: `B : LockBarrier (lunarOmega:ℝ) (lockCentre lunarLockCentre) Iin Iout`,
  `132/10000 ≤ Iin`, `Iout ≤ 163/10000`, `h₀ : libAction lunarOmega lunarSyncOrbit (q₀,p₀,φ₀) < 129/10000`
  ⇒ verbatim the conclusion of `lunar_sync_lock`. The final theorem is then
  `lunar_sync_lock_of_barrier B hlo hhi q₀ p₀ φ₀ h₀` once LOCK-GRAPH/DATA deliver B with pLo−disp ≥ 0.0132 and
  pHi+disp ≤ 0.0163 (LOCK-GEN-1: P ∈ [0.013238, 0.016258], so margins 3.8·10⁻⁵ and 4.2·10⁻⁵).
  If the kernel-passed range is outside this window, use `_check` with other lo/hi (re-run `decide +kernel`).
  Margin check: (√0.0129+δ)² ≈ 0.01315 < 0.0132; Rψ bound ≈ 0.2054 ≤ 0.21; Rp ≈ 0.0255 ≤ 0.026.

## Approach
abs bound: `Real.abs_le_sqrt` from π Ω X² < I, π Y²/Ω < I. Transfer: write 𝓘 = (√π√Ω X)² + (√π Y/√Ω)², planar
triangle inequality `sqrt_sq_add_sq_le` (via `sqrt_le_iff`, nlinarith). Centre bounds by list induction
(HasDerivAt of the finite sine sum). Path: transfer ⇒ 𝓘_c(x₀) < lo ≤ Iin'; `lock_confinement`;
`abs_le_of_libAction_lt` with hi; pointwise triangle back to ψ*; |q−φ| ≤ Rψ + r₀ < 1/4.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-lockasm KAM.SpinOrbit.Lock.Assembly` → `Build completed successfully
  (2962 jobs).` No warnings/sorry in Assembly.lean.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS (1639 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK;
  only remaining complaint: "KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/SpinOrbit.lean)"
  — expected for a new module; orchestrator regenerates (rule 10 forbids me).
- `main_shortname_check.py /root/code/KAM-inp-lockasm KAM.SpinOrbit.Lock.Assembly` → `short-name check OK`.
- `#print axioms` (scratch file, deleted): sqrt_libAction_le, abs_le_of_libAction_lt, lockLiteralCheck_sound,
  lunar_literalCheck, lunar_sync_lock_of_barrier_check, lunar_sync_lock_of_barrier: all
  `[propext, Classical.choice, Quot.sound]`.
- No maxHeartbeats or other overrides; no design signals.

## Uncertainties
- The hypotheses window [132/10000, 163/10000] for `lunar_sync_lock_of_barrier` is my choice from LOCK-GEN-1
  numbers; adjust if the N = 65 kernel certificate's range differs.
- `lockLiteralCheck` body is a new design choice (the signature left it `sorry`); LOCK-ASSEMBLY part 2's
  `lunar_sync_lock_of_cert` should consume `lockLiteralCheck_sound` / `lunar_sync_lock_of_barrier_check`.

## Errata / deviations
- No source errata found. Deviation: extra sign checks in `lockLiteralCheck` (above). `lunar_sync_lock_of_cert`
  skipped per brief.
