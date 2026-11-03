# Handoff B4-TCHECK

**Files:** `KAM/EffectiveStability/TorusCheck.lean` (176 lines). Only file added; it imports `TorusStep.Smoke` (for `torusSmokeH`, which also brings in `TorusStep`).

**Approach:** mirrors `OscillatorCheck.lean`.
- `TorusStepCert n` is data only (H χ Nact P : FTPoly, L : ℕ, ℚ radii and bounds, lists a b η r).
- `checkTorusStep` is a right-nested `&&` chain of 18 global checks plus a `(List.range n).all` of 8 per-index checks.
  - Global: `ftFitsCheck` for H, χ and P; `ftActOnly Nact`; `1 ≤ L`; `ftEqCheck` of the Lie-sum identity; σ'>0, ρ'>0, δc>0; 0≤ε≤1/2; `ftPiUB ≤ πub`; `2 πub σ < 1`; `1/(1-2 πub σ) ≤ lam`; εb>0; T≥0; σ'<σ; δc+σ'/2<σ.
  - Per index i<n: hJ and hφ majorants; b≤r; b+εb+ρ'≤ρ; r+δc+ρ'/2<ρ; η≥0; drift `ftAngleDriftBound P i πub b + Bmaj/(L! δc) ≤ η`; margin `a+Tη<b`.
- `ρl = List.replicate n ρ`; `bl = c.b`.
- `π ≤ πub` is obtained from `pi_le_ftPiUB` and the ℚ check `ftPiUB ≤ πub`.

**Exact signature:**
```
theorem checkTorusStep_sound {n : ℕ} (c : TorusStepCert n) (hc : checkTorusStep c = true)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j : Fin n, |w₀.2 j| ≤ (c.a.getD j 0 : ℝ)) :
    ∃ T₁ : ℝ, (c.T : ℝ) < T₁ ∧ ∃ z, z 0 = torusChart c.χ c.σ c.ρ w₀ ∧ ... (conclusion of
    torusStep_confinement with σ ρ T cast from ℚ, a := c.a.getD, η := c.η.getD)
```
Full text is at lines 86–108 of the file. `checkTorusStep` and `TorusStepCert.torusBmaj` are the other public declarations.

**Smoke:** `torusSmokeCert` (n=1, H=Nact=J₀²/2, χ=0, P=0, L=1, σ=1/10, ρ=5, σ'=1/20, ρ'=1, δc=1/20, ε=0, εb=1, T=1, πub=ftPiUB, lam=3, a=[0], b=[1], η=[0], r=[2]).
- `torusSmokeCert_check : checkTorusStep torusSmokeCert = true := by decide +kernel`.
- `torusSmokeCert_zeroDrift` feeds it to the soundness theorem.
- Kernel time: type checking 19.4 ms in the profiler. The whole module builds in about 2.5 s.

**Checks (all run, all OK):**
- `b_build.sh $PWD KAM.EffectiveStability.TorusStep.Smoke KAM.EffectiveStability.TorusCheck`: build completed successfully, no warnings.
- `sh scripts/lint_sources.sh`: OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- Line-length check over `KAM/EffectiveStability/**`: `[]`.
- `main_shortname_check.py`: "short-name check OK". An earlier run flagged `Bmaj`, which collided with `OscillatorCheck`; it is now `torusBmaj`.

**Axioms** (`checkTorusStep_sound`, `torusSmokeCert_check`, `torusSmokeCert_zeroDrift`): `[propext, Classical.choice, Quot.sound]`.

**Signature changes:** none beyond the brief. `Nact` has no `ftFitsCheck`, because `torusStep_confinement` does not assume `FTFits Nact`.

**Design signals:** none. **Uncertainties:** none. **Errata / deviations:** none. `torusStep_confinement` was not changed.

## AUDIT FOCUS (kam-b1)
Track B, program B4 (overnight D71; nothing frozen; OD-B11). Torus analogue of the landed, audited B2-CHECK
(OscillatorCheck.lean), wrapping torusStep_confinement (B4-TSTEP, audit 1 PASS WITH NOTES). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B4-TCHECK.md and brief-B1-common.md. Scope: commit 5bf6bd3b3 (TorusCheck.lean).
Check: (1) checkTorusStep is a total computable Bool over data only and encodes EVERY non-binder premise of
torusStep_confinement faithfully (no premise dropped, weakened or mis-indexed; the π bound via ftPiUB ≤ πub and
pi_le_ftPiUB; the strip checks 2πubσ < 1, 1/(1−2πubσ) ≤ lam; ℚ→ℝ casts; replicate radius list); (2)
checkTorusStep_sound's only hypotheses are hc and the chart initial box; conclusion = torusStep_confinement's with
data from c; (3) kernel evaluation only (no native_decide/ofReduceBool); (4) hygiene (AGENTS rules 3, 4, 7; widths ≤
100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
