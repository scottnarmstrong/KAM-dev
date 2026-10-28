# P23-02 prover handoff (branch inp-p2302, 9251e41; off inp with inp-design-p23; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/TwoScale/Constants.lean` (~190 lines). Commit on branch inp-p2302 (see git log).

**Declarations (verbatim from P23Signatures.lean):** `ScaleData`, `constants`, `cutoff`, `rhoHat`, `eHat`, `kamConstant`,
`complementConstant`, `initialL`, `nextScale`, `seq` (all verbatim). Proved: `rem_norm` (bpP:p3:rem-norm), `rem_norm_blocks`,
`sums` (bpP:p3:sums; the abstract scalar recurrence, all four conjuncts). Helpers (new, extra): `cutoff_pos`, `rhoHat_pos`.

**Approach:** `rem_norm`: case split `le_total Mhat M` for `initialL`; `cutoff` is definitionally unchanged (`rfl`);
`rhoHat` monotone via `min_le_min` and `div_le_div_of_nonneg_left` (cutoff > 0 since `K ≥ 6/s`); `eHat` via `E L / R^2` antitone in `R`.
`sums`: `e k ≤ e m^(2^(k-m))` by `Nat.le_induction`; `e(m+k) ≤ e m (1/2)^k`; `c^k e k ≤ e 0 (1/2)^k` from
`(c e0)^k ≤ (1/2)^k` and `e0^(2^k-k) ≤ e0`; geometric tsum; `R`, `s` by induction.

**Checks:**
- `lake env lean` on the file: no output (no warnings/sorry).
- Gate: `inp_lake_build.sh /root/code/KAM-inp-p2302 KAM.Planetary.TwoScale.Constants` → `Built KAM.Planetary.TwoScale.Constants (34s)`, `Build completed successfully`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; reports only
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (I did not touch KAM.lean per rules; orchestrator must regenerate).
- `#print axioms` of `rem_norm`, `rem_norm_blocks`, `sums`: `[propext, Classical.choice, Quot.sound]`.

**Deviation (needs orchestrator action):** the signature of `rem_norm_blocks` uses `firstBlock`/`lastBlock`, which are owned by
P23-01 (`Averaging/Setting.lean`), while P23-02's allowed imports are frozen/Mathlib only. I did NOT define them here (would clash
with P23-01). Instead `rem_norm_blocks` is stated with the unfolded bodies
`‖fun i : Fin a => A v (Fin.castAdd b i)‖ ≤ ‖A‖ * ‖v‖` and `‖fun i : Fin b => A v (Fin.natAdd a i)‖ ≤ ‖A‖ * ‖v‖`
(definitionally equal to the signature once `firstBlock (b := b) (A v)` is unfolded). Downstream (P23-14) can use it via `exact`/`show`;
alternatively a facade in P23-01-importing module can restate it verbatim.

**Other notes:** `rem_norm` hypotheses `0 < p.τ`, `0 < p.Mbar` are unused (kept as signature). No heartbeat overrides; no file near cap.
**Uncertainties:** none. **Suspected errata:** none.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md rev 2 row P23-02 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; blueprint-P p3a constants, scale sequence): (1) statements = design signatures and blueprint (two-scale constants, initial scale, next scale, sequence, remainder norms, scalar sums; source gap p3a L91 Ê monotonicity handled as designed); (2) definitions are the intended objects; (3) hygiene (lint incl. 100-char lines). Audit ONLY the P23-02 module(s) (KAM/Planetary/TwoScale/Constants*).
