# S7-3 prover handoff (branch inp-s73, 640de98; contains inp-s71 (S7-1, delivered); offloaded package run by the main orchestrator; prover on claude-12)


**Branch** inp-s73. **Files (new):** `KAM/Nekhoroshev/Stability/Conjugation.lean` (141 lines),
`KAM/Nekhoroshev/Stability/Transfer.lean` (~265 lines). No existing file changed; `KAM.lean` not edited.

## Nodes
- `bpN:p7:conjugation` -> `KAM.Stability.conjugation` (Conjugation). Approach: complex field identity
  `DΨ X_{H'} = X_H∘Ψ` from `KAM.Canonical.map_hamiltonianJ_comp` (with `H' = H∘Ψ` near the point, chain rule),
  restricted to real points through `real_system` (b) (`ι₂ X^ℝ = X^ℂ ι`), real derivative of `reMap Ψ`
  as `Re ∘ DΨ ∘ ι₂` with `ι₂ ∘ Dψ = DΨ ∘ ι₂` by uniqueness of derivatives, then the chain rule along the orbit.
- `bpN:p7:stopped-extension` -> `KAM.Stability.stopped_extension` (Transfer). Private `stay_forward` (first exit via
  `KAM.ODE.gen_exit`, closed set `{Nrm(I-I₀) ≤ ϱ} ⊆ W_r`, closed-ball containment from `Nrm ≥ ‖·‖` and `ϱ<r`);
  negative times by time reversal of the same lemma.
- `bpN:p7:transfer` -> `KAM.Stability.transfer` (Transfer). Preimage by (T2), maximal `H'`-orbit (`gen_maximal`),
  (T3) puts it in a compact `Nrm`-ball inside `U_{r'}D` (needs `d+ϱ<r'`), `gen_continuation_periodic` shows the
  maximal interval contains `t`, `conjugation` + `gen_uniqueness_inter` identifies `z = Re Ψ ∘ z'`, then (T1) and
  the triangle inequality give `ϱ+2d`.
- `IsActionNorm`, instances and `exit_ball` already in S7-1 `Setting` (not touched).

All signatures copied verbatim from `NPart67Signatures.lean` (only binder names/shared variables differ in private lemmas).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-s73 KAM.Nekhoroshev.Stability.Conjugation` and `...Transfer`: Build completed
  successfully; no sorry. Only warning in my files: unused `hϱ` in `transfer` (signature-mandated).
- `#print axioms` of `conjugation`, `transfer`, `stopped_extension`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK, no long lines.
  It prints `KAM.lean is out of date; run scripts/gen_root_imports.py` — expected, since I must not edit KAM.lean
  (the orchestrator should regenerate it: new modules Conjugation, Transfer).

## Uncertainties / errata / deviations
None. No heartbeat issues (no overrides used; all files far below 1500 lines). No suspected source defects.
Note: `transfer` does not use `hϱ : 0 < ϱ` (the compactness argument works for any `ϱ`); harmless.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row S7-3 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p7 conjugation, transfer, stopped-extension): (1) statements = design v2 signatures and blueprint; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the S7-3 module(s) (KAM/Nekhoroshev/Stability/Conjugation*, Transfer*).
