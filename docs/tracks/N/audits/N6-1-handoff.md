# N6-1 prover handoff (branch inp-n61, 2fd6a16; off inp (N67 design merged); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/NormalForm/Setting.lean` (≈176 lines, path as in the brief). Nothing else touched.

**Nodes proved:** `p6#data` (`zBall`, `freq`, `dotC`, `conjExp` defs), `setting` (`IsNonresonant`, `FreqLipschitz`,
`DivisorBound`, `IsDecomp`, `starNorm` defs), `lipschitz` (`KAM.NormalForm.lipschitz`, `lipschitz_entries`),
`divisor` (`KAM.NormalForm.divisor`). Definitions and theorem statements are copied verbatim from
`NPart67Signatures.lean`, except that the `IsNonresonant` signature line is wrapped to stay within 100 columns
(formatting only; the lint requires it).
Helpers (new, unconditional): `norm_dotC_le`, `differentiableAt_freq`.

**Approach:** as in design §7.1 N6-1. `lipschitz`: `Convex.norm_image_sub_le_of_norm_fderiv_le` on `ball I₀ r ⊆ polyNbhd D r`;
differentiability of `freq h` from `holomorphic_regularity`. `lipschitz_entries`: `fderiv_pi`, expansion of `v` in the
basis, `opNorm_le_bound` (separate `n = 0` case). `divisor`: `norm_dotC_le`, reverse triangle, `α/conjExp p = α - α/p`.

**Checks:**
- `inp_lake_build.sh … KAM.Nekhoroshev.NormalForm.Setting`: `Built … successfully`, no warnings.
- `#print axioms` of `lipschitz`, `lipschitz_entries`, `divisor`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: final output is below the commit. Only the expected remaining message is
  `KAM.lean is out of date; run scripts/gen_root_imports.py` (I did not edit `KAM.lean`; orchestrator to regenerate).

**Uncertainties / design signals:** none; no heartbeat issues, no sorry. **Errata / deviations:** none.
Note: the brief's module path is `KAM/Nekhoroshev/NormalForm/Setting`, while the design text says `KAM/NormalForm/Setting`;
I followed the brief. Downstream packages must import `KAM.Nekhoroshev.NormalForm.Setting`.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-1 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p6 data, setting, lipschitz, divisor): (1) statements = design v2 signatures and blueprint; (2) definitions are the intended objects; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N6-1 module(s) (KAM/Nekhoroshev/NormalForm/Setting*).
