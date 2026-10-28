# P23-01 prover handoff (branch inp-p2301, d3ac220; off inp with inp-design-p23; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Averaging/Setting.lean` (~115 lines), the only committed file.

**Declarations (verbatim from P23Signatures.lean, bodies proved):** `CPhase`, `CHam`, `geometricWidth`, `realBase`,
`coefficientDom`, `realTube`, `firstBlock`, `lastBlock`, `block_bridge` (`⟨rfl, rfl⟩`), `conv_data` (set extensionality
on the two existentials, then unfolding `coefficientDom`/`Dom`), `setting`, `DirectHyp`, `TwoDiv`, `AvgHyp`.
Not in this package: `direct`, `split`, `nfb`, `avg`, the oscillator declarations and the P1 fixtures
(`twoScaleDiophantine`, `IsLatticeTorus`), which belong to other packages.

**DEPENDENCY NOTE (needs orchestrator action):** `setting`/`TwoDiv` need `zBall`, `freq`, `dotC`, `DivisorBound`
(namespace `KAM.NormalForm`). These are NOT on `inp`; they live in `KAM/Nekhoroshev/NormalForm/Setting.lean` on branch
`inp-n61` (commit 2fd6a16, N6-1, not yet landed). They match the signature-file fixtures exactly. My module imports
`KAM.Nekhoroshev.NormalForm.Setting`. To build here I copied that file from `inp-n61` into the worktree as an
UNTRACKED file and did not commit it. This branch therefore builds only once N6-1 is landed on `inp`.
Not merged or cherry-picked.

**Checks:**
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-p2301 KAM.Planetary.Averaging.Setting`: Build completed
  successfully, no warnings (a `Set.mem_setOf_eq` deprecation was fixed to `Set.mem_ofPred_eq`).
- `#print axioms` for `block_bridge` and `conv_data`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK, no long lines.
  Its only complaint is "KAM.lean is out of date", expected because KAM.lean is generated and I must not edit it.
  Please run `scripts/gen_root_imports.py` when landing.

**Uncertainties / design signals:** none. No heartbeat issues; no premises added.
**Suspected errata / deviations:** none. The only change from the signature file is that the upstream fixtures
are replaced by the owner import (as the signature file instructs).

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md rev 2 row P23-01 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; blueprint-P p2 conv#data, setting): (1) statements = design signatures and blueprint; (2) definitions/structures are the intended objects (no conclusion-shaped fields); (3) hygiene (lint incl. 100-char lines). Audit ONLY the P23-01 module(s) (KAM/Planetary/Averaging/Setting*).
