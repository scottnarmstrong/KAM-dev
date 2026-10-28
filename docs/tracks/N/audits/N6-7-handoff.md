# N6-7 prover handoff (branch inp-n67, 66c3746; contains inp-n66 (N6-6, audited) and everything below it; offloaded package run by the main orchestrator; prover on claude-12)


**Files (new):** `KAM/Nekhoroshev/NormalForm/IterativeReal.lean` (~135 lines), `KAM/Nekhoroshev/NormalForm/Iterative.lean` (pure facade over IterativeMap, IterativeRemainder, IterativeReal).

**Nodes:** `bpN:p6:iterative-direct` (e) = `KAM.NormalForm.iterative_direct_e` (signature verbatim from NPart67Signatures.lean, no change). Extra public helper: `freq_im_real` (h real on real points of `Dom r s`, s>0, h holomorphic on `polyNbhd D r` ⇒ `(freq h (ι I) i).im = 0`).

**Approach:** `freq_im_real`: derivative of the real-variable path `t ↦ h(ι I + t e_i)`, whose imaginary part vanishes near 0 (hypothesis at points `(0, I + t e_i)`), via `HasFDerivAt.restrictScalars`, `Complex.imCLM`, uniqueness of derivatives. Main theorem: `homological_direct` (c) with that real frequency gives `homGen`, `homRes` real; `iterG` real by sum; `iterF` real from `composition_real` (via `IterHyp.compose`, radii `r-ρ-ρ` rewritten to `r-2ρ`) applied to `h∘snd + g + f`, minus the real `h∘snd` and `iterG`; last clause is `canonical_map_b` (second clause) with `IterHyp.canon`.

**Checks:** gate build of `KAM.Nekhoroshev.NormalForm.IterativeReal` and `...Iterative`: success, no sorry. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; it reports "KAM.lean is out of date" (not edited per rules; orchestrator must regenerate for the two new modules).
`#print axioms` of `iterative_direct_e` and `freq_im_real`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations / design signals:** none. No heartbeat issues. Remaining unused-simp-arg linter warnings are cosmetic, if any.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-7 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p6 iterative (e)): (1) statements = design v2 signatures and blueprint (iterative (e): reality of the iterated map); the facade Iterative has only public imports; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Nekhoroshev/NormalForm/IterativeReal.lean and the facade KAM/Nekhoroshev/NormalForm/Iterative.lean; the other files in the diff are inherited from inp merges (compare with branch inp-n66).
