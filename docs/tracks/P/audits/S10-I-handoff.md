# S10-I prover handoff (branch inp-s10i, 49f4ff14; off inp (S10-R, S10-F, S10-H, S10-C, S10-S on inp); offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/Nondegeneracy/Interface.lean` (191 lines). KAM.lean NOT edited (lint reports it out of date; orchestrator regenerates).

**Declarations:** `KAM.Planetary.Nondegeneracy.interface` (statement verbatim from P810Signatures.lean ~l.557; blueprint `bpP:p10:interface`, steps if-a..if-d). Helpers (unique names, grepped): `image_action_open`, `exists_good_patch`. The signature file assigns no other declaration to this module.

**Approach:** (a) `generic` applied to the family (good∘sigma, f_j) on `axes n` gives an open dense set; pick a closed cube inside it and inside `ball aStar η` (also yields the f_j ≠ 0 clause). (b) α: the set is the image of the compact `closedBall ×ˢ k4` (`k4_finite`, discrete ℤ) under a continuous map (`sorted_analytic` on `simpleAxes ⊇ goodAxes`); `IsCompact.sInf_mem` plus NR4 (`good_ne_zero_iff`) gives α>0. (c) B open via `image_action_open` (action is a homeomorphism onto `actionDomain`), connected, K compact, volume K>0 (contains the image of an open ball), analyticity and `rnd_def` from `rnd`. (d) μ0 := `Nat.find` of the `cp09_lemma1` existence; minimality, monotonicity (`betaFamily_mono`) and `betaFamily_le` give the remaining clauses.

**Checks:** `inp_lake_build.sh … KAM.Planetary.Nondegeneracy.Interface`: Build completed successfully, no warnings in my file. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message "KAM.lean is out of date" (not mine to edit).
`#print axioms KAM.Planetary.Nondegeneracy.interface`: [propext, Classical.choice, Quot.sound].

**Uncertainties / design signals:** none (no heartbeat issues, no overrides; file ≪1500 lines). **Errata / deviations:** none.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S10-I (line ~452: 'interface, all simultaneous patch witnesses') and its node table/proof plan; P810 design audits; signatures /root/code/KAM-inp/.drafts/design/P810Signatures.lean line ~557): (1) interface = signature file EXACTLY, and the S10-I slice COMPLETE: all simultaneous patch witnesses, and every graph proof step the node table maps to S10-I (siblings S8-Q, S9-Q, S8-4 failed for unexported graph cuts; check each step's literal conclusion); (2) proof soundness: the consumption of S10-R (action_diffeomorphism, frequency, rnd, scaling), S10-H, S10-C (finite_type, cp09_lemma1), S10-S as designed; that the witnesses are SIMULTANEOUS (one choice serving all clauses, not separate existentials); no added premises; (3) hygiene (no EuclideanSpace; no public short name used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/Nondegeneracy/Interface.lean.
