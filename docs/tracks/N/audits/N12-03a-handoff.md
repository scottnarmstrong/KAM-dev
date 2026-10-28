# N12-03a prover handoff (branch inp-n1203a, 4a33d5a; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**File:** KAM/Nekhoroshev/Averaging/PicardFamilies.lean (new, ~330 lines). Committed on inp-n1203a. KAM.lean not touched.

**IMPORTANT deviation / report:** /root/code/KAM-inp/.drafts/design/N12Signatures.lean contains NO declarations for
N12-03a (only ext_dep etc. for later packages). The design gives only prose ("bounded continuous families on
[-a,a]x closedBall x0 r, closed trap, Mathlib contraction"). I therefore designed the statements myself; downstream
packages N12-03b/c should be checked against them (or the statements adjusted by the orchestrator).

**Declarations:** `PicardBounds` (Prop structure: 0<=a, 0<=L, r+aL<=ρ, ‖F‖<=L and Λ-Lipschitz on closedBall x0 ρ, aΛ<1),
`PicardBase`, `PicardTrap`, `PicardSpace` (closed trap in `Icc(-a)a × closedBall x0 r →ᵇ E`; `isClosed_picardTrap`, CompleteSpace instance),
`picardFun`, `picardMap`, `contractingWith_picardMap` (node ext-dep#complete-contraction, constant a·Λ),
`picardStart`, `picardExt` (+ `picardExt_of_mem`, `continuousOn_picardExt`, `picardExt_picardMap`, `dist_picardStart_le`),
`picard_family` (node ext-dep#picard): iterates u m (u 0 t x = x, u(m+1)=x+∫F(u m)), continuous trapped limit y with
integral equation, uniform rate ‖u m - y‖ <= aL(aΛ)^m/(1-aΛ), HasDerivAt (s↦y s x) (F (y t x)) on Ioo(-a)a.
Dependencies: Mathlib only (did not need KAM.ODE.Existence).

**Approach:** Φ y (t,x)=x+∫_0^t F(y(clamp τ,x)); continuity via intervalIntegral.continuous_parametric_intervalIntegral_of_continuous;
ContractingWith.fixedPoint and apriori_dist_iterate_fixedPoint_le; FTC via integral_hasDerivAt_right.

**Checks:** `lake build KAM.Nekhoroshev.Averaging.PicardFamilies` via gate: success, no sorry, no errors.
`scripts/lint_sources.sh`: check_lean_modules PASS (459 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
`#print axioms` for picard_family and contractingWith_picardMap: [propext, Classical.choice, Quot.sound].
Remaining warnings: unusedSectionVars linter notes only (no heartbeat issues, no set_option used).

**Uncertainties:** statement shape (above). No uniqueness statement for the fixed point included. **Errata:** none. 

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-03a and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design signatures (ext-dep#complete-contraction, #picard: trap and contract bounded continuous families); (2) proofs sound (contraction, Bochner integration, KAM.ODE.Existence used correctly); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N12-03a module (PicardFamilies).
