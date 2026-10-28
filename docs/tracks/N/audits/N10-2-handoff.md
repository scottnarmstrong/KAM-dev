# N10-2 prover handoff (branch inp-n102, cafc344; contains inp-n101 (N10-1, delivered); offloaded package run by the main orchestrator; prover on claude-12)


**Branch/worktree:** inp-n102, /root/code/KAM-inp-n102. Commit `cafc344`.

## Files
- New: `KAM/Nekhoroshev/Assembly/Hypotheses.lean` (189 lines). Nothing else changed (KAM.lean, frozen, manifest untouched).

## Declarations proved (signatures copied verbatim from N10Signatures.lean)
`hc_tubes`, `hc_h`, `hc_qc`, `hc_f`, `hc_exc`, `hc_time`, `head_field_locality`, `hypotheses_check`.

## Approach
- `hc_tubes`: `const_tubes`, `ball_subset_realActionDomain`; nonemptiness via `ι 0`; `ι I ∈ centralSet` for `I` in the half-ball.
- `hc_h`: `hessian_convert` (n·Mc operator bound), then `n*Mc ≤ B` from `q_pos` (as in `const_hyp`). Reality from the frozen clause of (H1) at real points of the tube (via `hc_tubes`).
- `hc_qc`: `qc_convert` (.2.1) at points of the real preimage of the tube (in `actionBall n R` by `hc_tubes`). No tilde scaling is used, so there is no `2π` to cancel.
- `hc_f`: `Dom n _ r0 s1 ⊆ complexDomain n R s` gives InClass (holomorphy, periodicity); `const_perturbation.1` gives WBound (`epsPrime = coth^n*ε` is defeq); RealOn from the frozen reality clause at real points of the tube.
- `hc_exc`: `mu*r0 ≤ 4*wmin` from `r0_le_wmin_div`, so `mu*r0/8 ≤ wmin/2 < wmin`. Lower bound from (H3) and `norm_le_euclid`.
- `hc_time`: `partials` (euclid bound `√n*M`) at `I ∈ realActionDomain` (using `R0 ≤ R/176`).
- `head_field_locality`: `univ ×ˢ ι⁻¹' polyNbhd` is open (`isOpen_polyNbhd`); `EqOn` on an open set gives `EventuallyEq` at each point, so `Filter.EventuallyEq.fderiv_eq` gives equal fderivs, then unfold `hamiltonianVectorField`.
- `hypotheses_check`: assembly of `Data` (`⟨hR, hs, hh.1, hf⟩`), `hc_h`, `hc_qc`, `hc_f`, `cp_dict`.

## Checks
- Gate build: `inp_lake_build.sh /root/code/KAM-inp-n102 KAM.Nekhoroshev.Assembly.Hypotheses` → `Build completed successfully (3194 jobs)`; no warnings in my file.
- `#print axioms` for all 8 theorems: `[propext, Classical.choice, Quot.sound]`.
- grep: no `sorry`, no `maxHeartbeats` in the file; file is 189 lines.
- `scripts/lint_sources.sh`: check_lean_modules PASS (417 files), FROZEN-ANCHOR GUARD OK. It also printed `KAM.lean is out of date; run scripts/gen_root_imports.py` — expected: new modules (Choice, Hypotheses) are not yet in the generated root; I did not edit KAM.lean (rule 10). Overall lint exit status is 1 solely because of the out-of-date generated root `KAM.lean` (orchestrator must run `scripts/gen_root_imports.py` on landing); no forbidden-pattern, module or frozen-anchor failure was reported.

## Uncertainties / design signals
- None: no heartbeat problems; no statement needed changing or extra hypotheses.
- Imports are broader than the signature file (added `Interfaces.QuasiConvex`, `HoloReal`, `Setting`, which `ConstantsAnalytic` did not import transitively); no provider/DRAFT_SORRY import.

## Suspected errata / deviations
- None. `hc_f`/`head_field_locality` need no positivity of `ε`/`p`, consistent with audit notes.

AUDIT FOCUS (design docs/tracks/N/design/N10-LEAN-DESIGN.md row N10-2 and proof plan; its audit DESIGN-N10-design-audit-1.md; blueprint-N p10 hypotheses check): (1) statements = design signatures and blueprint (each hc_* verifies a hypothesis of the stopped Theorem 1 from the headline data, with the stated constants); (2) no hypothesis assumed; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N10-2 module(s) (KAM/Nekhoroshev/Assembly/Hypotheses*).
