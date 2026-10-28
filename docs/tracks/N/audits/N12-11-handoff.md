# N12-11 prover handoff (branch inp-n1211, e8c6a0a; contains inp-n1210b and inp-n1202 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/Exit.lean` (≈250 lines). Nothing else changed. KAM.lean not edited.

**Declarations (signatures verbatim):** `avgStay`, `avgTau`, `exit` (bpN:p12:exit, ex-exit, ex-g, ex-open).
Extra helper theorem `isOpen_avgStay_relative` (relative openness, the last conjunct of `exit`); private
`sSup_coe_image`, `sSup_coe_image_top`, `avgField_periodic`.

**Approach:** `z = avgFlow · x` is the maximal solution (`avgMaximal_spec`); `V = {y | ‖y.2 - x.2‖ < R/8}`.
`KAM.ODE.gen_exit` on `J = eIoo Tm Tp`. The stay set at `x` equals `{t ∈ J, 0 ≤ t, z '' [0,t] ⊆ V}`.
No exit: `gen_continuation_periodic` (U = actionBall n R, K = closedBall 0 (5R/8)) gives `Tp = ⊤`, so `avgTau = ⊤`.
Exit at `ts`: `avgTau = ts` (EReal sSup lemma), `‖z ts .2 - x.2‖ = R/8` from `ts ∈ closure V \ V`,
`avgG` from `‖x.2‖ < R/2` plus displacement ≤ R/8 < 3R/4. Relative openness: set `A = flowDomain ∩ {g < R/8}`
is open (`continuousOn_avgFlow`); `generalized_tube_lemma` on `[0,t₀] × {y₀}` plus a collar `t < t₀ + η`.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n1211 KAM.Nekhoroshev.Averaging.Exit`: "Build completed successfully (2972 jobs)",
  no warnings in Exit.lean.
- `scripts/lint_sources.sh`: no long lines; `check_lean_modules: PASS (523 Lean files)`; FROZEN-ANCHOR GUARD OK;
  ABI HASHES OK. It reports "KAM.lean is out of date; run scripts/gen_root_imports.py": expected, because the new
  module is not yet in the generated root (I did not edit KAM.lean; the orchestrator regenerates it).
- `#print axioms KAM.Nekhoroshev.exit` and `isOpen_avgStay_relative`: `[propext, Classical.choice, Quot.sound]`.
  (Probe `.drafts/scratch/N1211Axioms.lean`, not committed.)

**Uncertainties / deviations:** none. `hε : 0 < ε` is unused in the proof (kept for the signature; `have _ := hε`).
`CompactMaximum` is imported per the design edge but not used. No errata. No heartbeat design signals.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-11 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (exit dichotomy, avgTau, avgStay, relative openness, compact action collar); (2) proofs sound (KAM.ODE.{Exit,Continuation}, N12-02, N12-10b consumed as designed); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the Exit module(s) (compare with branch inp-n1210b).
