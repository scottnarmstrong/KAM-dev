# N12-15 prover handoff (branch inp-n1215, fdd4419; contains N12-01..N12-14 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/GoodSet.lean` (181 lines). No other file touched (KAM.lean not regenerated).
**Proved:** `avgGood` (def, verbatim), `good` (`bpN:p12:good`), `bad` (`bpN:p12:bad`, bd-exit/bd-stay/bd-concl). Signatures verbatim.
Auxiliary lemmas: `mem_flowDomain_of_omega`, `continuousOn_disp`, `continuousOn_sSup_disp`, `exists_max_disp`.

**Approach.** `good`: `compact_max_on` gives continuity of `x ↦ sSup_{[0,1/ε]} ‖flow t x .2 - x.2‖` on the open set
`avgOmega (1/ε)` (joint continuity from `continuousOn_avgFlow`, time slice inside the flow domain by ordConnectedness of
`eIoo`); `{x ∈ Ω | M x < η}` is open, so avgGood = K ∩ O is relatively open and K \ avgGood = K \ O is measurable.
`bad`: obtain `M₂ A₁` from `stopped` (applied with `f₁ := f`, `d.hf`). Threshold (η ≤ R/8): if `τ < 1/ε`, then `exit`
gives a real exit time with displacement exactly R/8 and the stopped bound at `u = τ` gives `ofReal (R/8) ≤ avgStopped`;
otherwise `τ ≥ 1/ε`, so by `exit` x ∈ avgOmega (1/ε), x ∉ good forces `sSup ≥ η`, the sup is attained (compactness), and the
stopped bound at `t = 1/ε` finishes. Good bound at level R/8: if `τ < 1/ε` the exit displacement R/8 would be ≤ sSup < R/8
(strictness), so `τ ≥ 1/ε` and the stopped bound applies.

**Checks.** `inp_lake_build.sh /root/code/KAM-inp-n1215 KAM.Nekhoroshev.Averaging.GoodSet`: "Build completed successfully", no
warning in GoodSet. `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only
message is "KAM.lean is out of date" (expected: new module, KAM.lean must not be edited by me; orchestrator regenerates).
`#print axioms` of `good` and `bad`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations:** none. No heartbeat overrides; no design signals. Strict-good (`< η`) vs nonstrict-bad
(`η ≤`) threshold confirmed consistent with the proofs above. Imports: Stopped, CompactMaximum (Exit/Flow come through Stopped).

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-15 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (avgGood, good, bad; strict-good versus nonstrict-bad threshold exactly as designed); (2) proofs sound (N12-02 CompactMaximum, N12-11 Exit, N12-14 Stopped consumed as designed); no added premises; (3) hygiene. Audit ONLY the GoodSet module(s) (compare with branch inp-n1214).
