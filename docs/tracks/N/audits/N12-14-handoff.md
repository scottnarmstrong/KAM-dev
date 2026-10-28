# N12-14 prover handoff (branch inp-n1214, b2282ed; contains N12-01..N12-13 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/Stopped.lean` (383 lines). No other file touched (KAM.lean not edited).

**Nodes:** `bpN:p12:s-trans#psi` → `avgStopped` (verbatim from the signature file);
`bpN:p12:stopped` (+ `st-meas`, `st-pt`, `st-int`) → `stopped` (verbatim signature, no extra premise).

**Approach:** `M₂` from `envelopes d` (depends only on `h`, `R`); `A₁ = max 1 (N·(max 0 cΦ + 4·max 0 cW))`,
`N` = size of a finite set of angle cells covering K (`exists_cell_cover`, from boundedness of K).
Both are chosen before f₁ and ε; for each f₁ the data `d₁ := {d with hf := hf₁}` is used.
- st-meas: `measurableSet_avgStay` (stay set is relatively open by `isOpen_avgStay_relative`, inducing embedding),
  `measurable_killed` (split on the open flow domain, flow continuous there), `avgStoppedExt`
  (zero-extended envelopes; equals `avgStopped` on K via `flow_mem_of_stay`) measurable by
  `Measurable.lintegral_prod_right'`, then `K.indicator`.
- st-int: cell decomposition (`lintegral_biUnion_finset`), per cell Tonelli swap, `transport` per time slice
  (`lintegral_slice_le`, `lintegral_time_le`), and `transport` at t = 0 (flow 0 = id) for the corrector term
  (`lintegral_cell_le`); ε·(1/ε)=1; envelope integral bounds from `envelopes`.
- st-pt: `pointwise` (κ=√ε) + `exit`; integral over Icc 0 t replaced by Ico 0 t (endpoint null, `Ico_ae_eq_Icc`),
  where `mem_avgStay_of_lt_tau` puts v<t≤τ in the stay set.

**Checks:**
- `inp_lake_build.sh … KAM.Nekhoroshev.Averaging.Stopped`: Build completed successfully (only pre-existing warnings
  from other modules; none from Stopped.lean). No `sorry`, no heartbeat options.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, no long lines.
  It prints `KAM.lean is out of date; run scripts/gen_root_imports.py` — expected (rule 10: KAM.lean is generated
  and not edited here; the orchestrator regenerates it to include Stopped).
- `#print axioms KAM.Nekhoroshev.stopped` and `avgStopped`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations:** none. No statement was changed. The signature file's `avgStopped` binder
order (`R s M₂ ε`) was copied verbatim. Extra public helpers (all in `KAM.Nekhoroshev`): `measurableSet_avgStay`,
`measurable_killed`, `avgFlow_zero`, `zero_mem_avgOmega`, `mem_avgDomain_of_half`, `mem_avgStay_of_lt_tau`,
`flow_mem_of_stay`, `avgG_subset_actionBall`, `lintegral_slice_le`, `lintegral_time_le`, `exists_cell_cover`,
`avgStoppedExt`, `avgStopped_eq_ext`, `measurable_avgStoppedExt`, `lintegral_cell_le`. No design signals
(Stopped elaborates in ~8 s at default heartbeats).

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-14 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (avgStopped, stopped: finite cell cover of K, epsilon*T = 1, measurable killed integrand, constants uniform over all size-one f1); (2) proofs sound (N12-09/11/12/13 consumed as designed); no added premises; (3) hygiene. Audit ONLY the Stopped module(s) (compare with branch inp-n1213).
