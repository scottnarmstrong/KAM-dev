# N12-03c prover handoff (branch inp-n1203c, c0fdfc5; base inp-n1203b; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/LocalDependence.lean` (464 lines). Branch inp-n1203c. KAM.lean not touched
(`lint_sources.sh` reports "KAM.lean is out of date": the orchestrator must regenerate; otherwise PASS, rc 0).

**Nodes proved**
- `#derivative-limit`: `KAM.Nekhoroshev.voltIter` (iterates Y_0=id, Y_{m+1}=id+∫DF(u_m)∘Y_m), `voltIter_spec`
  (continuity, bound 1/(1-aΛ), Y_m = D_x u_m on the open ball, by `hasFDerivAt_intervalIntegral_comp`),
  `voltIter_step` (recurrence ‖Y_{m+1}-Y‖ ≤ q‖Y_m-Y‖ + a d_m/(1-q)), `voltIter_uniform` (uniform convergence Y_m→Y,
  from the recurrence + uniform continuity of DF on the compact trap; no contraction of (y,Y)).
- `#identify`: `hasFDerivAt_limit` (D_x y = Y via `hasFDerivAt_of_tendstoUniformlyOn`).
- `ext_dep`: `KAM.Nekhoroshev.ext_dep`, signature copied verbatim from N12Signatures.lean (only C¹ on W; no C²/Lipschitz-DF premise).
  Proof: δ with closedBall x₀ δ ⊆ W, bounds L,Λ by compactness, r=δ/2, ρ=δ, a=min(δ/(2(L+1)),1/(2(Λ+1))),
  `picard_family` (03a), `linear_family` with G=DF(y) (03b), `hasFDerivAt_limit`, variational equation from linear_family.
- Helper `continuousOn_intervalIntegral_param`, structure `IterData` (regularity data of the iterates; all fields are source/typing data, no conclusions).

**Checks**
- `inp_lake_build.sh /root/code/KAM-inp-n1203c KAM.Nekhoroshev.Averaging.LocalDependence`: success, no sorry, no errors.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (only note: KAM.lean out of date).
- `#print axioms` of `ext_dep`, `voltIter_uniform`, `hasFDerivAt_limit`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat overrides, no design signals (all proofs at default heartbeats;
two early timeouts were fixed by stating hypotheses of `hasFDerivAt_intervalIntegral_comp` as separate `have`s).

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-03c and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (#derivative-limit, #identify, ext_dep) — derivative convergence PROVED, not merely a candidate Y; (2) proofs sound (hasFDerivAt_of_tendstoUniformlyOn hypotheses discharged); no added premises; (3) hygiene. Audit ONLY the LocalDependence module(s) (compare with branch inp-n1203b).
