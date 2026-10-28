# N12-13 prover handoff (branch inp-n1213, 1dfeb81; contains inp-n1210b (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/Transport.lean` (196 lines), commit 1dfeb81 on `inp-n1213`. No other file changed
(KAM.lean not touched; the root-import regeneration is the orchestrator's job).

**Nodes:** `bpN:p12:s-trans#data` -> `KAM.Nekhoroshev.avgCell`; `bpN:p12:transport` (tr-cov, tr-cells, tr-sum) ->
`KAM.Nekhoroshev.transport`. Both signatures are verbatim from N12Signatures.lean, with `d` and `ε` as section
variables (same argument order). The hypothesis `ht : 0 ≤ t` is required by the signature but unused (it only
produces an unused-variable linter warning).

**Approach:**
- Change of variables on `D ⊆ Ω_t` using `lintegral_image_eq_lintegral_abs_det_fderiv_mul`. The flow is C¹ on the open set Ω_t,
  injective there via `avgFlow_inverse`, with `det = 1` (`det_fderiv_avgFlow`). Measurability of the image `Φ(D)` comes from
  Lusin–Souslin (`MeasurableSet.image_of_continuousOn_injOn`).
- General lemma `lintegral_le_of_disjoint_cellPieces`, independent of the flow. For S measurable it splits S into the integer
  angle cells `S ∩ avgCell k` (`lintegral_iUnion`), translates each cell piece to the fundamental cell (`cellPiece`,
  measure-preserving translation), and uses pairwise disjointness of the pieces, `⋃ ⊆ [0,1)^n × G`, Tonelli and
  `volume [0,1)^n = 1`.
- Disjointness of the pieces uses `avgFlow_translate` and injectivity of the flow on Ω_t. Two points of D lie in the same
  half-open initial cell, so the integer shift is zero.
- No global flow-domain assumption. Local instance `avgPhase_isAddHaar` (product Haar instance for `volume` on `AvgPhase n`;
  Mathlib does not infer it).

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n1213 KAM.Nekhoroshev.Averaging.Transport`: Build completed successfully; only warning in
  my file is the unused `ht`.
- `sh scripts/lint_sources.sh`: passes (FROZEN-ANCHOR GUARD OK; ABI HASHES OK, 144 frozen declarations).
- `#print axioms KAM.Nekhoroshev.transport`: [propext, Classical.choice, Quot.sound]; same for
  `lintegral_le_of_disjoint_cellPieces`.

**Uncertainties / errata / deviations:** none. No heartbeat issues. The statement is not under-hypothesised.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-13 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (transport, avgCell; disjoint translated image pieces, NO global flow-domain assumption); (2) proofs sound (change of variables, Tonelli, translation invariance); no added premises; (3) hygiene. Audit ONLY the Transport module(s) (compare with branch inp-n1210b).
