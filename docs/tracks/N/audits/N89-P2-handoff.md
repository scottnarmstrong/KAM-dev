# N89-P2 prover handoff (branch inp-n89p2, d43b651; contains inp-n89p1 (N89-P1, audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- New: `KAM/Nekhoroshev/Poschel/Frequency.lean` (≈415 lines). No other file touched.
  `KAM.lean` was NOT edited; `scripts/lint_sources.sh` reports "KAM.lean is out of date" solely because this new
  module is not yet in the generated root (orchestrator regenerates it).

## Declarations (signatures copied verbatim from N89Signatures.lean; mechanically compared, all identical)
`m_le_M`, `local_real_regularity`, `FrequencyBall`, `FrequencyBall.points`, `FrequencyBall.maximum`,
`frequency_maximum`, `omega0_radius`, `omega0Ball`, `omega0`. No `blockBall` (P3).
Private helpers (not API): `im_eq_zero_of_realOn`, `contDiffOn_realPart`, `real_fderiv`, `freq_eq`,
`freq_deriv`, `freq_bound`, `hessR_eq_dot`, `freq_lip`, `euclid_ofReal`, `euclid_sq_real`.

## Approach
- Reality of `h` on real points of `V_{r0}P` from `S.real` via `realInclusion₂_mem_Dom_iff`; holomorphic regularity
  (`KAM.holomorphic_regularity[_of_finiteDimensional]`) restricted to ℝ gives `C²` of `realPart h` on `U_{r0}P`.
- `real_fderiv` (adapted from the local argument of `holo_real_b/c`, not the `Data`-specialised theorems):
  `D(Re g) e = Dg(ι e)`. Applied to `g = h` (frequency = complex gradient) and to `g_i = ∂_i h`
  (derivative of frequency map; mixed-partial symmetry via `fderiv_apply_comm_of_differentiableOn`).
  `freq_deriv` packages `L = D(frequencyMap h)(I)` with its complex formula and real-Hessian formula.
- `m_le_M`: pick `I ∈ P`, nonzero `ξ ⟂ ω(I)` (n ≥ 2), QC first disjunct excluded by `0 ≤ ell`,
  `m|ξ|² ≤ Q[ξ,ξ] = ξ·Lξ ≤ |ξ||Lξ| ≤ M|ξ|²`, divide by `|ξ|² > 0`. Uses neither `hmM`, `0<m`, `0<M`.
- `frequency_maximum`: ball ⊆ `U_{r0}P` (max norm ≤ Euclid < r0), closed+bounded ⇒ compact, continuity from
  local regularity, `IsCompact.exists_isMaxOn`, `IsGreatest.csSup_eq`; M-radius bound by a scalar mean-value
  argument on `t ↦ F·ω(c + t(I-c))` with `F = ω(I)-ω(c)` and Cauchy–Schwarz (no EuclideanSpace).
- `omega0_radius`: `11 ≤ thmA m M` (own 3-line proof; Elementary's lemma is private).

## Checks
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-n89p2 KAM.Nekhoroshev.Poschel.Frequency`:
  `Build completed successfully (3219 jobs)`, no warnings from this file, no `sorry`.
- `sh scripts/lint_sources.sh`: line-length, module check PASS (452 files), FROZEN-ANCHOR GUARD OK,
  ABI HASHES OK; only the expected "KAM.lean is out of date" line.
- `grep sorry|maxHeartbeats|axiom` in the file: empty.
- `#print axioms` for `m_le_M`, `local_real_regularity`, `frequency_maximum`, `omega0_radius`, `omega0`,
  `FrequencyBall.maximum`: all `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / design signals
- None: no heartbeat problem; every proof elaborates at default heartbeats.
- `ω` is notation (`ℕ∞ω`) under `open scoped ContDiff`; avoided as a variable name.

## Suspected errata / deviations
- None found. No signature changed; no hypotheses added.

AUDIT FOCUS (design docs/tracks/N/design/N89-LEAN-DESIGN.md row N89-P2 and proof plan; audits DESIGN-N89-design-audit-{1,2}.md; signatures .drafts/design/N89Signatures.lean): (1) statements = design signatures and blueprint (local regularity, m_le_M, all maximum definitions/theorems; no blockBall here); (2) proofs sound (holomorphic regularity, scalar restriction, compact maximum used correctly); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Nekhoroshev/Poschel/Frequency.lean (compare with branch inp-n89p1).
