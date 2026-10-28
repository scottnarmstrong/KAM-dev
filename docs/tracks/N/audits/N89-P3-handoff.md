# N89-P3 prover handoff (branch inp-n89p3, 8ef61bd; contains inp-n89g7 and inp-n89p2 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**File (new):** KAM/Nekhoroshev/Poschel/BlockHypotheses.lean (375 lines). Branch inp-n89p3. No other file touched.

**Declarations (signatures copied verbatim; checked by whitespace-normalised text diff against N89Signatures.lean):**
`full_rank_zone`, `block_frequency_radius`, `blockBall`, `blockAdm`, `local_field`, `block_hyp`.
Private helpers: tube inclusions (`polyNbhd_single_sub`, `realNbhd_single_sub`, `realStrip_single_sub`, `Dom_single_sub`,
`inClass_single`, `realOn_single`), `fderiv_freq_bound`, `im_eq_zero_single`, `dotC_realInclusion`, `cover_valid`, `block_arith`.

**Approach.**
- `cover_valid`: last conjunct of `elementary`. Radius/alpha/delta facts from `CoverParams.Valid.radius_bounds`, `radius_nonneg`, `one_le_volume`.
- `block_arith` (pure real arithmetic of block_hyp: positivity, `eps ≤ m r²/2^10` from `radius ⊥ ≤ r` and `eps = m(r0/(AK)^n)²/2^10`,
  the `9/8` identities via `√n·Ka = K`, `r ≤ r0 ≤ 4ell/m`, `M r ≤ ell/2` from S.radius, and the Λ=⊥ bound from `m ≤ M ≤ M√n`).
- Nonresonance: `freq_realInclusion` converts to the real frequency, `dotC_realInclusion` to `integerReal k ⬝ᵥ ω`, then `cutoffs` (3rd conjunct).
  Close-to-resonance: `projection_distance` (compProj ∈ resonance, distance = resonanceDistance) + `cutoffs` (4th conjunct, which covers Λ=⊥).
- Lipschitz: `KAM.NormalForm.lipschitz` with `fderiv_freq_bound` (Hessian symmetry via `fderiv_apply_comm_of_differentiableOn`, Euclid→max costs √n once, L = √n M).
- `full_rank_zone`: `lattice ⊤ = ⊤` by finrank, `proj = id`, `zoneStratum (n+1) = ∅`, `lam n / vol ⊤ = m r0/8`.
- `local_field`: open strip (`isOpen_univ.prod isOpen_realNbhd`); the indicator equals the Hamiltonian on a neighbourhood, so `fderiv`s agree (`EventuallyEq.fderiv_eq`). Local, never global equality.

**Checks.**
- `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89p3 KAM.Nekhoroshev.Poschel.BlockHypotheses` → "Build completed successfully (3235 jobs)"; only warnings are unused-variable `S` (local_field) and `hr` (local_field), both forced by the verbatim signature.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS (553 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK. It prints "KAM.lean is out of date; run scripts/gen_root_imports.py" — expected (new module not yet in the generated root; I did not edit KAM.lean per instructions; the orchestrator must regenerate).
- grep: no sorry / maxHeartbeats / axiom in the file.
- `#print axioms` for full_rank_zone, block_hyp, block_frequency_radius, blockBall, blockAdm, local_field: each `[propext, Classical.choice, Quot.sound]`.

**Imports:** Poschel.Setting/Elementary/Frequency, ResonanceGeometry.Covering, NormalForm.Setting, Strip.Bridges. No provider / DRAFT_SORRY import.

**Uncertainties / deviations.** None: no statement needed changing, no extra hypothesis. No heartbeat issues (all default). Notes: `S` and `hr` of `local_field` are unused in the proof (hr could be dropped, but the signature is frozen by the design). `block_hyp` does not need `hfb` beyond restriction of WBound.

**Suspected errata.** None.

AUDIT FOCUS (design docs/tracks/N/design/N89-LEAN-DESIGN.md row N89-P3 and proof plan; audits DESIGN-N89-design-audit-{1,2}.md; signatures .drafts/design/N89Signatures.lean): (1) statements = design signatures (block_hyp, full_rank_zone, block radius guards, blockBall, local_field, blockAdm); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY Poschel/BlockHypotheses*.lean (compare with branch inp-n89g7).
