# N89-G3 prover handoff (branch inp-n89g3, 0d95056; contains inp-n89g2 (N89-G1, N89-G2, audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/ResonanceGeometry/Volume.lean` only (branch inp-n89g3). KAM.lean not touched
(lint reports "KAM.lean is out of date" — generated root import; orchestrator must regenerate).

**Nodes proved (signatures verbatim, no changes, no extra hypotheses):** `gram`, `volume_def`, `addVector`,
`lattice_volume` (all 7 conjuncts), `lattice_volume_index`, `lattice_volume_cyclic`, `lattice_volume_hadamard`.
Extra helpers (all in namespace KAM.Nekhoroshev): gram_eq_map, gram_det_eq, gramZ_det_mul, gramZ_det_pos,
gramZ_det_basis_change, volume_sq_eq, volume_nonneg/_sq_int/one_le_volume/_bot/_top/_mono, topBasis,
snocCol, det_gram_snoc_orth, shearMat, det_shearMat, snocCol_mul_shear, det_gram_snoc_shear,
integer_independent_of_real, closureBasis (+ basisMatrix_/latticeDim_/lattice_closure_range), basis_closure_eq,
addVector_eq_closure_snoc, snoc_independent, addVector_facts.

**Approach:** basis independence and the index formula via integer determinant det(AN)ᵀ(AN)=det(N)²det(AᵀA)
and unimodular change (lattice_basis_change); positivity via Matrix.PosDef.conjTranspose_mul_self; ⊥/⊤ via
empty determinant / standard basis; monotonicity from lattice_basis_sub + index formula; addVector: explicit
Z-basis Fin.snoc of latticeBasis with k (closureBasis), real unitriangular shear replacing k by compProj, and
Laplace expansion on the last row of the block-diagonal Gram (Schur step), using proj ∈ span and
compProj ⊥ lattice from G2 (`projection`); cyclic via closureBasis on one vector; Hadamard by induction on d
with the addVector formula and ‖compProj‖ ≤ ‖·‖.

**Checks:** gate build `inp_lake_build.sh ... KAM.Nekhoroshev.ResonanceGeometry.Volume`: "Build completed
successfully" (no warnings in Volume.lean). `scripts/lint_sources.sh`: line-length, module check, frozen guard,
ABI hashes PASS; only message is "KAM.lean is out of date". No sorry/axiom/maxHeartbeats.
`#print axioms` of lattice_volume, lattice_volume_index, lattice_volume_cyclic, lattice_volume_hadamard:
all `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations / design signals:** none. No statement was false or under-hypothesised.
No heartbeat problems; the heaviest file elaborates in a few seconds.

AUDIT FOCUS (design docs/tracks/N/design/N89-LEAN-DESIGN.md row N89-G3 and proof plan; audits DESIGN-N89-design-audit-{1,2}.md; signatures .drafts/design/N89Signatures.lean): (1) statements = design signatures (volume_def, the full lattice_volume, index/cyclic/Hadamard companions); (2) proofs sound (Gram/Schur facts used correctly); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Nekhoroshev/ResonanceGeometry/Volume*.lean (compare with branch inp-n89g2).
