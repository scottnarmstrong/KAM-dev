# S10-W prover handoff (branch inp-s10w, 3aa0f5c; contains inp-s9n (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Nondegeneracy/Weyl.lean` (173 lines). Branch inp-s10w, committed. KAM.lean not edited
(lint reports "KAM.lean is out of date"; the orchestrator regenerates it).

**Declarations:** `KAM.Planetary.Nondegeneracy.weyl` (`bpP:p10:weyl`), signature verbatim from P810Signatures.lean.
Helpers in `SecularSpectrum`: `exists_eigenframe`, `sorted_mono`, `abs_dot_mulVec_le`, and the min-max subspace
helper `sorted_le_of_quad_le`.

**Approach:** no Courant-Fischer. `exists_eigenframe` builds the sorted-index orthonormal frame from Mathlib's
`eigenvectorUnitary` and spectral theorem (matrix level; no EuclideanSpace, as the lint forbids it), giving Parseval
and the diagonal quadratic form. `sorted_le_of_quad_le`: if `xᵀBx ≤ xᵀCx + t|x|²` for all x then
`sorted B i ≤ sorted C i + t`. It uses a linear map `Vec n → ({j // j ≠ i} → ℝ)` (kills the B-coordinates `j<i` and
the C-coordinates `j>i`); its kernel is nonzero by `ker_ne_bot_of_finrank_lt`, and on a kernel vector
`b_i|x|² ≤ xBx ≤ xCx + t|x|² ≤ (c_i+t)|x|²`. `weyl` applies this both ways with `t = op2 E`, using
`|xᵀEx| ≤ op2 E |x|²` (Cauchy-Schwarz plus `length2_mulVec_le_op2`).

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-s10w KAM.Planetary.Nondegeneracy.Weyl`: success; the only warning in my file is the
  unused binder `hE` in `weyl` (the signature is verbatim, so it is kept).
- `scripts/lint_sources.sh`: the only complaint is "KAM.lean is out of date"; check_lean_modules PASS, frozen-anchor
  guard OK, ABI hashes OK.
- `#print axioms` for `Nondegeneracy.weyl` and `SecularSpectrum.sorted_le_of_quad_le`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties:** none; the statement was true as written. **Errata/deviations:** none. **Design signals:** none
(default heartbeats, file far under the cap).

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S10-W and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures (weyl, the min-max subspace helper); (2) proofs sound (matrix spectral theorem); no added premises; (3) hygiene. Audit ONLY Nondegeneracy/Weyl*.lean (compare with branch inp-s9n).
