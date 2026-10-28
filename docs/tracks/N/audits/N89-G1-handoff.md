# N89-G1 prover handoff (branch inp-n89g1, 3bc8106; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/ResonanceGeometry/Lattice.lean` (216 lines). Nothing else changed (KAM.lean not regenerated; lint reports it out of date as expected).

**Declarations (signatures verbatim from N89Signatures.lean):** `Lattice, lattice, latticeDim, integerReal, eBall, resonance, basisMatrix` (defs); theorems `integer_independent_real` (bpN:p8:ext-indep), `lattice_basis`, `lattice_resonance` (bpN:p8:lattice), `lattice_basis_change`, `lattice_basis_sub` (bpN:p8:lattice-basis); def `latticeBasis`. Imports upstream `resSpan` (Stability.Gradient), `resSpace` (Stability.Energy), Interfaces.Norms; no provider / frozen theorem.
Extra public helper lemmas (not in signature file): `integerReal_injective`, `integerReal_mem_lattice`, `basis_val_linearIndependent`, `basis_real_linearIndependent`, `basisMatrix_apply_repr`, `basis_span_eq`, `basis_card_eq_latticeDim`, `exists_basis`, `basisMatrix_eq_mul`.

**Approach:** `integer_independent_real` is Mathlib `linearIndependent_algebraMap_comp_iff` (ℤ→ℝ, ℤ a domain, faithful). Existence of bases: `Submodule.basisOfPid` on `toIntSubmodule`, transported by `AddEquiv.refl.toIntLinearEquiv`. Basis real-span = `lattice Λ` via `Basis.sum_repr`; finrank via `finrank_span_eq_card`. `lattice_resonance` by `span_induction`; rank 0 iff ⊥ via `Submodule.finrank_eq_zero`. Basis change: `U = b.toMatrix c`, unit det via `Basis.isUnit_det`; converse via `LinearEquiv.ofIsUnitDet` and `Basis.map`. Sub-lattice: `N` = coordinates of `c j` in `b`; `det N ≠ 0` because a real kernel vector of N would be killed by the real-independent columns of `basisMatrix c`.

**Checks:** `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-n89g1 KAM.Nekhoroshev.ResonanceGeometry.Lattice` → "Built ... Build completed successfully" (no warnings in my file). `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message "KAM.lean is out of date" (generated, not edited). `#print axioms` of all five theorems: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations:** none. No statement needed changing; no heartbeat issues (build ≈ 8 s). Signature file's extra `open KAM.Weighted KAM.Canonical` omitted (unused).

AUDIT FOCUS (design docs/tracks/N/design/N89-LEAN-DESIGN.md row N89-G1 and its proof plan; audits DESIGN-N89-design-audit-{1,2}.md; signatures .drafts/design/N89Signatures.lean; blueprint-N p8/p9 resonance-lattice nodes): (1) statements = design signatures and blueprint (lattice/rank/bases, integer_independent_real); (2) proofs sound (PID/free-module API used correctly); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N89-G1 module(s) (KAM/Nekhoroshev/ResonanceGeometry/Lattice*).
