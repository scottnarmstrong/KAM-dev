# N89-G4 prover handoff (branch inp-n89g4, 68cc498; base inp-n89g3; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/ResonanceGeometry/Maximal.lean` (≈312 lines). No other file touched (KAM.lean not regenerated; lint reports "KAM.lean is out of date", orchestrator to run gen_root_imports.py).

**Nodes:** `klattice`, `maximalK`, `maximal` (all 10 conjuncts, verbatim signature), imports only `ResonanceGeometry.Volume`.
Extra helpers (names new, no premises beyond the obvious): `eBall_finite`, `klattice_finite` (finiteness: set of K-lattices is finite, hence also of maximal ones, for G5's `blocks_cover`), `klattice_short_basis` (K-lattice has ℝ-independent family of `latticeDim Λ` generators in Λ ∩ eBall), `volume_le_of_klattice` (vol ≤ K^dim for any K-lattice, via short sublattice + `volume_mono` + Hadamard), `mem_of_maximalK`, `maximalK_of_forall`, `maximalK_bot`, `exists_maximalK_above`, `klattice_addVector`, `klattice_top`, `lattice_le_iff`, `lattice_mono`, `units_top`, etc.

**Approach:** eBall ⊆ coordinate box ⇒ finite; klattices injectively determined by Λ ∩ eBall ⇒ finite; maximal element of finite nonempty set for existence; saturation characterization via addVector and equal-rank span equality; short basis by extracting an independent subset from the spanning set integerReal '' (Λ ∩ eBall).

**Checks:** `inp_lake_build.sh … KAM.Nekhoroshev.ResonanceGeometry.Maximal` succeeds (only warning: unused `hK` in `maximal`; the hypothesis is kept as the verbatim signature; statement holds for every K). `#print axioms` of `maximal`, `klattice_finite`, `klattice_short_basis`, `volume_le_of_klattice`: propext, Classical.choice, Quot.sound only. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only note is KAM.lean out of date (not mine to edit). No sorry/axiom, no heartbeat options, file ≪1500 lines.

**Uncertainties / errata / deviations:** none. Signatures unchanged; no design signals.

AUDIT FOCUS (design docs/tracks/N/design/N89-LEAN-DESIGN.md row N89-G4 and proof plan; audits DESIGN-N89-design-audit-{1,2}.md; signatures .drafts/design/N89Signatures.lean): (1) statements = design signatures (klattice, maximalK, finiteness, all maximal parts, the short independent generating sublattice); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY ResonanceGeometry/Maximal*.lean.
