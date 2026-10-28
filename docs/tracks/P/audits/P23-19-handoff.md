# P23-19 prover handoff (branch inp-p2319, 98b67de; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/TwoScale/RealDynamics.lean` (~160 lines). KAM.lean not edited (lint reports it out of date, as expected; the orchestrator regenerates it).

**Declarations (signatures verbatim, only line-wrapped):**
- `KAM.Planetary.real_curve_limit` (`stepP:p3:inv-lim`, gap G5): Mathlib `hasDerivAt_of_tendsto_locally_uniformly_on'` on `univ`; the pointwise limit comes from `hc`, differentiability from `hx`. `hv` (continuity of v) is unused. The statement is verbatim, so it stays; the linter warns about it (harmless).
- `KAM.Planetary.real_symplectic_conjugation` (`stepP:p3:inv-conj`, gap G4):
  - symplectic derivative gives injective, hence bijective (finite dim), so strict derivative and `HasStrictFDerivAt.map_nhds_eq_of_equiv` show `Ψ '' V` is a neighbourhood of every image point, so it is open;
  - the real derivative of `Ψr` is restricted via `ι ∘ DΨr = DΨ ∘ ι`;
  - `KAM.hamiltonianVectorField_eq_of_real` is applied to `G` on `Ψ '' V` and to `G ∘ Ψ` on `V`;
  - `Canonical.map_hamiltonianJ_comp` closes the identity.
  - No conjugation premise assumed.
- private helpers: `bijective_of_sympl`, `image_mem_nhds_of_sympl`.

**Checks:**
- `inp_lake_build.sh ... KAM.Planetary.TwoScale.RealDynamics` succeeded; only warning is the unused `hv`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message is "KAM.lean is out of date".
- `#print axioms` of both theorems: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties:** none. No heartbeat issues (build ~8s). No errata or deviations.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-19 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean): (1) statements = design signatures (real_symplectic_conjugation, real_curve_limit (pays design gaps G4/G5 exactly as the design states; no new premise)); (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the P23-19 module(s) (KAM/Planetary/TwoScale/RealDynamics*).
