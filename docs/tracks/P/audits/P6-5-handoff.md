# P6-5 prover handoff (branch inp-p65, 1548226; contains inp-pp17 (PP1-7, delivered) and P6-3/P6-4 via inp; offloaded package run by the main orchestrator; prover on claude-12)


Hard rules honoured: no `set_option` (no maxHeartbeats), file 156 lines (<1500), module header, no sorry/axiom.

## Files
- NEW `KAM/Planetary/Newtonian/Assembly.lean` (only file touched). KAM.lean NOT edited (needs regeneration by the orchestrator).

## Nodes / declarations (statements verbatim from KeplerSignaturesP.lean)
- measure-positive (a): `KAM.Planetary.circularTube_norm_lt`, `volume_lt_top_of_subset_circularTube`
  (bounded via `pi_norm_le_iff_of_nonneg` on the circular point, then `Bornology.IsBounded.measure_lt_top`).
- measure-positive (b): NOT re-declared. Part 1's `KAM.Planetary.measure_chart_image`
  (`KAM/Planetary/Hamiltonian/Liouville.lean`) is the delivered declaration; its signature matches the
  design's D17 restatement verbatim. Assembly does not import Liouville (no need); `#print axioms` checked below.
- movkol-assembly: `movingKolmogorovSet_of_tube`; fixkol-assembly: `fixedKolmogorovSet_of_tube`
  (tube inclusion + `circularTube_mono` for the frozen `S ⊆ circularTube ... η`; `circularTube_pair_bounds`
  for NoCollision; `orbit_transfer_moving/_fixed`; `circularTube_pairBounds_barycentric/_fixed`).
- Hypotheses `hn`, `hG` (fixed), `hG`/`hm0` (norm_lt) are unused in the proofs (kept as in the signatures, silenced with `have _ :=`).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-p65 KAM.Planetary.Newtonian.Assembly`: Build completed successfully, no warning in Assembly.lean
  (only pre-existing unused-variable warnings in KAM/Kepler/Energy.lean).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS (427 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK (144).
  Two notes, neither mine: "KAM.lean is out of date" (expected; orchestrator regenerates), and a pre-existing
  >100-char line at Liouville.lean:35:108 (PP1-7).
- `#print axioms` for circularTube_norm_lt, volume_lt_top_of_subset_circularTube, movingKolmogorovSet_of_tube,
  fixedKolmogorovSet_of_tube, measure_chart_image: all `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations
- None: no statement was changed; no suspected source errata; no heartbeat issues (build ~6 s).

AUDIT FOCUS (Kepler/Delaunay design docs/tracks/P/design/KEPLER-LEAN-DESIGN.md row P6-5, section 7.1 and its Part 1 dependency section; its audits; blueprint-P measure-positive (a)(b), movkol-assembly, fixkol-assembly): (1) statements = design signatures and blueprint; measure-positive (b) consumes Part 1's measure_chart_image (not a re-declaration); (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the P6-5 module(s) (KAM/Planetary/Newtonian/Assembly* or as named in the handoff).
